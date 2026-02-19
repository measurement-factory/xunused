#include "clang/AST/AST.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Basic/Version.h"
#include "clang/Driver/Options.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Index/USRGeneration.h"
#include "clang/Tooling/AllTUsExecution.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/CompilationDatabase.h"
#include "llvm/Support/Signals.h"
#include <list>
#include <memory>
#include <mutex>
#include <map>
#include <unordered_set>


using namespace clang;
using namespace clang::ast_matchers;

class DefInfo;

using OverridenUSRs = std::unordered_set<std::string>;
using AllDeclarations = std::map<std::string, DefInfo>;
using ClassDeclarations = std::map<std::string, bool>;
using ClassDeclarationsIterator = ClassDeclarations::const_iterator;
using AllDeclarationsIterator = AllDeclarations::iterator;
using DeclarationsList = std::list<AllDeclarationsIterator>;

ClassDeclarations ClassDecls;
bool getUSRForDecl (const Decl *F, std::string &USR);

template <class T, class Comp, class Alloc, class Predicate>
void discard_if(std::set<T, Comp, Alloc> &c, Predicate pred) {
  for (auto it{c.begin()}, end{c.end()}; it != end;) {
    if (pred(*it)) {
      it = c.erase(it);
    } else {
      ++it;
    }
  }
}

struct DeclLoc {
  DeclLoc() = default;
  DeclLoc(const FunctionDecl *F, const SourceManager &SM) {
    auto range = F->getSourceRange();

    // expand to include 'template<...>' if it exists
    if (clang::FunctionTemplateDecl *TD = F->getDescribedFunctionTemplate())
        range = TD->getSourceRange();

    // Resolve macros to the "File" level (where the macro is called, not
    // where it is defined). Without that Begin and End may even point
    // to different files!
    const auto Begin = SM.getFileLoc(range.getBegin());
    const auto End = SM.getFileLoc(range.getEnd());

    FirstLine = SM.getSpellingLineNumber(Begin);
    LastLine = SM.getSpellingLineNumber(End);
    Filename = SM.getFilename(Begin).str();
    assert(!Filename.empty());
    SM.getFileManager().makeAbsolutePath(Filename);
    // normalize paths
    llvm::sys::path::remove_dots(Filename, true);

    const auto &context = F->getASTContext();
    if (const auto RC = context.getRawCommentForDeclNoCache(F)) {
        clang::SourceRange cRange = RC->getSourceRange();
        const auto cBegin = SM.getFileLoc(cRange.getBegin());
        const auto cEnd = SM.getFileLoc(cRange.getEnd());

        CommentFirstLine = SM.getSpellingLineNumber(cBegin);
        CommentLastLine = SM.getSpellingLineNumber(cEnd);
        assert(CommentFirstLine);
        assert(CommentLastLine);
        assert(CommentFirstLine <= CommentLastLine);

        // proximity check: function must follow the comment with no empty lines
        // between them
        if (FirstLine <= CommentLastLine || (FirstLine - CommentLastLine) > 1) {
            CommentFirstLine = 0;
            CommentLastLine = 0;
        }
    }
  }
  bool operator==(const DeclLoc& other) const {
    return Filename == other.Filename &&
           FirstLine == other.FirstLine &&
           LastLine == other.LastLine;
  }
  SmallString<128> Filename;
  unsigned FirstLine = 0;
  unsigned LastLine = 0; // same as FirstLine for single-line code
  unsigned CommentFirstLine = 0;
  unsigned CommentLastLine = 0;
};

struct DeclLocHash {
    size_t operator()(const DeclLoc& fr) const {
      return llvm::hash_combine(fr.Filename, fr.FirstLine, fr.LastLine);
    }
};

bool IsSpecialMember(const FunctionDecl *F)
{
    if (const auto *MD = dyn_cast<CXXMethodDecl>(F)) {
        if (dyn_cast<CXXConstructorDecl>(MD)) {
            // a specific constructor type may be checked by CD->isCopyConstructor()) and CD->isCopyConstructor()
            return true;
        }
        if (isa<CXXDestructorDecl>(MD))
            return true;

        if (MD->isCopyAssignmentOperator())
            return true;

        if (MD->isMoveAssignmentOperator())
            return true;
    }
    return false;
}

void HandleSpecialMember(const FunctionDecl *F, const bool used) {
    if (!IsSpecialMember(F))
        return;
    const auto classDecl = dyn_cast<CXXMethodDecl>(F)->getParent();
    assert(classDecl);
    std::string USR;
    if (!getUSRForDecl(classDecl, USR))
        return;
    auto it = ClassDecls.find(USR);
    if (it == ClassDecls.end())
        ClassDecls.emplace(USR, used);
    else if (used)
        it->second = used;
}

// Converts, e.g., SomeType<int>::print	to SomeType::print
std::string RemoveTemplateFromMember(const FunctionDecl *F) {
    if (const auto *MD = dyn_cast<CXXMethodDecl>(F)) {
        const CXXRecordDecl *Parent = MD->getParent();
        if (auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(Parent)) {
            // Get the 'T' from 'T<int>'
            std::string ClassName = Spec->getSpecializedTemplate()->getNameAsString();
            return ClassName + "::" + MD->getNameAsString();
        }
    }
    return F->getQualifiedNameAsString();
}

struct DefInfo {
  // Use this constructor when you find a use of a never-seen-before function
  explicit DefInfo() {}

  // Use this constructor when you find a declaration or a definition of a never-seen-before function
  explicit DefInfo(const FunctionDecl * const F)
    : Uses(0), Name(RemoveTemplateFromMember(F)), specialMember(IsSpecialMember(F)) {
        addClassReference(F);
  }

  bool sawDefinition() const { return !Definitions.empty(); }
  void addDeclarationsAndDefinitions(const FunctionDecl *F, const SourceManager &SM) {
    if (Name.empty()) {
        Name = RemoveTemplateFromMember(F);
        specialMember = IsSpecialMember(F);
        addClassReference(F);
    }
    for (const FunctionDecl *R : F->redecls()) {
      if (!R->getLocation().isValid()) {
        continue; // no physical file representation
      }
      auto &ds = R->doesThisDeclarationHaveABody() ? Definitions : Declarations;
      ds.insert({R, SM});
    }
  }
  void addUses(const unsigned uses) {
      if (base)
          base->addUses(uses);
      else
          Uses += uses;
  }
  void addBase(DefInfo *info) {
      assert(info);
      if (info != this && !base)
          base = info;
  }
  unsigned getUses(const bool handleSpecialMembers) const {
      if (handleSpecialMembers && specialMember) {
          assert(classRef != ClassDecls.end());
          return classRef->second;
      }
      return base ? base->getUses(handleSpecialMembers) : Uses;
  }

  void addClassReference(const FunctionDecl *F) {
    if (const auto *MD = dyn_cast<CXXMethodDecl>(F)) {
        const auto classDecl = MD->getParent();
        assert(classDecl);
        std::string USR;
        if (!getUSRForDecl(classDecl, USR))
            return;
        classRef = ClassDecls.find(USR);
        assert(classRef != ClassDecls.end());
    }
  }

  size_t Uses = 0;
  std::string Name;
  std::unordered_set<DeclLoc, DeclLocHash> Declarations;
  std::unordered_set<DeclLoc, DeclLocHash> Definitions;
  DefInfo *base = nullptr; // the base virtual definition
  ClassDeclarationsIterator classRef = ClassDecls.end();
  bool specialMember = false;
};

std::mutex Mutex;
AllDeclarations AllDecls;

bool getUSRForDecl (const Decl *D, std::string &USR) {
    const Decl *Target = D;

    if (const auto MD = dyn_cast<CXXMethodDecl>(D)) {
        // matches the template definition (SomeType<T>::find<U>())
        // or template <typename T> template <> void SomeType<T>::find<int>()
        if (const auto FTD = MD->getDescribedFunctionTemplate()) {
            Target = FTD;
        }
        // matches a specific instantiation of a template method
        // SomeType::find<int>() -> SomeType::find<U>() or
        // SomeType<double>::find<int>() -> SomeType<double>::find<U>()
        // The remaining class type (double) is stripped below (Parent class template block)
        else if (const auto FTD = MD->getPrimaryTemplate()) {
            Target = FTD;
        }
        // matches a member of a template class
        // e.g., SomeType<int>::parse() -> SomeType<T>::parse()
        else if (const auto Pattern = MD->getInstantiatedFromMemberFunction()) {
            Target = Pattern;
        }

        // Handle Parent class template
        // E.g., SomeType<int>
        const CXXRecordDecl *Parent = MD->getParent();
        // go further if Parent is a template
        if (const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(Parent)) {
            // Jump from SomeType<int> to the generic template SomeType<T>
            ClassTemplateDecl *PrimaryClassTemplate = Spec->getSpecializedTemplate();
            CXXRecordDecl *ClassPattern = PrimaryClassTemplate->getTemplatedDecl();

            // Find the method inside the PRIMARY class pattern
            // This is the "uninstantiated" version of the function.
            auto Lookups = ClassPattern->lookup(MD->getDeclName());
            for (NamedDecl *ND : Lookups) {
                // it's a template member function
                if (auto *FTD = dyn_cast<FunctionTemplateDecl>(ND)) {
                    Target = FTD;
                    break;
                }
                // it's a normal member function in a template class
                if (auto *Method = dyn_cast<CXXMethodDecl>(ND)) {
                    Target = Method;
                    break;
                }
            }
        }
    } else if (const auto F = dyn_cast<FunctionDecl>(D)) {
        if (F->isTemplateInstantiation())
            Target = F->getTemplateInstantiationPattern();
    }

    assert(Target);

    llvm::SmallVector<char, 128> Buff;
    if (clang::index::generateUSRForDecl(Target, Buff)) {
        return false;
    }
    USR = std::string(Buff.data(), Buff.size());
    return true;
}

// Whether this is a compiler-generated function, including a method of a
// compiler-generated class.
static
bool isCompilerGenerated(const FunctionDecl * const f) {
  if (f->isImplicit())
    return true;

  // LLVM does not automatically mark every member of an isImplicit() class as
  // isImplicit(). For example, isImplicit() is false for generated lambda
  // operators (i.e. members of an isImplicit() "closure type" class). We assume
  // that all methods of an implicit class were generated by the compiler.
  if (const auto method = dyn_cast<CXXMethodDecl>(f)) {
    if (const auto parent = method->getParent()) {
      if (parent->isImplicit())
        return true;
    }
  }

  return false;
}

// whether this method belongs to a class inherited from an external library class
static
bool externalBase(const CXXMethodDecl *MD, const SourceManager &SM) {
    const auto parent = MD->getParent();
    assert(parent);
    if (!parent->hasDefinition() || !parent->getNumBases())
        return false;
    bool foundLibraryBase = false;
    const auto v = parent->forallBases([&](const CXXRecordDecl *base) {
            const auto loc = base->getLocation();
            // Check if the base class is defined in a system header
            if (SM.isInSystemHeader(loc)) {
                foundLibraryBase = true;
                return false; // stop searching
            }
            return false; // continue searching other bases;
    });
    return foundLibraryBase;
}

class FunctionDeclMatchHandler : public MatchFinder::MatchCallback {
public:
  void finalize(const SourceManager &SM) {
    std::unique_lock<std::mutex> LockGuard(Mutex);

    for (const auto declaration: Defs) {
      std::string USR;
      if (!getUSRForDecl(declaration, USR))
        continue;

      const auto F = declaration->getDefinition();
      assert(F);
      auto [it, success] = AllDecls.try_emplace(USR, DefInfo(F));
      it->second.addDeclarationsAndDefinitions(F, SM);
      DeclarationsList overridenList{it};
      handleOverridenMethods(F, it->second, overridenList);
      // llvm::errs() << "saw definition: " << declaration->getNameAsString() << " USR: " << it_inserted.first->first <<
      //    " definitions: " << it_inserted.first->second.Definitions <<
      //    " uses: " << it_inserted.first->second.Uses << "\n";
    }

    for (const auto pair: Uses) {
      const auto F = pair.first;
      std::string USR;
      if (!getUSRForDecl(F, USR))
        continue;
      auto [it, success] = AllDecls.try_emplace(USR, DefInfo());
      DeclarationsList overridenList{it};
      handleOverridenMethods(F, it->second, overridenList);
      it->second.addUses(pair.second);
    }
      // llvm::errs() << "saw usage: " << F->getNameAsString() << " USR: " << it_inserted.first->first <<
      //    " definitions: " << it_inserted.first->second.Definitions <<
      //    " uses: " << it_inserted.first->second.Uses << "\n";
  }

  void handleOverridenMethods(const FunctionDecl *F, DefInfo &info, DeclarationsList &overridenList) {
      if (const auto *MD = dyn_cast<CXXMethodDecl>(F)) {
          if (MD->size_overridden_methods()) {
            for (const auto method: MD->overridden_methods()) {
                const auto canonicalMethod = method->getCanonicalDecl();
                std::string overridenUSR;
                if (!getUSRForDecl(canonicalMethod, overridenUSR))
                    continue;
                auto [it, success] = AllDecls.try_emplace(overridenUSR, DefInfo(canonicalMethod));
                overridenList.push_back(it);
                handleOverridenMethods(canonicalMethod, it->second, overridenList);
            }
          } else {
              if (overridenList.size() < 2)
                  return; // already added by the caller
              for (const auto &def : overridenList) {
                  def->second.addBase(&info);
              }
          }
      }
  }

  void handleUse(const ValueDecl *D, const SourceManager *SM) {
    auto *FD = dyn_cast<FunctionDecl>(D);
    if (!FD)
      return;

    if (const auto MD = dyn_cast<CXXMethodDecl>(D)) {
      if (externalBase(MD, *SM))
          return;
    }

    HandleSpecialMember(FD, true);

    if (isCompilerGenerated(FD))
        return;

    // ignore uses of declarations mentioned in a system header
    if (SM->isInSystemHeader(FD->getSourceRange().getBegin()))
      return;

#if 0
    llvm::errs() << "Use ";
    FD->printName(llvm::errs());
    //llvm::errs() << " USR:" << USR;
    llvm::errs() << "\n";
#endif
     auto [it, success] = Uses.try_emplace(FD->getCanonicalDecl(), 1);
     if (!success) {
         it->second++;
     }
  }
  void run(const MatchFinder::MatchResult &Result) override {
    if (const auto *F = Result.Nodes.getNodeAs<FunctionDecl>("fnDecl")) {

      if (!F->hasBody())
        return; // Ignore '= delete' and '= default' definitions.

      auto Begin = F->getSourceRange().getBegin();
      if (Result.SourceManager->isInSystemHeader(Begin))
        return;

      auto *MD = dyn_cast<CXXMethodDecl>(F);
      if (MD) {
        if (externalBase(MD, *Result.SourceManager))
            return;

        HandleSpecialMember(MD, false);
        if (isa<CXXDestructorDecl>(MD))
          return; // We don't see uses of destructors.
      }

      if (F->isMain())
        return;

      if (isCompilerGenerated(F))
        return;

#if 0
      llvm::errs() << "FunctionDecl ";
      F->printName(llvm::errs());
      llvm::errs() << " USR:" << USR << "\n";
#endif
      Defs.insert(F->getCanonicalDecl());

      // __attribute__((constructor())) are always used
      if (F->hasAttr<ConstructorAttr>())
        handleUse(F, Result.SourceManager);

    } else if (const auto *R = Result.Nodes.getNodeAs<DeclRefExpr>("declRef")) {
      handleUse(R->getDecl(), Result.SourceManager);
    } else if (const auto *R =
                   Result.Nodes.getNodeAs<MemberExpr>("memberRef")) {
      handleUse(R->getMemberDecl(), Result.SourceManager);
    } else if (const auto *R = Result.Nodes.getNodeAs<CXXConstructExpr>(
                   "cxxConstructExpr")) {
      handleUse(R->getConstructor(), Result.SourceManager);
    } else if (const auto *R = Result.Nodes.getNodeAs<CXXNewExpr>("cxxNewExpr")) {
        if (const auto opNew = R->getOperatorNew())
            handleUse(opNew, Result.SourceManager);
        // a new expression calls operator delete on initialization failures
        if (const auto opDelete = R->getOperatorDelete())
            handleUse(opDelete, Result.SourceManager);
    } else if (const auto *R = Result.Nodes.getNodeAs<CXXDeleteExpr>("cxxDeleteExpr")) {
        if (const auto opDelete = R->getOperatorDelete())
            handleUse(opDelete, Result.SourceManager);
    }
  }

  std::set<const FunctionDecl *> Defs;
  // value: the number of uses
  std::map<const FunctionDecl *, unsigned> Uses;
};

class XUnusedASTConsumer : public ASTConsumer {
public:
  XUnusedASTConsumer() {
    Matcher.addMatcher(
        functionDecl(isDefinition()).bind("fnDecl"),
        &Handler);
    Matcher.addMatcher(cxxNewExpr().bind("cxxNewExpr"), &Handler);
    Matcher.addMatcher(cxxDeleteExpr().bind("cxxDeleteExpr"), &Handler);
    Matcher.addMatcher(declRefExpr().bind("declRef"), &Handler);
    Matcher.addMatcher(memberExpr().bind("memberRef"), &Handler);
    Matcher.addMatcher(cxxConstructExpr().bind("cxxConstructExpr"), &Handler);
  }

  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
    Handler.finalize(Context.getSourceManager());
  }

private:
  FunctionDeclMatchHandler Handler;
  MatchFinder Matcher;
};

// For each source file provided to the tool, a new FrontendAction is created.
class XUnusedFrontendAction : public ASTFrontendAction {
public:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance & /*CI*/,
                                                 StringRef /*File*/) override {
    return std::make_unique<XUnusedASTConsumer>();
  }
};

class XUnusedFrontendActionFactory : public tooling::FrontendActionFactory {
public:
  std::unique_ptr<FrontendAction> create() override { return std::make_unique<XUnusedFrontendAction>(); }
};

int main(int argc, const char **argv) {
  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);

  const char *Overview = R"(
  xunused is tool to find unused functions and methods across a whole C/C++ project.
  )";

  tooling::ExecutorName.setInitialValue("all-TUs");
  static llvm::cl::OptionCategory XUnusedCategory("xunused options");
  static llvm::cl::opt<bool> reportFunctions("report-functions",
          llvm::cl::desc("Report (to stdout) the number of times a candidate function was used."), llvm::cl::cat(XUnusedCategory));
  static llvm::cl::opt<bool> specialMembers("special-members",
          llvm::cl::desc("If one of the special class methods in a class is used, treat all other as used."), llvm::cl::cat(XUnusedCategory));

  auto Executor = clang::tooling::createExecutorFromCommandLineArgs(
      argc, argv, XUnusedCategory, Overview);
  if (!Executor) {
    llvm::errs() << llvm::toString(Executor.takeError()) << "\n";
    return 1;
  }

  auto OptionsParser = clang::tooling::CommonOptionsParser::create(argc, argv, XUnusedCategory);
  if (!OptionsParser) {
      llvm::errs() << OptionsParser.takeError() << "\n";
      return 1;
  }
  auto &DB = OptionsParser->getCompilations();
  // collect libraries sources for exclusion
  std::set<std::string> librarySourceFiles;
  for (auto &File : DB.getAllFiles()) {
      for (const auto &Cmd : DB.getCompileCommands(File)) {
          if (!Cmd.Output.empty() && Cmd.Output.find("_la-") != std::string::npos) {
              librarySourceFiles.insert(File);
          }
      }
  }

  auto Adjuster = clang::tooling::getInsertArgumentAdjuster("-fparse-all-comments");

  auto Err =
      Executor->get()->execute(std::unique_ptr<XUnusedFrontendActionFactory>(
          new XUnusedFrontendActionFactory()), Adjuster);

  if (Err) {
    llvm::errs() << llvm::toString(std::move(Err)) << "\n";
    return 1;
  }

  for (auto &KV : AllDecls) {
    DefInfo &I = KV.second;

    if (!I.sawDefinition())
        continue; // assume this function is external to the project being scanned

    if (I.getUses(specialMembers.getValue()) > 0 && !reportFunctions)
        continue; // a used function that does not need to be reported

    const auto &reportDefinition = *I.Definitions.begin();

    if (librarySourceFiles.find(std::string(reportDefinition.Filename.str())) != librarySourceFiles.end()) {
        llvm::errs() << "Skip library source: " << reportDefinition.Filename << "\n";
        continue;
    }

    if (I.getUses(specialMembers.getValue()) == 0) {
      llvm::errs() << reportDefinition.Filename << ":" << reportDefinition.FirstLine << ": warning:"
                   << " Function '" << I.Name << "' is unused\n";
    } else {
      assert(reportFunctions);
      llvm::errs() << reportDefinition.Filename << ":" << reportDefinition.FirstLine <<
          ": note: Function '" << I.Name << "' uses=" << I.getUses(specialMembers.getValue()) << "\n";
    }
    for (auto &D : I.Declarations) {
      llvm::errs() << D.Filename << ":" << D.FirstLine << ": note:"
                   << " declared here\n";
      llvm::errs() << D.Filename << ":" << D.LastLine << ": note:"
                   << " declaration ends here\n";
      if (D.CommentFirstLine) {
        llvm::errs() << D.Filename << ":" << D.CommentFirstLine << ": note:"
                     << " comment starts here\n";
        llvm::errs() << D.Filename << ":" << D.CommentLastLine << ": note:"
                   << " comment ends here\n";
      }
    }
    for (auto &D : I.Definitions) {
      llvm::errs() << D.Filename << ":" << D.FirstLine << ": note:"
                   << " defined here\n";
      llvm::errs() << D.Filename << ":" << D.LastLine << ": note:"
                   << " definition ends here\n";
      if (D.CommentFirstLine) {
        llvm::errs() << D.Filename << ":" << D.CommentFirstLine << ": note:"
                     << " comment starts here\n";
        llvm::errs() << D.Filename << ":" << D.CommentLastLine << ": note:"
                   << " comment ends here\n";
      }
    }
  }
}
