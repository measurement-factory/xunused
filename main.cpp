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
#include <optional>
#include <unordered_set>


using namespace clang;
using namespace clang::ast_matchers;

class DefInfo;
class VarInfo;

using OverridenUSRs = std::unordered_set<std::string>;
using AllDeclarations = std::map<std::string, DefInfo>;
using AllDeclarationsIterator = AllDeclarations::iterator;
using DeclarationsList = std::list<AllDeclarationsIterator>;

using VarDeclarations = std::map<std::string, VarInfo>;

static llvm::cl::OptionCategory XUnusedCategory("xunused options");
static llvm::cl::opt<bool> ReportFunctions("report-functions",
        llvm::cl::desc("Report (to stdout) the number of times a candidate function was used."), llvm::cl::cat(XUnusedCategory));
static llvm::cl::opt<bool> SpecialFunctions("special-functions",
        llvm::cl::desc("If one function of a specific function group is used, treat all other functions as used."), llvm::cl::cat(XUnusedCategory));
static llvm::cl::opt<bool> ReportGlobals("report-globals",
        llvm::cl::desc("For each global or static variable report (to stdout) the number of usages or its unsed status"), llvm::cl::cat(XUnusedCategory));

bool getUSRForDecl (const Decl *F, std::string &USR);
bool getUSRForFirstArgumentType(const FunctionDecl *F, std::string &USR);

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
  DeclLoc(const Decl *D, const SourceManager &SM) {
    auto range = D->getSourceRange();

    if (const auto F = dyn_cast<FunctionDecl>(D)) {
      // expand to include 'template<...>' if it exists
      if (clang::FunctionTemplateDecl *TD = F->getDescribedFunctionTemplate())
          range = TD->getSourceRange();
    }

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

    const auto &context = D->getASTContext();
    if (const auto RC = context.getRawCommentForDeclNoCache(D)) {
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
  size_t operator() (const DeclLoc& fr) const {
    return llvm::hash_combine(fr.Filename, fr.FirstLine, fr.LastLine);
  }
};

class ClassInfo
{
  public:
    void addSpecialMember(const FunctionDecl *);

    bool anySpecialMemberIsUsed() const {
        return specialMethodIsUsed || incrementOperatorIsUsed || equalityOperatorIsUsed || comparisonOperatorIsUsed || dereferenceOperatorIsUsed;
    }
    // whether at least one special method is used
    // (this may be a hidden method without DefInfo)
    bool specialMethodIsUsed = false;
    // whether at least one of the overloaded operators '++' and '--' (prefix postfix forms), is used
    bool incrementOperatorIsUsed = false;
    // whether at least one of the overloaded operators '==' and '!=' is used
    bool equalityOperatorIsUsed = false;
    // whether at least one of the overloaded operators '>=', '<=', '<', '>', '<=>' is used
    bool comparisonOperatorIsUsed = false;
    // whether at least one of the overloaded operators '*', '->', '->*' is used
    bool dereferenceOperatorIsUsed = false;
};

using ClassDeclarations = std::map<std::string, ClassInfo>;
using ClassDeclarationsIterator = ClassDeclarations::iterator;
ClassDeclarations ClassDecls;

bool IsSpecialMethod(const FunctionDecl *F)
{
    if (const auto *MD = dyn_cast<CXXMethodDecl>(F)) {
        if (const auto *constr = dyn_cast<CXXConstructorDecl>(MD)) {
            return (constr->isCopyConstructor() || constr->isMoveConstructor());
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

bool IsEqualityOperator(const clang::FunctionDecl *FD) {
    const auto operatorKind = FD->getOverloadedOperator();
    switch (operatorKind) {
        case clang::OO_EqualEqual:       // ==
        case clang::OO_ExclaimEqual:     // !=
            return true;
        default:
            return false;
    }
}

bool IsComparisonOperator(const clang::FunctionDecl *FD) {
    const auto operatorKind = FD->getOverloadedOperator();
    switch (operatorKind) {
        case clang::OO_Less:             // <
        case clang::OO_Greater:          // >
        case clang::OO_LessEqual:        // <=
        case clang::OO_GreaterEqual:     // >=
        case clang::OO_Spaceship:        // <=> (C++20)
            return true;
        default:
            return false;
    }
}

bool IsIncrementOperator(const clang::FunctionDecl *FD) {
    const auto operatorKind = FD->getOverloadedOperator();
    switch (operatorKind) {
        case clang::OO_PlusPlus:
        case clang::OO_MinusMinus:
            return true;
        default:
            return false;
    }
}

bool IsDereferenceOperator(const clang::FunctionDecl *FD) {
    const auto operatorKind = FD->getOverloadedOperator();
    switch (operatorKind) {
        case clang::OO_Star:           // operator*
        case clang::OO_Arrow:          // operator->
        case clang::OO_ArrowStar:      // operator->*
            return true;
        default:
            return false;
    }
}

bool IsAnySpecialFunction(const FunctionDecl *F) {
    return IsSpecialMethod(F) || IsIncrementOperator(F) || IsEqualityOperator(F) || IsComparisonOperator(F) || IsDereferenceOperator(F);
}

void ClassInfo::addSpecialMember(const FunctionDecl *F) {
    if (IsSpecialMethod(F))
        specialMethodIsUsed = true;
    if (IsIncrementOperator(F))
        incrementOperatorIsUsed = true;
    else if (IsEqualityOperator(F))
        equalityOperatorIsUsed = true;
    else if (IsComparisonOperator(F))
        comparisonOperatorIsUsed = true;
    else if (IsDereferenceOperator(F))
        dereferenceOperatorIsUsed = true;
}

void HandleSpecialMember(const FunctionDecl *F, const bool used) {
    if (!IsAnySpecialFunction(F))
        return;

    std::string USR;
    if (const auto MD = dyn_cast<CXXMethodDecl>(F)) { // special class methods
        const auto decl = MD->getParent();
        if (!getUSRForDecl(decl, USR))
            return;
    }
    // stand-alone operators, e.g., operator==(T a, T b) and operator!==(T a, T b)
    // group these functions by the first argument's type USR
    else if (!getUSRForFirstArgumentType(F, USR)) {
        return;
    }

    auto it = ClassDecls.find(USR);
    if (it == ClassDecls.end()) {
        const auto inserted = ClassDecls.emplace(USR, ClassInfo());
        it = inserted.first;
    }
    it->second.addSpecialMember(F);
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
    : Uses(0), Name(RemoveTemplateFromMember(F)) {
        addClassReference(F);
  }

  bool sawDefinition() const { return !Definitions.empty(); }
  void addDeclarationsAndDefinitions(const FunctionDecl *F, const SourceManager &SM) {
    if (Name.empty()) {
        Name = RemoveTemplateFromMember(F);
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

  // the number of times this function is actually used
  // without 'special' cases
  unsigned getRawUses() const {
      return base ? base->getRawUses() : Uses;
  }

  // Returns the positive number of times this function is used, or
  // 0, marking the special usage case, when the usage of one function
  // of a group marks any function in the group as 'used', or
  // std::nullopt for the unused function.
  std::optional<unsigned> getUses() const {
      if (const auto uses = getRawUses())
          return uses;

      if (classRef == ClassDecls.end())
          return std::nullopt;

      if (SpecialFunctions.getValue() && classRef->second.anySpecialMemberIsUsed())
          return 0;

      return std::nullopt;
  }

  void addClassReference(const FunctionDecl *F) {
    if (!IsAnySpecialFunction(F))
        return;

    std::string USR;
    if (const auto *MD = dyn_cast<CXXMethodDecl>(F)) {
        const auto classDecl = MD->getParent();
        assert(classDecl);
        if (!getUSRForDecl(classDecl, USR))
            return;
    } else if (!getUSRForFirstArgumentType(F, USR)) {
        return;
    }

    classRef = ClassDecls.find(USR);
    assert(classRef != ClassDecls.end());
  }

  size_t Uses = 0;
  std::string Name;
  std::unordered_set<DeclLoc, DeclLocHash> Declarations;
  std::unordered_set<DeclLoc, DeclLocHash> Definitions;
  DefInfo *base = nullptr; // the base virtual definition
  ClassDeclarationsIterator classRef = ClassDecls.end();
};

struct VarInfo {
    explicit VarInfo(const VarDecl *decl) : Name(decl->getQualifiedNameAsString()) {}

    void addDeclarationsAndDefinitions(const VarDecl *D, const SourceManager &SM) {
        for (const auto R: D->redecls()) {
            if (!R->getLocation().isValid()) {
                continue; // no physical file representation
            }
            Definitions.insert({R, SM});
        }
    }

    void addUses(const unsigned uses) { Uses += uses; }
    unsigned getUses() const { return Uses; }

    size_t Uses = 0;
    std::string Name;
    std::unordered_set<DeclLoc, DeclLocHash> Definitions;
};

std::mutex Mutex;
AllDeclarations AllDecls;
VarDeclarations VarDecls;

const Decl* getRootTemplateDecl(const Decl *decl) {
  if (const auto F = dyn_cast<FunctionDecl>(decl)) {
    if (F->isFunctionTemplateSpecialization()) { // handle template functions or template methods inside template classes
      if (const FunctionTemplateDecl *FTD = F->getPrimaryTemplate()) {
        if (FunctionTemplateDecl *pattern = FTD->getInstantiatedFromMemberTemplate()) {
          // template method inside template classes
          return pattern->getCanonicalDecl();
        }
        return FTD->getCanonicalDecl(); // template function
      }
    } else if (auto *MD = dyn_cast<CXXMethodDecl>(F)) { // handle non-template methods inside template classes
      if (auto pattern = MD->getInstantiatedFromMemberFunction()) {
        return pattern->getCanonicalDecl();
      }
    }

    if (auto *FTD = F->getDescribedFunctionTemplate())
      return FTD->getCanonicalDecl(); // template method inside a non-template class
  }
  return nullptr;
}

bool isSameMethodSignature(const CXXMethodDecl *specMethod, const CXXMethodDecl *primaryMethod) {
    // name and number of Parameters
    if (specMethod->getDeclName() != primaryMethod->getDeclName() ||
        specMethod->param_size() != primaryMethod->param_size()) {
        return false;
    }

    // check const qualifiers (e.g., void f() vs void f() const)
    if (specMethod->getMethodQualifiers() != primaryMethod->getMethodQualifiers())
        return false;

    for (auto i = 0; i < specMethod->param_size(); ++i) {
        const auto primType = primaryMethod->getParamDecl(i)->getType();
        if (primType->isDependentType())
            continue;

        // if types are not dependent, they must be identical
        const auto specType = specMethod->getParamDecl(i)->getType();
        if (!specMethod->getASTContext().hasSameType(specType, primType))
            return false;
    }
    return true;
}


Decl *getPrimaryTemplateMethod(const Decl *decl) {
    const auto method = dyn_cast<CXXMethodDecl>(decl);
    if (!method)
        return nullptr;

    const ClassTemplateDecl *primaryClassTemp = nullptr;

    if (const auto spec = dyn_cast<ClassTemplateSpecializationDecl>(method->getParent())) {
        auto from = spec->getSpecializedTemplateOrPartial();
        if (from.is<ClassTemplatePartialSpecializationDecl*>()) { // partial specialization
            const auto partial = from.get<ClassTemplatePartialSpecializationDecl*>();
            primaryClassTemp = partial->getSpecializedTemplate(); // get the primary template (<T>)
        } else if (spec->getSpecializationKind() == TSK_ExplicitSpecialization) { // full specialization
            primaryClassTemp = spec->getSpecializedTemplate(); // get the primary template (<T>)
        }
    }

    if (primaryClassTemp) {
        // get the "pattern" (the class body inside the template)
        CXXRecordDecl *primaryRecord = primaryClassTemp->getTemplatedDecl();

        // search for a method with the same name and signature
        for (auto foundDecl : primaryRecord->lookup(method->getDeclName())) {
            if (const auto primaryMethod = dyn_cast<CXXMethodDecl>(foundDecl)) {
                if (isSameMethodSignature(method, primaryMethod)) {
                    return primaryMethod->getCanonicalDecl();
                }
            }
        }
    }
    return nullptr;
}

bool getUSRForFirstArgumentType(const FunctionDecl *F, std::string &USR) {
    if (F->getNumParams() > 0) {
        const auto firstParam = F->getParamDecl(0);
        QualType rawType = firstParam->getType();
        const auto cleanType = rawType.getNonReferenceType().getUnqualifiedType().getCanonicalType();
        llvm::SmallVector<char, 128> Buff;
        if (index::generateUSRForType(cleanType, F->getASTContext(), Buff))
            return false;
        USR = std::string(Buff.data(), Buff.size());
        return true;
    }
    return false;
}

bool getUSRForDecl(const Decl *D, std::string &USR) {
    auto target = D;
    if (const auto templDecl = getPrimaryTemplateMethod(D)) // handle class specializations
        target = templDecl;
    else if (const auto templDecl = getRootTemplateDecl(D)) // handle function/method instantinations
        target = templDecl;

    assert(target);

    llvm::SmallVector<char, 128> Buff;
    if (clang::index::generateUSRForDecl(target, Buff)) {
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
bool externalBase(const FunctionDecl *F, const SourceManager &SM) {
    const auto MD = dyn_cast<CXXMethodDecl>(F);
    if (!MD)
        return false;
    for (const auto *overridden : MD->overridden_methods()) {
        const auto parent = overridden->getParent();
        assert(parent);
        if (SM.isInSystemHeader(parent->getLocation()))
            return true;
        return externalBase(overridden, SM);
    }
    return false;
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
      auto adjustedUses = pair.second;
      const auto recursiveIt = RecursiveUses.find(pair.first);
      if (recursiveIt != RecursiveUses.end()) {
          const auto recursiveUses = recursiveIt->second;
          adjustedUses = (adjustedUses>recursiveUses) ? (adjustedUses-recursiveUses) : 0;
      }
      it->second.addUses(adjustedUses);
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

  void handleUse(const ValueDecl *D, const SourceManager *SM, bool isRecursion = false) {
    auto *FD = dyn_cast<FunctionDecl>(D);
    if (!FD)
      return;

    HandleSpecialMember(FD, true);

    if (isCompilerGenerated(FD))
        return;

    // ignore uses of declarations mentioned in a system header
    if (SM->isInSystemHeader(FD->getSourceRange().getBegin()))
      return;

    if (externalBase(FD, *SM))
        return;
#if 0
    llvm::errs() << "Use ";
    FD->printName(llvm::errs());
    //llvm::errs() << " USR:" << USR;
    llvm::errs() << "\n";
#endif
     auto currentUses = isRecursion ? &RecursiveUses : &Uses;
     auto [it, success] = currentUses->try_emplace(FD->getCanonicalDecl(), 1);
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

      HandleSpecialMember(F, false);
      auto *MD = dyn_cast<CXXMethodDecl>(F);
      if (MD) {
        if (isa<CXXDestructorDecl>(MD))
          return; // We don't see uses of destructors.
      }

      if (F->isMain())
        return;

      if (isCompilerGenerated(F))
        return;

      if (externalBase(F, *Result.SourceManager))
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
    } else if(const auto *CE = Result.Nodes.getNodeAs<clang::CallExpr>("callee_expr")) {
        // handle recursive calls
        if (const auto *caller = Result.Nodes.getNodeAs<clang::FunctionDecl>("caller")) {
            if (const auto callee = CE->getDirectCallee()) {
                if (callee->getCanonicalDecl() == caller->getCanonicalDecl()) {
                    handleUse(callee, Result.SourceManager, true);
                }
            }
        }
    } else if (const auto D = Result.Nodes.getNodeAs<VarDecl>("globalDecl")) {
        if (!ReportGlobals)
            return;

        if (Result.SourceManager->isInSystemHeader(D->getLocation()))
            return;

        // avoid side effects by allowing only constant initialization
        // (i.e., values known at compilation/linkage phase)
        if (!D->hasConstantInitialization())
            return;

        std::string USR;
        if (!getUSRForDecl(D->getCanonicalDecl(), USR))
            return;

        auto [it, success] = VarDecls.try_emplace(USR, VarInfo(D));
        it->second.addDeclarationsAndDefinitions(D, *Result.SourceManager);

    } else if (const auto D = Result.Nodes.getNodeAs<DeclRefExpr>("globalVarUsage")) {
        if (!ReportGlobals)
            return;

        const auto var = Result.Nodes.getNodeAs<VarDecl>("globalVar");
        assert(var);
        if (Result.SourceManager->isInSystemHeader(var->getLocation()))
            return;

        std::string USR;
        if (!getUSRForDecl(var->getCanonicalDecl(), USR))
            return;

        auto [it, success] = VarDecls.try_emplace(USR, VarInfo(var));
        it->second.addUses(1);
    }
  }

  std::set<const FunctionDecl *> Defs;
  // value: the number of uses
  std::map<const FunctionDecl *, unsigned> Uses;
  std::map<const FunctionDecl *, unsigned> RecursiveUses;
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
    // This matcher is used for recursive call detection.
    // It matches nested calls, e.g.:
    // void myFunc() {   // <--- "caller" (FunctionDecl)
    //   other();      // <--- "callee_expr" (CallExpr)
    // }
    Matcher.addMatcher(callExpr(hasAncestor(functionDecl().bind("caller"))).bind("callee_expr"), &Handler);
    Matcher.addMatcher(varDecl(hasGlobalStorage(), isDefinition()).bind("globalDecl"), &Handler);
    Matcher.addMatcher(declRefExpr(to(varDecl(hasGlobalStorage()).bind("globalVar"))).bind("globalVarUsage"), &Handler);
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

    const auto uses = I.getUses();

    if (uses && !ReportFunctions)
        continue; // a used function that does not need to be reported

    const auto &reportDefinition = *I.Definitions.begin();

    if (!uses) {
      llvm::errs() << reportDefinition.Filename << ":" << reportDefinition.FirstLine << ": warning:"
                   << " Function '" << I.Name << "' is unused\n";
    } else {
      assert(ReportFunctions);
      llvm::errs() << reportDefinition.Filename << ":" << reportDefinition.FirstLine <<
          ": note: Function '" << I.Name << "' uses=" << *uses << "\n";
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

  if (ReportGlobals) {
    for (auto &KV : VarDecls) {
      VarInfo &I = KV.second;

      const auto uses = I.getUses();

      if (I.Definitions.empty())
          continue;

      const auto &reportDefinition = *I.Definitions.begin();

      if (!uses) {
          llvm::errs() << reportDefinition.Filename << ":" << reportDefinition.FirstLine << ": warning: '" <<
              I.Name << "' is unused\n";
      } else {
          llvm::errs() << reportDefinition.Filename << ":" << reportDefinition.FirstLine << ": note: '" <<
              I.Name << "' uses=" << uses << "\n";
      }

      for (auto &D : I.Definitions) {
          llvm::errs() << D.Filename << ":" << D.FirstLine << ": note: declared here\n";
          llvm::errs() << D.Filename << ":" << D.LastLine << ": note: declaration ends here\n";
          if (D.CommentFirstLine) {
              llvm::errs() << D.Filename << ":" << D.CommentFirstLine << ": note: comment starts here\n";
              llvm::errs() << D.Filename << ":" << D.CommentLastLine << ": note: comment ends here\n";
          }
      }
    }
  }
}
