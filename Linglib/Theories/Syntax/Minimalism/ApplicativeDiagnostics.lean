import Linglib.Theories.Syntax.Minimalism.Applicative

/-!
# Applicative diagnostics
@cite{pylkkanen-2008}

Cluster-based diagnostic classifier for the high/low applicative
distinction (@cite{pylkkanen-2008}, Table 2.1). Three diagnostics:

1. Can unergative verbs be applicativized? (Ch. 2 §2.1.2)
2. Can static verbs be applicativized? (Ch. 2 §2.1.2)
3. *If the language has English-style depictive secondary predicates*,
   is the applied argument available for depictive modification?
   (Ch. 2 §2.1.3)

The diagnostic infrastructure lives in `Theories/` because it is
reusable: any applicative-typology paper using Pylkkänen's framework
(Wood 2015, Bruening 2021, Cuervo 2003 extensions) consumes the same
classifier. Per-paper instantiation lives in Studies files.

## Cluster-based classification

A high applicative passes *all* tests; a low applicative fails *all*
tests. Test 3 is conditional — when a language lacks English-style
depictives (e.g., Korean) or has too-broad depictives (Venda, Albanian),
the test is *inapplicable* (`.inapplicable`), not "fails." The
classifier ignores inapplicable tests and classifies on the cluster of
applicable ones.

This is stricter than an OR-based classifier (which would misclassify
a language passing one test by accident). Languages that don't pattern
cleanly with either cluster yield `none`, requiring further
investigation rather than a forced classification.
-/

namespace Minimalism

/-- The result of running a single Pylkkänen diagnostic on a language. -/
inductive ApplDiagnosticResult where
  /-- The diagnostic is applicable and the language passes
      (the construction in question is grammatical). -/
  | passes
  /-- The diagnostic is applicable and the language fails
      (the construction is ungrammatical). -/
  | fails
  /-- The diagnostic is *inapplicable* in this language — e.g., Korean
      lacks English-style depictives entirely, so Test 3 cannot be run.
      Distinct from `.fails`: an inapplicable test contributes no
      classification evidence. -/
  | inapplicable
  deriving DecidableEq, Repr

/-- A bundle of Pylkkänen Table 2.1's three diagnostic results for a
    given language. Test 3's `inapplicable` value handles the
    language-conditional cases (Korean lacks depictives; Venda and
    Albanian have too-broad depictives to test). -/
structure ApplDiagnosticBundle where
  /-- Test 1: can unergative verbs be applicativized? -/
  unergative : ApplDiagnosticResult
  /-- Test 2: can static verbs be applicativized? -/
  staticVerb : ApplDiagnosticResult
  /-- Test 3: depictive modification of applied argument
      (conditional on language having English-style depictives). -/
  depictive : ApplDiagnosticResult
  deriving Repr

/-- The list of diagnostic results in a bundle, for cluster checks. -/
def ApplDiagnosticBundle.results (b : ApplDiagnosticBundle) : List ApplDiagnosticResult :=
  [b.unergative, b.staticVerb, b.depictive]

/-- The applicable (non-`.inapplicable`) results in a bundle. -/
def ApplDiagnosticBundle.applicableResults (b : ApplDiagnosticBundle) :
    List ApplDiagnosticResult :=
  b.results.filter (· ≠ .inapplicable)

/-- Cluster-based classification (@cite{pylkkanen-2008}, Table 2.1):
    a language has *high* applicatives iff every applicable diagnostic
    passes; *low* iff every applicable diagnostic fails; otherwise the
    pattern is mixed and the classifier returns `none`, requiring
    further investigation rather than forcing a classification.

    Note: this returns `Option ApplType` collapsed to `.high` or
    `.lowRecipient` — distinguishing recipient from source low
    applicatives requires *additional* diagnostics (transfer
    directionality, §2.2 + §2.3) not in Table 2.1. -/
def classifyByDiagnostics (b : ApplDiagnosticBundle) : Option ApplType :=
  let applicable := b.applicableResults
  if applicable.isEmpty then none
  else if applicable.all (· = .passes) then some .high
  else if applicable.all (· = .fails) then some .lowRecipient
  else none

/-! ## Soundness theorems

The classifier returns `.high` only on all-pass bundles, `.lowRecipient`
only on all-fail bundles. Mixed bundles and empty/all-inapplicable
bundles yield `none`. Soundness is checked structurally on the four
canonical bundle shapes below. -/

/-- A bundle with all three results `.passes` classifies as high. -/
theorem all_pass_classifies_high :
    classifyByDiagnostics
      { unergative := .passes, staticVerb := .passes, depictive := .passes } =
        some .high := by decide

/-- A bundle with all three results `.fails` classifies as low. -/
theorem all_fail_classifies_low :
    classifyByDiagnostics
      { unergative := .fails, staticVerb := .fails, depictive := .fails } =
        some .lowRecipient := by decide

/-- A bundle with mixed results does not classify. -/
theorem mixed_does_not_classify :
    classifyByDiagnostics
      { unergative := .passes, staticVerb := .fails, depictive := .fails } = none := by decide

/-- An all-inapplicable bundle does not classify. -/
theorem all_inapplicable_does_not_classify :
    classifyByDiagnostics
      { unergative := .inapplicable, staticVerb := .inapplicable, depictive := .inapplicable } =
        none := by decide

/-- Inapplicable tests are excluded from the cluster: a bundle with
    one `.inapplicable` and two `.passes` still classifies as high. -/
theorem inapplicable_excluded :
    classifyByDiagnostics
      { unergative := .passes, staticVerb := .passes, depictive := .inapplicable } =
        some .high := by decide

/-- Inapplicable + all-fails still classifies as low. -/
theorem inapplicable_with_fails_classifies_low :
    classifyByDiagnostics
      { unergative := .fails, staticVerb := .fails, depictive := .inapplicable } =
        some .lowRecipient := by decide

end Minimalism
