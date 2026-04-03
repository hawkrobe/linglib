import Linglib.Theories.Syntax.Minimalism.Formal.HeadMovement.Basic

/-!
# Verb Movement Parameter
@cite{chomsky-1995} @cite{pollock-1989}

@cite{pollock-1989} established that languages differ parametrically in whether
lexical verbs raise to T (Inflection). French lexical verbs obligatorily raise
past negation, adverbs, and floating quantifiers; English lexical verbs remain
in situ. English auxiliaries, however, *do* raise — patterning with French
lexical verbs rather than English lexical verbs.

This asymmetry explains do-support: when T must be realized high (in C for
questions, above negation) but the lexical verb cannot raise, a dummy 'do'
is inserted to host tense features.

## The Four Diagnostics

Pollock identifies four positions that diagnose V-raising:
1. **Negation**: V > Neg (French) vs. *V > Neg (English)
2. **Adverbs**: V > Adv (French) vs. *V > Adv (English)
3. **Floating quantifiers**: V > FQ (French) vs. *V > FQ (English)
4. **Subject inversion**: V-Subj (French) vs. *V-Subj (English lexical V)

All four converge: a language either raises V past all four, or past none.

-/

namespace Minimalism

-- ============================================================================
-- Part 1: Verb Movement Parameter
-- ============================================================================

/-- The verb movement parameter: does V raise to T? -/
inductive VMovementParam where
  /-- V raises to T (French lexical verbs, English auxiliaries) -/
  | raises
  /-- V stays in situ below T (English lexical verbs) -/
  | inSitu
  deriving DecidableEq, Repr

/-- Pollock's four diagnostics for verb position relative to T. -/
inductive VDiagnostic where
  /-- Does V precede sentential negation? -/
  | negation
  /-- Does V precede VP-adverbs (e.g., 'often', 'souvent')? -/
  | adverb
  /-- Does V precede floating quantifiers (e.g., 'all', 'tous')? -/
  | floatingQ
  /-- Can V invert with the subject (V-to-C via T)? -/
  | inversion
  deriving DecidableEq, Repr, Inhabited

/-- Prediction: does V precede the diagnostic position?

    If V raises to T, it precedes all four diagnostic positions (negation,
    adverbs, floating quantifiers, and can reach C for inversion).
    If V stays in situ, it follows all four. -/
def verbPrecedesDiagnostic (p : VMovementParam) (_ : VDiagnostic) : Bool :=
  match p with
  | .raises => true
  | .inSitu => false

-- ============================================================================
-- Part 2: Do-Support
-- ============================================================================

/-- Contexts where tense features need overt support in T/C position.

    When V cannot raise to T (English lexical verbs), these contexts
    require do-insertion because tense must be realized above VP. -/
inductive TenseSupportContext where
  /-- Sentential negation: "Sue does not eat fish" -/
  | negation
  /-- Questions (SAI requires T-to-C): "Does she eat fish?" -/
  | question
  /-- Verum focus (stressed T): "She DOES eat fish" -/
  | verumFocus
  /-- Tag questions: "She likes him, doesn't she?" -/
  | tagQuestion
  /-- VP ellipsis (stranded T): "She runs faster than he does" -/
  | vpEllipsis
  deriving DecidableEq, Repr, Inhabited

/-- Does this parameter setting require do-support in the given context?

    Do-support is needed exactly when V is in situ: T cannot lower to V
    (blocked by the intervening material), so a dummy 'do' hosts tense. -/
def needsDoSupport (p : VMovementParam) (_ : TenseSupportContext) : Bool :=
  match p with
  | .raises => false
  | .inSitu => true

-- ============================================================================
-- Part 3: Language-Specific Instances
-- ============================================================================

/-- French lexical verbs raise to T. -/
def french : VMovementParam := .raises

/-- English lexical verbs stay in situ. -/
def englishLexical : VMovementParam := .inSitu

/-- English auxiliaries raise to T — patterning with French, not with
    English lexical verbs. This is Pollock's key observation. -/
def englishAux : VMovementParam := .raises

-- ============================================================================
-- Part 4: Theorems
-- ============================================================================

/-- V-raising languages: V precedes all four diagnostic positions. -/
theorem raises_verb_precedes_all (d : VDiagnostic) :
    verbPrecedesDiagnostic .raises d = true := by
  cases d <;> rfl

/-- V-in-situ languages: V follows all four diagnostic positions. -/
theorem inSitu_verb_follows_all (d : VDiagnostic) :
    verbPrecedesDiagnostic .inSitu d = false := by
  cases d <;> rfl

/-- English auxiliaries have the same movement parameter as French
    lexical verbs. This is Pollock's central observation: the
    aux/lexical split in English mirrors the English/French split. -/
theorem english_aux_patterns_with_french :
    englishAux = french := rfl

/-- V-raising languages never need do-support. -/
theorem raises_never_needs_do (ctx : TenseSupportContext) :
    needsDoSupport .raises ctx = false := by
  cases ctx <;> rfl

/-- V-in-situ languages always need do-support. -/
theorem inSitu_always_needs_do (ctx : TenseSupportContext) :
    needsDoSupport .inSitu ctx = true := by
  cases ctx <;> rfl

/-- All four diagnostics converge for any parameter setting: they
    either all return true (raises) or all return false (inSitu). -/
theorem diagnostics_converge (p : VMovementParam) (d₁ d₂ : VDiagnostic) :
    verbPrecedesDiagnostic p d₁ = verbPrecedesDiagnostic p d₂ := by
  cases p <;> rfl

/-- Do-support and verb raising are perfectly anticorrelated:
    do-support is needed iff V does not precede negation. -/
theorem doSupport_anticorrelates_raising (p : VMovementParam) (ctx : TenseSupportContext) :
    needsDoSupport p ctx = !verbPrecedesDiagnostic p .negation := by
  cases p <;> rfl

end Minimalism
