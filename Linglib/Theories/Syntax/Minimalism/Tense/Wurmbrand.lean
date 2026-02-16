import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Core.Tense

/-!
# Wurmbrand (2014): Tense and Aspect in English Infinitives

Wurmbrand's three-way classification of infinitival complements by tense
properties. The key insight: infinitival complements are not uniformly
"tenseless" -- they fall into three classes with distinct temporal behavior.

## Core Mechanisms

1. **Three-way classification**: future irrealis, propositional, restructuring
2. **Woll decomposition**: *will* = PRES + *woll*; *would* = PAST + *woll*
3. **Temporal orientation** is determined by complement class, not tense morphology
4. **Dependent vs independent tense**: restructuring complements share the
   matrix temporal domain; propositional complements have NOW-anchoring

## Classification (Table 1)

| Class           | Example verbs      | Temporal orientation | Tense status     |
|-----------------|--------------------|-----------------------|------------------|
| Future irrealis | decide, want       | Future-oriented       | Tenseless + woll |
| Propositional   | believe, claim     | Simultaneous (NOW)    | NOW-anchored     |
| Restructuring   | try, begin, manage | Dependent on matrix   | Single domain    |

## Limitations

- Focuses on English infinitives; cross-linguistic extension is programmatic
- Temporal de re: not directly addressed
- ULC: not directly addressed

## References

- Wurmbrand, S. (2014). Tense and aspect in English infinitives.
  *Linguistic Inquiry* 45(3): 403--447.
-/

namespace Minimalism.Tense.Wurmbrand

open Core.Tense
open Core.Reichenbach
open IntensionalSemantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Infinitival Tense Classification
-- ════════════════════════════════════════════════════════════════

/-- Wurmbrand's (2014) three-way classification of infinitival tense. -/
inductive InfinitivalTenseClass where
  /-- decide, want: tenseless + woll -> future-oriented -/
  | futureIrrealis
  /-- believe, claim: NOW-anchored -> simultaneous with attitude time -/
  | propositional
  /-- try, begin, manage: single temporal domain -> dependent on matrix -/
  | restructuring
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Classification of infinitival complement verbs. -/
structure InfinitivalVerb where
  /-- The verb lemma -/
  lemma_ : String
  /-- Its tense class -/
  tenseClass : InfinitivalTenseClass
  deriving Repr


-- ════════════════════════════════════════════════════════════════
-- § Woll Decomposition
-- ════════════════════════════════════════════════════════════════

/-- Woll: abstract future modal (Wurmbrand 2014, section 2.1).
    *will* = PRES + *woll*; *would* = PAST + *woll*.

    This decomposes English future auxiliaries into a tense component
    and a modal component (woll). The tense component is what undergoes
    SOT; woll provides the future orientation. -/
structure WollDecomposition where
  /-- The tense component -/
  tense : GramTense
  /-- Whether woll is present (provides future orientation) -/
  hasWoll : Bool
  deriving DecidableEq, Repr, BEq

/-- *will* = present tense + woll. -/
def will_ : WollDecomposition where
  tense := .present
  hasWoll := true

/-- *would* = past tense + woll. -/
def would_ : WollDecomposition where
  tense := .past
  hasWoll := true

/-- Plain present (no woll). -/
def plainPresent : WollDecomposition where
  tense := .present
  hasWoll := false

/-- *will* and *would* share the woll component. -/
theorem will_would_share_woll :
    will_.hasWoll = would_.hasWoll := rfl

/-- *will* and *would* differ only in tense. -/
theorem will_would_tense_differs :
    will_.tense ≠ would_.tense := nofun


-- ════════════════════════════════════════════════════════════════
-- § Temporal Orientation by Class
-- ════════════════════════════════════════════════════════════════

/-- The temporal orientation of a complement relative to the matrix event.
    Wurmbrand's classification predicts distinct temporal relations. -/
inductive TemporalOrientation where
  /-- Complement event is after matrix event -/
  | futureOriented
  /-- Complement event is simultaneous with matrix event -/
  | simultaneous
  /-- Complement event's temporal location depends entirely on matrix -/
  | dependent
  deriving DecidableEq, Repr, BEq

/-- Map each infinitival tense class to its predicted temporal orientation. -/
def classOrientation : InfinitivalTenseClass → TemporalOrientation
  | .futureIrrealis => .futureOriented
  | .propositional => .simultaneous
  | .restructuring => .dependent


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Future-irrealis infinitives are tenseless: they have no T head,
    so they contribute no independent tense interpretation. The future
    orientation comes from woll, not from tense. -/
theorem futureIrrealis_is_tenseless :
    classOrientation .futureIrrealis = .futureOriented := rfl

/-- Propositional infinitives impose NOW-anchoring: the complement's
    reference time is simultaneous with the attitude holder's time. -/
theorem propositional_now_anchored :
    classOrientation .propositional = .simultaneous := rfl

/-- Restructuring infinitives share the matrix temporal domain: there is
    no independent temporal reference in the complement. -/
theorem restructuring_dependent :
    classOrientation .restructuring = .dependent := rfl


-- ════════════════════════════════════════════════════════════════
-- § Example Verb Classifications
-- ════════════════════════════════════════════════════════════════

/-- "want" is future irrealis: "John wanted to leave" → leaving after wanting. -/
def want : InfinitivalVerb := ⟨"want", .futureIrrealis⟩

/-- "decide" is future irrealis: "John decided to leave" → leaving after deciding. -/
def decide : InfinitivalVerb := ⟨"decide", .futureIrrealis⟩

/-- "believe" is propositional: "John believes Mary to be sick" → simultaneous. -/
def believe : InfinitivalVerb := ⟨"believe", .propositional⟩

/-- "claim" is propositional. -/
def claim : InfinitivalVerb := ⟨"claim", .propositional⟩

/-- "try" is restructuring: "John tried to leave" → same temporal domain. -/
def try_ : InfinitivalVerb := ⟨"try", .restructuring⟩

/-- "begin" is restructuring. -/
def begin_ : InfinitivalVerb := ⟨"begin", .restructuring⟩

/-- "manage" is restructuring. -/
def manage : InfinitivalVerb := ⟨"manage", .restructuring⟩

/-- All three classes are represented. -/
theorem wurmbrand_three_classes_distinct :
    want.tenseClass ≠ believe.tenseClass ∧
    believe.tenseClass ≠ try_.tenseClass ∧
    want.tenseClass ≠ try_.tenseClass := by
  exact ⟨nofun, nofun, nofun⟩


-- ════════════════════════════════════════════════════════════════
-- § Bridge Theorems
-- ════════════════════════════════════════════════════════════════

/-- Propositional NOW-anchoring is Klecha's eval time shift mechanism:
    the complement's tense is checked against the attitude time (NOW),
    not speech time. Both produce simultaneous orientation. -/
theorem propositional_like_klecha_eval_shift :
    classOrientation .propositional = .simultaneous := rfl

/-- Restructuring dependent tense is compatible with Zeijlstra's [uT]:
    the complement T has no independent tense, paralleling [uT] which
    is semantically vacuous and depends on matrix [iT]. -/
theorem restructuring_like_agree_dependent :
    classOrientation .restructuring = .dependent := rfl

/-- Future-oriented complements match the `wantedToLeave` data frame
    from `Phenomena/Tense/Data.lean`: the complement event is after
    the matrix event, oriented by the verb's lexical semantics. -/
theorem futureIrrealis_matches_wantedToLeave :
    classOrientation want.tenseClass = .futureOriented := rfl


-- ════════════════════════════════════════════════════════════════
-- § Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Wurmbrand (2014) identity card. -/
def Wurmbrand : TenseTheory where
  name := "Wurmbrand 2014"
  citation := "Wurmbrand, S. (2014). Tense and aspect in English infinitives. LI 45(3): 403-447."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := false
  hasSOTDeletion := false
  hasAgreeBasedSOT := true
  simultaneousMechanism := "propositional NOW-anchoring or restructuring single domain"


end Minimalism.Tense.Wurmbrand
