import Linglib.Syntax.ConstructionGrammar.Resultatives
import Linglib.Semantics.Causation.CCSelection
import Linglib.Semantics.Causation.VerbClass
import Linglib.Semantics.Aspect.ChangeOfState

/-!
# Resultatives as concealed causatives

This file connects the resultative construction to the semantics of causatives. A causative
resultative such as *hammer the metal flat* brings a result state about by means of the verbal
event, and the means relation of Goldberg and Jackendoff together with the construction's CAUSE
determines the `Causative` it expresses, `make`, the neutral sufficiency causative. On the
selection account of Baglini and Bar-Asher Siegal the construction picks the completion of a
sufficient set, as a change-of-state verb does. A bounded result phrase telicizes an activity
into an accomplishment, and the constructional BECOME is an inception, a change from the
result state failing to hold to its holding. Two typological parameters are defined here, how
a language realizes the result phrase and whether it is oriented to the object or the subject;
the Mandarin phase complements that instantiate them live with the Mandarin fragment, and the
per-scenario causal models with Levin's study.

## Main definitions

* `deriveCausativeBuilder` — the causative a subevent relation and a constructional subevent
  description determine, `make` for means with CAUSE and nothing otherwise.
* `resultativeCausativeBuilder` — the causative of the causative resultative, `make`.
* `resultativeCCSelection` — the selection constraint of the construction, completion of a
  sufficient set.
* `ResultativeRealization`, `ResultOrientation` — the typological parameters.

## Main results

* `causative_iff_has_cause` — a subconstruction is causative iff its constructional subevent
  carries CAUSE.
* `make_unique_neutral_sufficiency`, `derived_asserts_sufficiency` — the derived causative
  asserts sufficiency, and `make` is the only sufficiency causative that neither coerces nor
  removes a barrier.
* `resultative_telicizes`, `resultative_aspect_agrees_with_telicize` — the aspectual shift.

## References

* [goldberg-jackendoff-2004]
* [baglini-bar-asher-siegal-2025]
* [levin-2019]
-/

namespace Causation.Resultatives

open ConstructionGrammar
open ConstructionGrammar.Resultatives
open Aspect
open ArgumentStructure
open Causation.CCSelection

/-! ### Agreement with the constructional flags -/

/-- A subconstruction is causative iff its constructional subevent carries CAUSE. -/
theorem causative_iff_has_cause (sc : ResultativeSubconstruction) :
    sc.isCausative = sc.constructionalDesc.hasCause := by
  cases sc <;> rfl

/-! ### Selection -/

/-- Resultatives select by completion of a sufficient set, as change-of-state verbs do: the
verbal subevent is the final condition that makes the result inevitable. -/
def resultativeCCSelection : CCSelectionMode := .completionOfSufficientSet

/-! ### The causative derived from the means relation and CAUSE

The verbal subevent of a causative resultative is the means by which the constructional
subevent comes about, and a causative subconstruction carries CAUSE, so the construction
asserts sufficiency; among the sufficiency causatives `make` is the neutral one, neither the
coercive `force` nor the barrier-removing `enable`. The derivation covers means-relation
resultatives only; the sound-emission and disappearance subtypes, with the result and
instance relations, are left undetermined. -/

/-- The causative a subevent relation and a constructional subevent description determine,
`make` for the means relation with CAUSE and nothing otherwise. -/
def deriveCausativeBuilder (rel : SubeventRelation) (desc : SubeventDesc) :
    Option Causative :=
  match rel, desc.hasCause with
  | .means, true => some .make
  | _, _ => none

/-- `make` is the one sufficiency causative that neither coerces nor removes a barrier. -/
theorem make_unique_neutral_sufficiency (b : Causative)
    (hs : b.AssertsSufficiency)
    (hc : b ≠ .force)
    (hp : b ≠ .enable) :
    b = .make := by
  rcases hs with rfl | rfl | rfl <;> simp_all

/-- The means relation with CAUSE derives `make`. -/
theorem means_cause_derives_make (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc = some .make := by
  simp [deriveCausativeBuilder, h]

/-- Every causative subconstruction with the means relation derives `make`. -/
theorem causative_means_derives_make (sc : ResultativeSubconstruction)
    (h : sc.isCausative = true) :
    deriveCausativeBuilder .means sc.constructionalDesc = some .make := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [deriveCausativeBuilder, ResultativeSubconstruction.constructionalDesc]

/-- A noncausative subconstruction derives no causative. -/
theorem noncausative_no_builder (sc : ResultativeSubconstruction)
    (h : sc.isCausative = false) :
    deriveCausativeBuilder .means sc.constructionalDesc = none := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [deriveCausativeBuilder, ResultativeSubconstruction.constructionalDesc]

/-- No relation other than means derives a causative. -/
theorem non_means_no_builder (desc : SubeventDesc) :
    deriveCausativeBuilder .result desc = none ∧
    deriveCausativeBuilder .instance_ desc = none ∧
    deriveCausativeBuilder .coOccurrence desc = none := by
  simp [deriveCausativeBuilder]

/-- A derived causative asserts sufficiency. -/
theorem derived_asserts_sufficiency (rel : SubeventRelation) (desc : SubeventDesc)
    (b : Causative) (h : deriveCausativeBuilder rel desc = some b) :
    b.AssertsSufficiency := by
  unfold deriveCausativeBuilder at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact .inl rfl
  · simp at h

/-- The causative of the causative resultative, derived from the means relation and CAUSE. -/
def resultativeCausativeBuilder : Causative :=
  match deriveCausativeBuilder .means
    ResultativeSubconstruction.causativeProperty.constructionalDesc with
  | some b => b
  | none => .cause

/-- The derived causative is `make`. -/
theorem resultative_is_make :
    resultativeCausativeBuilder = .make := rfl

/-- `prevent` is incompatible with the resultative. -/
theorem prevent_incompatible_with_resultative :
    Causative.prevent ≠ resultativeCausativeBuilder := by decide

/-! ### Aspect -/

/-- A bounded result phrase telicizes an activity. -/
theorem resultative_telicizes :
    activityProfile.telicize.toVendlerClass = .accomplishment :=
  telicize_activity

/-- The construction's aspect shift. -/
theorem resultative_aspect_shift :
    resultativeVendlerClass .bounded = .accomplishment :=
  rfl

theorem resultative_aspect_agrees_with_telicize :
    resultativeVendlerClass .bounded =
    activityProfile.telicize.toVendlerClass :=
  rfl

/-! ### Change of state -/

/-- The constructional BECOME is an inception, a change from the result state failing to hold
to its holding. -/
def resultStateMapsToCoS : CoSType := .inception

/-- An inception presupposes that the state failed to hold before. -/
theorem inception_presupposes_not_prior {W : Type*} (P : W → Prop) (w : W) :
    priorStatePresup .inception P w ↔ ¬P w := Iff.rfl

/-- An inception asserts the state afterwards. -/
theorem inception_asserts_result {W : Type*} (P : W → Prop) :
    resultStateAssertion .inception P = P := rfl

/-! ### Typological parameters -/

/-- How a language realizes the result phrase. -/
inductive ResultativeRealization where
  | syntacticAdjunct
  | verbCompound
  | deComplement
  deriving DecidableEq, Repr

/-- Whether the result phrase is predicated of the object or the subject. -/
inductive ResultOrientation where
  | objectOriented
  | subjectOriented
  deriving DecidableEq, Repr

end Causation.Resultatives
