import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.List.Basic

/-!
# Rules of exponence: derived specificity and Elsewhere selection
[kiparsky-1973] [halle-marantz-1993] [stump-2001]

The shared realization core of the morphology formalisms. A rule of
exponence pairs an exponent with an applicability condition on
contexts; Pāṇinian specificity is *derived* as applicability-set
inclusion ([kiparsky-1973]'s Elsewhere Condition compares rule domains,
not stipulated ranks); an Elsewhere winner is a maximally specific
applicable rule.

Framework engines specialize the context type and expose *intensional*
context specifications from which the derived order is computable:

* `Morphology.Containment.ExponenceRule` — contexts are the grades of a
  containment hierarchy; specificity is threshold comparison
  (`Containment.ExponenceRule.moreSpecific_iff_threshold_le`).
* `Minimalist.VocabEntry` (`Morphology/DM/VocabSimple.lean`) — contexts
  are feature bundles; feature-superset entries are at least as
  specific.
* `Morphology.DM.VI.VocabItem` — contexts are opaque predicates, so the
  derived order is not computable and the engine stipulates a
  `specificity` rank; `SpecificityFaithful` states that the stipulation
  refines the derived order, and under it the engine's selection is an
  Elsewhere winner.

## Main declarations

* `Rule Ctx F` — exponent plus applicability condition
* `Rule.MoreSpecific` — derived Pāṇinian specificity
* `IsElsewhereWinner` — maximally specific applicable rule in a
  vocabulary
-/

namespace Morphology.Exponence

variable {Ctx F : Type*}

/-- A **rule of exponence**: an exponent paired with the condition on
contexts under which the rule applies. The realizational core shared by
vocabulary-insertion engines; framework engines specialize `Ctx` and
recover applicability from intensional specifications (thresholds,
feature bundles). -/
structure Rule (Ctx : Type*) (F : Type*) where
  /-- The exponent the rule inserts. -/
  exponent : F
  /-- The contexts in which the rule applies. -/
  Applies : Ctx → Prop

namespace Rule

/-- Derived Pāṇinian specificity: `r` is at least as specific as `s`
when `r` applies in a subset of the contexts `s` applies in. -/
def MoreSpecific (r s : Rule Ctx F) : Prop :=
  ∀ ⦃c : Ctx⦄, r.Applies c → s.Applies c

@[refl] theorem MoreSpecific.refl (r : Rule Ctx F) : r.MoreSpecific r :=
  λ _ h => h

theorem MoreSpecific.trans {r s t : Rule Ctx F}
    (hrs : r.MoreSpecific s) (hst : s.MoreSpecific t) : r.MoreSpecific t :=
  λ _ h => hst (hrs h)

instance : Trans (MoreSpecific (Ctx := Ctx) (F := F)) MoreSpecific MoreSpecific :=
  ⟨MoreSpecific.trans⟩

end Rule

/-- `r` is an **Elsewhere winner** for vocabulary `v` at context `c`:
`r` is an applicable member of `v`, and no applicable member is
strictly more specific — any applicable rival at least as specific as
`r` is exactly as specific. -/
def IsElsewhereWinner (v : List (Rule Ctx F)) (c : Ctx) (r : Rule Ctx F) : Prop :=
  r ∈ v ∧ r.Applies c ∧
    ∀ s ∈ v, s.Applies c → s.MoreSpecific r → r.MoreSpecific s

/-- Two Elsewhere winners at the same context are mutually specific
whenever their specificities are comparable. -/
theorem IsElsewhereWinner.mutual {v : List (Rule Ctx F)} {c : Ctx}
    {r s : Rule Ctx F} (hr : IsElsewhereWinner v c r)
    (hs : IsElsewhereWinner v c s) (h : s.MoreSpecific r) :
    r.MoreSpecific s :=
  hr.2.2 s hs.1 hs.2.1 h

end Morphology.Exponence
