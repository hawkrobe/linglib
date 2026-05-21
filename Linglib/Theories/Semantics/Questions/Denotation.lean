import Linglib.Theories.Semantics.Questions.Basic
import Linglib.Core.Logic.Modal.Inquisitive

/-!
# Denotations of logics into Question

@cite{ciardelli-2022} @cite{ciardelli-groenendijk-roelofsen-2018}

Semantic-theory claim: formulas of various inquisitive-flavored logics
denote inquisitive contents (`Question`). This file collects the
denotation maps for each logic in tree that can be interpreted into
Question-space.

## Logics covered

* **InqML** (`Core/Logic/Modal/Inquisitive.lean`) — Ciardelli 2022 Ch 8
  modal inquisitive logic. The denotation `ofInqML M φ` packages the
  set of supporting teams (viewed as info states via the canonical
  `Finset W → Set W` coercion) into a `Question W`.

## Type alignment

InqML's support is `support M φ : Finset W → Prop` (teams = Finsets of
worlds). CGR's `Question W` has `props : Set (Set W)` (info states
= subsets of worlds). The bridge uses the `Finset W → Set W` coercion
to translate supporting teams into info states.

## Compositionality

The compositionality theorems — `ofInqML (.conj φ ψ) = ofInqML φ ⊓ ofInqML ψ`
and similarly for inqDisj, impl, bot — hold mathematically but require
careful handling of the Finset/Set bridge. They're deferred to a
follow-up PR once a downstream consumer (TRA 2018 study) needs them.
The current PR establishes only the bridge itself + the membership
characterization.

## Future logics

* MDL — same closure cell as InqML (downward-closed + empty); direct
  analogue of `ofInqML` should work.
* MIL — sup-closed but NOT downward-closed; standard `Question`
  denotation doesn't apply. Would need a sibling content substrate.

## References

* @cite{ciardelli-2022} Chapter 8 — InqML modal preview
* @cite{ciardelli-groenendijk-roelofsen-2018} Chapter 2 + 3 —
  inquisitive proposition algebra
-/

namespace Theories.Semantics.Questions.Denotation

open Core.Logic.Modal (KripkeModel)
open Core.Logic.Modal.Inquisitive

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

/-- The inquisitive content denoted by an InqML formula at a Kripke
    model. A state `s : Set W` is in the denotation iff some supporting
    team `t : Finset W` coerces to `s`.

    Downward closure follows from InqML's persistence
    (`support_isLowerSet`); empty-team property follows from
    `support_empty`. -/
def ofInqML (M : KripkeModel W Atom) (φ : Formula Atom) : Question W where
  props := (fun t : Finset W => (↑t : Set W)) '' { t : Finset W | support M φ t }
  contains_empty := ⟨∅, support_empty M φ, by simp⟩
  downward_closed := fun p ⟨t, ht_supp, ht_eq⟩ q hq => by
    have hqfin : q.Finite := Set.toFinite q
    refine ⟨hqfin.toFinset, ?_, by simp⟩
    apply support_isLowerSet M φ _ ht_supp
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    have : w ∈ p := hq hw
    rw [← ht_eq] at this
    exact Finset.mem_coe.mp this

/-- Membership in the InqML denotation: a state `s : Set W` is in the
    Question iff some supporting team `t : Finset W` coerces to `s`. -/
theorem mem_ofInqML (M : KripkeModel W Atom) (φ : Formula Atom) (s : Set W) :
    s ∈ (ofInqML M φ).props ↔ ∃ t : Finset W, ↑t = s ∧ support M φ t := by
  simp only [ofInqML, Set.mem_image, Set.mem_setOf_eq]
  exact ⟨fun ⟨t, ht_supp, ht_eq⟩ => ⟨t, ht_eq, ht_supp⟩,
         fun ⟨t, ht_eq, ht_supp⟩ => ⟨t, ht_supp, ht_eq⟩⟩

end Theories.Semantics.Questions.Denotation
