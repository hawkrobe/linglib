import Linglib.Semantics.Questions.Hamblin
import Mathlib.Data.Fintype.Powerset

/-!
# Question entailment through alternatives

Question entailment is the lattice order on `Question W`: `P ≤ Q` when every state resolving
`P` resolves `Q` ([ciardelli-groenendijk-roelofsen-2018]). This file characterises the order
through alternatives, the maximal resolving states: under finiteness `P ≤ Q` iff every
alternative of `P` lies under some alternative of `Q` (`le_iff_forall_alt_exists_alt`),
[roberts-2012]'s statement (8) of [groenendijk-stokhof-1984]'s entailment, and on polar
questions the order reduces to set inclusions (`polar_le_polar_iff`).

## Implementation notes

The alternative characterisation matches [groenendijk-stokhof-1984] entailment only where
alternatives are complete answers (partition and polar contents; not mention-some `which`),
[roberts-2012]'s own caveat, and the finiteness hypotheses are what supply maximal extensions;
without them a question may have no alternatives at all.

## References

* [ciardelli-groenendijk-roelofsen-2018]
* [groenendijk-stokhof-1984]
* [roberts-2012]
-/

namespace Question

variable {W : Type*} {P Q : Question W}

/-- Every alternative of `P` lies under some alternative of `Q` when `P ≤ Q`; finiteness
supplies the maximal extension. -/
theorem forall_alt_exists_alt_of_le (h : P ≤ Q) (hQ : Q.props.Finite) :
    ∀ p ∈ alt P, ∃ q ∈ alt Q, p ⊆ q :=
  λ _ hp => exists_alt_above Q hQ ((le_def.mp h) (alt_subset_props P hp))

/-- `P ≤ Q` once every alternative of `P` lies under some alternative of `Q`; finiteness of
`P` places every resolving state under an alternative. -/
theorem le_of_forall_alt_exists_alt (hP : P.props.Finite)
    (h : ∀ p ∈ alt P, ∃ q ∈ alt Q, p ⊆ q) : P ≤ Q := by
  rw [le_def]
  intro s hs
  obtain ⟨p, hp, hsp⟩ := exists_alt_above P hP hs
  obtain ⟨q, hq, hpq⟩ := h p hp
  exact Q.downward_closed q (alt_subset_props Q hq) s (hsp.trans hpq)

/-- Under finiteness, question entailment is the alternative-wise condition. -/
theorem le_iff_forall_alt_exists_alt (hP : P.props.Finite) (hQ : Q.props.Finite) :
    P ≤ Q ↔ ∀ p ∈ alt P, ∃ q ∈ alt Q, p ⊆ q :=
  ⟨(forall_alt_exists_alt_of_le · hQ), le_of_forall_alt_exists_alt hP⟩

/-- Entailment between polar questions is a pair of inclusion disjunctions. -/
theorem polar_le_polar_iff (p q : Set W) :
    polar p ≤ polar q ↔ (p ⊆ q ∨ p ⊆ qᶜ) ∧ (pᶜ ⊆ q ∨ pᶜ ⊆ qᶜ) := by
  rw [polar_eq_sup p, sup_le_iff, ← mem_iff_ofSet_le, ← mem_iff_ofSet_le, mem_polar, mem_polar]

end Question
