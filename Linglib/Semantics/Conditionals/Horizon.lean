module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Presupposition.Defs

/-!
# The modal-horizon counterfactual

On von Fintel's dynamic strict analysis, a counterfactual quantifies over a modal horizon, a set
of worlds accessible from each evaluation point that the context widens as needed. *If p, would
q* presupposes that the horizon admits `p` and asserts that every `p`-world of the horizon is a
`q`-world, the strict conditional `Conditional.strictImp` over the horizon. Strengthening the
antecedent is then not classically valid, since the strengthened antecedent may fall outside the
horizon, but it is valid wherever the conclusion's presupposition holds.

## Main definitions

* `Conditional.horizonCounterfactual`: the counterfactual over a modal horizon.

## Main results

* `Conditional.exists_mem_of_holds_horizonCounterfactual`: a defined and true counterfactual has a
  horizon-world where antecedent and consequent hold together.

## Implementation notes

The admissibility of the horizon with respect to an ordering source, a condition on the context
that does not mention the antecedent, is left to the caller. Von Fintel's page prints the
consequent as evaluated at `w`; it is evaluated at the horizon-world `w'`, as here.

## References

* [von-fintel-1999]
* [von-fintel-2000]
-/

@[expose] public section

namespace Conditional

open Presupposition

variable {I W : Type*} (horizon : I → Set W) (p q : Set W)

/-- *If p, would q* over a modal horizon presupposes that the horizon admits `p` and asserts the
strict conditional over the horizon ([von-fintel-1999]'s (82) and (83)). -/
def horizonCounterfactual : PartialProp I where
  presup i := (horizon i ∩ p).Nonempty
  assertion i := i ∈ strictImp horizon p q

variable {horizon p q} {i : I}

@[simp] theorem horizonCounterfactual_presup :
    (horizonCounterfactual horizon p q).presup i ↔ (horizon i ∩ p).Nonempty := Iff.rfl

@[simp] theorem horizonCounterfactual_assertion :
    (horizonCounterfactual horizon p q).assertion i ↔ horizon i ∩ p ⊆ q := Iff.rfl

/-- A defined and true counterfactual has a horizon-world where its antecedent and consequent hold
together. -/
theorem exists_mem_of_holds_horizonCounterfactual
    (h : (horizonCounterfactual horizon p q).holds i) : ∃ w ∈ horizon i, w ∈ p ∧ w ∈ q :=
  let ⟨w, hw⟩ := h.1
  ⟨w, hw.1, hw.2, h.2 hw⟩

end Conditional
