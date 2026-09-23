module

public import Linglib.Semantics.Conditionals.Counterfactual.Lumping

/-!
# Premise-semantic counterfactuals

This file defines the premise semantics for counterfactuals of [kratzer-2012] §5.4.4. A
counterfactual is evaluated at a world against a Base Set of true propositions characterizing
it. Its Crucial Set for an antecedent consists of the sets of Base-Set propositions that, together
with the antecedent, are consistent and closed under lumping at the world. *If p, would q* is true
when every member of the Crucial Set extends to one from which `q` follows, and *if p, might q*
when some member has every extension compatible with `q`.

## Main definitions

* `PremiseSemantic.CrucialSet`: the Crucial Set of a Base Set and an antecedent.
* `PremiseSemantic.wouldCF`, `PremiseSemantic.mightCF`: the *would* and *might* counterfactuals.

## Implementation notes

The Base Set is a parameter. Kratzer's admissibility conditions on it (pp. 132–133) are not
enforced, one of them, cognitive viability, being in her words "the big unknown" (p. 133).

## References

* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
-/

@[expose] public section


namespace Conditional.PremiseSemantic

open _root_.Conditional.Counterfactual (Lumps IsConsistent IsCompatible Follows
  isCompatible_iff_not_follows_compl)

variable {S : Type*} [Preorder S]

/-- A subset `A` of `Fw ∪ {p}` belongs to the Crucial Set at `w` when it contains the antecedent, is
consistent, and is closed under lumping at `w` ([kratzer-2012] §5.4.4, p. 133). -/
structure IsCrucialSet (Fw : Set (Set S)) (w : S)
    (p : Set S) (A : Set (Set S)) : Prop where
  /-- `A` is a subset of `Fw ∪ {p}`. -/
  subset_insert : A ⊆ insert p Fw
  /-- The antecedent is in `A`. -/
  antecedent_mem : p ∈ A
  /-- Some world satisfies every member of `A`. -/
  consistent : IsConsistent A
  /-- Every Base-Set proposition lumped at `w` by a member of `A` is in `A`. -/
  lumping_closed : ∀ q ∈ A, ∀ r ∈ Fw, Lumps q r w → r ∈ A

/-- The Crucial Set of the Base Set `Fw` and the antecedent `p` at `w` ([kratzer-2012] §5.4.4,
p. 133). -/
def CrucialSet (Fw : Set (Set S)) (w : S) (p : Set S) :
    Set (Set (Set S)) :=
  { A | IsCrucialSet Fw w p A }

@[simp] theorem mem_crucialSet_iff {Fw : Set (Set S)} {w : S}
    {p : Set S} {A : Set (Set S)} :
    A ∈ CrucialSet Fw w p ↔ IsCrucialSet Fw w p A := Iff.rfl

/-- The *would*-counterfactual *if p, would q* is true at `w` when every member of the Crucial Set
has an extension in the Crucial Set from which `q` follows ([kratzer-2012] §5.4.4, p. 133). -/
def wouldCF (Fw : Set (Set S)) (w : S) (p q : Set S) :
    Prop :=
  ∀ A ∈ CrucialSet Fw w p, ∃ A' ∈ CrucialSet Fw w p, A ⊆ A' ∧ Follows A' q

/-- The *might*-counterfactual *if p, might q* is true at `w` when some member of the Crucial
Set has every extension in the Crucial Set compatible with `q` ([kratzer-2012] §5.4.4,
p. 133). -/
def mightCF (Fw : Set (Set S)) (w : S) (p q : Set S) :
    Prop :=
  ∃ A ∈ CrucialSet Fw w p,
    ∀ A' ∈ CrucialSet Fw w p, A ⊆ A' → IsCompatible q A'

/-! ### Basic API -/

/-- With an empty Crucial Set the *would*-counterfactual is vacuously true. -/
theorem wouldCF_of_crucialSet_empty {Fw : Set (Set S)} {w : S}
    {p q : Set S} (h : CrucialSet Fw w p = ∅) :
    wouldCF Fw w p q := by
  intro A hA
  exact ((Set.mem_empty_iff_false A).mp (h ▸ hA)).elim

/-- With an empty Crucial Set the *might*-counterfactual is false. -/
theorem not_mightCF_of_crucialSet_empty {Fw : Set (Set S)}
    {w : S} {p q : Set S} (h : CrucialSet Fw w p = ∅) :
    ¬ mightCF Fw w p q := by
  rintro ⟨A, hA, _⟩
  exact (Set.mem_empty_iff_false A).mp (h ▸ hA)

/-- *If p, might q* is the negation of *if p, would not q* ([kratzer-2012] p. 125), since
compatibility with a premise set is the failure of the complement to follow from it. -/
theorem mightCF_iff_not_wouldCF_compl {Fw : Set (Set S)} {w : S}
    {p q : Set S} :
    mightCF Fw w p q ↔ ¬ wouldCF Fw w p qᶜ := by
  simp only [mightCF, wouldCF, isCompatible_iff_not_follows_compl, not_forall, not_exists,
    not_and, exists_prop]

end Conditional.PremiseSemantic
