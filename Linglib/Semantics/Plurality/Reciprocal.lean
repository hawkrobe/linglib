module

public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Logic.Relation
public import Mathlib.Order.Partition.Finpartition
public import Linglib.Core.Data.Set.Functor

/-!
# Reciprocal predicates

A reciprocal scheme is a predicate on a relation `R : A → A → Prop` and a finite set
`X : Finset A`, saying how much of `R` must hold among the members of `X` for *the Xs R each
other* to be true. Dalrymple, Kanazawa, Kim, Mchombo and Peters vary the schemes along two
parameters: how `R` must cover `X` (every two distinct members related directly, every two
joined by an `R`-chain, or every member related to some other), and whether `R` is taken as it
is or with its direction ignored, as `Relation.SymmGen R`. Their six schemes are ordered by
entailment as the product of the two parameters. Weak Reciprocity and Partitioned Strong
Reciprocity lie outside the parameterization; with them the file covers the six readings that
Beck orders by entailment.

## Main definitions

* `Reciprocal.StrongReciprocity R X`: any two distinct members of `X` are `R`-related.
* `Reciprocal.IntermediateReciprocity R X`: any two distinct members of `X` are joined by an
  `R`-chain within `X`.
* `Reciprocal.OneWayWeakReciprocity R X`: every member of `X` is `R`-related to another member.
* `Reciprocal.StrongAlternativeReciprocity`, `Reciprocal.IntermediateAlternativeReciprocity`,
  `Reciprocal.InclusiveAlternativeOrdering`: the three schemes at `Relation.SymmGen R`.
* `Reciprocal.WeakReciprocity R X`: every member of `X` is `R`-related to another member, and
  another member is `R`-related to it.
* `Reciprocal.PartitionedStrongReciprocity R X`: `X` has a `Finpartition` into strongly
  reciprocal cells of two or more members.

## Main results

* `Reciprocal.StrongReciprocity.intermediate`, `Reciprocal.IntermediateReciprocity.oneWayWeak`
  and the monotonicity of the schemes in `R`: the entailments among the six parameterized
  schemes, as the dot lemmas leaving each scheme.
* `Reciprocal.IntermediateReciprocity.weak`, `Reciprocal.PartitionedStrongReciprocity.weak`:
  Weak Reciprocity follows from the intermediate and the partitioned schemes.
* `Reciprocal.weakReciprocity_iff_liftRel`: Weak Reciprocity is the cumulation `Set.LiftRel` of
  `R` with non-identity conjoined in.

## Implementation notes

Every scheme of Dalrymple and colleagues also requires `X` to have two or more members. Here
that requirement is a hypothesis of the entailments that need it rather than a conjunct of the
definitions, so that a scheme is a condition on `R` alone.

## References

* [D. T. Langendoen, *The logic of reciprocity* (1978)][langendoen-1978]
* [R. Fiengo and H. Lasnik, *The logical structure of reciprocal sentences in English*
  (1973)][fiengo-lasnik-1973]
* [Z. Kański, *Logical symmetry and natural language reciprocals* (1987)][kanski-1987]
* [M. Dalrymple, M. Kanazawa, Y. Kim, S. A. Mchombo and S. Peters, *Reciprocal expressions and
  the concept of reciprocity* (1998)][dalrymple-et-al-1998]
* [S. Beck, *Reciprocals are definites* (2001)][beck-2001]
* [W. Sternefeld, *Reciprocity and cumulative predication* (1998)][sternefeld-1998]
-/

@[expose] public section

namespace Reciprocal

open Relation

variable {A : Type*} {R S : A → A → Prop} {X : Finset A}

/-! ### The parameterized schemes -/

/-- Strong Reciprocity ([langendoen-1978]) holds when any two distinct members of `X` are
`R`-related. -/
def StrongReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  (X : Set A).Pairwise R

/-- Intermediate Reciprocity ([langendoen-1978]) is Strong Reciprocity of the transitive closure
of `R` within `X`: any two distinct members are joined by a chain of `R`-steps through `X`. -/
def IntermediateReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  StrongReciprocity (TransGen fun a b ↦ a ∈ X ∧ b ∈ X ∧ R a b) X

/-- One-way Weak Reciprocity ([dalrymple-et-al-1998]) holds when every member of `X` is
`R`-related to another member. -/
def OneWayWeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y

/-- Strong Alternative Reciprocity ([dalrymple-et-al-1998]) is Strong Reciprocity with the
direction of `R` ignored. -/
def StrongAlternativeReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  StrongReciprocity (SymmGen R) X

/-- Intermediate Alternative Reciprocity ([dalrymple-et-al-1998]) is Intermediate Reciprocity
with the direction of `R` ignored: `X` is connected by `R`. -/
def IntermediateAlternativeReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  IntermediateReciprocity (SymmGen R) X

/-- Inclusive Alternative Ordering ([kanski-1987]) is One-way Weak Reciprocity with the direction
of `R` ignored: every member of `X` is `R`-related to another member in one direction or the
other. -/
def InclusiveAlternativeOrdering (R : A → A → Prop) (X : Finset A) : Prop :=
  OneWayWeakReciprocity (SymmGen R) X

section Decidable

variable [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A)

instance : Decidable (StrongReciprocity R X) :=
  inferInstanceAs (Decidable ((X : Set A).Pairwise R))

instance : Decidable (OneWayWeakReciprocity R X) :=
  inferInstanceAs (Decidable (∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y))

instance : Decidable (StrongAlternativeReciprocity R X) :=
  inferInstanceAs (Decidable (StrongReciprocity (SymmGen R) X))

instance : Decidable (InclusiveAlternativeOrdering R X) :=
  inferInstanceAs (Decidable (OneWayWeakReciprocity (SymmGen R) X))

end Decidable

/-! ### Entailments among the parameterized schemes -/

theorem StrongReciprocity.mono (h : StrongReciprocity R X) (hRS : R ≤ S) :
    StrongReciprocity S X :=
  Set.Pairwise.mono' hRS h

theorem IntermediateReciprocity.mono (h : IntermediateReciprocity R X) (hRS : R ≤ S) :
    IntermediateReciprocity S X :=
  StrongReciprocity.mono h <| TransGen.mono fun a b ⟨ha, hb, hab⟩ ↦ ⟨ha, hb, hRS a b hab⟩

theorem OneWayWeakReciprocity.mono (h : OneWayWeakReciprocity R X) (hRS : R ≤ S) :
    OneWayWeakReciprocity S X :=
  fun x hx ↦ (h x hx).imp fun y ⟨hy, hxy, hne⟩ ↦ ⟨hy, hRS x y hxy, hne⟩

theorem StrongReciprocity.intermediate (h : StrongReciprocity R X) :
    IntermediateReciprocity R X :=
  fun _ hx _ hy hxy ↦ .single ⟨hx, hy, h hx hy hxy⟩

theorem StrongReciprocity.strongAlternative (h : StrongReciprocity R X) :
    StrongAlternativeReciprocity R X :=
  h.mono fun _ _ ↦ .of_rel

theorem IntermediateReciprocity.intermediateAlternative (h : IntermediateReciprocity R X) :
    IntermediateAlternativeReciprocity R X :=
  h.mono fun _ _ ↦ .of_rel

theorem StrongAlternativeReciprocity.intermediateAlternative
    (h : StrongAlternativeReciprocity R X) : IntermediateAlternativeReciprocity R X :=
  StrongReciprocity.intermediate h

theorem OneWayWeakReciprocity.inclusiveAlternativeOrdering (h : OneWayWeakReciprocity R X) :
    InclusiveAlternativeOrdering R X :=
  h.mono fun _ _ ↦ .of_rel

/-! ### Weak Reciprocity -/

/-- Weak Reciprocity ([langendoen-1978]) holds when every member of `X` is `R`-related to another
member, and another member is `R`-related to it. -/
def WeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  (∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y) ∧ ∀ y ∈ X, ∃ x ∈ X, R x y ∧ x ≠ y

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (WeakReciprocity R X) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Weak Reciprocity is `**` of the relation with non-identity conjoined into it, in the coverage
form `Set.LiftRel`: the bivalent common ground of [beck-2001] and [sternefeld-1998]. -/
theorem weakReciprocity_iff_liftRel (R : A → A → Prop) (X : Finset A) :
    WeakReciprocity R X ↔ Set.LiftRel (fun a b ↦ R a b ∧ a ≠ b) ↑X ↑X := Iff.rfl

theorem WeakReciprocity.oneWayWeak (h : WeakReciprocity R X) : OneWayWeakReciprocity R X :=
  h.1

private theorem exists_rel_ne_of_transGen {r : A → A → Prop} {x y : A}
    (h : TransGen r x y) (hyx : y ≠ x) : ∃ z, z ≠ x ∧ r x z := by
  induction h with
  | single h => exact ⟨_, hyx, h⟩
  | @tail b c _ hbc ih =>
    by_cases hbx : b = x
    · exact ⟨c, hyx, hbx ▸ hbc⟩
    · exact ih hbx

theorem IntermediateReciprocity.weak (h : IntermediateReciprocity R X) (hX : 2 ≤ X.card) :
    WeakReciprocity R X := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;> obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hX x
  · obtain ⟨z, hzx, -, hz, hR⟩ := exists_rel_ne_of_transGen (h hx hy hyx.symm) hyx
    exact ⟨z, hz, hR, hzx.symm⟩
  · obtain ⟨z, hzx, hz, -, hR⟩ :=
      exists_rel_ne_of_transGen (transGen_swap.2 (h hy hx hyx)) hyx
    exact ⟨z, hz, hR, hzx⟩

theorem IntermediateReciprocity.oneWayWeak (h : IntermediateReciprocity R X) (hX : 2 ≤ X.card) :
    OneWayWeakReciprocity R X :=
  (h.weak hX).oneWayWeak

theorem IntermediateAlternativeReciprocity.inclusiveAlternativeOrdering
    (h : IntermediateAlternativeReciprocity R X) (hX : 2 ≤ X.card) :
    InclusiveAlternativeOrdering R X :=
  IntermediateReciprocity.oneWayWeak h hX

/-! ### Partitioned Strong Reciprocity -/

/-- Partitioned Strong Reciprocity ([fiengo-lasnik-1973]) holds when `X` splits into disjoint
cells of two or more members, within each of which Strong Reciprocity holds. -/
def PartitionedStrongReciprocity [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ P : Finpartition X, ∀ c ∈ P.parts, 2 ≤ c.card ∧ StrongReciprocity R c

variable [DecidableEq A]

theorem StrongReciprocity.partitionedStrong (h : StrongReciprocity R X) (hX : 2 ≤ X.card) :
    PartitionedStrongReciprocity R X :=
  ⟨.indiscrete (Finset.card_pos.1 (by omega)).ne_empty, fun c hc ↦ by
    rw [Finpartition.indiscrete_parts, Finset.mem_singleton] at hc
    exact hc ▸ ⟨hX, h⟩⟩

theorem PartitionedStrongReciprocity.weak (h : PartitionedStrongReciprocity R X) :
    WeakReciprocity R X := by
  obtain ⟨P, hP⟩ := h
  have hW {x} (hx : x ∈ X) : ∃ c ∈ P.parts, x ∈ c ∧ WeakReciprocity R c :=
    let ⟨c, hc, hxc⟩ := P.exists_mem hx
    ⟨c, hc, hxc, (hP c hc).2.intermediate.weak (hP c hc).1⟩
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;> obtain ⟨c, hc, hxc, hWc⟩ := hW hx
  · obtain ⟨y, hy, hR⟩ := hWc.1 x hxc
    exact ⟨y, P.le hc hy, hR⟩
  · obtain ⟨y, hy, hR⟩ := hWc.2 x hxc
    exact ⟨y, P.le hc hy, hR⟩

end Reciprocal
