module

public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Logic.Relation
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Data.Set.Functor

/-!
# Reciprocal predicates

A reciprocal scheme is a predicate on a relation `R : A → A → Prop` and a finite set
`X : Finset A`, saying how much of `R` must hold among the members of `X` for *the Xs R each
other* to be true. Dalrymple, Kanazawa, Kim, Mchombo and Peters vary the schemes along two
parameters: how `R` must cover `X` (every two distinct members related directly, every two
joined by an `R`-chain, or every member related to some other), and whether `R` is taken as it
is or with its direction ignored, as `Relation.SymmGen R`. Their six schemes, `Reciprocal.Recip`
at the six settings, are ordered by entailment as the product of the two parameters. Weak
Reciprocity and Partitioned Strong Reciprocity lie outside the parameterization; with them the
file covers the six readings that Beck orders by entailment.

## Main definitions

* `Reciprocal.StrongReciprocity R X`: any two distinct members of `X` are `R`-related.
* `Reciprocal.IntermediateReciprocity R X`: any two distinct members of `X` are joined by an
  `R`-chain within `X`.
* `Reciprocal.OneWayWeakReciprocity R X`: every member of `X` is `R`-related to another member.
* `Reciprocal.InclusiveAlternativeOrdering R X`: One-way Weak Reciprocity at
  `Relation.SymmGen R`.
* `Reciprocal.Recip q R X`: the scheme at a setting `q : Coverage × Direction` of the two
  parameters.
* `Reciprocal.WeakReciprocity R X`: every member of `X` is `R`-related to another member, and
  another member is `R`-related to it.
* `Reciprocal.PartitionedStrongReciprocity R X`: `X` has a `Finpartition` into strongly
  reciprocal cells of two or more members.

## Main results

* `Reciprocal.recip_antitone`: on two or more members, a stronger setting of the parameters
  entails a weaker one.
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
of `R` within `X`, so any two distinct members are joined by a chain of `R`-steps through
`X`. -/
def IntermediateReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  StrongReciprocity (TransGen fun a b ↦ a ∈ X ∧ b ∈ X ∧ R a b) X

/-- One-way Weak Reciprocity ([dalrymple-et-al-1998]) holds when every member of `X` is
`R`-related to another member. -/
def OneWayWeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y

/-- Inclusive Alternative Ordering ([kanski-1987]) is One-way Weak Reciprocity with the direction
of `R` ignored, so every member of `X` is `R`-related to another member in one direction or the
other. -/
def InclusiveAlternativeOrdering (R : A → A → Prop) (X : Finset A) : Prop :=
  OneWayWeakReciprocity (SymmGen R) X

section Decidable

variable [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A)

instance : Decidable (StrongReciprocity R X) :=
  inferInstanceAs (Decidable ((X : Set A).Pairwise R))

instance : Decidable (OneWayWeakReciprocity R X) :=
  inferInstanceAs (Decidable (∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y))

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
form `Set.LiftRel`, the bivalent common ground of [beck-2001] and [sternefeld-1998]. -/
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

/-! ### The two parameters

Dalrymple and colleagues obtain their six schemes from two parameters: how the relation must cover
the antecedent set, and whether it is the scope relation or that relation with its direction
ignored. Each parameter is ordered by strength, and on two or more members the schemes are
antitone in the product order. -/

/-- How the reciprocal's relation must cover the antecedent set, ordered by strength. -/
inductive Coverage where
  /-- Every member is related to another member, `TOT∖I`. -/
  | tot
  /-- Every two distinct members are joined by a chain, `LIN∖I`. -/
  | lin
  /-- Every two distinct members are related directly, `FUL∖I`. -/
  | ful
  deriving DecidableEq, Repr, Fintype

/-- The strength of a coverage requirement. -/
def Coverage.rank : Coverage → ℕ
  | .tot => 0
  | .lin => 1
  | .ful => 2

instance : LinearOrder Coverage := LinearOrder.lift' Coverage.rank (by decide)

/-- Whether the reciprocal relates the members by the scope relation itself or by that relation
with its direction ignored, ordered by strength. -/
inductive Direction where
  /-- The relation with its direction ignored, `Relation.SymmGen R`. -/
  | alternative
  /-- The scope relation itself. -/
  | plain
  deriving DecidableEq, Repr, Fintype

/-- The strength of a direction setting. -/
def Direction.rank : Direction → ℕ
  | .alternative => 0
  | .plain => 1

instance : LinearOrder Direction := LinearOrder.lift' Direction.rank (by decide)

/-- The relation a direction setting takes from the scope relation `R`. -/
def Direction.rel : Direction → (A → A → Prop) → A → A → Prop
  | .alternative, R => SymmGen R
  | .plain, R => R

theorem Direction.rel_anti {d d' : Direction} (h : d ≤ d') : d'.rel R ≤ d.rel R := by
  cases d <;> cases d'
  · exact le_rfl
  · exact fun _ _ ↦ .of_rel
  · exact absurd h (by decide)
  · exact le_rfl

/-- The reciprocal quantifier of [dalrymple-et-al-1998] at a setting of the two parameters. The
setting `(.ful, .plain)` gives Strong Reciprocity, `(.lin, .plain)` Intermediate Reciprocity,
`(.tot, .plain)` One-way Weak Reciprocity, and `(.tot, .alternative)` Inclusive Alternative
Ordering. -/
def Recip : Coverage × Direction → (A → A → Prop) → Finset A → Prop
  | (.ful, d), R, X => StrongReciprocity (d.rel R) X
  | (.lin, d), R, X => IntermediateReciprocity (d.rel R) X
  | (.tot, d), R, X => OneWayWeakReciprocity (d.rel R) X

/-- The entailment diagram of [dalrymple-et-al-1998]. On two or more members, a stronger setting
of the two parameters entails a weaker one. -/
theorem recip_antitone (hX : 2 ≤ X.card) : Antitone fun q ↦ Recip q R X := by
  rintro ⟨c, d⟩ ⟨c', d'⟩ hle h
  obtain ⟨hc, hd⟩ := Prod.mk_le_mk.1 hle
  have h' : Recip (c', d) R X := by
    cases c' with
    | ful => exact StrongReciprocity.mono h (Direction.rel_anti hd)
    | lin => exact IntermediateReciprocity.mono h (Direction.rel_anti hd)
    | tot => exact OneWayWeakReciprocity.mono h (Direction.rel_anti hd)
  cases c <;> cases c'
  all_goals first
    | exact h'
    | exact absurd hc (by decide)
    | exact StrongReciprocity.intermediate h'
    | exact IntermediateReciprocity.oneWayWeak h' hX
    | exact IntermediateReciprocity.oneWayWeak (StrongReciprocity.intermediate h') hX

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
