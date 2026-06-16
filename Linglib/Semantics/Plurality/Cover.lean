import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Linglib.Core.Order.Mereology

/-!
# Schwarzschild Covers and Partitions
[schwarzschild-1996] [champollion-2017]

A *cover* of a plurality `P` is a set of nonempty subpluralities of `P`
that jointly exhaust it ([schwarzschild-1996]). [schwarzschild-1996]'s
`Part` operator distributes a predicate over a *contextually-supplied*
cover (the free variable `Cov`), generalizing [higginbotham-1980]'s
partition-based distributivity to overlapping covers — so that
[gillon-1987]'s *the men wrote musicals* (Rodgers, Hammerstein, Hart; no
partition works, but the overlapping cover {Rodgers⊕Hammerstein,
Rodgers⊕Hart} does) comes out true.

Here covers are recast mereologically: parts are join-semilattice
elements and "jointly exhaust" becomes "least upper bound = whole" — the
⊕C = X form of [sauerland-2003] (the downstream consumer,
`Studies/Sauerland2003.lean`), which [champollion-2017] also adopts,
extending it to the temporal domain via stratified reference.
`IsFinCover` and `algClosure_of_finCover` are the substrate
[sauerland-2003]'s distributive ∗-operator uses.

## Main declarations

* `IsCover` — a set of parts whose least upper bound is the whole;
  definitionally mathlib's `IsLUB` (`isCover_iff_isLUB`), renamed for
  literature grounding.
* `IsPartition` — a cover whose parts are pairwise disjoint. The
  `Set`-valued, possibly-infinite analogue of mathlib's `Finpartition`;
  distinct from the `Setoid`-based `Questions.Partition.IsPartition`.
* `IsFinCover` — finite-cover specialisation via `Finset.sup'`, bridged
  to the general notion by `isFinCover_iff_isCover`.
* `algClosure_of_finCover` / `exists_finCover_of_algClosure` /
  `algClosure_iff_exists_finCover` — the equivalence between
  `Mereology.AlgClosure` (the implicit `∗`-closure) and existence of an
  explicit finite cover. This is [champollion-2017]'s Theorem 14
  (`x ∈ ∗λy[C(y)] ⇔ ∃ cover C′ of x with cells in C`), the bridge his
  stratified-reference ∗-operator rests on.

## Implementation notes

A cover is an EXPLICIT decomposition; `AlgClosure` is the IMPLICIT
closure. `algClosure_iff_exists_finCover` makes the two interconvertible
in the finite case. Stratified reference (`Semantics/Aspect/Stratified.lean`)
uses `AlgClosure` because the strata are existentially closed; covers are
the right primitive when the parts must be supplied (anaphoric
distributivity, contextually-salient partitions). The closure does not
fix a *unique* cover — the inductive `sum` constructor can be applied in
many orders — which is why the forward bridge yields *some* cover
(`∃`), not a canonical one.
-/

namespace Semantics.Plurality.Cover

open _root_.Mereology

/-! ### Cover -/

/-- *Cover* (mereological form): a set of parts whose least upper bound is
    the whole. [schwarzschild-1996] defines a cover set-theoretically — a
    set of nonempty subsets of the whole, with every atom in some cell;
    over a join-semilattice that exhaustion condition is `IsLUB parts
    whole` (`isCover_iff_isLUB`), the ⊕C = X form of [sauerland-2003].
    Parts may overlap; the "every part ≤ whole" condition is automatic,
    since the whole is by definition an upper bound. -/
def IsCover {α : Type*} [Preorder α] (parts : Set α) (whole : α) : Prop :=
  IsLUB parts whole

@[simp] theorem isCover_iff_isLUB {α : Type*} [Preorder α]
    {parts : Set α} {whole : α} : IsCover parts whole ↔ IsLUB parts whole :=
  Iff.rfl

/-! ### Partition -/

/-- [schwarzschild-1996] *partition*: a cover whose parts pairwise don't
    overlap — [higginbotham-1980]'s original partition-based
    distributivity domain, which [schwarzschild-1996] generalizes to
    arbitrary (possibly overlapping) covers to handle readings like
    [gillon-1987]'s *the men wrote musicals*. The `Set`-valued,
    possibly-infinite analogue of mathlib's `Finpartition`; not the
    `Setoid`-based `Questions.Partition.IsPartition`. Disjointness is
    meet-bottom, so the carrier needs `Lattice` + `OrderBot`. -/
def IsPartition {α : Type*} [Lattice α] [OrderBot α]
    (parts : Set α) (whole : α) : Prop :=
  IsCover parts whole ∧ parts.PairwiseDisjoint id

/-! ### Finite covers -/

/-- Finite cover: the typical linguistic case where the contextually
    salient set of parts is enumerable. Formalises [sauerland-2003]'s
    cover condition "⊕C = X" with `Finset.sup'`, which avoids the
    `OrderBot` requirement of `Finset.sup`.

    Example: in *the shoes cost fifty dollars* with the salient cover "by
    pairs of shoes", the cover is the finite set of pairs. -/
def IsFinCover {α : Type*} [SemilatticeSup α]
    (parts : Finset α) (h : parts.Nonempty) (whole : α) : Prop :=
  parts.sup' h id = whole

/-- A finite cover is a cover of its underlying set, via `isLUB_sup'`. -/
theorem isFinCover_iff_isCover {α : Type*} [SemilatticeSup α]
    {parts : Finset α} (h : parts.Nonempty) {whole : α} :
    IsFinCover parts h whole ↔ IsCover (↑parts) whole := by
  rw [isCover_iff_isLUB]
  constructor
  · intro hc
    unfold IsFinCover at hc
    exact hc ▸ Finset.isLUB_sup' h
  · intro hc
    exact (Finset.isLUB_sup' h).unique hc

/-! ### Bridge to `Mereology.AlgClosure`

`AlgClosure C x` (the implicit `∗`-closure of `C`) holds iff `x` admits an
explicit finite cover whose cells all satisfy `C` — [champollion-2017]'s
Theorem 14, the algebraic core of his stratified-reference ∗-operator
(`∗P` holds of a whole iff some cover has all cells in `P`). The forward
direction collects the `base`-leaves of the closure derivation into a
`Finset`; the reverse is `Finset.sup'_induction`. -/

/-- A finite cover whose parts all satisfy `P` witnesses `AlgClosure P whole`.
    The reverse direction of `algClosure_iff_exists_finCover`. -/
theorem algClosure_of_finCover {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {parts : Finset α} {h : parts.Nonempty} {whole : α}
    (hCover : IsFinCover parts h whole)
    (hP : ∀ p ∈ parts, P p) : AlgClosure P whole := by
  unfold IsFinCover at hCover
  rw [← hCover]
  exact Finset.sup'_induction h id
    (λ _ ha _ hb => AlgClosure.sum ha hb)
    (λ p hp => AlgClosure.base (hP p hp))

/-- Every `AlgClosure P` witness is covered by an explicit finite cover
    whose cells satisfy `P`: the `base`-leaves of the closure derivation,
    merged along each `sum`. The forward direction of
    `algClosure_iff_exists_finCover` ([champollion-2017] Theorem 14). -/
theorem exists_finCover_of_algClosure {α : Type*} [SemilatticeSup α] [DecidableEq α]
    {P : α → Prop} {whole : α} (h : AlgClosure P whole) :
    ∃ (parts : Finset α) (hne : parts.Nonempty),
      IsFinCover parts hne whole ∧ ∀ p ∈ parts, P p := by
  induction h with
  | @base z hz =>
    refine ⟨{z}, ⟨z, Finset.mem_singleton_self z⟩, ?_, ?_⟩
    · simp [IsFinCover]
    · intro p hp; rw [Finset.mem_singleton] at hp; exact hp ▸ hz
  | @sum a b _ _ iha ihb =>
    obtain ⟨pa, hpa, hcova, hCa⟩ := iha
    obtain ⟨pb, hpb, hcovb, hCb⟩ := ihb
    refine ⟨pa ∪ pb, hpa.mono Finset.subset_union_left, ?_, ?_⟩
    · have ha : IsLUB (↑pa) a := by
        rw [← isCover_iff_isLUB, ← isFinCover_iff_isCover]; exact hcova
      have hb : IsLUB (↑pb) b := by
        rw [← isCover_iff_isLUB, ← isFinCover_iff_isCover]; exact hcovb
      rw [isFinCover_iff_isCover, isCover_iff_isLUB, Finset.coe_union]
      exact ha.union hb
    · intro p hp
      rcases Finset.mem_union.mp hp with hpm | hpm
      · exact hCa p hpm
      · exact hCb p hpm

/-- **[champollion-2017] Theorem 14.** `AlgClosure P x` ⇔ `x` has an
    explicit finite cover with all cells in `P`. The implicit `∗`-closure
    and explicit Schwarzschild decomposition coincide in the finite case. -/
theorem algClosure_iff_exists_finCover {α : Type*} [SemilatticeSup α] [DecidableEq α]
    {P : α → Prop} {whole : α} :
    AlgClosure P whole ↔
      ∃ (parts : Finset α) (hne : parts.Nonempty),
        IsFinCover parts hne whole ∧ ∀ p ∈ parts, P p :=
  ⟨exists_finCover_of_algClosure,
   λ ⟨_, _, hCover, hP⟩ => algClosure_of_finCover hCover hP⟩

end Semantics.Plurality.Cover
