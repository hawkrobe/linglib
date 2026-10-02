/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.BirkhoffFactorizationSemiring
public import Linglib.Core.Algebra.RootedTree.Coproduct.Primitive
public import Linglib.Syntax.Minimalist.Linearization.Externalization
public import Linglib.Syntax.Minimalist.Economy.Derivation
public import Linglib.Syntax.Minimalist.SyntacticObject.Selection
public import Linglib.Syntax.Minimalist.FormCopy
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Marcolli, Chomsky and Berwick (2025): Mathematical Structure of Syntactic Merge

This file formalizes parts of Marcolli, Chomsky and Berwick's algebraic model of Merge.

Internal Merge (§1.4.4) is checked on the book's example, which raises *the apple* out of
`T = {was, {eaten, {the, apple}}}`. The unit stage `M_{T₂,1}` splits `T` into *the apple* beside
the quotient `T/T₂`, the composite with `M_{T/T₂,T₂}` merges the two (Proposition 1.4.2), and the
step satisfies Minimal Yield under trace counting (Proposition 1.6.4).

The core computational structure of Merge (§1.10) is a fixed point. Proposition 1.10.2 works in
`V(𝔗)`, the free `ℤ`-module on the nonplanar binary trees with unlabelled leaves, graded by the
number of leaves. It generates these trees by recursively solving `X = 𝔐(X, X)` over formal sums
`X = ∑ Xₗ`, with the initial condition `X₁ = x`, and reads the integer coefficients of the solution
as numbers of planar embeddings. Here `V(𝔗)` sits in the Connes–Kreimer algebra of unlabelled
trees, Merge is the grafting operator after the disjoint union (Lemma 1.3.3), and a formal sum is a
power series whose degree counts leaves. The sum of the planar binary trees, their planar
structure forgotten, solves the equation (`isMergeSolution_mergeSolution`) and is its only solution
(`IsMergeSolution.eq`). The coefficient of each tree is its number of planar embeddings
(`coeff_planarSum_succ`), and the coefficients of `Xₙ₊₁` sum to the Catalan number `Cₙ`
(`aeval_planarSum_succ`). On syntactic objects, Lemma 1.3.3 is `toCK_merge`.

The book's worked examples of externalization are stated on the `SyntacticObject` carrier of
the Minimalist substrate: the harmonic head-initial and head-final orders of a determiner–noun
Merge, the head-side convention flipping the yield, and exocentric elimination, two saturated
nouns determining no head and hence no order. The framework itself is the `Syntax/Minimalist/`
theory layer; the examples are kernel-checked against it.

FormSet (§1.16) groups components of a workspace under a new root. Definition 1.16.1 writes it as
`⊔ ∘ (B ⊗ id) ∘ Π_(k) ∘ Δ_P`, where the primitive coproduct `Δ_P` splits a workspace in every way,
so `FS^(k)(F)` sums `B(S) ⊔ (F - S)` over the `k`-component subworkspaces `S` (`formSet_of'`). On
workspaces of syntactic objects it lands in the extended workspaces of (1.16.3) (`map_formSet_le`).

The book's syntax–semantics interface (Chapter 3) replaces per-feature checking by a single
recursive map, the Birkhoff renormalization of a character of the Connes–Kreimer Hopf algebra
of the syntactic object. The Boolean parsing semiring `Consistency` of §3.5 is the target,
`toCK` embeds a syntactic object into the Hopf algebra, `featureConsistency` is the renormalized
character, and `headConsistency` instantiates it for the head-following character of Lemma 3.2.5,
whose probe reads the §1.13 selection head. The machinery is noncomputable, so these are
specifications of consistency rather than checkers.

Obligatory control (§3.8.2) is derived by External Merge alone. In *the man tried to read a
book* both inscriptions of *the man* merge into theta positions, as repetitions of one another,
and Form Copy restricts the object to the diagonal on which they are one
(`theMan_mem_copyRel`), while *a book*, not structurally identical to *the man*, is no copy of it
(`not_mem_copyRel_aBook`).

## Correspondence with the book

The book's algebra lives in `Core/` and in `Syntax/Minimalist/{Workspace,Merge,Economy}/`:

* Definitions 1.2.6 and 1.2.8 (admissible cuts, the coproducts `Δ^ω`): `ConnesKreimer.cutSummandsN`
  and `comulAlgHomN` for `Δ^ρ`, which Remark 1.2.9 identifies with the Connes–Kreimer coproduct;
  `cutSummandsCN` and `comulCAlgHomN` for `Δ^c`.
* Lemma 1.2.10: `ConnesKreimer.comulCN_coassoc` and the edge grading of `Workspace/TraceGrading`.
* Lemma 1.2.11 and (1.2.12): `ConnesKreimer.instBialgebraRho`, the `HopfAlgebra` instance, and
  `antipodeTreeN`.
* The comparison of `Δ^d` with `Δ^ρ` displayed before (1.3.10):
  `ConnesKreimer.comulDN_embedInl_eq_comulAlgHomN`.
* Definition 1.3.4: `Minimalist.Merge.mergeOpG` over a cut enumeration, with `mergeOp` at `Δ^ρ`
  and `mergeOpC` at `Δ^c`.
* Lemma 1.4.1: `Minimalist.Merge.mergeOpG_pair`, `mergeOpG_pair_residual`.
* Proposition 1.4.2: `Minimalist.Merge.mergeOpG_im_composition`; on syntactic objects
  `Minimalist.SyntacticObject.mergeOpC_im`, and for a derivation
  `Minimalist.SyntacticObject.Derivation.mergeOpList_initial`.
* Definition 1.6.1 and Proposition 1.6.4: `Minimalist.MinimalYield` over a counting,
  `MinimalYield.em_pair`, `em_pair_accessibleCount`, `im_accessibleCount_of_cut`.
* Definition 1.6.2 and Proposition 1.6.10: `Minimalist.NoComplexityLoss`,
  `NoComplexityLoss.em_case1`, `im_residual`, `not_map_sideward_2b`.
* Definition 1.6.2's degree `#L`: `UnorderedTree.numLeaves`; Lemma 1.6.3:
  `ConnesKreimer.cutSummandsCN_numNodes`.
* Lemma 1.7.3, for `Δ^ρ`: `ConnesKreimer.lcoeff_singleton_isDualPrimitive` and
  `lie_lcoeff_singleton_apply_ofTree`.
* Definitions 3.1.1 and 3.1.2: `RotaBaxter`, `RotaBaxterSemiring`; Remark 3.2.2: `RotaBaxter.id`.
* Definitions 3.1.3, 3.1.5 and 3.1.6, Proposition 3.1.7, Remark 3.1.8:
  `ConnesKreimer.birkhoffMinus`, `birkhoffPrepTree`, `birkhoffPlus`, `birkhoffPlus_eq_convMul`,
  `birkhoffFactorization`; Proposition 3.1.9:
  `ConnesKreimer.SemiringRenorm.birkhoffFactorization_ofTree`.
* Proposition 3.5.2 and (3.5.4): `LaurentSeries.rotaBaxterPolar`; Proposition 3.5.6:
  `ConnesKreimer.polarHahn_birkhoffPlus_of'`.

## Implementation notes

In §1.4.4 the book displays the result with the deletion quotient `T/d T₂ = {was, eaten}`, and
alternatively with the contraction quotient `T/c T₂`, whose contracted leaf it labels by the
extracted term `{the, apple}`. The trace cuts of the carrier label that leaf by the head of the
extracted term (`traceEncoder`), so the example's quotient is `{was, {eaten, t}}` with `t` the
trace of *the*.

The equation carries its initial term, `X = x t + 𝔐(X, X)`. The book writes `X = 𝔐(X, X)` and
supplies `X₁ = x` as an initial condition, but `𝔐(X, X)` has no degree-one term
(`coeff_one_mergeSeries`), so the leaf enters as an inhomogeneous term.

`TreeAlgebra` is spanned by the forests of unlabelled trees, not only by the binary trees of `𝔗`.
`V(𝔗)` is the span of the single binary trees in it, and every term of the solution lies there.

`formSet` is defined for every `k` on all forests, with the root label of `B` a parameter.
Definition 1.16.1 takes `k ≥ 3` and the domain `V(𝔉_{SO₀})` of workspaces of syntactic objects;
`map_formSet_le` is stated on that domain, with the bare root label of the syntactic objects.

The proof of Proposition 1.10.2 prints `X₄ = 2{x{x{xx}}} + {{xx}{xx}}`. Its recursion gives
`𝔐(X₁, X₃) + 𝔐(X₂, X₂) + 𝔐(X₃, X₁) = 4{x{x{xx}}} + {{xx}{xx}}` (`planarSum_four`), and four is
the number of planar embeddings that the proof says the coefficient counts: the five planar binary
trees with four leaves split as four and one.

## TODO

§1.17 reads (1.10.1) as the quadratic case of the combinatorial Dyson–Schwinger equation
`X = B(P(X))` of (1.17.2), with the grafting operator `B` of Definition 1.3.2 and the recursive
solution (1.17.3), which the book cites rather than proves. Stating it needs `B` on formal series
in the grading by vertices, in which `B` raises the degree by one. With `x = B(1)` the Merge case
is `P(t) = 1 + t²`, while the book writes `P(X) = X²` next to its requirement `a₀ = 1`.

Lemma 1.10.1 identifies `𝔗` with the free nonassociative commutative magma on one generator; the
link to the syntactic-object carrier, the free commutative magma on the lexical items, is not
stated.

Lemma 1.16.5 extends the coproducts `Δ^ω` to extended workspaces by excluding the cuts of edges at
a root of valence at least three, so that Merge does not undo the grouping FormSet builds
(§1.16.2). It is not formalized.

The book's section locators (§1.12.1, §1.13, §1.13.2) are transcribed from an earlier
version of this file and are UNVERIFIED against the published text.

## References

* [marcolli-chomsky-berwick-2025]
* [chomsky-etal-2023]
-/

@[expose] public section

namespace MarcolliChomskyBerwick2025

open RoseTree UnorderedTree Minimalist SyntacticObject ConnesKreimer

/-! ### Internal Merge: an example (§1.4.4) -/

/-- A token of the simple lexical item of category `c` selecting `sel`, pronounced `pf`. -/
def tok (c : Cat) (sel : SelStack) (pf : String) (i : ℕ) : LIToken :=
  ⟨.simple c sel (phonForm := pf), i⟩

/-- *the apple*, the term `T₂` that Internal Merge raises in §1.4.4. -/
private def theApple : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf (tok .D [.N] "the" 0))
    (.leaf (tok .N [] "apple" 1))).toSyntacticObject

/-- The workspace `T = {was, {eaten, {the, apple}}}` of §1.4.4. -/
private def wasEatenTheApple : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf (tok .T [.V] "was" 2))
    (.merge (.leaf (tok .V [.D] "eaten" 3))
      (.merge (.leaf (tok .D [.N] "the" 0)) (.leaf (tok .N [] "apple" 1))))).toSyntacticObject

/-- The quotient `T/T₂`, with the trace of the head *the* in place of *the apple*. -/
private def wasEatenTrace : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf (tok .T [.V] "was" 2))
    (.merge (.leaf (tok .V [.D] "eaten" 3)) (.traceOf (tok .D [.N] "the" 0)))).toSyntacticObject

/-- The remainder of raising *the apple* out of `T` is the quotient `T/T₂`. -/
example : deleteAccessible theApple wasEatenTheApple = wasEatenTrace := by decide

/-- The first stage `M_{T₂,1}` splits `T` into `T₂` beside the quotient `T/T₂`. -/
example :
    Merge.mergeOpUnitC (R := ℤ) traceEncoder theApple.val
        (of' ({wasEatenTheApple.val} : Forest (UnorderedTree Vertex)))
      = of' ({theApple.val, wasEatenTrace.val} : Forest (UnorderedTree Vertex)) := by
  rw [mergeOpUnitC_current (by decide) (by decide) (by decide),
    show deleteAccessible theApple wasEatenTheApple = wasEatenTrace by decide]

/-- The composite `M_{T/T₂,T₂} ∘ M_{T₂,1}` is Internal Merge of *the apple*: it merges `T₂` with the
    quotient `T/T₂` (Proposition 1.4.2). -/
example :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare wasEatenTrace.val theApple.val
        (Merge.mergeOpUnitC traceEncoder theApple.val
          (of' ({wasEatenTheApple.val} : Forest (UnorderedTree Vertex))))
      = of' ({(merge wasEatenTrace theApple).val} : Forest (UnorderedTree Vertex)) := by
  rw [show wasEatenTrace = deleteAccessible theApple wasEatenTheApple by decide]
  exact mergeOpC_im (by decide) (by decide) (by decide)

/-- This Internal Merge satisfies Minimal Yield under trace counting, the Δᶜ row of the table of
    Proposition 1.6.4. -/
example :
    MinimalYield UnorderedTree.accessibleCount
      (({wasEatenTheApple} : Workspace).map Subtype.val)
      (({merge wasEatenTrace theApple} : Workspace).map Subtype.val) := by
  rw [show wasEatenTrace = deleteAccessible theApple wasEatenTheApple by decide]
  exact Step.minimalYield (step := .im theApple) (W := 0)
    ⟨by decide, by decide, by decide, by simp⟩ (by decide) (by simp [Step.items])

/-! ### The core computational structure of Merge (§1.10) -/

section CoreMerge

open PowerSeries Finset
open Finset.HasAntidiagonal.antidiagonal (fst_le snd_le)

/-- The Connes–Kreimer algebra of unlabelled trees over `ℤ`, in which the free `ℤ`-module `V(𝔗)`
on the nonplanar binary trees sits as the span of single trees. -/
abbrev TreeAlgebra := ConnesKreimer ℤ (UnorderedTree Unit)

/-- Forgetting the planar structure of a planar binary tree, whose leaves are its `nil`s. -/
def forgetPlanar : BinaryTree Unit → UnorderedTree Unit
  | .nil => UnorderedTree.leaf ()
  | .node _ l r => UnorderedTree.node () {forgetPlanar l, forgetPlanar r}

/-- The single variable `x`, the one-leaf tree. -/
noncomputable def generator : TreeAlgebra := ofTree (UnorderedTree.leaf ())

/-- Merge on `V(𝔗)` is the grafting operator after the disjoint union (Lemma 1.3.3), a bilinear
map. -/
noncomputable def mergeLin : TreeAlgebra →ₗ[ℤ] TreeAlgebra →ₗ[ℤ] TreeAlgebra :=
  (LinearMap.mul ℤ TreeAlgebra).compr₂ (bPlusLin ())

@[simp] theorem mergeLin_apply (a b : TreeAlgebra) : mergeLin a b = bPlusLin () (a * b) := rfl

theorem mergeLin_comm (a b : TreeAlgebra) : mergeLin a b = mergeLin b a := by
  rw [mergeLin_apply, mergeLin_apply, _root_.mul_comm]

theorem mergeLin_ofTree (s t : UnorderedTree Unit) :
    mergeLin (ofTree s) (ofTree t) = ofTree (UnorderedTree.node () {s, t}) := by
  rw [mergeLin_apply, ← of'_singleton, ← of'_singleton, ← of'_add, bPlusLin_of']
  rfl

/-- Merge extends to formal series `X = ∑ Xₗ` degree by degree, the degree-`n` term of `𝔐(X, Y)`
being `∑_{i+j=n} 𝔐(Xᵢ, Yⱼ)`. -/
noncomputable def mergeSeries (X Y : TreeAlgebra⟦X⟧) : TreeAlgebra⟦X⟧ :=
  PowerSeries.mk fun n ↦ bPlusLin () (coeff n (X * Y))

@[simp] theorem coeff_mergeSeries (X Y : TreeAlgebra⟦X⟧) (n : ℕ) :
    coeff n (mergeSeries X Y) = ∑ p ∈ antidiagonal n, mergeLin (coeff p.1 X) (coeff p.2 Y) := by
  rw [mergeSeries, coeff_mk, coeff_mul, map_sum]; rfl

/-- `𝔐(X, X)` has no degree-one term, so the printed `X = 𝔐(X, X)` cannot meet `X₁ = x`. -/
theorem coeff_one_mergeSeries {X : TreeAlgebra⟦X⟧} (h0 : coeff 0 X = 0) :
    coeff 1 (mergeSeries X X) = 0 := by
  simp [Finset.Nat.sum_antidiagonal_succ, h0]

/-- A series solves (1.10.1) with its initial condition `X₁ = x` when it has no constant term and
`X = x t + 𝔐(X, X)`. -/
def IsMergeSolution (X : TreeAlgebra⟦X⟧) : Prop :=
  coeff 0 X = 0 ∧ X = monomial 1 generator + mergeSeries X X

/-- The formal sum of the planar binary trees with `n` leaves, planarity forgotten. -/
noncomputable def planarSum : ℕ → TreeAlgebra
  | 0 => 0
  | n + 1 => ∑ P ∈ BinaryTree.treesOfNumNodesEq n, ofTree (forgetPlanar P)

/-- The series `X = ∑ₗ Xₗ` of Proposition 1.10.2. -/
noncomputable def mergeSolution : TreeAlgebra⟦X⟧ := PowerSeries.mk planarSum

/-- The recursion of the proof of Proposition 1.10.2, `Xₙ = ∑_{j=1}^{n-1} 𝔐(Xⱼ, X_{n-j})`. -/
theorem planarSum_add_two (n : ℕ) :
    planarSum (n + 2) =
      ∑ p ∈ antidiagonal n, mergeLin (planarSum (p.1 + 1)) (planarSum (p.2 + 1)) := by
  rw [planarSum, BinaryTree.treesOfNumNodesEq_succ, sum_biUnion]
  · refine sum_congr rfl fun p _ ↦ ?_
    simp only [BinaryTree.pairwiseNode, sum_map, sum_product, planarSum, map_sum,
      LinearMap.sum_apply, mergeLin_ofTree]
    rw [sum_comm]
    rfl
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
    aesop

private theorem sum_antidiagonal_add_two {f : ℕ → TreeAlgebra} (h0 : f 0 = 0) (n : ℕ) :
    ∑ p ∈ antidiagonal (n + 2), mergeLin (f p.1) (f p.2) =
      ∑ p ∈ antidiagonal n, mergeLin (f (p.1 + 1)) (f (p.2 + 1)) := by
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ', h0]
  simp

/-- The sum of the planar binary trees solves (1.10.1) with `X₁ = x` (Proposition 1.10.2). -/
theorem isMergeSolution_mergeSolution : IsMergeSolution mergeSolution := by
  refine ⟨by simp [mergeSolution, planarSum], PowerSeries.ext fun n ↦ ?_⟩
  rw [map_add, coeff_mergeSeries, coeff_monomial]
  rcases n with _ | _ | n
  · simp [mergeSolution, planarSum]
  · simp [mergeSolution, planarSum, generator, Finset.Nat.sum_antidiagonal_succ, forgetPlanar]
  · rw [ite_eq_right (by omega), zero_add, mergeSolution]
    simp only [coeff_mk]
    show planarSum (n + 2) = ∑ p ∈ antidiagonal (n + 2), mergeLin (planarSum p.1) (planarSum p.2)
    rw [sum_antidiagonal_add_two (f := planarSum) rfl n]
    exact planarSum_add_two n

/-- The solution of Proposition 1.10.2 is unique, since the recursion determines each term from
the lower ones. -/
theorem IsMergeSolution.eq {X : TreeAlgebra⟦X⟧} (h : IsMergeSolution X) : X = mergeSolution := by
  obtain ⟨h0, hX⟩ := h
  refine PowerSeries.ext fun n ↦ ?_
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [h0, mergeSolution, planarSum]
    · have := congrArg (PowerSeries.coeff 1) hX
      rw [this, map_add, coeff_mergeSeries, coeff_monomial_same, Finset.Nat.sum_antidiagonal_succ,
        h0]
      simp [mergeSolution, planarSum, generator, forgetPlanar, h0]
    · have := congrArg (PowerSeries.coeff (n + 2)) hX
      rw [this, map_add, coeff_mergeSeries, coeff_monomial, ite_eq_right (by omega), zero_add]
      show ∑ p ∈ antidiagonal (n + 2), mergeLin (PowerSeries.coeff p.1 X) (PowerSeries.coeff p.2 X)
        = PowerSeries.coeff (n + 2) mergeSolution
      rw [sum_antidiagonal_add_two (f := fun i ↦ PowerSeries.coeff i X) h0, mergeSolution,
        coeff_mk, planarSum_add_two]
      refine sum_congr rfl fun p hp ↦ ?_
      rw [ih (p.1 + 1) (by have := fst_le hp; omega), ih (p.2 + 1) (by have := snd_le hp; omega),
        mergeSolution, coeff_mk, coeff_mk]

/-- The coefficient of a nonplanar tree in `Xₙ₊₁` is its number of planar embeddings. -/
theorem coeff_planarSum_succ (n : ℕ) (T : UnorderedTree Unit) :
    (planarSum (n + 1)).coeff {T} =
      #{P ∈ BinaryTree.treesOfNumNodesEq n | forgetPlanar P = T} := by
  rw [planarSum, ← lcoeff_apply (R := ℤ), map_sum, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun P _ ↦ ?_
  rw [lcoeff_apply, ← of'_singleton, coeff_of']
  simp [Multiset.singleton_inj]

/-- The coefficients of `Xₙ₊₁` sum to the Catalan number `Cₙ`, the number of planar binary trees
with `n + 1` leaves. -/
theorem aeval_planarSum_succ (n : ℕ) :
    aeval (R := ℤ) (fun _ ↦ (1 : ℤ)) (planarSum (n + 1)) = catalan n := by
  simp [planarSum, BinaryTree.treesOfNumNodesEq_card_eq_catalan]

/-- `X₁ = x`. -/
theorem planarSum_one : planarSum 1 = generator := by
  simp [planarSum, generator, forgetPlanar]

/-- `X₂ = {xx}`. -/
theorem planarSum_two : planarSum 2 = mergeLin generator generator := by
  rw [planarSum_add_two]
  simp [planarSum_one]

/-- `X₃ = {x{xx}} + {{xx}x} = 2{x{xx}}`. -/
theorem planarSum_three :
    planarSum 3 = 2 • mergeLin generator (mergeLin generator generator) := by
  rw [planarSum_add_two]
  simp [Finset.Nat.sum_antidiagonal_succ, planarSum_one, planarSum_two, two_smul, _root_.mul_comm]

/-- `X₄ = 4{x{x{xx}}} + {{xx}{xx}}`; the proof of Proposition 1.10.2 prints the coefficient
`2`. -/
theorem planarSum_four :
    planarSum 4 = 4 • mergeLin generator (mergeLin generator (mergeLin generator generator)) +
      mergeLin (mergeLin generator generator) (mergeLin generator generator) := by
  rw [planarSum_add_two]
  simp only [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, sum_singleton,
    zero_add, Nat.reduceAdd, planarSum_one, planarSum_two, planarSum_three, map_nsmul,
    LinearMap.smul_apply]
  rw [mergeLin_comm (mergeLin generator (mergeLin generator generator)) generator]
  abel

/-- The printed `X₄ = 2{x{x{xx}}} + {{xx}{xx}}` is not the degree-four term of the solution. -/
example : planarSum 4 ≠
    2 • mergeLin generator (mergeLin generator (mergeLin generator generator)) +
      mergeLin (mergeLin generator generator) (mergeLin generator generator) := by
  rw [planarSum_four]
  intro h
  have h' := congrArg (lcoeff ℤ {UnorderedTree.node () {UnorderedTree.leaf (),
    UnorderedTree.node () {UnorderedTree.leaf (), UnorderedTree.node () {UnorderedTree.leaf (),
      UnorderedTree.leaf ()}}}}) (add_right_cancel h)
  simp only [generator, mergeLin_ofTree] at h'
  simp only [map_nsmul, lcoeff_apply, ← of'_singleton, coeff_of'] at h'
  norm_num at h'

end CoreMerge

/-! ### Externalization (§1.12–1.13) -/

/-- A determiner over a noun, in which `D` selects `N` and so projects. -/
private def theDog : SyntacticObject :=
  ⟨UnorderedTree.mk (.node Vertex.bare
    [.node (Vertex.lex ⟨.simple .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Vertex.lex ⟨.simple .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

/-- In the harmonic head-initial order the projecting `D`'s yield comes first. -/
example : (theDog.linearize .initial).map (·.map (·.id)) = some [0, 1] := by decide

/-- In the harmonic head-final order the same head function is mirrored. -/
example : (theDog.linearize .final).map (·.map (·.id)) = some [1, 0] := by decide

example : theDog.phonYield .initial = some ["the", "dog"] := by decide
example : theDog.phonYield .final = some ["dog", "the"] := by decide

/-- Exocentric Merge of two saturated `N`s, neither selecting the other, determines no head and
no order. -/
private def exoNN : SyntacticObject :=
  ⟨UnorderedTree.mk (.node Vertex.bare
    [.node (Vertex.lex ⟨.simple .N [] (phonForm := "cats"), 0⟩) [],
     .node (Vertex.lex ⟨.simple .N [] (phonForm := "dogs"), 1⟩) []]), by decide⟩

example : exoNN.linearize .initial = none := by decide
example : exoNN.linearize .final = none := by decide

/-! ### FormSet (§1.16) -/

section FormSet

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- FormSet `FS^(k) = ⊔ ∘ (B ⊗ id) ∘ Π_(k) ∘ Δ_P` (Definition 1.16.1, (1.16.2)) splits the
workspace by the primitive coproduct, keeps the terms whose left factor has `k` components,
grafts those under a new root labelled `a`, and multiplies back. -/
noncomputable def formSet (a : α) (k : ℕ) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mul' R _ ∘ₗ (bPlusLin a).rTensor _ ∘ₗ (homogeneousComponent k).rTensor _ ∘ₗ
    comulPrim.toLinearMap

variable [DecidableEq α]

/-- FormSet groups `k` components of a workspace in every way, summing `B(S) ⊔ (F - S)` over
the `k`-component subworkspaces `S` of `F`, counted with multiplicity (Remark 1.16.4). -/
theorem formSet_of' (a : α) (k : ℕ) (F : Forest (UnorderedTree α)) :
    formSet (R := R) a k (of' F) =
      ((F.powersetCard k).map fun S ↦ of' (.node a S ::ₘ (F - S))).sum := by
  rw [formSet, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, rTensor_homogeneousComponent_comulPrim_of', map_multiset_sum,
    map_multiset_sum, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun S _ ↦ ?_)
  simp [bPlusLin_of', ← of'_singleton, ← of'_add, Multiset.singleton_add]

/-- With fewer than `k` components there is nothing to group. -/
theorem formSet_of'_of_card_lt (a : α) {k : ℕ} {F : Forest (UnorderedTree α)}
    (h : F.card < k) : formSet (R := R) a k (of' F) = 0 := by
  rw [formSet_of', Multiset.powersetCard_eq_empty _ h, Multiset.map_zero, Multiset.sum_zero]

/-- With exactly `k` components FormSet groups the whole workspace, as in the unbounded
unstructured sequences of p. 144. -/
theorem formSet_of'_card (a : α) (F : Forest (UnorderedTree α)) :
    formSet (R := R) a F.card (of' F) = ofTree (.node a F) := by
  simp [formSet_of']

/-- A forest is an extended workspace, in `𝔉̃ᴿ` of (1.16.3), when each component is a syntactic
object or a bare root of any valence over syntactic objects, binary below that root. -/
def IsExtendedWorkspace (G : Forest (UnorderedTree Vertex)) : Prop :=
  ∀ T ∈ G, IsSyntacticObject T ∨
    ∃ S : Forest (UnorderedTree Vertex), T = .node Vertex.bare S ∧ ∀ T' ∈ S, IsSyntacticObject T'

/-- On workspaces of syntactic objects, the range of FormSet lies in the span of the extended
workspaces (Definition 1.16.1). -/
theorem map_formSet_le (k : ℕ) :
    (Submodule.span R (of' '' {F | ∀ T ∈ F, IsSyntacticObject T})).map
        (formSet Vertex.bare k) ≤
      Submodule.span R (of' '' {G | IsExtendedWorkspace G}) := by
  rw [Submodule.map_span_le]
  rintro _ ⟨F, hF, rfl⟩
  rw [formSet_of']
  refine multiset_sum_mem _ fun x hx ↦ ?_
  obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.mp hx
  refine Submodule.subset_span ⟨_, fun T hT ↦ ?_, rfl⟩
  rw [Multiset.mem_powersetCard] at hS
  rcases Multiset.mem_cons.mp hT with rfl | hT
  · exact .inr ⟨S, rfl, fun T' hT' ↦ hF T' (Multiset.mem_of_le hS.1 hT')⟩
  · exact .inl (hF T (Multiset.mem_of_le (Multiset.sub_le_self F S) hT))

end FormSet

/-! ### Feature consistency as Birkhoff renormalization (Chapter 3) -/

/-- The Boolean consistency semiring of §3.5, the two-element idempotent commutative semiring
with disjunction as addition, some decomposition being consistent, and conjunction as
multiplication, all parts agreeing. -/
inductive Consistency where
  | inconsistent
  | consistent
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Consistency

/-- Disjunction, consistent iff at least one argument is. -/
def or : Consistency → Consistency → Consistency
  | consistent, _ => consistent
  | _, consistent => consistent
  | _, _ => inconsistent

/-- Conjunction, consistent iff both arguments are. -/
def and : Consistency → Consistency → Consistency
  | consistent, consistent => consistent
  | _, _ => inconsistent

instance : CommSemiring Consistency where
  add := or
  mul := and
  zero := inconsistent
  one := consistent
  nsmul n a := n.rec inconsistent fun _ acc => or acc a
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  add_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  zero_add := by rintro ⟨⟩ <;> rfl
  add_zero := by rintro ⟨⟩ <;> rfl
  add_comm := by rintro ⟨⟩ ⟨⟩ <;> rfl
  mul_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  one_mul := by rintro ⟨⟩ <;> rfl
  mul_one := by rintro ⟨⟩ <;> rfl
  mul_comm := by rintro ⟨⟩ ⟨⟩ <;> rfl
  left_distrib := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  right_distrib := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  zero_mul := by rintro ⟨⟩ <;> rfl
  mul_zero := by rintro ⟨⟩ <;> rfl

/-- The identity Rota–Baxter operator of weight `+1` on `Consistency` (Lemma 3.2.7), valid
because disjunction is idempotent, so the weight-`+1` term is absorbed. On a Boolean target the
threshold operator collapses to the identity, since disagreement already is the additive zero. -/
def rbId : RotaBaxterSemiring Consistency where
  op := AddMonoidHom.id Consistency
  rotaBaxter := by rintro ⟨⟩ ⟨⟩ <;> rfl

end Consistency

/-- A syntactic object as an element of the Connes–Kreimer Hopf algebra over `ℕ`, the singleton
forest of its underlying nonplanar tree. The base ring is `ℕ` because every commutative
semiring, `Consistency` included, is an `ℕ`-algebra, while a Boolean target is no `ℤ`-algebra. -/
noncomputable def toCK (S : SyntacticObject) : ConnesKreimer ℕ (UnorderedTree Vertex) :=
  ofTree S.val

/-- Merge factors through the grafting operator on the disjoint union of its arguments, with the
bare root label (Lemma 1.3.3). -/
theorem toCK_merge (l r : SyntacticObject) :
    toCK (merge l r) = bPlusLin Vertex.bare (toCK l * toCK r) := by
  rw [toCK, toCK, toCK, ← of'_singleton (R := ℕ) l.val, ← of'_singleton (R := ℕ) r.val, ← of'_add,
    bPlusLin_of', merge_val]
  rfl

open scoped TensorProduct

/-- The feature-consistency map `φ₊` on a syntactic object, the renormalized value of a feature
character `φ` with weight-`+1` Rota–Baxter operator `RB` at the object, the single recursive map
of §3.1.5 that incorporates consistency checking over all substructures. -/
noncomputable def featureConsistency
    (φ : ConnesKreimer ℕ (UnorderedTree Vertex) →ₗ[ℕ] Consistency)
    (RB : RotaBaxterSemiring Consistency) (S : SyntacticObject) : Consistency :=
  SemiringRenorm.birkhoffPlusTree φ RB S.val

/-- The feature-consistency map factors as the semiring Birkhoff convolution `φ₊ = φ₋ ⋆ φ` on
the object's Hopf-algebra image (Definition 3.1.6, Proposition 3.1.9), for a unital `φ`. -/
theorem featureConsistency_eq_convMul
    (φ : ConnesKreimer ℕ (UnorderedTree Vertex) →ₗ[ℕ] Consistency)
    (RB : RotaBaxterSemiring Consistency) (hφ : φ 1 = 1) (S : SyntacticObject) :
    LinearMap.mul' ℕ Consistency
        ((TensorProduct.map (SemiringRenorm.birkhoffMinus φ RB).toLinearMap φ)
          (comulAlgHomN (toCK S)))
      = featureConsistency φ RB S :=
  SemiringRenorm.birkhoffFactorization_ofTree φ RB hφ S.val

/-- The head-probe value `Υ_{s,h}` on a tree (equation (3.2.1)), the probe `Υ` applied to the
tree's selection head, and `inconsistent` when the tree has no well-defined head. -/
def headProbeTree (Υ : LIToken → Consistency) (T : UnorderedTree Vertex) : Consistency :=
  (selCheckN T).head.elim Consistency.inconsistent Υ

/-- The head-following feature character `ϕ_{Υ,s,h}` of Lemma 3.2.5 as an algebra homomorphism:
`Υ_{s,h}` extended multiplicatively to forests, so that a workspace is consistent iff each of its
trees is. The unrenormalized feature assignment whose Birkhoff renormalization is the consistency
map. -/
noncomputable def headProbeChar (Υ : LIToken → Consistency) :
    ConnesKreimer ℕ (UnorderedTree Vertex) →ₐ[ℕ] Consistency :=
  aeval (headProbeTree Υ)

@[simp] theorem headProbeChar_apply_of' (Υ : LIToken → Consistency)
    (F : Forest (UnorderedTree Vertex)) :
    headProbeChar Υ (of' F) = (F.map (headProbeTree Υ)).prod :=
  aeval_of' _ F

@[simp] theorem headProbeChar_apply_ofTree (Υ : LIToken → Consistency) (T : UnorderedTree Vertex) :
    headProbeChar Υ (ofTree T) = headProbeTree Υ T :=
  aeval_ofTree _ T

theorem headProbeChar_one (Υ : LIToken → Consistency) : headProbeChar Υ 1 = 1 := map_one _

/-- The feature-consistency verdict on a syntactic object (§3.1.5, Lemmas 3.2.5 and 3.2.7), the
Birkhoff renormalization with the identity operator of the head-following character, consistent
iff the head-probe agreements cohere across all substructures. -/
noncomputable def headConsistency (Υ : LIToken → Consistency) (S : SyntacticObject) :
    Consistency :=
  featureConsistency (headProbeChar Υ).toLinearMap Consistency.rbId S

/-- The head-driven verdict factors as the semiring Birkhoff convolution `φ₊ = φ₋ ⋆ φ` of the
head-following character (Definition 3.1.6, Lemma 3.2.7). -/
theorem headConsistency_eq_convMul (Υ : LIToken → Consistency) (S : SyntacticObject) :
    LinearMap.mul' ℕ Consistency
        ((TensorProduct.map
            (SemiringRenorm.birkhoffMinus (headProbeChar Υ).toLinearMap
              Consistency.rbId).toLinearMap
            (headProbeChar Υ).toLinearMap)
          (comulAlgHomN (toCK S)))
      = headConsistency Υ S :=
  featureConsistency_eq_convMul _ _ (headProbeChar_one Υ) S

/-! ### Obligatory control by Form Copy (§3.8.2) -/

/-- The controller *the man*, from tokens 0 and 1. -/
noncomputable def theMan : SyntacticObject :=
  merge (leaf (tok .D [.N] "the" 0)) (leaf (tok .N [] "man" 1))

/-- The controlled subject *the man*, from fresh tokens 4 and 5. -/
noncomputable def theMan' : SyntacticObject :=
  merge (leaf (tok .D [.N] "the" 4)) (leaf (tok .N [] "man" 5))

/-- *a book*, the object of *read*. -/
noncomputable def aBook : SyntacticObject :=
  merge (leaf (tok .D [.N] "a" 7)) (leaf (tok .N [] "book" 8))

/-- The syntactic object (3.8.4) of *the man tried to read a book*, built by External Merge
alone: the controller merges into the theta position of *tried* and the controlled subject into
that of *read*, since Internal Merge into a theta position would break the dichotomy of §3.8.1. -/
noncomputable def triedToRead : SyntacticObject :=
  merge theMan (merge (leaf (tok .V [.T] "tried" 2)) (merge (leaf (tok .T [.V] "to" 3))
    (merge theMan' (merge (leaf (tok .V [.D] "read" 6)) aBook))))

/-- The two inscriptions of *the man* are repetitions, structurally identical distinct tokens. -/
theorem theMan_isRepetition : IsRepetition theMan theMan' := by
  refine ⟨by simp [StructurallyIdentical, theMan, theMan', tok], fun h ↦ ?_⟩
  have : immediatelyContains theMan' (leaf (tok .D [.N] "the" 0)) := h ▸ by simp [theMan]
  simp [theMan', tok] at this

/-- Form Copy relates the controller to the controlled subject, the restriction of (3.8.4) to
the diagonal `Diag₁,₄` of (3.8.5). -/
theorem theMan_mem_copyRel : (theMan, theMan') ∈ triedToRead.copyRel :=
  mk_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains]) theMan_isRepetition.1

/-- *a book* is no copy of *the man*, since Form Copy relates only structurally identical
inscriptions. -/
theorem not_mem_copyRel_aBook : (theMan, aBook) ∉ triedToRead.copyRel := fun h ↦ by
  have := h.2
  simp only [StructurallyIdentical, theMan, aBook, erase_merge, erase_leaf, tok] at this
  exact absurd this (by decide)

end MarcolliChomskyBerwick2025
