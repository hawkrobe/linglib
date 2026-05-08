import Linglib.Core.Combinatorics.RootedTree.Insertion

set_option autoImplicit false

/-!
# Counterexample: pre-Lie identity is FALSE on planar `TraceTree`

@cite{marcolli-chomsky-berwick-2025} Definition 1.7.1 (book p. 77)
states the right pre-Lie identity (Lemma 1.7.2) for **nonplanar**
binary rooted trees `T₁, T₂ ∈ 𝔗_{SO₀}`. The current `TraceTree α β`
formalization is planar (`.node l r ≠ .node r l`), and on this carrier
the identity fails strictly. This file exhibits a Lean-verified
counterexample.

The discrepancy is the `newEprime` case at each MCB-edge: the new
sibling pair `{T₂, T₃}` versus `{T₃, T₂}` is identical only under
nonplanar identification, which planar `TraceTree` does not provide.

Concrete witness:
- `T₁ = .node (.leaf 0) (.leaf 1)`
- `T₂ = .leaf 2`
- `T₃ = .leaf 3`
- `e = .rootL : Edge T₁`

Both `T₂` and `T₃` have empty edge sets, so `T₁ ◇ (T₂ ◁ T₃) = T₁ ◇ (T₃ ◁ T₂) = 0`
and the pre-Lie identity reduces to `(T₁ ◁ T₂) ◇ T₃ = (T₁ ◁ T₃) ◇ T₂`
at the multiset level. `decide` confirms this fails.

## FCM-native resolution (LANDED, Phase 3.E.4 2026-05-07)

`Linglib/Core/Algebra/Free/PreLie.lean` formalizes the strict pre-Lie
identity on the natural nonplanar carrier `(FreeCommMagma α) →₀ ℤ`:

  `FreeCommMagma.insertSumLift_right_preLie : ∀ f g h, f ◇ g ◇ h - f ◇ (g ◇ h) = f ◇ h ◇ g - f ◇ (h ◇ g)`

with `RightPreLieRing` / `RightPreLieAlgebra ℤ` / `LieRing` /
`LieAlgebra ℤ` instances on `FreeCommMagma.InsertionAlgebra α`. The
counterexample below remains as motivation for choosing the nonplanar
carrier: on planar `TraceTree`, the (c) `newEprime` Case 3 sub-pair
demonstrably differs; the FCM `Quot.sound .swap` collapses it. -/

open ConnesKreimer
open ConnesKreimer.TraceTree

namespace ConnesKreimer.PreLiePlanarCheck

/-- Concrete T₁ with two edges. -/
def T1 : TraceTree Nat Nat := .node (.leaf 0) (.leaf 1)

/-- Two distinct subtrees to insert. Use leaves 2 and 3 to keep them
    distinguishable from T₁'s leaves. -/
def T2 : TraceTree Nat Nat := .leaf 2
def T3 : TraceTree Nat Nat := .leaf 3

/-- The rootL edge of T₁. -/
def eRootL : Edge T1 := .rootL (.leaf 0) (.leaf 1)

/-- Compute and reduce the LHS newEprime tree. -/
example : insertAt (Edge.newEprime eRootL T2) T3
        = .node (.node (.leaf 0) (.node (.leaf 2) (.leaf 3))) (.leaf 1) := by
  rfl

/-- Compute and reduce the RHS newEprime tree. -/
example : insertAt (Edge.newEprime eRootL T3) T2
        = .node (.node (.leaf 0) (.node (.leaf 3) (.leaf 2))) (.leaf 1) := by
  rfl

/-- These two trees are not equal — direct disequality witness. -/
example : insertAt (Edge.newEprime eRootL T2) T3
        ≠ insertAt (Edge.newEprime eRootL T3) T2 := by
  intro h
  -- Extract contradiction from the leaves being out of order: 2 = 3.
  injection h with hL hR
  injection hL with hL1 hL2
  injection hL2 with hLa hLb
  injection hLa with h2_eq_3
  exact Nat.succ_ne_self 2 (by omega)

/-- The newE1 ↔ newE2 swap DOES work, however. -/
example : insertAt (Edge.newE1 eRootL T2) T3
        = insertAt (Edge.newE2 eRootL T3) T2 := by
  rfl

example : insertAt (Edge.newE2 eRootL T2) T3
        = insertAt (Edge.newE1 eRootL T3) T2 := by
  rfl

/-! ### Pre-Lie counterexample at the multiset level

For `T₁ = .node (.leaf 0) (.leaf 1)`, `T₂ = .leaf 2`, `T₃ = .leaf 3`,
both `T₂` and `T₃` have empty edge sets so `T₂ ◁ T₃ = T₃ ◁ T₂ = 0` and
the pre-Lie identity reduces to `(T₁ ◁ T₂) ◇ T₃ = (T₁ ◁ T₃) ◇ T₂`
(at the basis level), i.e., the two iterated insertSums must match
as multisets.

We construct the 8 trees on each side and exhibit two specific trees
on the LHS that are not present on the RHS. -/

/-- The "newEprime under rootL" tree on the LHS: `T₂` and `T₃` are
    siblings under a fresh vertex, `T₂` to the left. -/
def witnessLHS : TraceTree Nat Nat :=
  .node (.node (.leaf 0) (.node (.leaf 2) (.leaf 3))) (.leaf 1)

/-- The "newEprime under rootL" tree on the RHS: same structure but
    `T₃` to the left (and `T₂` to the right). -/
def witnessRHS : TraceTree Nat Nat :=
  .node (.node (.leaf 0) (.node (.leaf 3) (.leaf 2))) (.leaf 1)

/-- The "iterated insertSum" computed by fanning out over the first
    multiset and inserting `T₃` at each tree in it. This is the
    `T₁ ◁ T₂ ◇ T₃` pattern at the multiset level (where `◇` is the
    bilinear extension to `Finsupp ℤ`). -/
def iteratedInsert (T₁ T₂ T₃ : TraceTree Nat Nat) :
    Multiset (TraceTree Nat Nat) :=
  (T₁ ◁ T₂).bind (fun T' => T' ◁ T₃)

/-- LHS contains `witnessLHS`. -/
example : witnessLHS ∈ iteratedInsert T1 T2 T3 := by
  decide

/-- RHS does NOT contain `witnessLHS` — the planar order T₂-then-T₃
    cannot be produced by the swapped (T₂↔T₃) sum. -/
example : witnessLHS ∉ iteratedInsert T1 T3 T2 := by
  decide

/-- The two iterated multisets are NOT equal. This is the pre-Lie
    identity failing in planar trees: at the multiset (uncoefficient)
    level, `(T₁ ◁ T₂) ◇ T₃ ≠ (T₁ ◁ T₃) ◇ T₂` — which transfers to
    the Finsupp lift level, falsifying `insertSumLift_right_preLie`
    on the basis triple `(T₁, T₂, T₃)` since the second-difference
    terms `T₁ ◇ (T₂ ◁ T₃)` and `T₁ ◇ (T₃ ◁ T₂)` both vanish here
    (T₂ and T₃ are leaves with no edges). -/
example : iteratedInsert T1 T2 T3 ≠ iteratedInsert T1 T3 T2 := by
  intro h
  have h1 : witnessLHS ∈ iteratedInsert T1 T2 T3 := by decide
  have h2 : witnessLHS ∉ iteratedInsert T1 T3 T2 := by decide
  exact h2 (h ▸ h1)

end ConnesKreimer.PreLiePlanarCheck
