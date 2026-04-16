/-
@cite{kratzer-1981} World Ordering

Worlds are ordered by set-inclusion of satisfied propositions:
w ≤_A z iff {p ∈ A : z ∈ p} ⊆ {p ∈ A : w ∈ p}.

Best worlds are those maximal under this ordering among accessible worlds.

All types are polymorphic over the world type `W`.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Background
import Linglib.Core.Logic.SatisfactionOrdering
import Mathlib.Order.Basic

namespace Semantics.Modality.Kratzer

variable {W : Type*} [DecidableEq W] [Fintype W]

/--
The set of propositions from A that world w satisfies.

This is {p ∈ A : w ∈ p} in Kratzer's notation.
-/
def satisfiedPropositions (A : List (W → Bool)) (w : W) : List (W → Bool) :=
  A.filter (λ p => p w)

/--
Kratzer's ordering relation: w ≤_A z

Definition (p. 39): "For all worlds w and z ∈ W:
  w ≤_A z iff {p: p ∈ A and z ∈ p} ⊆ {p: p ∈ A and w ∈ p}"

Intuitively: w is at least as good as z (w.r.t. ideal A) iff every
ideal proposition that z satisfies, w also satisfies.

Note: This is the CORRECT definition using subset inclusion,
NOT counting (which would be incorrect).
-/
def atLeastAsGoodAs (A : List (W → Bool)) (w z : W) : Bool :=
  -- Every proposition in A satisfied by z is also satisfied by w
  (satisfiedPropositions A z).all λ p => p w

notation:50 w " ≤[" A "] " z => atLeastAsGoodAs A w z

/--
Strict ordering: w <_A z iff w ≤_A z but not z ≤_A w.

This means w satisfies strictly more ideal propositions than z.
-/
def strictlyBetter (A : List (W → Bool)) (w z : W) : Bool :=
  atLeastAsGoodAs A w z && !atLeastAsGoodAs A z w

notation:50 w " <[" A "] " z => strictlyBetter A w z


open Core.SatisfactionOrdering

/--
Kratzer's world ordering as a `SatisfactionOrdering`.

A world w satisfies proposition p iff p(w) = true.
This connects Kratzer semantics to the generic ordering framework.
-/
def worldOrdering (A : List (W → Bool)) : SatisfactionOrdering W (W → Bool) where
  satisfies := λ w p => p w
  criteria := A

omit [DecidableEq W] [Fintype W] in
/--
**Kratzer's ordering matches the generic framework.**

This theorem establishes that `atLeastAsGoodAs` is exactly the
generic `SatisfactionOrdering.atLeastAsGood` for worlds.
-/
theorem atLeastAsGoodAs_eq_generic (A : List (W → Bool)) (w z : W) :
    atLeastAsGoodAs A w z = (worldOrdering A).atLeastAsGood w z := by
  unfold atLeastAsGoodAs worldOrdering SatisfactionOrdering.atLeastAsGood
         SatisfactionOrdering.satisfiedBy satisfiedPropositions
  rfl

omit [DecidableEq W] [Fintype W] in
/-- Reflexivity via generic framework. -/
theorem ordering_reflexive (A : List (W → Bool)) (w : W) :
    atLeastAsGoodAs A w w = true := by
  rw [atLeastAsGoodAs_eq_generic]
  exact SatisfactionOrdering.atLeastAsGood_refl (worldOrdering A) w

omit [DecidableEq W] [Fintype W] in
/-- Transitivity via generic framework. -/
theorem ordering_transitive (A : List (W → Bool)) (u v w : W)
    (huv : atLeastAsGoodAs A u v = true)
    (hvw : atLeastAsGoodAs A v w = true) :
    atLeastAsGoodAs A u w = true := by
  rw [atLeastAsGoodAs_eq_generic] at *
  exact SatisfactionOrdering.atLeastAsGood_trans (worldOrdering A) u v w huv hvw

-- NormalityOrder instance (via generic framework)

/--
**Kratzer's ordering as a `NormalityOrder`.**

Connects Kratzer's ordering source to the default reasoning infrastructure,
enabling `optimal`, `refine`, `respects`, and CR1–CR4 for modal semantics.
-/
def kratzerNormality (A : List (W → Bool)) : Core.Order.NormalityOrder W :=
  (worldOrdering A).toNormalityOrder

/-- Backwards-compatible alias. -/
@[reducible] def kratzerPreorder (A : List (W → Bool)) : Preorder W where
  le := (kratzerNormality A).le
  le_refl := (kratzerNormality A).le_refl
  le_trans a b c := (kratzerNormality A).le_trans a b c

/-- Equivalence under the ordering (via generic framework). -/
def orderingEquiv (A : List (W → Bool)) (w z : W) : Prop :=
  (worldOrdering A).equiv w z

omit [DecidableEq W] [Fintype W] in
theorem orderingEquiv_refl (A : List (W → Bool)) (w : W) : orderingEquiv A w w :=
  SatisfactionOrdering.equiv_refl (worldOrdering A) w

omit [DecidableEq W] [Fintype W] in
theorem orderingEquiv_symm (A : List (W → Bool)) (w z : W)
    (h : orderingEquiv A w z) : orderingEquiv A z w :=
  SatisfactionOrdering.equiv_symm (worldOrdering A) w z h

omit [DecidableEq W] [Fintype W] in
theorem orderingEquiv_trans (A : List (W → Bool)) (u v w : W)
    (huv : orderingEquiv A u v) (hvw : orderingEquiv A v w) :
    orderingEquiv A u w :=
  SatisfactionOrdering.equiv_trans (worldOrdering A) u v w huv hvw

omit [DecidableEq W] [Fintype W] in
/--
**Theorem 2: Empty ordering makes all worlds equivalent.**

If A = ∅, then for all w, z: w ≤_A z and z ≤_A w.

Proof: The set of propositions in ∅ satisfied by any world is ∅.
Vacuously, ∅ ⊆ ∅.
-/
theorem empty_ordering_all_equivalent (w z : W) :
    atLeastAsGoodAs [] w z = true ∧ atLeastAsGoodAs [] z w = true := by
  constructor <;> (unfold atLeastAsGoodAs satisfiedPropositions; simp)

omit [DecidableEq W] [Fintype W] in
theorem empty_ordering_trivial (w z : W) :
    (kratzerPreorder (W := W) []).le w z :=
  (empty_ordering_all_equivalent w z).1

omit [DecidableEq W] [Fintype W] in
theorem empty_ordering_universal_equiv (w z : W) :
    orderingEquiv (W := W) [] w z :=
  ⟨(empty_ordering_all_equivalent w z).1, (empty_ordering_all_equivalent w z).2⟩

/--
The set of worlds **accessible** from w given modal base f.

These are exactly the worlds in ∩f(w) - worlds compatible with all facts in f(w).
-/
def accessibleWorlds (f : ModalBase W) (w : W) : Finset W :=
  propIntersection (f w)

/--
**Accessibility predicate**: w' is accessible from w iff w' ∈ ∩f(w).
-/
def accessibleFrom (f : ModalBase W) (w w' : W) : Bool :=
  (f w).all (λ p => p w')

/--
The **best** worlds among accessible worlds, according to ordering source g.

These are the accessible worlds that are maximal under ≤_{g(w)}:
worlds w' such that for all accessible w'', w' ≤_{g(w)} w''.

When g(w) = ∅, all accessible worlds are best (by Theorem 2).
-/
def bestWorlds (f : ModalBase W) (g : OrderingSource W) (w : W) : Finset W :=
  let accessible := accessibleWorlds f w
  let ordering := g w
  accessible.filter λ w' =>
    decide (∀ w'' ∈ accessible, atLeastAsGoodAs ordering w' w'' = true)

/--
**Theorem 3: Empty ordering source reduces to simple accessibility.**

When g(w) = ∅, bestWorlds = accessibleWorlds.
-/
theorem empty_ordering_simple (f : ModalBase W) (w : W) :
    bestWorlds f (λ _ => []) w = accessibleWorlds f w := by
  unfold bestWorlds accessibleWorlds
  ext w'
  simp only [Finset.mem_filter, decide_eq_true_eq, and_iff_left_iff_imp]
  intro _
  exact fun w'' _ => (empty_ordering_all_equivalent w' w'').1

/-- Variant of `empty_ordering_simple` matching `emptyBackground` by name.
    Avoids the `unfold emptyBackground` workaround needed before `rw [empty_ordering_simple]`. -/
theorem empty_ordering_emptyBackground (f : ModalBase W) (w : W) :
    bestWorlds f emptyBackground w = accessibleWorlds f w := by
  unfold emptyBackground
  exact empty_ordering_simple f w

/-- The best worlds among a given set, ranked by an ordering.
    Unlike `bestWorlds` which computes accessible worlds from a modal base,
    `bestAmong` takes a precomputed world list. This is needed when the
    domain has already been restricted (e.g., by promoted priorities in
    @cite{rubinstein-2014}'s favored worlds). -/
def bestAmong (worlds : Finset W) (ordering : List (W → Bool)) : Finset W :=
  worlds.filter λ w' =>
    decide (∀ w'' ∈ worlds, atLeastAsGoodAs ordering w' w'' = true)

/-- With empty ordering, all worlds are best (Kratzer's theorem 2). -/
theorem bestAmong_empty (worlds : Finset W) :
    bestAmong worlds [] = worlds := by
  unfold bestAmong
  ext w
  simp only [Finset.mem_filter, decide_eq_true_eq, and_iff_left_iff_imp]
  intro _
  exact fun w' _ => (empty_ordering_all_equivalent w w').1

/-- bestAmong is a subset of the input worlds. -/
theorem bestAmong_sub (worlds : Finset W) (ordering : List (W → Bool)) :
    ∀ w, w ∈ bestAmong worlds ordering → w ∈ worlds :=
  λ _ hw => Finset.mem_of_mem_filter _ hw

/-- Best worlds in a superset that belong to a subset are best in the subset.

    If w' beats every world in a larger set, it certainly beats every world
    in any subset. This is the key lemma for showing that star-revision
    (domain widening) preserves strong necessity. -/
theorem bestAmong_superset {sub sup : Finset W} {ordering : List (W → Bool)} {w' : W}
    (hSub : ∀ v, v ∈ sub → v ∈ sup)
    (hBest : w' ∈ bestAmong sup ordering)
    (hMem : w' ∈ sub) :
    w' ∈ bestAmong sub ordering := by
  unfold bestAmong at hBest ⊢
  simp only [Finset.mem_filter, decide_eq_true_eq] at hBest ⊢
  exact ⟨hMem, λ v hv => hBest.2 v (hSub v hv)⟩

end Semantics.Modality.Kratzer
