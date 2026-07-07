/-
[kratzer-1981] World Ordering

Worlds are ordered by set-inclusion of satisfied propositions:
w ≤_A z iff {p ∈ A : z ∈ p} ⊆ {p ∈ A : w ∈ p}.

Best worlds are those maximal under this ordering among accessible worlds.

All types are polymorphic over the world type `W`. Propositions are
`W → Prop` (mathlib-native); reasoning is classical.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

import Linglib.Semantics.Modality.Kratzer.ConversationalBackground
import Linglib.Core.Order.Normality
import Linglib.Semantics.Dynamic.UpdateSemantics.Default
import Linglib.Core.Order.OfCriteria
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

namespace Semantics.Modality.Kratzer

/-! The premise primitives live in `Intensional.Premise`; re-export
them under `Semantics.Modality.Kratzer` so the historical `Kratzer.foo` call
style continues to work. The conversational-background primitives
(`ConvBackground`, `ModalBase`, …) are defined directly in this namespace by
`ConversationalBackground.lean`. -/

export Intensional.Premise
  (propExtension propIntersection followsFrom isConsistent isCompatibleWith)

variable {W : Type*}

/--
The list of propositions from A that world w satisfies.

This is `{p ∈ A : w ∈ p}` in Kratzer's notation. We use classical
decidability to filter the list, so this definition is noncomputable —
downstream uses are about lengths/membership, not evaluation.
-/
noncomputable def satisfiedPropositions (A : List (W → Prop)) (w : W) : List (W → Prop) :=
  haveI : DecidablePred (fun p : W → Prop => p w) := fun p => Classical.propDecidable (p w)
  A.filter (fun p => p w)

/--
Kratzer's world ordering as a `Preorder` on worlds — the criteria-derived
preorder (`Preorder.ofCriteria`) with the ordering source `A` as criteria
set and truth-at-a-world as satisfaction. The induced order is `≤[A]`.
Used by Phillips-Brown desire semantics and other consumers via
`letI := kratzerPreorder A`.
-/
@[reducible] def kratzerPreorder (A : List (W → Prop)) : Preorder W :=
  Preorder.ofCriteria (fun w p => p w) {p | p ∈ A}

/--
Kratzer's ordering relation: w ≤_A z — the `le` of `kratzerPreorder`.

[kratzer-1981]: `w ≤_A z` iff every ideal proposition `p ∈ A` that
holds at `z` also holds at `w`. Intuitively: `w` is at least as good as
`z` (w.r.t. ideal `A`) iff every ideal proposition that `z` satisfies,
`w` also satisfies.

UNVERIFIED page reference (p. 39 quoted in earlier version, not checked
against the original).
-/
def atLeastAsGoodAs (A : List (W → Prop)) (w z : W) : Prop :=
  (kratzerPreorder A).le w z

@[inherit_doc]
notation:50 w " ≤[" A "] " z => atLeastAsGoodAs A w z

/-- Unfolding lemma: the ordering in its pointwise form. Definitional. -/
theorem atLeastAsGoodAs_iff (A : List (W → Prop)) (w z : W) :
    (w ≤[A] z) ↔ ∀ p ∈ A, p z → p w :=
  Iff.rfl

/--
Strict ordering: w <_A z iff w ≤_A z but not z ≤_A w.

This means w satisfies strictly more ideal propositions than z.
-/
def strictlyBetter (A : List (W → Prop)) (w z : W) : Prop :=
  atLeastAsGoodAs A w z ∧ ¬ atLeastAsGoodAs A z w

@[inherit_doc]
notation:50 w " <[" A "] " z => strictlyBetter A w z

/-- Reflexivity. -/
theorem ordering_reflexive (A : List (W → Prop)) (w : W) :
    atLeastAsGoodAs A w w :=
  (kratzerPreorder A).le_refl w

/-- Transitivity. -/
theorem ordering_transitive (A : List (W → Prop)) (u v w : W)
    (huv : atLeastAsGoodAs A u v)
    (hvw : atLeastAsGoodAs A v w) :
    atLeastAsGoodAs A u w :=
  (kratzerPreorder A).le_trans u v w huv hvw

/-- Kratzer's ordering as a normality `Preorder` — definitionally
    `Normality.fromProps` (the same `Preorder.ofCriteria` order); connects to
    default-reasoning infrastructure (`Normality.optimal`, `refine`,
    `respects`, CR1–CR4). -/
def kratzerNormality (A : List (W → Prop)) : Preorder W :=
  Core.Order.Normality.fromProps A

/-- Equivalence under the ordering. -/
def orderingEquiv (A : List (W → Prop)) (w z : W) : Prop :=
  atLeastAsGoodAs A w z ∧ atLeastAsGoodAs A z w

theorem orderingEquiv_refl (A : List (W → Prop)) (w : W) : orderingEquiv A w w :=
  ⟨ordering_reflexive A w, ordering_reflexive A w⟩

theorem orderingEquiv_symm (A : List (W → Prop)) (w z : W)
    (h : orderingEquiv A w z) : orderingEquiv A z w :=
  ⟨h.2, h.1⟩

theorem orderingEquiv_trans (A : List (W → Prop)) (u v w : W)
    (huv : orderingEquiv A u v) (hvw : orderingEquiv A v w) :
    orderingEquiv A u w :=
  ⟨ordering_transitive A u v w huv.1 hvw.1,
   ordering_transitive A w v u hvw.2 huv.2⟩

/--
**Theorem 2: Empty ordering makes all worlds equivalent.**

If A = ∅, then for all w, z: w ≤_A z and z ≤_A w.

Proof: There are no propositions in `[]` to satisfy, so the universal is vacuous.
-/
theorem empty_ordering_all_equivalent (w z : W) :
    atLeastAsGoodAs ([] : List (W → Prop)) w z ∧
    atLeastAsGoodAs ([] : List (W → Prop)) z w := by
  refine ⟨?_, ?_⟩ <;> intro p hp <;> cases hp

theorem empty_ordering_trivial (w z : W) :
    (kratzerPreorder (W := W) []).le w z :=
  (empty_ordering_all_equivalent w z).1

theorem empty_ordering_universal_equiv (w z : W) :
    orderingEquiv (W := W) [] w z :=
  ⟨(empty_ordering_all_equivalent w z).1, (empty_ordering_all_equivalent w z).2⟩

/--
The set of worlds **accessible** from w given modal base f.

These are exactly the worlds in ⋂f(w) — worlds compatible with all facts in f(w).
-/
def accessibleWorlds (f : ModalBase W) (w : W) : Set W :=
  propIntersection (f w)

/--
The **best** worlds among accessible worlds, according to ordering source g.

These are the accessible worlds that are maximal under ≤_{g(w)}:
worlds w' such that for all accessible w'', w' ≤_{g(w)} w''.

When g(w) = ∅, all accessible worlds are best (by Theorem 2).
-/
def bestWorlds (f : ModalBase W) (g : OrderingSource W) (w : W) : Set W :=
  {w' | w' ∈ accessibleWorlds f w ∧
        ∀ w'' ∈ accessibleWorlds f w, atLeastAsGoodAs (g w) w' w''}

/--
**Theorem 3: Empty ordering source reduces to simple accessibility.**

When g(w) = ∅, bestWorlds = accessibleWorlds.
-/
theorem empty_ordering_simple (f : ModalBase W) (w : W) :
    bestWorlds f (fun _ => []) w = accessibleWorlds f w := by
  ext w'
  refine ⟨fun h => h.1, fun h => ⟨h, fun w'' _ => ?_⟩⟩
  exact (empty_ordering_all_equivalent w' w'').1

/-- Variant of `empty_ordering_simple` matching `emptyBackground` by name. -/
theorem empty_ordering_emptyBackground (f : ModalBase W) (w : W) :
    bestWorlds f emptyBackground w = accessibleWorlds f w := by
  unfold emptyBackground
  exact empty_ordering_simple f w

/-! ### The induced expectation state

[portner-2018] identifies the two components of his mood state with
Kratzer's parameters: "If we think of ⟨cs_c, <_c⟩ as a modal base and
ordering source, □_cs φ expresses simple necessity and □_< φ expresses
human necessity" (his commentary on (3), citing [kratzer-1981]).
`stateAt` is that identification read in the other direction: a
Kratzer pair is a world-indexed family of expectation states. -/

open Semantics.Dynamic.Default in
/-- The expectation state a modal base and ordering source induce at a
world: accessible worlds as information, the ordering-source ranking
as pattern. -/
def stateAt (f : ModalBase W) (g : OrderingSource W) (w : W) :
    ExpState W :=
  ⟨accessibleWorlds f w, kratzerNormality (g w)⟩

@[simp] theorem stateAt_info (f : ModalBase W) (g : OrderingSource W) (w : W) :
    (stateAt f g w).info = accessibleWorlds f w := rfl

@[simp] theorem stateAt_order (f : ModalBase W) (g : OrderingSource W) (w : W) :
    (stateAt f g w).order = kratzerNormality (g w) := rfl

/-- Dominant best worlds are optimal: `bestWorlds` requires being at
least as good as every accessible world, `ExpState.optimal` only
non-domination, so the former is the stronger notion on non-connected
orderings. -/
theorem bestWorlds_subset_optimal (f : ModalBase W) (g : OrderingSource W)
    (w : W) :
    bestWorlds f g w ⊆ (stateAt f g w).optimal :=
  fun _ hw => ⟨hw.1, fun v hv _ => hw.2 v hv⟩

/-- Realism is fiber-reflexivity: a modal base is realistic iff every
world belongs to its own induced information state. -/
theorem isRealistic_iff_mem_stateAt_info (f : ModalBase W)
    (g : OrderingSource W) :
    isRealistic f ↔ ∀ w, w ∈ (stateAt f g w).info :=
  ⟨fun h w p hp => h w p hp, fun h w p hp => h w p hp⟩

/-- On connected orderings the two best-world notions coincide. -/
theorem bestWorlds_eq_optimal_of_connected (f : ModalBase W)
    (g : OrderingSource W) (w : W)
    (hconn : Core.Order.Normality.connected (kratzerNormality (g w))) :
    bestWorlds f g w = (stateAt f g w).optimal :=
  Set.Subset.antisymm (bestWorlds_subset_optimal f g w)
    (fun w' hw' => ⟨hw'.1, fun v hv =>
      (hconn w' v).elim id (fun h => hw'.2 hv h)⟩)

/-- The best worlds among a given set, ranked by an ordering.
    Unlike `bestWorlds` which computes accessible worlds from a modal base,
    `bestAmong` takes a precomputed world set. This is needed when the
    domain has already been restricted (e.g., by promoted priorities in
    [rubinstein-2014]'s favored worlds). -/
def bestAmong (worlds : Set W) (ordering : List (W → Prop)) : Set W :=
  {w' | w' ∈ worlds ∧ ∀ w'' ∈ worlds, atLeastAsGoodAs ordering w' w''}

/-- With empty ordering, all worlds are best (Kratzer's theorem 2). -/
theorem bestAmong_empty (worlds : Set W) :
    bestAmong worlds [] = worlds := by
  ext w
  refine ⟨fun h => h.1, fun h => ⟨h, fun w' _ => ?_⟩⟩
  exact (empty_ordering_all_equivalent w w').1

/-- bestAmong is a subset of the input worlds. -/
theorem bestAmong_sub (worlds : Set W) (ordering : List (W → Prop)) :
    bestAmong worlds ordering ⊆ worlds :=
  fun _ hw => hw.1

/-- Best worlds in a superset that belong to a subset are best in the subset.

    If w' beats every world in a larger set, it certainly beats every world
    in any subset. This is the key lemma for showing that star-revision
    (domain widening) preserves strong necessity. -/
theorem bestAmong_superset {sub sup : Set W} {ordering : List (W → Prop)} {w' : W}
    (hSub : sub ⊆ sup)
    (hBest : w' ∈ bestAmong sup ordering)
    (hMem : w' ∈ sub) :
    w' ∈ bestAmong sub ordering :=
  ⟨hMem, fun v hv => hBest.2 v (hSub hv)⟩

end Semantics.Modality.Kratzer
