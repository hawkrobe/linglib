/-
@cite{kratzer-1981} World Ordering

Worlds are ordered by set-inclusion of satisfied propositions:
w ≤_A z iff {p ∈ A : z ∈ p} ⊆ {p ∈ A : w ∈ p}.

Best worlds are those maximal under this ordering among accessible worlds.

- Kratzer, A. (1981). The Notional Category of Modality. de Gruyter. pp. 38-74.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Background
import Linglib.Core.Logic.SatisfactionOrdering
import Linglib.Core.Semantics.Proposition
import Mathlib.Order.Basic

namespace Semantics.Modality.Kratzer

open Semantics.Attitudes.Intensional

/--
The set of propositions from A that world w satisfies.

This is {p ∈ A : w ∈ p} in Kratzer's notation.
-/
def satisfiedPropositions (A : List (BProp World)) (w : World) : List (BProp World) :=
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
def atLeastAsGoodAs (A : List (BProp World)) (w z : World) : Bool :=
  -- Every proposition in A satisfied by z is also satisfied by w
  (satisfiedPropositions A z).all λ p => p w

notation:50 w " ≤[" A "] " z => atLeastAsGoodAs A w z

/--
Strict ordering: w <_A z iff w ≤_A z but not z ≤_A w.

This means w satisfies strictly more ideal propositions than z.
-/
def strictlyBetter (A : List (BProp World)) (w z : World) : Bool :=
  atLeastAsGoodAs A w z && !atLeastAsGoodAs A z w

notation:50 w " <[" A "] " z => strictlyBetter A w z


open Core.SatisfactionOrdering

/--
Kratzer's world ordering as a `SatisfactionOrdering`.

A world w satisfies proposition p iff p(w) = true.
This connects Kratzer semantics to the generic ordering framework.
-/
def worldOrdering (A : List (BProp World)) : SatisfactionOrdering World (BProp World) where
  satisfies := λ w p => p w
  criteria := A

/--
**Kratzer's ordering matches the generic framework.**

This theorem establishes that `atLeastAsGoodAs` is exactly the
generic `SatisfactionOrdering.atLeastAsGood` for worlds.
-/
theorem atLeastAsGoodAs_eq_generic (A : List (BProp World)) (w z : World) :
    atLeastAsGoodAs A w z = (worldOrdering A).atLeastAsGood w z := by
  unfold atLeastAsGoodAs worldOrdering SatisfactionOrdering.atLeastAsGood
         SatisfactionOrdering.satisfiedBy satisfiedPropositions
  rfl

/-- Reflexivity via generic framework. -/
theorem ordering_reflexive (A : List (BProp World)) (w : World) :
    atLeastAsGoodAs A w w = true := by
  rw [atLeastAsGoodAs_eq_generic]
  exact SatisfactionOrdering.atLeastAsGood_refl (worldOrdering A) w

/-- Transitivity via generic framework. -/
theorem ordering_transitive (A : List (BProp World)) (u v w : World)
    (huv : atLeastAsGoodAs A u v = true)
    (hvw : atLeastAsGoodAs A v w = true) :
    atLeastAsGoodAs A u w = true := by
  rw [atLeastAsGoodAs_eq_generic] at *
  exact SatisfactionOrdering.atLeastAsGood_trans (worldOrdering A) u v w huv hvw

-- Mathlib Preorder Instance (via generic framework)

/--
**Kratzer's ordering as a mathlib Preorder.**

Derived from the generic `SatisfactionOrdering.toPreorder`.
-/
def kratzerPreorder (A : List (BProp World)) : Preorder World :=
  (worldOrdering A).toPreorder

/-- Equivalence under the ordering (via generic framework). -/
def orderingEquiv (A : List (BProp World)) (w z : World) : Prop :=
  (worldOrdering A).equiv w z

theorem orderingEquiv_refl (A : List (BProp World)) (w : World) : orderingEquiv A w w :=
  SatisfactionOrdering.equiv_refl (worldOrdering A) w

theorem orderingEquiv_symm (A : List (BProp World)) (w z : World)
    (h : orderingEquiv A w z) : orderingEquiv A z w :=
  SatisfactionOrdering.equiv_symm (worldOrdering A) w z h

theorem orderingEquiv_trans (A : List (BProp World)) (u v w : World)
    (huv : orderingEquiv A u v) (hvw : orderingEquiv A v w) :
    orderingEquiv A u w :=
  SatisfactionOrdering.equiv_trans (worldOrdering A) u v w huv hvw

/--
**Theorem 2: Empty ordering makes all worlds equivalent.**

If A = ∅, then for all w, z: w ≤_A z and z ≤_A w.

Proof: The set of propositions in ∅ satisfied by any world is ∅.
Vacuously, ∅ ⊆ ∅.
-/
theorem empty_ordering_all_equivalent (w z : World) :
    atLeastAsGoodAs [] w z = true ∧ atLeastAsGoodAs [] z w = true := by
  constructor <;> (unfold atLeastAsGoodAs satisfiedPropositions; simp)

theorem empty_ordering_trivial (w z : World) :
    (kratzerPreorder []).le w z :=
  (empty_ordering_all_equivalent w z).1

theorem empty_ordering_universal_equiv (w z : World) :
    orderingEquiv [] w z :=
  ⟨(empty_ordering_all_equivalent w z).1, (empty_ordering_all_equivalent w z).2⟩

-- Galois Connection (Proposition-World Duality)

open Core.Proposition.GaloisConnection

/--
**Kratzer's extension**: List-based version for the finite World type.

This is `propIntersection` renamed for clarity.
-/
def extension (props : List (BProp World)) : List World :=
  propIntersection props

/--
**Kratzer's intension**: Filter propositions true at all given worlds.
-/
def intension (worlds : List World) (props : List (BProp World)) : List (BProp World) :=
  intensionL worlds props

theorem extension_eq_core (props : List (BProp World)) :
    extension props = extensionL allWorlds props := by
  unfold extension propIntersection extensionL
  rfl

theorem extension_antitone (A B : List (BProp World)) (w : World)
    (hSub : ∀ p, p ∈ A → p ∈ B)
    (hw : w ∈ extension B) :
    w ∈ extension A := by
  rw [extension_eq_core] at hw ⊢
  exact extensionL_antitone allWorlds A B w hSub hw

theorem intension_antitone (W V : List World) (A : List (BProp World)) (p : BProp World)
    (hSub : ∀ w, w ∈ W → w ∈ V)
    (hp : p ∈ intension V A) :
    p ∈ intension W A :=
  intensionL_antitone A W V p hSub hp


/--
The set of worlds **accessible** from w given modal base f.

These are exactly the worlds in ∩f(w) - worlds compatible with all facts in f(w).
-/
def accessibleWorlds (f : ModalBase) (w : World) : List World :=
  propIntersection (f w)

theorem accessible_is_extension (f : ModalBase) (w : World) :
    accessibleWorlds f w = extension (f w) := rfl

/--
**Accessibility predicate**: w' is accessible from w iff w' ∈ ∩f(w).
-/
def accessibleFrom (f : ModalBase) (w w' : World) : Bool :=
  (f w).all (λ p => p w')

/--
The **best** worlds among accessible worlds, according to ordering source g.

These are the accessible worlds that are maximal under ≤_{g(w)}:
worlds w' such that for all accessible w'', w' ≤_{g(w)} w''.

When g(w) = ∅, all accessible worlds are best (by Theorem 2).
-/
def bestWorlds (f : ModalBase) (g : OrderingSource) (w : World) : List World :=
  let accessible := accessibleWorlds f w
  let ordering := g w
  accessible.filter λ w' =>
    accessible.all λ w'' => atLeastAsGoodAs ordering w' w''

/--
**Theorem 3: Empty ordering source reduces to simple accessibility.**

When g(w) = ∅, bestWorlds = accessibleWorlds.
-/
theorem empty_ordering_simple (f : ModalBase) (w : World) :
    bestWorlds f (λ _ => []) w = accessibleWorlds f w := by
  unfold bestWorlds accessibleWorlds
  simp only [List.filter_eq_self]
  intro w' _
  simp only [List.all_eq_true]
  intro w'' _
  exact (empty_ordering_all_equivalent w' w'').1

/-- Variant of `empty_ordering_simple` matching `emptyBackground` by name.
    Avoids the `unfold emptyBackground` workaround needed before `rw [empty_ordering_simple]`. -/
theorem empty_ordering_emptyBackground (f : ModalBase) (w : World) :
    bestWorlds f emptyBackground w = accessibleWorlds f w := by
  unfold emptyBackground
  exact empty_ordering_simple f w

/-- The best worlds among a given set, ranked by an ordering.
    Unlike `bestWorlds` which computes accessible worlds from a modal base,
    `bestAmong` takes a precomputed world list. This is needed when the
    domain has already been restricted (e.g., by promoted priorities in
    @cite{rubinstein-2014}'s favored worlds). -/
def bestAmong (worlds : List World) (ordering : List (BProp World)) : List World :=
  worlds.filter λ w' =>
    worlds.all λ w'' => atLeastAsGoodAs ordering w' w''

/-- With empty ordering, all worlds are best (Kratzer's theorem 2). -/
theorem bestAmong_empty (worlds : List World) :
    bestAmong worlds [] = worlds := by
  unfold bestAmong
  rw [List.filter_eq_self]
  intro w _
  rw [List.all_eq_true]
  intro w' _
  exact (empty_ordering_all_equivalent w w').1

/-- bestAmong is a subset of the input worlds. -/
theorem bestAmong_sub (worlds : List World) (ordering : List (BProp World)) :
    ∀ w, w ∈ bestAmong worlds ordering → w ∈ worlds :=
  λ _ hw => List.mem_of_mem_filter hw

end Semantics.Modality.Kratzer
