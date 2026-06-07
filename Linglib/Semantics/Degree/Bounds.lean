import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Data.Set.Basic
import Linglib.Core.Order.Boundedness
import Linglib.Semantics.Degree.Predicate

/-!
# Core/Scales/Bounds.lean — bounded-scale theorems + maxOnScale
[rett-2026]

Two clusters of theorems:

1. **Typeclass-driven licensing** (§4 of legacy Scale.lean):
   `open_no_upward_ceiling`, `upperBound_admits_optimum`, etc. — show how
   Mathlib boundedness typeclasses (`NoMaxOrder`, `OrderTop`, `OrderBot`,
   `NoMinOrder`) interact with monotonicity to admit/block optima.

2. **Order-sensitive maximality** (§6b of legacy Scale.lean):
   `maxOnScale R X`, `IsMaxDetermined`, `isAmbidirectional` — Rett 2026's
   relation-parameterized MAX operator + ambidirectionality scaffolding.

This file is part of the Phase A decomposition of the legacy
`Core/Scales/Scale.lean` dumping ground (master plan v4).
-/

namespace Semantics.Degree

open Core.Order

variable {α : Type*} [LinearOrder α]

-- ════════════════════════════════════════════════════
-- § 4. Typeclass-Based Licensing Theorems
-- ════════════════════════════════════════════════════

/-- On a scale with no maximum (`NoMaxOrder`), any upward monotone family
    that is nontrivial (i.e., some value yields a different set of worlds
    than another) cannot have a ceiling: for any candidate optimum, a
    strictly larger value exists.

    This is the typeclass-level counterpart of the data-level prediction
    `Boundedness.open_.isLicensed = false`: open scales block degree
    modification and TIA licensing because no element is maximal.

    Proof sketch: For any `x`, `NoMaxOrder` gives `y > x`. If `P` is
    upward monotone, `P x w → P y w`, so `x` is never the unique optimum. -/
theorem open_no_upward_ceiling [NoMaxOrder α]
    (P : α → Prop) (hMono : ∀ (x y : α), x ≤ y → P x → P y) (x : α) (hx : P x) :
    ∃ y, x < y ∧ P y := by
  obtain ⟨y, hy⟩ := NoMaxOrder.exists_gt x
  exact ⟨y, hy, hMono x y (le_of_lt hy) hx⟩

/-- On a scale with a top element (`OrderTop`), the predicate `· = ⊤` is
    upward monotone (vacuously — only ⊤ satisfies it) and nonconstant
    (on nontrivial types). This witnesses that upper-bounded scales admit
    an optimum.

    Proof sketch: `⊤` satisfies `· = ⊤`, and for any `x < ⊤`, `x` does not.
    So the family is not constant → `AdmitsOptimum` holds. -/
theorem upperBound_admits_optimum [OrderTop α] (h_nontrivial : ∃ x : α, x ≠ ⊤) :
    ∃ (P : α → Prop), (∀ x y : α, x ≤ y → P x → P y) ∧ ¬ (∀ x y : α, P x ↔ P y) := by
  refine ⟨(· = ⊤), fun x y hxy hx => ?_, fun h => ?_⟩
  · rw [hx] at hxy; exact le_antisymm le_top hxy
  · obtain ⟨x, hx⟩ := h_nontrivial
    exact hx ((h x ⊤).mpr rfl)

/-- On a scale with a bottom element (`OrderBot`), the predicate `· = ⊥` is
    downward monotone and nonconstant (on nontrivial types). This witnesses
    that lower-bounded scales admit an optimum. -/
theorem lowerBound_admits_optimum [OrderBot α] (h_nontrivial : ∃ x : α, x ≠ ⊥) :
    ∃ (P : α → Prop), (∀ x y : α, x ≤ y → P y → P x) ∧ ¬ (∀ x y : α, P x ↔ P y) := by
  refine ⟨(· = ⊥), fun x y hxy hy => ?_, fun h => ?_⟩
  · rw [hy] at hxy; exact le_antisymm hxy bot_le
  · obtain ⟨x, hx⟩ := h_nontrivial
    exact hx ((h x ⊥).mpr rfl)

/-- Boundedness is necessary for licensing: on a scale with no upper bound
    and no lower bound, there exists a monotone family with no optimum.
    Contrapositive: if every monotone family admits an optimum, the scale
    has a bound. -/
theorem open_scale_unlicensable [NoMaxOrder α] [NoMinOrder α]
    (h : ∃ x y : α, x ≠ y) :
    ∃ (P : α → Prop), (∀ x y, x ≤ y → P x → P y) ∧ ¬ (∀ x y, P x ↔ P y) ∧
      ∀ x, P x → ∃ y, x < y ∧ P y := by
  obtain ⟨x₀, _, _⟩ := h
  refine ⟨(x₀ ≤ ·), fun a b hab ha => le_trans ha hab, ?_, fun x hx => ?_⟩
  · intro hconst
    obtain ⟨z, hz⟩ := NoMinOrder.exists_lt x₀
    exact absurd ((hconst z x₀).mpr (le_refl x₀)) (not_le.mpr hz)
  · obtain ⟨y, hy⟩ := NoMaxOrder.exists_gt x
    exact ⟨y, hy, le_trans hx (le_of_lt hy)⟩

/-! ### Order-theoretic boundedness primitives

Whether a scale has a greatest degree, stated *structurally* via mathlib's
`OrderTop` / `NoMaxOrder` mixins rather than as stored data — the order-theoretic
facts that telicity and licensing derive from (see `Semantics/Aspect/ScalarTelicity.lean`). -/

/-- "Has a greatest element", as a proposition — usable when an `OrderTop`
    instance is not in hand (e.g. under a quantifier). -/
def HasGreatest (β : Type*) [LE β] : Prop := ∃ m : β, ∀ x : β, x ≤ m

theorem hasGreatest_of_orderTop {β : Type*} [LE β] [OrderTop β] : HasGreatest β :=
  ⟨⊤, fun _ => le_top⟩

theorem not_hasGreatest_of_noMaxOrder {β : Type*} [Preorder β] [NoMaxOrder β] :
    ¬ HasGreatest β := by
  rintro ⟨m, hm⟩
  obtain ⟨c, hc⟩ := exists_gt m
  exact absurd (hm c) (not_le_of_gt hc)

/-- `OrderTop` and `NoMaxOrder` are mutually exclusive — the rigorous sense in
    which a scale either has a greatest degree or does not. (Not in Mathlib.) -/
theorem not_noMaxOrder_of_orderTop {β : Type*} [Preorder β] [OrderTop β] :
    ¬ NoMaxOrder β := by
  intro h
  obtain ⟨c, hc⟩ := h.exists_gt ⊤
  exact absurd (lt_of_lt_of_le hc le_top) (lt_irrefl ⊤)

-- ════════════════════════════════════════════════════
-- § 6b. Order-Sensitive MAX ([rett-2026])
-- ════════════════════════════════════════════════════

/-! ### Scale-sensitive maximality operator

[rett-2026]: MAX_R(X) picks the element(s)
of X that R-dominate all other members. For the `<` scale this is the GLB
(earliest / smallest), for `>` the LUB (latest / largest). The same operator
underlies both temporal connectives (*before*/*after*) and degree comparatives.

- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
-/

/-- Order-sensitive maximality ([rett-2026], def. 1):
    MAX_R(X) = { x ∈ X | ∀ x' ∈ X, x' ≠ x → R x x' }.
    Domain-general over any relation R and set X. -/
def maxOnScale {α : Type*} (R : α → α → Prop) (X : Set α) : Set α :=
  { x | x ∈ X ∧ ∀ x' ∈ X, x' ≠ x → R x x' }

/-- MAX on a singleton is that singleton: MAX_R({x}) = {x}.
    The universal quantifier is vacuously satisfied. -/
theorem maxOnScale_singleton {α : Type*} (R : α → α → Prop) (x : α) :
    maxOnScale R {x} = {x} := by
  ext y
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl, _⟩; rfl
  · rintro rfl
    exact ⟨rfl, fun x' hx' hne => absurd hx' hne⟩

/-- MAX₍<₎ on a closed interval `{x | s ≤ x ∧ x ≤ f}` is the singleton `{s}`.
    The minimum element s R-dominates all others on the `<` scale.
    Dual: MAX₍>₎ on the same interval is `{f}`. -/
theorem maxOnScale_lt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale (· < ·) { x : α | s ≤ x ∧ x ≤ f } = {s} := by
  ext x
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hxs, _⟩, hdom⟩
    by_contra hne
    have : s < x := lt_of_le_of_ne hxs (Ne.symm hne)
    have := hdom s ⟨le_refl _, hsf⟩ (ne_of_lt ‹s < x›)
    exact absurd ‹s < x› (not_lt.mpr (le_of_lt this))
  · rintro rfl
    exact ⟨⟨le_refl _, hsf⟩, fun x' ⟨hx's, _⟩ hne =>
      lt_of_le_of_ne hx's (Ne.symm hne)⟩

/-- MAX₍>₎ on a closed interval `{x | s ≤ x ∧ x ≤ f}` is the singleton `{f}`.
    The maximum element R-dominates all others on the `>` scale. -/
theorem maxOnScale_gt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale (· > ·) { x : α | s ≤ x ∧ x ≤ f } = {f} := by
  ext x
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, hxf⟩, hdom⟩
    by_contra hne
    have : x < f := lt_of_le_of_ne hxf hne
    have := hdom f ⟨hsf, le_refl _⟩ (ne_of_gt ‹x < f›)
    exact absurd ‹x < f› (not_lt.mpr (le_of_lt this))
  · rintro rfl
    exact ⟨⟨hsf, le_refl _⟩, fun x' ⟨_, hx'f⟩ hne =>
      lt_of_le_of_ne hx'f hne⟩

/-- A scalar construction f is **ambidirectional** iff
    applying f to a set B and to its complement Bᶜ yields the same result,
    because MAX picks the same informative boundary from both.
    This is the mechanism behind expletive negation licensing: when
    f(B) ↔ f(Bᶜ), negating B is truth-conditionally vacuous. -/
def isAmbidirectional {α : Type*} (f : Set α → Prop) (B : Set α) : Prop :=
  f B ↔ f Bᶜ

/-- A predicate `f` is **MAX_R-determined** iff its value depends only on
    `maxOnScale R` of its argument: any two sets with the same `MAX_R`
    yield the same `f`-verdict. The before/until/comparative theorems all
    establish exactly this: *before* relates A to `MAX₍<₎` of B, the
    comparative *than*-clause to `MAX₍≥₎` of the degree set, etc. -/
def IsMaxDetermined {α : Type*} (R : α → α → Prop) (f : Set α → Prop) : Prop :=
  ∀ B₁ B₂ : Set α, maxOnScale R B₁ = maxOnScale R B₂ → (f B₁ ↔ f B₂)

/-- **Shared informative bound** ⇒ ambidirectionality. The general
    template behind Rett's typology: if a construction is `MAX_R`-determined
    and `B` and `Bᶜ` share their `MAX_R`-bound, then the construction is
    truth-conditionally insensitive to negation of B.

    Each per-construction ambidirectionality theorem in the library is an
    instance of this template — they prove the shared-bound side condition
    for a specific `f` and a class of `B`'s, then this lemma packages the
    result. See `Semantics.Tense.TemporalConnectives.before_preEvent_ambidirectional`
    for the canonical instance. -/
theorem ambidirectional_of_shared_max {α : Type*} {R : α → α → Prop}
    (f : Set α → Prop) (hf : IsMaxDetermined R f) (B : Set α)
    (hshared : maxOnScale R B = maxOnScale R Bᶜ) :
    isAmbidirectional f B :=
  hf B Bᶜ hshared

/-- **Converse**: an ambidirectional construction must share its `MAX_R`
    bound between B and Bᶜ — but only when MAX_R alone *witnesses* the
    distinction. Stated as a contrapositive to make the empirical content
    explicit: if MAX_R differs between B and Bᶜ but the construction
    cannot tell them apart by any *other* means (i.e. MAX_R-determined),
    then the construction is non-ambidirectional. The full converse
    requires assuming `f` separates sets with distinct MAX_R values, so
    we instead expose this as a derived fact only under that assumption. -/
theorem not_ambidirectional_of_distinct_max_separated {α : Type*}
    {R : α → α → Prop} (f : Set α → Prop) (B : Set α)
    (hsep : ∀ B₁ B₂ : Set α,
      maxOnScale R B₁ ≠ maxOnScale R B₂ → ¬ (f B₁ ↔ f B₂))
    (hdiff : maxOnScale R B ≠ maxOnScale R Bᶜ) :
    ¬ isAmbidirectional f B :=
  hsep B Bᶜ hdiff

/-- **Bridge**: `maxOnScale (· ≥ ·)` applied to the "at least" degree set
    `{d | d ≤ μ(w)}` yields `{μ(w)}` — the singleton containing the true
    value. This connects the relational MAX to `IsMaxInf`.

    The convention: `maxOnScale R X` picks elements x ∈ X with `R x x'` for
    all other x'. With `R = (· ≥ ·)`, this picks elements ≥ all others,
    i.e., the maximum. -/
theorem maxOnScale_atLeast_singleton {W : Type*} (μ : W → α) (w : W) :
    maxOnScale (· ≥ ·) { d : α | d ≤ μ w } = { μ w } := by
  ext x
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff, ge_iff_le]
  constructor
  · rintro ⟨hx, hdom⟩
    by_contra hne
    have hlt : x < μ w := lt_of_le_of_ne hx hne
    have := hdom (μ w) (le_refl _) (Ne.symm hne)
    exact not_le.mpr hlt this
  · rintro rfl
    exact ⟨le_refl _, fun x' hx' hne => le_of_lt (lt_of_le_of_ne hx' hne)⟩

/-- MAX₍≥₎ on {d | d ≤ b} is {b}. Corollary of `maxOnScale_atLeast_singleton`
    with `μ = id`. Used by the comparative boundary theorems. -/
theorem maxOnScale_ge_atMost (b : α) :
    maxOnScale (· ≥ ·) {d | d ≤ b} = {b} :=
  maxOnScale_atLeast_singleton id b

end Semantics.Degree
