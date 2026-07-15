import Linglib.Core.Order.Normality
import Linglib.Semantics.Dynamic.ContextChange

/-!
# Default Reasoning in Update Semantics

[veltman-1996]

[veltman-1996] extends update semantics with **expectation patterns** —
normality orderings on worlds — and two new operators:

- **Normally p**: refines the expectation pattern so p-worlds are preferred
- **Presumably p**: a test that passes iff all optimal worlds satisfy p

The key insight is that defaults are *dynamic*: "normally p" does not
eliminate worlds (like assertion does) but changes the normality ordering.
This means defaults persist under information growth — learning q does
not undo the expectation that p is normal.

## What's here (§3)

This module formalizes Veltman's §3: expectation states, the operators
"normally", "presumably", and "might", and the key results:
- Defaults create expectations (`normally_creates_respect`)
- Defaults persist under further updates (`persistence_assert`, `persistence_normally`)
- "Normally p; presumably p" succeeds (`normally_presumably_succeeds`)
- Conflicting defaults yield agnosticism (`conflicting_defaults_iff_agree`)
- Compatible defaults reinforce (`compatible_defaults_optimal`)
- Promotion is idempotent and commutative (`promote_respects_idempotent`, `promote_comm`)

## What's not here (§5)

§5 proves which inference patterns are valid for the default
conditional (contraposition fails, cautious monotonicity holds, etc.).
Key patterns are verified as regression tests in
`Studies/Veltman1996.lean`.

§4 (expectation frames, conditional defaults, specificity) is
formalized in `Frames.lean` alongside this module.

## Connection to existing infrastructure

- **Basic.lean**: Veltman's base language (§2) — states, updates, tests,
  might as consistency test — is formalized there. This module adds the
  default layer (§3).

- **BeliefRevision.lean**: `PreferentialConsequence` (System P) and
  `PlausibilityOrder` formalize the *static* characterization of default
  reasoning. Veltman's system is the *dynamic* realization: the default
  consequence relation it induces validates System P.

- **Core/Order/Normality.lean**: The normality ordering (mathlib
  `Preorder W`) and the `refine` operation are defined there as shared
  infrastructure. This module builds `ExpState` (expectation states) on
  top of that.

-/

namespace UpdateSemantics.Default

open Core.Order

variable {W : Type*}


-- ═══ Expectation States ═══

/-- An **expectation state**: an information state paired with a
    normality ordering on worlds.

    The information state tracks what is known (which worlds are
    compatible with the discourse so far). The normality ordering
    encodes expectations about what is normal (which worlds are
    most expected given the defaults processed so far).

    Veltman's notation: σ = ⟨ε, s⟩ where ε is a preorder (expectation
    pattern) and s ⊆ W is the information state. -/
structure ExpState (W : Type*) where
  /-- The information state: set of worlds compatible with the discourse -/
  info : Set W
  /-- The normality ordering (expectation pattern) -/
  order : Preorder W

/-- The initial expectation state: all worlds are possible and equally
    normal. No information, no expectations. -/
def ExpState.init : ExpState W where
  info := Set.univ
  order := Normality.total

/-- Optimal worlds in the current state: the most normal worlds
    among those compatible with the discourse. -/
def ExpState.optimal (σ : ExpState W) : Set W :=
  Normality.optimal σ.order σ.info


-- ═══ Update Operations ═══

/-- **Assertion update** (Veltman's factual update): eliminate
    non-φ-worlds, preserve the pattern. Information grows; expectations
    are unchanged. This is [portner-2018]'s `+`-update on the context
    set, and the standard eliminative update from CCP.lean lifted to
    expectation states. -/
def ExpState.assert (σ : ExpState W) (φ : W → Prop) : ExpState W :=
  ⟨{ w ∈ σ.info | φ w }, σ.order⟩

/-- **Promotion update** (Veltman's *normally φ*): refine the pattern
    so φ-worlds are preferred. The information state is unchanged — we
    don't learn that φ is true, only that φ is *expected*.

    This is the core innovation of [veltman-1996]: defaults operate on
    the expectation pattern, not on the information state. Read at the
    discourse level it is [portner-2018]'s `⋆`-update (the To-Do-List
    update of [portner-2004]). -/
def ExpState.promote (σ : ExpState W) (φ : W → Prop) : ExpState W :=
  ⟨σ.info, Normality.refine σ.order φ⟩

section Classical
open Classical

/-- **"Presumably p"**: a test that passes iff all optimal worlds
    satisfy p. Like `CCP.might`, this is a test — it either returns
    the state unchanged or crashes (empties the info state).

    "Presumably p" checks whether p follows from current expectations. -/
noncomputable def presumablyTest (φ : W → Prop) (σ : ExpState W) : ExpState W :=
  if ∀ w ∈ σ.optimal, φ w then σ else ⟨∅, σ.order⟩

/-- **"Might p"**: consistency test on the information state.
    Passes iff the information state has p-worlds.
    The expectation pattern is irrelevant — might is purely informational. -/
noncomputable def mightTest (φ : W → Prop) (σ : ExpState W) : ExpState W :=
  if ∃ w ∈ σ.info, φ w then σ else ⟨∅, σ.order⟩

end Classical


-- ═══ Basic Properties ═══

namespace ExpState

@[simp] theorem assert_info (σ : ExpState W) (φ : W → Prop) :
    (σ.assert φ).info = { w ∈ σ.info | φ w } := rfl

/-- Assertion preserves the normality ordering. -/
@[simp] theorem assert_order (σ : ExpState W) (φ : W → Prop) :
    (σ.assert φ).order = σ.order := rfl

/-- Promotion preserves the information state. -/
@[simp] theorem promote_info (σ : ExpState W) (φ : W → Prop) :
    (σ.promote φ).info = σ.info := rfl

@[simp] theorem promote_order (σ : ExpState W) (φ : W → Prop) :
    (σ.promote φ).order = Normality.refine σ.order φ := rfl

/-- Assertion is eliminative: it can only shrink the info state. -/
theorem assert_info_subset (σ : ExpState W) (φ : W → Prop) :
    (σ.assert φ).info ⊆ σ.info := fun _ hw => hw.1

/-! Refinement order on expectation states: more constrained ≤ less
constrained, componentwise — finer ≤ coarser, matching the `Setoid`
convention. (NB [veltman-1996] orients his `≤` the other way, weaker
below stronger; the content is the same.) Both updates are
deflationary, monotone, and idempotent for this order, and
*acceptance* — [veltman-1996]'s `σ ⊩ φ` iff `σ[φ] = σ` — is the
fixpoint condition `σ ≤ σ[φ]`. -/

instance : Preorder (ExpState W) where
  le σ τ := σ.info ⊆ τ.info ∧ σ.order ≤ τ.order
  le_refl _ := ⟨subset_rfl, le_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem le_iff {σ τ : ExpState W} :
    σ ≤ τ ↔ σ.info ⊆ τ.info ∧ σ.order ≤ τ.order := Iff.rfl

/-- Assertion lands below the input. -/
theorem assert_le_self (σ : ExpState W) (φ : W → Prop) : σ.assert φ ≤ σ :=
  ⟨σ.assert_info_subset φ, le_refl _⟩

/-- Promotion lands below the input. -/
theorem promote_le_self (σ : ExpState W) (φ : W → Prop) : σ.promote φ ≤ σ :=
  ⟨subset_rfl, inf_le_left⟩

theorem assert_mono {σ τ : ExpState W} (h : σ ≤ τ) (φ : W → Prop) :
    σ.assert φ ≤ τ.assert φ :=
  ⟨fun _ hw => ⟨h.1 hw.1, hw.2⟩, h.2⟩

theorem promote_mono {σ τ : ExpState W} (h : σ ≤ τ) (φ : W → Prop) :
    σ.promote φ ≤ τ.promote φ :=
  ⟨h.1, inf_le_inf_right _ h.2⟩

/-- Membership in the information state after a sequence of assertions:
    the input's information, filtered by every asserted proposition. -/
theorem mem_foldl_assert_info (ps : List (W → Prop)) (σ : ExpState W) (v : W) :
    v ∈ (ps.foldl ExpState.assert σ).info ↔ v ∈ σ.info ∧ ∀ p ∈ ps, p v := by
  induction ps generalizing σ with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [assert_info, Set.mem_setOf_eq, List.mem_cons, Set.mem_sep_iff]
    constructor
    · rintro ⟨⟨hv, hp⟩, hps⟩
      exact ⟨hv, fun q hq => hq.elim (fun h => h ▸ hp) (hps q)⟩
    · rintro ⟨hv, hall⟩
      exact ⟨⟨hv, hall p (Or.inl rfl)⟩, fun q hq => hall q (Or.inr hq)⟩

/-- The ordering after a sequence of promotions: the input's ordering,
    refined by the criterion preorder of every promoted proposition. -/
theorem foldl_promote_order_le (ps : List (W → Prop)) (σ : ExpState W) (w v : W) :
    (ps.foldl ExpState.promote σ).order.le w v ↔
      σ.order.le w v ∧ ∀ p ∈ ps, p v → p w := by
  induction ps generalizing σ with
  | nil => exact ⟨fun h => ⟨h, by simp⟩, And.left⟩
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [promote_order, Core.Order.Normality.refine_le, List.mem_cons]
    constructor
    · rintro ⟨⟨hle, hp⟩, hps⟩
      exact ⟨hle, fun q hq => hq.elim (fun h => h ▸ hp) (hps q)⟩
    · rintro ⟨hle, hall⟩
      exact ⟨⟨hle, hall p (Or.inl rfl)⟩, fun q hq => hall q (Or.inr hq)⟩

/-- Promotion sequences leave the information state fixed. -/
@[simp] theorem foldl_promote_info (ps : List (W → Prop)) (σ : ExpState W) :
    (ps.foldl ExpState.promote σ).info = σ.info := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih => rw [List.foldl_cons, ih]; rfl

/-- **Acceptance fixpoint for assertion** ([veltman-1996], §1): the
    input refines its own assertion iff φ already holds throughout the
    information state. -/
theorem le_assert_iff (σ : ExpState W) (φ : W → Prop) :
    σ ≤ σ.assert φ ↔ ∀ w ∈ σ.info, φ w :=
  ⟨fun h w hw => (h.1 hw).2, fun h => ⟨fun _ hw => ⟨hw, h _ hw⟩, le_refl _⟩⟩

/-- **Acceptance fixpoint for promotion** ([veltman-1996]: `e` is a
    *default* in `ε` iff `ε ∘ e = ε`, his Def 4.2): the input refines
    its own promotion iff the ordering already respects φ. This is the
    support notion for the preferential component — "φ is already on
    the To-Do List" — distinct from truth at the best worlds. -/
theorem le_promote_iff (σ : ExpState W) (φ : W → Prop) :
    σ ≤ σ.promote φ ↔ Normality.respects σ.order φ := by
  constructor
  · intro h w v hle hv
    exact (h.2 hle).2 hv
  · intro h
    exact ⟨subset_rfl, le_inf (le_refl _) (fun w v hle hv => h w v hle hv)⟩

end ExpState

/-- Presumably is a test: it either returns the state or empties info. -/
theorem presumably_isTest (φ : W → Prop) (σ : ExpState W) :
    (presumablyTest φ σ).info = σ.info ∨ (presumablyTest φ σ).info = ∅ := by
  unfold presumablyTest; split <;> simp

/-- Might is a test: it either returns the state or empties info. -/
theorem might_isTest (φ : W → Prop) (σ : ExpState W) :
    (mightTest φ σ).info = σ.info ∨ (mightTest φ σ).info = ∅ := by
  unfold mightTest; split <;> simp

/-- Tests preserve the ordering. -/
theorem mightTest_preserves_order (φ : W → Prop) (σ : ExpState W) :
    (mightTest φ σ).order = σ.order := by
  unfold mightTest; split <;> rfl

theorem presumablyTest_preserves_order (φ : W → Prop) (σ : ExpState W) :
    (presumablyTest φ σ).order = σ.order := by
  unfold presumablyTest; split <;> rfl


-- ═══ Key Theorem — "Normally p; Presumably p" Succeeds ═══

/-- **General presumably**: if the ordering is connected, respects φ,
    and the info state has φ-worlds, then "presumably φ" passes.

    This is the general form of Veltman's claim that defaults create
    valid presumptions. The connectedness condition is essential: without
    it, a non-φ-world can be optimal by being incomparable with all
    φ-worlds (see `Normality.optimal_of_respects_connected`). -/
theorem presumably_passes (σ : ExpState W) (φ : W → Prop)
    (hresp : Normality.respects σ.order φ) (hconn : Normality.connected σ.order)
    (hex : ∃ w ∈ σ.info, φ w) :
    presumablyTest φ σ = σ := by
  simp only [presumablyTest]
  rw [if_pos]
  intro w hw
  exact (Normality.optimal_of_respects_connected σ.order φ σ.info
    hresp hconn hex hw).2

/-- **The central result**: after processing "normally p", the test
    "presumably p" passes — provided the information state has p-worlds.

    Corollary of `presumably_passes`: "normally p" creates respect,
    and a single refinement from total preserves connectedness. -/
theorem normally_presumably_succeeds (φ : W → Prop) (d : Set W)
    (hex : ∃ w ∈ d, φ w) :
    let σ : ExpState W := ⟨d, Normality.total⟩
    presumablyTest φ (σ.promote φ) = σ.promote φ := by
  simp only [presumablyTest, ExpState.promote, ExpState.optimal]
  rw [if_pos]
  intro w hw
  rw [Normality.refine_total_optimal φ d hex] at hw
  exact hw.2


-- ═══ Persistence ═══

/-- **Persistence under assertion**: if the ordering respects p
    (i.e., the state has accepted "normally p"), then asserting any
    q preserves this. Learning new facts does not undo expectations.

    [veltman-1996], Proposition 3.6(iv). -/
theorem persistence_assert (σ : ExpState W) (φ ψ : W → Prop)
    (h : Normality.respects σ.order φ) :
    Normality.respects (σ.assert ψ).order φ := h

/-- **Persistence under further defaults**: if the ordering respects p,
    then processing "normally q" (for any q) preserves this. Later
    defaults do not undo earlier ones.

    [veltman-1996], Proposition 3.6(iv). -/
theorem persistence_normally (σ : ExpState W) (φ ψ : W → Prop)
    (h : Normality.respects σ.order φ) :
    Normality.respects (σ.promote ψ).order φ :=
  Normality.refine_preserves_respects σ.order φ ψ h

/-- After "normally p", the ordering respects p. Combined with
    persistence, this means "normally p" creates a permanent expectation. -/
theorem normally_creates_respect (σ : ExpState W) (φ : W → Prop) :
    Normality.respects (σ.promote φ).order φ :=
  Normality.refine_respects σ.order φ


-- ═══ Idempotency and Commutativity ═══

/-- **Idempotency**: if the state already accepts "normally φ" (the
    ordering respects φ), then processing "normally φ" again is a no-op.

    [veltman-1996], Proposition 3.6(ii) at the state level. -/
theorem promote_respects_idempotent (σ : ExpState W) (φ : W → Prop)
    (h : Normality.respects σ.order φ) :
    σ.promote φ = σ := by
  show ExpState.mk σ.info (Normality.refine σ.order φ) = σ
  congr 1
  exact Normality.refine_of_respects σ.order φ h

/-- Corollary: "normally φ; normally φ" = "normally φ" from any state. -/
theorem promote_promote_self (σ : ExpState W) (φ : W → Prop) :
    (σ.promote φ).promote φ = σ.promote φ :=
  promote_respects_idempotent _ φ (normally_creates_respect σ φ)

/-- **Commutativity**: the order of defaults doesn't matter.
    "Normally φ; normally ψ" = "normally ψ; normally φ". -/
theorem promote_comm (σ : ExpState W) (φ ψ : W → Prop) :
    (σ.promote φ).promote ψ = (σ.promote ψ).promote φ := by
  show ExpState.mk σ.info (Normality.refine (Normality.refine σ.order φ) ψ) =
       ExpState.mk σ.info (Normality.refine (Normality.refine σ.order ψ) φ)
  congr 1
  exact Normality.refine_comm σ.order φ ψ


-- ═══ Conflicting Defaults ═══

/-- **Conflicting defaults produce agnosticism.** After processing both
    "normally p" and "normally ¬p", the ordering relates worlds only
    when they agree on p. Both p-worlds and ¬p-worlds can be optimal,
    so neither "presumably p" nor "presumably ¬p" passes.

    This is the degenerate (unconditional) case of conflicting defaults.
    The full Nixon Diamond — where the conflict arises from conditional
    defaults "if Quaker then normally pacifist" and "if Republican then
    normally not pacifist" — requires Veltman's §4 expectation frames. -/
theorem conflicting_defaults_le (φ : W → Prop) (w v : W) :
    (Normality.refine (Normality.refine Normality.total φ) (fun x => ¬φ x)).le w v ↔
    (φ v → φ w) ∧ (¬φ v → ¬φ w) := by
  rw [Normality.refine_le, Normality.refine_le]
  exact ⟨fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨trivial, h1⟩, h2⟩⟩

/-- The conflicting-default ordering is equivalent to p-agreement:
    w is at most as normal as v iff they agree on p. -/
theorem conflicting_defaults_iff_agree (φ : W → Prop) [DecidablePred φ]
    (w v : W) :
    (Normality.refine (Normality.refine Normality.total φ) (fun x => ¬φ x)).le w v ↔
    (φ w ↔ φ v) := by
  rw [conflicting_defaults_le]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨fun hw => by_contra (fun hv => h2 hv hw), h1⟩
  · intro ⟨h1, h2⟩
    exact ⟨h2, fun hv hw => hv (h1 hw)⟩


-- ═══ Compatible Defaults ═══

/-- When two defaults are compatible (p implies q), processing both in
    sequence makes p-worlds optimal: the expectations reinforce rather
    than conflict. -/
theorem compatible_defaults_optimal (φ ψ : W → Prop) (d : Set W)
    (hφψ : ∀ w, φ w → ψ w) (hex : ∃ w ∈ d, φ w) :
    Normality.optimal (Normality.refine (Normality.refine Normality.total ψ) φ) d ⊆
      { w ∈ d | φ w } := by
  intro w hw
  rw [Normality.mem_optimal] at hw
  obtain ⟨hwd, hopt⟩ := hw
  obtain ⟨v, hvd, hφv⟩ := hex
  refine ⟨hwd, ?_⟩
  by_contra hnφw
  have hψv : ψ v := hφψ v hφv
  have hle : (Normality.refine (Normality.refine Normality.total ψ) φ).le v w :=
    Normality.refine_le.mpr ⟨Normality.refine_le.mpr ⟨trivial, fun _ => hψv⟩,
      fun h => absurd h hnφw⟩
  exact hnφw ((Normality.refine_le.mp (hopt hvd hle)).2 hφv)


end UpdateSemantics.Default
