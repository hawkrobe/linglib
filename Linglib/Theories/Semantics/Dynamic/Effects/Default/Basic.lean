import Linglib.Core.Order.Normality
import Linglib.Theories.Semantics.Dynamic.Core.CCP

/-!
# Default Reasoning in Update Semantics

@cite{veltman-1996}

Veltman (1996) extends update semantics with **expectation patterns** —
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
- "Normally" is idempotent and commutative (`normallyUpdate_idempotent`, `normallyUpdate_comm`)

## What's not here (§4–5)

Veltman's §4 — which he calls "the heart of the paper" — introduces
**expectation frames** for conditional defaults: "if φ then normally ψ"
(written φ ⇝ ψ). This enables specificity, the full Nixon Diamond,
and the Tweety Triangle. §5 proves which inference patterns are valid
for the default conditional (contraposition fails, cautious monotonicity
holds, etc.). These require substantially more infrastructure and are
left for future work.

## Connection to existing infrastructure

- **CCP.lean**: Veltman's base language (§2) — CCPs, tests, might as
  consistency test — is already formalized there. This module adds the
  default layer (§3).

- **BeliefRevision.lean**: `PreferentialConsequence` (System P) and
  `PlausibilityOrder` formalize the *static* characterization of default
  reasoning. Veltman's system is the *dynamic* realization: the default
  consequence relation it induces validates System P.

- **Core/Order/Normality.lean**: The `NormalityOrder` type and `refine`
  operation are defined there as shared infrastructure. This module
  builds `ExpState` (expectation states) on top of that.

## References

- Veltman, F. (1996). Defaults in update semantics. *Journal of
  Philosophical Logic* 25(3), 221-261.
-/

namespace Semantics.Dynamic.Default

open Core.Order (NormalityOrder)

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
  order : NormalityOrder W

/-- The initial expectation state: all worlds are possible and equally
    normal. No information, no expectations. -/
def ExpState.init : ExpState W where
  info := Set.univ
  order := NormalityOrder.total

/-- Optimal worlds in the current state: the most normal worlds
    among those compatible with the discourse. -/
def ExpState.optimal (σ : ExpState W) : Set W :=
  σ.order.optimal σ.info


-- ═══ Update Operations ═══

/-- **Assertion update**: eliminate non-p-worlds, preserve pattern.

    This is the standard eliminative update from CCP.lean, lifted to
    expectation states. Information grows; expectations are unchanged. -/
def assertUpdate (φ : W → Prop) (σ : ExpState W) : ExpState W :=
  ⟨{ w ∈ σ.info | φ w }, σ.order⟩

/-- **"Normally p"**: refine the pattern so p-worlds are preferred.
    The information state is unchanged — we don't learn that p is true,
    only that p is *expected*.

    This is the core innovation of Veltman (1996): defaults operate on
    the expectation pattern, not on the information state. -/
def normallyUpdate (φ : W → Prop) (σ : ExpState W) : ExpState W :=
  ⟨σ.info, σ.order.refine φ⟩

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

/-- Assertion preserves the normality ordering. -/
theorem assertUpdate_preserves_order (φ : W → Prop) (σ : ExpState W) :
    (assertUpdate φ σ).order = σ.order := rfl

/-- "Normally" preserves the information state. -/
theorem normallyUpdate_preserves_info (φ : W → Prop) (σ : ExpState W) :
    (normallyUpdate φ σ).info = σ.info := rfl

/-- Assertion is eliminative: it can only shrink the info state. -/
theorem assertUpdate_eliminative (φ : W → Prop) (σ : ExpState W) :
    (assertUpdate φ σ).info ⊆ σ.info := fun _ hw => hw.1

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
    φ-worlds (see `NormalityOrder.optimal_of_respects_connected`). -/
theorem presumably_passes (σ : ExpState W) (φ : W → Prop)
    (hresp : σ.order.respects φ) (hconn : σ.order.connected)
    (hex : ∃ w ∈ σ.info, φ w) :
    presumablyTest φ σ = σ := by
  simp only [presumablyTest]
  rw [if_pos]
  intro w hw
  exact (NormalityOrder.optimal_of_respects_connected σ.order φ σ.info
    hresp hconn hex hw).2

/-- **The central result**: after processing "normally p", the test
    "presumably p" passes — provided the information state has p-worlds.

    Corollary of `presumably_passes`: "normally p" creates respect,
    and a single refinement from total preserves connectedness. -/
theorem normally_presumably_succeeds (φ : W → Prop) (d : Set W)
    (hex : ∃ w ∈ d, φ w) :
    let σ : ExpState W := ⟨d, NormalityOrder.total⟩
    presumablyTest φ (normallyUpdate φ σ) = normallyUpdate φ σ := by
  simp only [presumablyTest, normallyUpdate, ExpState.optimal]
  rw [if_pos]
  intro w hw
  rw [NormalityOrder.refine_total_optimal φ d hex] at hw
  exact hw.2


-- ═══ Persistence ═══

/-- **Persistence under assertion**: if the ordering respects p
    (i.e., the state has accepted "normally p"), then asserting any
    q preserves this. Learning new facts does not undo expectations.

    Veltman (1996), Proposition 3.6(iv). -/
theorem persistence_assert (σ : ExpState W) (φ ψ : W → Prop)
    (h : σ.order.respects φ) :
    (assertUpdate ψ σ).order.respects φ := h

/-- **Persistence under further defaults**: if the ordering respects p,
    then processing "normally q" (for any q) preserves this. Later
    defaults do not undo earlier ones.

    Veltman (1996), Proposition 3.6(iv). -/
theorem persistence_normally (σ : ExpState W) (φ ψ : W → Prop)
    (h : σ.order.respects φ) :
    (normallyUpdate ψ σ).order.respects φ :=
  NormalityOrder.refine_preserves_respects σ.order φ ψ h

/-- After "normally p", the ordering respects p. Combined with
    persistence, this means "normally p" creates a permanent expectation. -/
theorem normally_creates_respect (σ : ExpState W) (φ : W → Prop) :
    (normallyUpdate φ σ).order.respects φ :=
  NormalityOrder.refine_respects σ.order φ


-- ═══ Idempotency and Commutativity ═══

/-- **Idempotency**: if the state already accepts "normally φ" (the
    ordering respects φ), then processing "normally φ" again is a no-op.

    Veltman (1996), Proposition 3.6(ii) at the state level. -/
theorem normallyUpdate_idempotent (σ : ExpState W) (φ : W → Prop)
    (h : σ.order.respects φ) :
    normallyUpdate φ σ = σ := by
  show ExpState.mk σ.info (σ.order.refine φ) = σ
  congr 1
  exact NormalityOrder.refine_of_respects σ.order φ h

/-- Corollary: "normally φ; normally φ" = "normally φ" from any state. -/
theorem normallyUpdate_normally_idempotent (σ : ExpState W) (φ : W → Prop) :
    normallyUpdate φ (normallyUpdate φ σ) = normallyUpdate φ σ :=
  normallyUpdate_idempotent _ φ (normally_creates_respect σ φ)

/-- **Commutativity**: the order of defaults doesn't matter.
    "Normally φ; normally ψ" = "normally ψ; normally φ". -/
theorem normallyUpdate_comm (σ : ExpState W) (φ ψ : W → Prop) :
    normallyUpdate ψ (normallyUpdate φ σ) = normallyUpdate φ (normallyUpdate ψ σ) := by
  show ExpState.mk σ.info ((σ.order.refine φ).refine ψ) =
       ExpState.mk σ.info ((σ.order.refine ψ).refine φ)
  congr 1
  exact NormalityOrder.refine_comm σ.order φ ψ


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
    (NormalityOrder.total.refine φ |>.refine (fun x => ¬φ x)).le w v ↔
    (φ v → φ w) ∧ (¬φ v → ¬φ w) := by
  show (True ∧ (φ v → φ w)) ∧ (¬φ v → ¬φ w) ↔ (φ v → φ w) ∧ (¬φ v → ¬φ w)
  exact ⟨fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨True.intro, h1⟩, h2⟩⟩

/-- The conflicting-default ordering is equivalent to p-agreement:
    w is at most as normal as v iff they agree on p. -/
theorem conflicting_defaults_iff_agree (φ : W → Prop) [DecidablePred φ]
    (w v : W) :
    (NormalityOrder.total.refine φ |>.refine (fun x => ¬φ x)).le w v ↔
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
    (NormalityOrder.total.refine ψ |>.refine φ).optimal d ⊆ { w ∈ d | φ w } := by
  intro w ⟨hwd, hopt⟩
  obtain ⟨v, hvd, hφv⟩ := hex
  refine ⟨hwd, ?_⟩
  by_contra hnφw
  have hψv : ψ v := hφψ v hφv
  have hle : (NormalityOrder.total.refine ψ |>.refine φ).le v w :=
    ⟨⟨True.intro, fun _ => hψv⟩, fun h => absurd h hnφw⟩
  exact hnφw ((hopt v hvd hle).2 hφv)


end Semantics.Dynamic.Default
