import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Events.Incrementality
import Linglib.Theories.Semantics.Events.MeasurePhrases
import Mathlib.Tactic.Linarith

/-!
# Gradual Change (GRAD) and the GRADSquare
@cite{krifka-1989} @cite{krifka-1998} @cite{kennedy-levin-2008}

GRAD: a thematic relation θ exhibits gradual change iff more object
measure entails more event measure. Captures the intuition that
eating more food takes more time, building more house takes more time,
etc. The GRADSquare extends `LaxMeasureSquare` with strict incrementality
to derive GRAD propositionally.

## Sections

1. `GRAD` definition (K89/K98)
2. `grad_of_sinc`: SINC + extensive measures + measure proportionality → GRAD
3. `GRADSquare` structure (SINC extension of `LaxMeasureSquare`)
4. GRADSquare lemmas (laxCommutativity, grad, objMereoDim, evMereoDim,
   qua_pullback_ev)

-/

namespace Semantics.Events.GradualChange

open Mereology
open Semantics.Events.Mereology
open Semantics.Events.Incrementality

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

-- ════════════════════════════════════════════════════
-- § 1. GRAD: Gradual Change (@cite{krifka-1989})
-- ════════════════════════════════════════════════════

/-- Graduality (GRAD): more object measure entails more event measure.
    @cite{krifka-1989}: GRAD(θ, μ_obj, μ_ev) ⇔ ∀x,y,e,e'. θ(x,e) ∧ θ(y,e') ∧
    μ_obj(x) < μ_obj(y) → μ_ev(e) < μ_ev(e').
    GRAD captures the intuition that eating more food takes more time. -/
def GRAD (θ : α → β → Prop) (μ_obj : α → ℚ) (μ_ev : β → ℚ) : Prop :=
  ∀ (x y : α) (e e' : β), θ x e → θ y e' →
    μ_obj x < μ_obj y → μ_ev e < μ_ev e'

/-- SINC + extensive measures + measure proportionality → GRAD.
    @cite{krifka-1989}: strictly incremental themes with extensive measures
    and a constant consumption rate exhibit gradual change.

    Proof: if μ_ev(e) = c · μ_obj(x) and μ_ev(e') = c · μ_obj(y),
    then μ_obj(x) < μ_obj(y) implies c · μ_obj(x) < c · μ_obj(y)
    since c > 0, giving μ_ev(e) < μ_ev(e'). -/
theorem grad_of_sinc {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    (θ : α → β → Prop) (μ_obj : α → ℚ) (μ_ev : β → ℚ)
    (_hSinc : SINC θ) [_hObj : ExtMeasure α μ_obj] [_hEv : ExtMeasure β μ_ev]
    (hProp : MeasureProportional θ μ_obj μ_ev) :
    GRAD θ μ_obj μ_ev := by
  intro x y e e' hθx hθy hlt
  rw [hProp.proportional x e hθx, hProp.proportional y e' hθy]
  have hrate := hProp.rate_pos
  linarith [mul_lt_mul_of_pos_left hlt hrate]

-- ════════════════════════════════════════════════════
-- § 2. GRAD Square: SINC Extension of LaxMeasureSquare
-- ════════════════════════════════════════════════════

/-- The GRAD square extends `LaxMeasureSquare` with strict incrementality
    (SINC), enabling the derivation of GRAD (gradual change). The non-SINC
    theorems (MereoDim, QUA pullback, lax commutativity) are inherited from
    `LaxMeasureSquare`. -/
structure GRADSquare {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    (θ : α → γ → Prop) (μ_obj : α → ℚ)
    (τ_fn : γ → β) (dur : β → ℚ)
    extends LaxMeasureSquare θ μ_obj τ_fn dur where
  /-- Strict incrementality of the thematic role. -/
  sinc : SINC θ

/-- The defining equation of the GRAD square: for any θ-pair (x,e),
    the temporal measure equals the rate times the object measure. -/
theorem GRADSquare.laxCommutativity {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {θ : α → γ → Prop} {μ_obj : α → ℚ}
    {τ_fn : γ → β} {dur : β → ℚ}
    (sq : GRADSquare θ μ_obj τ_fn dur)
    {x : α} {e : γ} (hθ : θ x e) :
    dur (τ_fn e) = sq.laxComm.rate * μ_obj x :=
  sq.toLaxMeasureSquare.laxCommutativity hθ

/-- GRAD follows from the square via `grad_of_sinc`. -/
theorem GRADSquare.grad {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {θ : α → γ → Prop} {μ_obj : α → ℚ}
    {τ_fn : γ → β} {dur : β → ℚ}
    (sq : GRADSquare θ μ_obj τ_fn dur) :
    GRAD θ μ_obj (dur ∘ τ_fn) := by
  haveI := sq.ext₁
  haveI := sq.ext₂
  exact grad_of_sinc θ μ_obj (dur ∘ τ_fn) sq.sinc sq.laxComm

/-- The object arm is a MereoDim (via ExtMeasure). -/
theorem GRADSquare.objMereoDim {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {θ : α → γ → Prop} {μ_obj : α → ℚ}
    {τ_fn : γ → β} {dur : β → ℚ}
    (sq : GRADSquare θ μ_obj τ_fn dur) :
    MereoDim μ_obj :=
  sq.toLaxMeasureSquare.mereoDim₁

/-- The temporal arm (composed path) is a MereoDim (via ExtMeasure). -/
theorem GRADSquare.evMereoDim {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {θ : α → γ → Prop} {μ_obj : α → ℚ}
    {τ_fn : γ → β} {dur : β → ℚ}
    (sq : GRADSquare θ μ_obj τ_fn dur) :
    MereoDim (dur ∘ τ_fn) :=
  sq.toLaxMeasureSquare.mereoDim₂

/-- QUA pullback through the temporal path: QUA on ℚ pulls back to
    QUA on events via the composed measure `dur ∘ τ_fn`. -/
theorem GRADSquare.qua_pullback_ev {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {θ : α → γ → Prop} {μ_obj : α → ℚ}
    {τ_fn : γ → β} {dur : β → ℚ}
    (sq : GRADSquare θ μ_obj τ_fn dur)
    {P : ℚ → Prop} (hP : QUA P) :
    QUA (P ∘ dur ∘ τ_fn) :=
  sq.toLaxMeasureSquare.qua_pullback₂ hP

-- ════════════════════════════════════════════════════
-- § 3. Krifka Event-Structure Instantiation
-- ════════════════════════════════════════════════════

/-! Specialization of `GRADSquare` to the canonical Krifka event
    structure: `Entity →θ Ev Time →runtime Interval Time →len ℚ`.
    Provides a constructor for `GRADSquare` from concrete extensivity
    + proportionality witnesses on the duration measure derived from
    runtime + interval-length. -/

open Semantics.Events.MeasurePhrases (durationMeasure)
open Core.Time

/-- `durationMeasure len = len ∘ (fun e => e.runtime)` by definition. -/
theorem durationMeasure_eq_comp {Time : Type*} [LinearOrder Time]
    (len : Interval Time → ℚ) :
    durationMeasure len = len ∘ (fun (e : Ev Time) => e.runtime) := rfl

/-- Constructor for the GRAD square in the Krifka event structure case:
    `Entity →θ Ev Time →runtime Interval Time →len ℚ`. -/
def krifkaGRADSquare
    {Entity Time : Type*}
    [SemilatticeSup Entity] [LinearOrder Time] [SemilatticeSup (Ev Time)]
    (θ : Entity → Ev Time → Prop) (μ_obj : Entity → ℚ) (len : Interval Time → ℚ)
    (hSinc : SINC θ) (hObjExt : ExtMeasure Entity μ_obj)
    (hEvExt : ExtMeasure (Ev Time) (durationMeasure len))
    (hProp : MeasureProportional θ μ_obj (durationMeasure len)) :
    GRADSquare θ μ_obj (fun e => e.runtime) len :=
  { laxComm := hProp
    ext₁ := hObjExt
    ext₂ := hEvExt
    sinc := hSinc }

/-- Named lax commutativity for the canonical case:
    `len(e.runtime) = rate * μ_obj(x)` for θ-pairs. -/
theorem krifka_lax_commutativity
    {Entity Time : Type*}
    [SemilatticeSup Entity] [LinearOrder Time] [SemilatticeSup (Ev Time)]
    {θ : Entity → Ev Time → Prop} {μ_obj : Entity → ℚ} {len : Interval Time → ℚ}
    (sq : GRADSquare θ μ_obj (fun e => e.runtime) len)
    {x : Entity} {e : Ev Time} (hθ : θ x e) :
    len e.runtime = sq.laxComm.rate * μ_obj x :=
  sq.laxCommutativity hθ

end Semantics.Events.GradualChange
