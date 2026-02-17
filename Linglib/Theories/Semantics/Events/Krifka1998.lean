/-
# Krifka (1998) "The Origins of Telicity"

Krifka's foundational linking theory explaining *why* incremental-theme
verbs transmit mereological properties from the NP to the VP. The core
result: a hierarchy of thematic role properties (UP, ME, MSE, UE, MO,
MSO, UO) combining into **strict incrementality (SINC)**, plus the
**telicity-through-quantization** theorems.

## Key results

- **CUM propagation** (§3.3): CumTheta(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ)
  "eat apples" is CUM because APPLES is CUM and EAT's θ is cumulative.

- **QUA propagation** (§3.3): SINC(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ)
  "eat two apples" is QUA because TWO-APPLES is QUA and EAT's θ is SINC.

## Sections

1. Thematic Role Properties (§3.2, eq. 43–52)
2. Strict Incrementality (§3.2, eq. 51)
3. Derived Properties (SINC → UP, ME, MO, CumTheta)
4. VP Formation (§3.3, eq. 53)
5. Telicity Theorems (§3.3) — THE PAYOFF
6. GRAD: Gradual Change (Krifka 1989)
7. Verb Annotations (Meaning Postulates)
8. General Incrementality (§3.6, eq. 59)
9. Bridge Theorems

Note: Overlap, ExtMeasure, and extMeasure_qua are in Mereology.lean (§10).

## References

- Krifka, M. (1998). The origins of telicity. In S. Rothstein (ed.),
  *Events and Grammar*, 197–235. Kluwer.
- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
- Champollion, L. (2017). *Parts of a Whole*. OUP.
-/

import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Events.StratifiedReference
import Mathlib.Tactic.Linarith

namespace Semantics.Events.Krifka1998

open Semantics.Events
open Semantics.Events.Mereology
open Core.Time
open Semantics.Lexical.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Thematic Role Properties (§3.2, eq. 43–52)
-- ════════════════════════════════════════════════════

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- Uniqueness of Participant (UP): each event has at most one θ-filler.
    Krifka (1998) eq. (43): θ(x,e) ∧ θ(y,e) → x = y. -/
def UP (θ : α → β → Prop) : Prop :=
  ∀ (x y : α) (e : β), θ x e → θ y e → x = y

/-- Cumulative theta (CumTheta): θ preserves sums.
    Krifka (1998) eq. (44): θ(x,e) ∧ θ(y,e') → θ(x⊕y, e⊕e').
    This is the relational analog of IsSumHom. -/
def CumTheta (θ : α → β → Prop) : Prop :=
  ∀ (x y : α) (e e' : β), θ x e → θ y e' → θ (x ⊔ y) (e ⊔ e')

/-- Mapping to Events (ME): object parts map to event parts.
    Krifka (1998) eq. (45): θ(x,e) ∧ y ≤ x → ∃e'. e' ≤ e ∧ θ(y,e'). -/
def ME (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y : α), θ x e → y ≤ x → ∃ e', e' ≤ e ∧ θ y e'

/-- Mapping to Strict subEvents (MSE): proper object parts map to proper subevents.
    Krifka (1998) eq. (46): θ(x,e) ∧ y < x → ∃e'. e' < e ∧ θ(y,e'). -/
def MSE (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y : α), θ x e → y < x → ∃ e', e' < e ∧ θ y e'

/-- Uniqueness of Events (UE): each object part maps to a unique event part.
    Krifka (1998) eq. (47): θ(x,e) ∧ y ≤ x → ∃!e'. e' ≤ e ∧ θ(y,e'). -/
def UE (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y : α), θ x e → y ≤ x →
    ∃ e', e' ≤ e ∧ θ y e' ∧ ∀ e'', e'' ≤ e → θ y e'' → e'' = e'

/-- Mapping to Objects (MO): event parts map to object parts.
    Krifka (1998) eq. (48): θ(x,e) ∧ e' ≤ e → ∃y. y ≤ x ∧ θ(y,e'). -/
def MO (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (e' : β), θ x e → e' ≤ e → ∃ y, y ≤ x ∧ θ y e'

/-- Mapping to Strict subObjects (MSO): proper subevents map to proper object parts.
    Krifka (1998) eq. (49): θ(x,e) ∧ e' < e → ∃y. y < x ∧ θ(y,e'). -/
def MSO (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (e' : β), θ x e → e' < e → ∃ y, y < x ∧ θ y e'

/-- Uniqueness of Objects (UO): each event part maps to a unique object part.
    Krifka (1998) eq. (50): θ(x,e) ∧ e' ≤ e → ∃!y. y ≤ x ∧ θ(y,e'). -/
def UO (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (e' : β), θ x e → e' ≤ e →
    ∃ y, y ≤ x ∧ θ y e' ∧ ∀ z, z ≤ x → θ z e' → z = y

/-- Generalized Uniqueness of Events (GUE): each object participates in
    at most one event.
    Krifka (1998) eq. (52): θ(x,e) ∧ θ(x,e') → e = e'. -/
def GUE (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e e' : β), θ x e → θ x e' → e = e'

-- ════════════════════════════════════════════════════
-- § 2. Strict Incrementality (§3.2, eq. 51)
-- ════════════════════════════════════════════════════

/-- Strict Incrementality (SINC): the conjunction of MSO, UO, MSE, UE
    plus a non-degeneracy condition requiring extended entities.
    Krifka (1998) eq. (51):

    SINC(θ) iff
      (i)  MSO(θ) ∧ UO(θ) ∧ MSE(θ) ∧ UE(θ)
      (ii) ∃x,y∈U_P ∃e,e'∈U_E [y < x ∧ e' < e ∧ θ(x,e) ∧ θ(y,e')]

    Condition (i) guarantees a bijective correspondence between the part
    structure of the object and the part structure of the event.
    Condition (ii) ensures θ actually applies to extended entities (ones
    with proper parts), ruling out degenerate cases where θ only relates
    atoms. This is the key property of incremental-theme verbs like
    "eat", "build", "read". -/
structure SINC (θ : α → β → Prop) : Prop where
  /-- Proper subevents map to proper object parts. -/
  mso : MSO θ
  /-- Each event part has a unique object counterpart. -/
  uo  : UO θ
  /-- Proper object parts map to proper subevents. -/
  mse : MSE θ
  /-- Each object part has a unique event counterpart. -/
  ue  : UE θ
  /-- Non-degeneracy: θ applies to at least one extended entity pair.
      Krifka (1998) eq. (51.ii): the relation must involve entities with
      proper parts, not just atoms. -/
  extended : ∃ (x y : α) (e e' : β), y < x ∧ e' < e ∧ θ x e ∧ θ y e'

-- ════════════════════════════════════════════════════
-- § 3. Derived Properties
-- ════════════════════════════════════════════════════

-- Note on UP vs UO + GUE: Krifka (1998) lists UP (eq. 43) as a
-- separate property from the SINC components. UO is relativized to
-- an outer (x,e) pair, so two independent fillers x,y of the same
-- event e aren't directly connected by UO's uniqueness clause.
-- UP must be assumed separately where needed (e.g., in `qua_propagation`).

/-- MSE implies ME: weaken strict to non-strict.
    Krifka (1998): if proper parts map to proper subevents, then
    parts (including the whole) also map, taking e' = e when y = x. -/
theorem me_of_mse {θ : α → β → Prop} (h : MSE θ) : ME θ := by
  intro x e y hθ hle
  by_cases heq : y = x
  · exact ⟨e, le_rfl, heq ▸ hθ⟩
  · have hlt : y < x := lt_of_le_of_ne hle heq
    obtain ⟨e', hlt', hθ'⟩ := h x e y hθ hlt
    exact ⟨e', le_of_lt hlt', hθ'⟩

/-- MSO implies MO: weaken strict to non-strict (dual of me_of_mse). -/
theorem mo_of_mso {θ : α → β → Prop} (h : MSO θ) : MO θ := by
  intro x e e' hθ hle
  by_cases heq : e' = e
  · exact ⟨x, le_rfl, heq ▸ hθ⟩
  · have hlt : e' < e := lt_of_le_of_ne hle heq
    obtain ⟨y, hlt', hθ'⟩ := h x e e' hθ hlt
    exact ⟨y, le_of_lt hlt', hθ'⟩

/-- SINC implies ME (via MSE). -/
theorem me_of_sinc {θ : α → β → Prop} (h : SINC θ) : ME θ :=
  me_of_mse h.mse

/-- SINC implies MO (via MSO). -/
theorem mo_of_sinc {θ : α → β → Prop} (h : SINC θ) : MO θ :=
  mo_of_mso h.mso

-- In CEM models, SINC implies CumTheta: the bijection between object
-- parts and event parts extends to sums. However, CumTheta does not
-- follow from SINC in arbitrary join semilattices (it requires CEM
-- complementation to decompose sums). Following Krifka (1998), who
-- lists CumTheta (eq. 44) as a separate property from SINC (eq. 51),
-- we require CumTheta as a separate hypothesis where needed (see
-- `sinc_cum_propagation`).

-- ════════════════════════════════════════════════════
-- § 4. VP Formation (§3.3, eq. 53)
-- ════════════════════════════════════════════════════

/-- VP predicate formed by existential closure over the object argument.
    Krifka (1998) eq. (53): VP_θ,OBJ = λe.∃y[OBJ(y) ∧ θ(y,e)].
    "eat apples" = λe.∃y[apples(y) ∧ eat.theme(y,e)]. -/
def VP (θ : α → β → Prop) (OBJ : α → Prop) : β → Prop :=
  fun e => ∃ y, OBJ y ∧ θ y e

-- ════════════════════════════════════════════════════
-- § 5. Telicity Theorems (§3.3) — THE PAYOFF
-- ════════════════════════════════════════════════════

/-- **CUM propagation**: cumulative θ transmits CUM from NP to VP.
    Krifka (1998) §3.3: CumTheta(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ).

    "eat apples" is CUM because:
    - APPLES is CUM (mass/bare-plural NPs are cumulative)
    - EAT's incremental theme is cumulative (CumTheta)
    - Therefore VP = λe.∃y[apples(y) ∧ eat(y,e)] is CUM

    Proof: Given VP(e₁) and VP(e₂), we have y₁ with OBJ(y₁) ∧ θ(y₁,e₁)
    and y₂ with OBJ(y₂) ∧ θ(y₂,e₂). By CumTheta, θ(y₁⊔y₂, e₁⊔e₂).
    By CUM(OBJ), OBJ(y₁⊔y₂). So VP(e₁⊔e₂). -/
theorem cum_propagation {θ : α → β → Prop} {OBJ : α → Prop}
    (hCum : CumTheta θ) (hObj : CUM OBJ) :
    CUM (VP θ OBJ) := by
  intro e₁ e₂ ⟨y₁, hobj₁, hθ₁⟩ ⟨y₂, hobj₂, hθ₂⟩
  exact ⟨y₁ ⊔ y₂, hObj y₁ y₂ hobj₁ hobj₂, hCum y₁ y₂ e₁ e₂ hθ₁ hθ₂⟩

/-- **QUA propagation**: UP + MSO + UO transmit QUA from NP to VP.
    Krifka (1998) §3.3: UP(θ) ∧ MSO(θ) ∧ UO(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ).

    "eat two apples" is QUA because:
    - TWO-APPLES is QUA (quantized NPs have no P-proper-parts)
    - EAT's incremental theme is SINC + UP
    - Therefore VP = λe.∃y[two-apples(y) ∧ eat(y,e)] is QUA

    Proof: Suppose VP(e) via ⟨y, OBJ(y), θ(y,e)⟩ and e' < e.
    We must show ¬VP(e'). Suppose for contradiction VP(e') via
    ⟨z, OBJ(z), θ(z,e')⟩. By UP, z = y' for any other filler of e'.
    By MSO, ∃ y' < y with θ(y',e'). By UP, z = y'.
    So OBJ(y') with y' < y. But QUA(OBJ) says ¬OBJ(y'). Contradiction.

    **Functional case**: When θ is a function (not a relation) with
    `IsSumHom` + `Function.Injective`, this reduces to
    `qua_of_injective_sumHom` in `Core/Dimension.lean` via
    `qua_pullback`. The relational UP + MSO conditions collapse to
    functional injectivity + monotonicity. -/
theorem qua_propagation {θ : α → β → Prop} {OBJ : α → Prop}
    (hUP : UP θ) (hMSO : MSO θ) (hQua : QUA OBJ) :
    QUA (VP θ OBJ) := by
  intro e e' ⟨y, hobj, hθ⟩ hlt ⟨z, hobj_z, hθ_z⟩
  -- By MSO: θ(y,e) and e' < e give ∃ y', y' < y ∧ θ(y',e')
  obtain ⟨y', hy'_lt, hθ_y'⟩ := hMSO y e e' hθ hlt
  -- By UP: θ(z,e') and θ(y',e') give z = y'
  have hz_eq : z = y' := hUP z y' e' hθ_z hθ_y'
  -- So OBJ(z) = OBJ(y'), but y' < y and QUA(OBJ) gives ¬OBJ(y')
  exact hQua y y' hobj hy'_lt (hz_eq ▸ hobj_z)

/-- QUA propagation from SINC + UP (convenience wrapper).
    In practice, incremental-theme verbs satisfy both SINC and UP. -/
theorem qua_propagation_sinc {θ : α → β → Prop} {OBJ : α → Prop}
    (hUP : UP θ) (hSinc : SINC θ) (hQua : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_propagation hUP hSinc.mso hQua

-- ════════════════════════════════════════════════════
-- § 6. GRAD: Gradual Change (Krifka 1989)
-- ════════════════════════════════════════════════════

/-- Graduality (GRAD): more object measure entails more event measure.
    Krifka (1989): GRAD(θ, μ_obj, μ_ev) ⇔ ∀x,y,e,e'. θ(x,e) ∧ θ(y,e') ∧
    μ_obj(x) < μ_obj(y) → μ_ev(e) < μ_ev(e').
    GRAD captures the intuition that eating more food takes more time. -/
def GRAD (θ : α → β → Prop) (μ_obj : α → ℚ) (μ_ev : β → ℚ) : Prop :=
  ∀ (x y : α) (e e' : β), θ x e → θ y e' →
    μ_obj x < μ_obj y → μ_ev e < μ_ev e'

/-- Measure proportionality: the SINC bijection preserves measure up to
    a constant factor. For any θ-pair (x,e), the event measure equals
    some constant c times the object measure: μ_ev(e) = c * μ_obj(x).

    This axiom captures the idealized "constant rate" of incremental-theme
    verbs: eating twice as much food takes twice as long. SINC alone
    constrains the part structure *within* a single (x,e) pair but says
    nothing about how measures relate *across* independent pairs.
    MeasureProportional bridges that gap.

    Krifka (1989) implicitly assumes this when deriving GRAD from SINC
    + extensive measures. -/
structure MeasureProportional {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (θ : α → β → Prop) (μ_obj : α → ℚ) (μ_ev : β → ℚ) where
  /-- The proportionality constant (rate). -/
  rate : ℚ
  /-- The rate is positive. -/
  rate_pos : 0 < rate
  /-- For any θ-pair, event measure = rate × object measure. -/
  proportional : ∀ (x : α) (e : β), θ x e → μ_ev e = rate * μ_obj x

/-- SINC + extensive measures + measure proportionality → GRAD.
    Krifka (1989): strictly incremental themes with extensive measures
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
-- § 7. Verb Annotations (Meaning Postulates)
-- ════════════════════════════════════════════════════

/-- Incrementality annotations for verbs.
    Krifka (1998) §3.2–3.7: verbs differ in which thematic role properties
    their incremental theme satisfies. -/
inductive VerbIncClass where
  /-- Strictly incremental: consumption/creation verbs (eat, build).
      SINC + GUE on object role. Krifka §3.3. -/
  | sinc
  /-- Incremental: allows backups (read, write).
      INC but ¬SINC on object role. Krifka §3.6. -/
  | inc
  /-- Cumulative only: non-incremental (push, carry).
      CumTheta but ¬MSE on object role. Krifka §3.2. -/
  | cumOnly
  deriving DecidableEq, Repr, BEq

/-- Meaning postulates for verb incrementality.
    These axiomatize which verbs have which incrementality properties
    on their object/theme role. -/
class VerbIncrementality (α β : Type*) [SemilatticeSup α] [SemilatticeSup β]
    (eat push build read_ : α → β → Prop) where
  /-- "eat" has a strictly incremental theme: consumption creates a
      bijection between food parts and eating subevents. -/
  eat_sinc : SINC eat
  /-- "eat" satisfies GUE: each portion of food is eaten at most once. -/
  eat_gue : GUE eat
  /-- "push" is cumulative but not strictly incremental:
      the cart doesn't have parts that correspond to pushing subevents. -/
  push_cum : CumTheta push
  /-- "build" has a strictly incremental theme: creation mirrors consumption. -/
  build_sinc : SINC build
  /-- "build" satisfies GUE: each part is built at most once. -/
  build_gue : GUE build
  /-- "read" is incremental but not strictly so: allows re-reading. -/
  read_cum : CumTheta read_

-- ════════════════════════════════════════════════════
-- § 8. General Incrementality (§3.6, eq. 59)
-- ════════════════════════════════════════════════════

/-- General Incrementality (INC): θ is the closure of some strictly
    incremental θ' under sum formation.
    Krifka (1998) eq. (59): θ is incremental iff there exists a SINC θ'
    such that θ(x,e) holds iff (x,e) can be decomposed into θ'-pairs
    that sum to (x,e). This handles "read the article" (allows
    re-reading/backups): reading events are built from strictly
    incremental reading-parts that can overlap in their object coverage.

    Formulated inductively: the smallest relation containing θ' and
    closed under componentwise sum. -/
inductive IncClosure (θ' : α → β → Prop) : α → β → Prop where
  /-- Base: anything in θ' is in the closure. -/
  | base {x : α} {e : β} : θ' x e → IncClosure θ' x e
  /-- Sum: if (x₁,e₁) and (x₂,e₂) are in the closure, so is (x₁⊔x₂, e₁⊔e₂). -/
  | sum {x₁ x₂ : α} {e₁ e₂ : β} :
      IncClosure θ' x₁ e₁ → IncClosure θ' x₂ e₂ →
      IncClosure θ' (x₁ ⊔ x₂) (e₁ ⊔ e₂)

/-- General Incrementality: θ is the IncClosure of some SINC θ'. -/
def INC (θ : α → β → Prop) : Prop :=
  ∃ θ' : α → β → Prop, SINC θ' ∧ ∀ (x : α) (e : β), θ x e ↔ IncClosure θ' x e

/-- SINC + CumTheta implies INC: a strictly incremental θ that is
    cumulative is trivially its own closure. CumTheta ensures the
    reverse direction: IncClosure θ ⊆ θ. -/
theorem inc_of_sinc {θ : α → β → Prop} (h : SINC θ) (hCum : CumTheta θ) : INC θ := by
  exact ⟨θ, h, fun x e => ⟨fun hθ => IncClosure.base hθ, by
    intro hcl
    induction hcl with
    | base h => exact h
    | sum _ _ ih₁ ih₂ => exact hCum _ _ _ _ ih₁ ih₂⟩⟩

-- ════════════════════════════════════════════════════
-- § 9. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- Bridge: CUM propagation via CumTheta + CUM(OBJ).
    CumTheta(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ).
    In CEM models, SINC implies CumTheta, so this covers the
    "SINC verb + CUM noun → CUM VP" case from Krifka (1998) §3.3. -/
theorem sinc_cum_propagation {θ : α → β → Prop} {OBJ : α → Prop}
    (hCumTheta : CumTheta θ) (hObj : CUM OBJ) :
    CUM (VP θ OBJ) :=
  cum_propagation hCumTheta hObj

/-- Bridge: QUA propagation from SINC + UP (renamed for API). -/
theorem sinc_qua_propagation {θ : α → β → Prop} {OBJ : α → Prop}
    (hUP : UP θ) (hSinc : SINC θ) (hQua : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_propagation hUP hSinc.mso hQua

/-- Bridge: RoleHom (functional θ from Mereology.lean) implies CumTheta
    (relational θ). A sum-homomorphic function θ : β → α induces a
    cumulative relation λ x e, θ(e) = x.

    With injectivity, we additionally get `StrictMono` via
    `IsSumHom.strictMono_of_injective` (Core/Dimension.lean §6),
    which enables `qua_of_injective_sumHom` — the functional
    QUA propagation theorem. -/
theorem roleHom_implies_cumTheta
    {f : β → α} (hf : IsSumHom f) :
    CumTheta (fun (x : α) (e : β) => f e = x) := by
  intro x y e e' hx hy
  rw [← hx, ← hy]
  exact hf.map_sup e e'

end Semantics.Events.Krifka1998
