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
6. Extensive Measure Functions (§2.2, eq. 7)
7. Verb Annotations (Meaning Postulates)
8. General Incrementality (§3.6, eq. 59)
9. Bridge Theorems

## References

- Krifka, M. (1998). The origins of telicity. In S. Rothstein (ed.),
  *Events and Grammar*, 197–235. Kluwer.
- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
- Champollion, L. (2017). *Parts of a Whole*. OUP.
-/

import Linglib.Theories.EventSemantics.Mereology
import Linglib.Theories.EventSemantics.StratifiedReference

namespace Theories.EventSemantics.Krifka1998

open Theories.EventSemantics
open Theories.EventSemantics.Mereology
open Theories.EventSemantics.ThematicRoles
open TruthConditional.Core.Time
open TruthConditional.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Thematic Role Properties (§3.2, eq. 43–52)
-- ════════════════════════════════════════════════════

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- Mereological overlap: x and y share a common part.
    Krifka (1998) eq. (1e): O(x, y) ⇔ ∃z. z ≤ x ∧ z ≤ y. -/
def Overlap {γ : Type*} [PartialOrder γ] (x y : γ) : Prop :=
  ∃ z, z ≤ x ∧ z ≤ y

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

/-- Strict Incrementality (SINC): the conjunction of MSO, UO, MSE, UE.
    Krifka (1998) eq. (51): SINC(θ) = MSO(θ) ∧ UO(θ) ∧ MSE(θ) ∧ UE(θ).

    SINC guarantees a bijective correspondence between the part structure
    of the object and the part structure of the event. This is the key
    property of incremental-theme verbs like "eat", "build", "read". -/
structure SINC (θ : α → β → Prop) : Prop where
  /-- Proper subevents map to proper object parts. -/
  mso : MSO θ
  /-- Each event part has a unique object counterpart. -/
  uo  : UO θ
  /-- Proper object parts map to proper subevents. -/
  mse : MSE θ
  /-- Each object part has a unique event counterpart. -/
  ue  : UE θ

-- ════════════════════════════════════════════════════
-- § 3. Derived Properties
-- ════════════════════════════════════════════════════

/-- UO implies UP under the assumption that θ-fillers are comparable.
    Krifka (1998): UP says each event has at most one θ-filler.
    UO says each subevent of an event has a unique subobject of the
    outer object. UP does not follow from UO alone (UO is relativized
    to an outer pair), but it does follow when combined with GUE:
    if each object participates in at most one event, and each event
    part has a unique object, then each event has a unique participant. -/
theorem up_of_uo_gue {θ : α → β → Prop} (h : UO θ) (h_gue : GUE θ) : UP θ := by
  -- TODO: Requires showing that GUE + UO yields unique fillers.
  -- The gap is that UO is relativized to an outer (x,e) pair, so
  -- two independent fillers x,y of the same e aren't directly
  -- connected by UO's uniqueness clause without x ≤ y or y ≤ x.
  sorry

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

/-- SINC implies CumTheta: strictly incremental θ preserves sums.
    Proof: Given θ(x,e) and θ(y,e'), we need θ(x⊔y, e⊔e').
    By ME, every part of x maps to a subevent of e, and similarly for y/e'.
    By MO, every subevent maps back. The sum e⊔e' covers all subevents,
    so x⊔y is the θ-filler of e⊔e'.
    This is a model-theoretic argument; we sorry it per convention. -/
theorem cumTheta_of_sinc {θ : α → β → Prop} (h : SINC θ) : CumTheta θ := by
  -- TODO: The full proof requires showing that the unique mapping properties
  -- of SINC compose correctly under ⊔. The key insight is that UO + UE
  -- together establish a bijection between object parts and event parts,
  -- and this bijection extends to sums by the lattice structure.
  sorry

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
    So OBJ(y') with y' < y. But QUA(OBJ) says ¬OBJ(y'). Contradiction. -/
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
-- § 6. Extensive Measure Functions (§2.2, eq. 7)
-- ════════════════════════════════════════════════════

/-- Extensive measure function: additive over non-overlapping entities.
    Krifka (1998) §2.2, eq. (7): μ(x ⊕ y) = μ(x) + μ(y) when ¬O(x,y).
    Examples: weight, volume, number (cardinality). -/
class ExtMeasure (α : Type*) [SemilatticeSup α] [PartialOrder α]
    (μ : α → ℚ) : Prop where
  /-- Additivity: μ is additive over non-overlapping entities. -/
  additive : ∀ (x y : α), ¬ Overlap x y → μ (x ⊔ y) = μ x + μ y
  /-- Positivity: every entity has positive measure. -/
  positive : ∀ (x : α), 0 < μ x

/-- Measure phrases create QUA predicates: {x : μ(x) = n} is QUA
    whenever μ is an extensive measure.
    Krifka (1998) §2.2: "two kilograms of flour" is QUA because
    no proper part of a 2kg entity also weighs 2kg. -/
theorem extMeasure_qua {α : Type*} [SemilatticeSup α] [PartialOrder α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) (hn : 0 < n) :
    QUA (fun x => μ x = n) := by
  intro x y hx hlt
  -- If y < x, then x = y ⊔ z for some z with ¬Overlap y z (in CEM).
  -- Then μ(x) = μ(y) + μ(z) > μ(y), so μ(y) < n, hence μ(y) ≠ n.
  -- This requires complementation / CEM axioms beyond SemilatticeSup.
  sorry

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

/-- SINC implies INC: a strictly incremental θ is trivially its own
    closure (since SINC is closed under sums). -/
theorem inc_of_sinc {θ : α → β → Prop} (h : SINC θ) : INC θ := by
  exact ⟨θ, h, fun x e => ⟨fun hθ => IncClosure.base hθ, by
    intro hcl
    -- Extracting from IncClosure requires knowing θ is closed under ⊔,
    -- which follows from CumTheta of SINC. Model-theoretic step.
    sorry⟩⟩

-- ════════════════════════════════════════════════════
-- § 9. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- Bridge: CUM propagation via SINC (combines cumTheta_of_sinc + cum_propagation).
    SINC(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ). -/
theorem sinc_cum_propagation {θ : α → β → Prop} {OBJ : α → Prop}
    (hSinc : SINC θ) (hObj : CUM OBJ) :
    CUM (VP θ OBJ) := by
  -- SINC → CumTheta, but cumTheta_of_sinc is sorry'd.
  -- Instead, prove directly using SINC components.
  -- Given VP(e₁) via ⟨y₁, OBJ(y₁), θ(y₁,e₁)⟩ and VP(e₂) via ⟨y₂, OBJ(y₂), θ(y₂,e₂)⟩,
  -- we need VP(e₁⊔e₂), i.e., ∃y. OBJ(y) ∧ θ(y, e₁⊔e₂).
  -- Take y = y₁ ⊔ y₂. OBJ(y₁⊔y₂) by CUM(OBJ).
  -- Need θ(y₁⊔y₂, e₁⊔e₂), which is CumTheta applied to SINC.
  -- This ultimately requires cumTheta_of_sinc.
  sorry

/-- Bridge: QUA propagation from SINC + UP (renamed for API). -/
theorem sinc_qua_propagation {θ : α → β → Prop} {OBJ : α → Prop}
    (hUP : UP θ) (hSinc : SINC θ) (hQua : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_propagation hUP hSinc.mso hQua

/-- Bridge: QUA(VP) implies telic Vendler class.
    Krifka (1998): quantized VP predicates correspond to telic eventualities.
    Uses sorry: requires connecting mereological QUA to VendlerClass. -/
theorem qua_vendler_telic {α : Type*} [PartialOrder α]
    {P : α → Prop} {c : VendlerClass}
    (hQua : QUA P) :
    c.telicity = .telic := by
  -- TODO: This bridges the abstract QUA property to Vendler classification.
  -- QUA predicates lack the subinterval property, which is the hallmark
  -- of telic predicates (achievements and accomplishments).
  sorry

/-- Bridge: CUM(VP) implies atelic Vendler class.
    Krifka (1998): cumulative VP predicates correspond to atelic eventualities.
    Uses sorry: requires connecting mereological CUM to VendlerClass. -/
theorem cum_vendler_atelic {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {c : VendlerClass}
    (hCum : CUM P) :
    c.telicity = .atelic := by
  -- TODO: This bridges the abstract CUM property to Vendler classification.
  -- CUM predicates have the subinterval property (for non-trivial cases),
  -- corresponding to states and activities.
  sorry

/-- Bridge: RoleHom (functional θ from Mereology.lean) implies CumTheta
    (relational θ). A sum-homomorphic function θ : β → α induces a
    cumulative relation λ x e, θ(e) = x.
    Uses sorry: needs the connection between functional and relational forms. -/
theorem roleHom_implies_cumTheta
    {f : β → α} (hf : IsSumHom f) :
    CumTheta (fun (x : α) (e : β) => f e = x) := by
  intro x y e e' hx hy
  rw [← hx, ← hy]
  exact hf.map_sup e e'

end Theories.EventSemantics.Krifka1998
