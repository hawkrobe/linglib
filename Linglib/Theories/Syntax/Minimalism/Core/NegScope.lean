import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic
import Linglib.Core.Negation
import Linglib.Theories.Semantics.Negation.CzechNegation
import Linglib.Theories.Semantics.Negation.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Negation Merge Position and Scope

Minimalist analysis of where negation merges in the extended projection
and how merge position determines EN type, EN strength, and polarity
licensing.

The central result: `NegMergePosition` determines both `ENType` and
`PolarityLicensing`. CP-area negation cannot scope into vP (phase
transferred), so it is non-truth-conditional (high EN) and cannot
license polarity-sensitive elements (strong EN). TP-area negation
retains vP scope, so it is truth-conditional (low EN) and retains
some polarity licensing (weak EN).

This is @cite{greco-2020}'s core theoretical claim, unified with
@cite{rett-2026}'s high/low EN distinction.
-/

namespace Minimalism.NegScope

open Minimalism (Cat fValue isCPArea)
open Core (ENType ENStrength PolarityLicensing PolarityClass
           weakENProfile strongENProfile)

-- ════════════════════════════════════════════════════
-- § 1. Neg merge position
-- ════════════════════════════════════════════════════

/-- Where a negation head is merged in the extended projection.

    Standard NegP is in the inflectional domain (F2, between v and C).
    In expletive negation, negation may merge in the CP layer (F3+),
    above the inflectional domain. The merge position determines scope,
    truth-conditionality, and polarity licensing.

    Compare `Semantics.Negation.CzechNegation.NegPosition`
    which classifies three LF positions (inner/medial/outer) for
    Czech negation. This type is coarser: TP subsumes both inner
    and medial positions. -/
inductive NegMergePosition where
  | tp   -- Inflectional domain (F0–F2): standard NegP
  | cp   -- Left periphery (F3+): CP-area negation
  deriving DecidableEq, Repr

/-- Whether a Neg head at this position can scope into the vP domain.

    Under PIC: vP complement is transferred when the CP-phase head is
    merged. TP-area Neg (F2) is merged before the phase head, so vP is
    still accessible. CP-area Neg is merged during/after the CP-phase,
    when vP complement has been transferred. -/
def NegMergePosition.scopesIntoVP : NegMergePosition → Bool
  | .tp => true    -- Merged before CP-phase head, vP still accessible
  | .cp => false   -- Merged with/after CP-phase head, vP transferred

-- ── NegMergePosition: Equiv, Fintype, LinearOrder ──

/-- NegMergePosition ≃ Bool: tp ↦ false, cp ↦ true.
    Aligned with the LinearOrder (tp < cp) and the ENType/ENStrength
    equivalences (low/weak ↦ false, high/strong ↦ true). -/
def NegMergePosition.equivBool : NegMergePosition ≃ Bool where
  toFun | .tp => false | .cp => true
  invFun | false => .tp | true => .cp
  left_inv p := by cases p <;> rfl
  right_inv b := by cases b <;> rfl

instance : Fintype NegMergePosition := Fintype.ofEquiv _ NegMergePosition.equivBool.symm

/-- Numeric embedding: tp ↦ 0, cp ↦ 1 (by f-value position). -/
def NegMergePosition.toNat : NegMergePosition → Nat
  | .tp => 0 | .cp => 1

instance : LinearOrder NegMergePosition :=
  LinearOrder.lift' NegMergePosition.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [NegMergePosition.toNat])

-- ════════════════════════════════════════════════════
-- § 2. Bridge: merge position → EN type
-- ════════════════════════════════════════════════════

/-- CP-area negation is non-truth-conditional (high EN).
    TP-area negation is truth-conditional (low EN). -/
def NegMergePosition.toENType : NegMergePosition → ENType
  | .tp => .low   -- Can scope → truth-conditional
  | .cp => .high  -- Cannot scope → non-truth-conditional

-- ════════════════════════════════════════════════════
-- § 3. Bridge: merge position → EN strength + polarity
-- ════════════════════════════════════════════════════

/-- Merge position determines EN strength. -/
def NegMergePosition.toENStrength : NegMergePosition → ENStrength
  | .tp => .weak
  | .cp => .strong

/-- Merge position determines polarity licensing profile.

    CP-area negation cannot create a downward-entailing context in vP
    (the vP phase complement has been transferred), so it cannot license
    any polarity-sensitive elements. TP-area negation retains scope into
    vP, preserving some licensing ability (weak NPIs, N-words).

    This is @cite{greco-2020}'s core theoretical claim: the weak/strong
    EN distinction reduces to where negation merges relative to the
    vP-phase boundary. -/
def NegMergePosition.polarityProfile : NegMergePosition → PolarityLicensing
  | .tp => weakENProfile
  | .cp => strongENProfile

-- ── Equiv chain: NegMergePosition ≃ ENType ≃ ENStrength ≃ Bool ──

/-- NegMergePosition ≃ ENType: tp ↦ low, cp ↦ high. -/
def NegMergePosition.equivENType : NegMergePosition ≃ ENType where
  toFun := NegMergePosition.toENType
  invFun | .low => .tp | .high => .cp
  left_inv p := by cases p <;> rfl
  right_inv t := by cases t <;> rfl

/-- NegMergePosition ≃ ENStrength: tp ↦ weak, cp ↦ strong. -/
def NegMergePosition.equivENStrength : NegMergePosition ≃ ENStrength where
  toFun := NegMergePosition.toENStrength
  invFun | .weak => .tp | .strong => .cp
  left_inv p := by cases p <;> rfl
  right_inv s := by cases s <;> rfl

/-- The Equiv chain factors through Bool:
    `toENType p = equivBool.symm (scopesIntoVP p)` pointwise. -/
theorem equiv_factors_entype (p : NegMergePosition) :
    NegMergePosition.equivENType p =
    ENType.equivBool.invFun (NegMergePosition.equivBool p) := by
  cases p <;> rfl

/-- The Equiv chain factors through Bool:
    `equivENStrength = equivBool ∘ ENStrength.equivBool⁻¹` pointwise. -/
theorem equiv_factors_enstrength (p : NegMergePosition) :
    NegMergePosition.equivENStrength p =
    ENStrength.equivBool.invFun (NegMergePosition.equivBool p) := by
  cases p <;> rfl

-- ── Bridge to Defs.lean semantic chain ──

open Semantics.Negation (scopeToENType scopeToLicensing enTypeToLicensing)

/-- Merge position's `scopesIntoVP` determines EN type via the
    semantic chain from `Defs.lean`. -/
theorem merge_position_semantic_bridge (pos : NegMergePosition) :
    scopeToENType pos.scopesIntoVP = pos.toENType := by
  cases pos <;> rfl

/-- Merge position determines licensing via the full semantic chain:
    merge → scopesIntoVP → scopeToENType → enTypeToLicensing. -/
theorem merge_position_licensing (pos : NegMergePosition) :
    scopeToLicensing pos.scopesIntoVP = pos.polarityProfile := by
  cases pos <;> rfl

-- ════════════════════════════════════════════════════
-- § 4. The classification chain
-- ════════════════════════════════════════════════════

/-! ### All classifications are in bijection

`NegMergePosition`, `ENType`, `ENStrength`, and `Bool` (via `scopesIntoVP`)
are all two-element types. The bridge functions between them are bijections.
Rather than proving each pairwise, we state a single theorem: all four
two-valued properties agree on which merge position they classify as
"active" (scope-bearing, low, weak, NPI-licensing). -/

/-- The classification chain: all four two-valued properties of
    `NegMergePosition` are in bijection. Scope access, EN type,
    EN strength, and weak-NPI licensing all partition merge positions
    the same way.

    This means any result proved about one classification
    automatically constrains the others. -/
theorem classifications_agree (pos : NegMergePosition) :
    (pos.scopesIntoVP = true) = (pos.toENType == .low) ∧
    (pos.toENType == .low) = (pos.toENStrength == .weak) ∧
    (pos.toENStrength == .weak) = (pos.polarityProfile.licenses .weakNPI) := by
  cases pos <;> exact ⟨rfl, rfl, rfl⟩

/-- Scope determines EN type (Iff form). -/
theorem scope_determines_entype (pos : NegMergePosition) :
    (pos.scopesIntoVP = true) ↔ (pos.toENType = .low) := by
  cases pos <;> simp [NegMergePosition.scopesIntoVP, NegMergePosition.toENType]

/-- High EN is strong EN. -/
theorem high_en_is_strong (pos : NegMergePosition)
    (h : pos.toENType = .high) :
    pos.toENStrength = .strong := by
  cases pos <;> simp_all [NegMergePosition.toENType, NegMergePosition.toENStrength]

-- ════════════════════════════════════════════════════
-- § 5. F-value grounding
-- ════════════════════════════════════════════════════

/-! ### Grounding scope in the extended projection

The TP/CP distinction in `NegMergePosition` is not stipulated — it
corresponds to position in the extended projection relative to the
CP boundary (F3 = Fin). This section connects `scopesIntoVP` to
`isCPArea` and `fValue`, showing that scope accessibility follows
from f-value ordering under PIC. -/

/-- Scope into vP = NOT in CP area (for the canonical heads).

    Standard NegP (F2) is below the CP boundary → scope into vP.
    FocP (F4) is above the CP boundary → no scope into vP.
    This grounds the two-way scope distinction in the extended
    projection's f-value monotonicity. -/
theorem scope_iff_not_cp_area :
    NegMergePosition.tp.scopesIntoVP = !isCPArea .Neg ∧
    NegMergePosition.cp.scopesIntoVP = !isCPArea .Foc := by decide

/-- Standard NegP (F2) is in the inflectional domain, not the CP area. -/
theorem neg_in_tp : isCPArea .Neg = false := by decide

/-- Foc (F4) is in the CP area. -/
theorem foc_in_cp : isCPArea .Foc = true := by decide

/-- Fin (F3) is the CP boundary (inclusive — lowest CP head). -/
theorem fin_is_cp_boundary : isCPArea .Fin = true := by decide

/-- The f-value boundary: CP area is strictly above standard NegP. -/
theorem cp_area_above_neg : fValue .Fin > fValue .Neg := by decide

-- ════════════════════════════════════════════════════
-- § 6. Bridge: Czech NegPosition → NegMergePosition
-- ════════════════════════════════════════════════════

/-! ### Coarsening Czech three-way negation
@cite{stankova-2025}

Czech polar questions distinguish three LF positions for negation:
inner (TP), medial (ModP), and outer (PolP). The EN-relevant
`NegMergePosition` is coarser: inner and medial are both in the
inflectional domain (tp), while outer is in the CP area (cp).

This coercion shows that the two-way EN distinction is a proper
abstraction over the three-way Czech distinction — any result
proved for `NegMergePosition` applies to Czech negation positions
via this mapping. -/

open Semantics.Negation.CzechNegation (NegPosition)

/-- Map Czech three-way negation positions to the coarser two-way
    EN merge position.

    - **Inner** (TP, propositional ¬p): inflectional domain → tp
    - **Medial** (ModP, scopes over □_ev): still inflectional → tp
    - **Outer** (PolP, FALSUM): CP area → cp -/
def NegPosition.toNegMergePosition : NegPosition → NegMergePosition
  | .inner  => .tp
  | .medial => .tp
  | .outer  => .cp

/-- Inner/medial map to tp, outer maps to cp. -/
theorem inner_is_tp : NegPosition.toNegMergePosition .inner = .tp := rfl
theorem medial_is_tp : NegPosition.toNegMergePosition .medial = .tp := rfl
theorem outer_is_cp : NegPosition.toNegMergePosition .outer = .cp := rfl

/-- The Czech NCI licensing diagnostic aligns with vP scope:
    inner licenses NCIs (scopes into vP), outer does not (no vP scope). -/
theorem nci_licensing_matches_scope :
    Semantics.Negation.CzechNegation.licenses .inner .nciLicensed =
    (NegPosition.toNegMergePosition .inner).scopesIntoVP ∧
    Semantics.Negation.CzechNegation.licenses .outer .nciLicensed =
    (NegPosition.toNegMergePosition .outer).scopesIntoVP := ⟨rfl, rfl⟩

/-- The Czech three-way → two-way coarsening preserves scope ordering:
    inner ≤ medial ≤ outer maps to tp ≤ tp ≤ cp (monotone). -/
theorem toNegMergePosition_monotone :
    Monotone NegPosition.toNegMergePosition := by
  intro a b hab
  -- Both ≤ relations reduce to toNat comparisons via LinearOrder.lift'
  change NegMergePosition.toNat _ ≤ NegMergePosition.toNat _
  change NegPosition.toNat a ≤ NegPosition.toNat b at hab
  cases a <;> cases b <;>
    simp only [NegPosition.toNegMergePosition, NegMergePosition.toNat,
               NegPosition.toNat] at * <;> omega

end Minimalism.NegScope
