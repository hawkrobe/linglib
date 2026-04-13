import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine

/-!
# Selective Opacity @cite{keine-2019}

Selective Opacity. *Linguistic Inquiry* 50(1), 13–62.

## Summary

@cite{keine-2019} argues that selective opacity — where the same
domain is opaque to some operations but transparent to others — is
a property of *probes*, not of domains. The constraint targets Agree,
the operation underlying both movement and φ-agreement. Different
probes have different *horizons* (categories that terminate their
search), and the interplay of probe location and horizon setting
produces the observed selective opacity patterns.

## Core Contributions Formalized

1. **The transparency table** (58): four operations (φ-agreement,
   A-movement, wh-licensing, Ā-movement) × three clause sizes
   (CP, TP, vP) yield a non-binary opacity pattern.

2. **Upward Entailment** (40): if a clause is opaque to a probe,
   all larger clauses are too.

3. **Height-Locality Connection** (33/62): the higher a probe sits
   in the clausal spine, the more structures are transparent to it.

4. **Hindi LDA generalizations**:
   - (21): A-movement of *any* element renders the embedded clause
     obligatorily transparent for LDA
   - (23): finite clauses are opaque to A-movement and φ-agreement
     but not Ā-movement
   - (25): the transparency/opacity table by clause type and operation

## Relationship to @cite{keine-2020}

This article's simplified fValue model (`transparentTo`) treats clause
types as linearly ordered. @cite{keine-2020} introduces bilateral labeling
(`transparentToLabel`) which correctly handles partially ordered clause
types (NmlzP vs CP in Hindi). The article probes remain useful for
verifying the paper's original predictions, but the book's model
supersedes the fValue approximation. See `Keine2020.lean` for the
book's 4×4 transparency tables and bilateral-labeling theorems.

Key refinements in @cite{keine-2020}:
- Hindi φ/A horizon refined from ⊣ C to ⊣ T (book (219))
- Hindi Ā horizon specified as ⊣ Nmlz (not just "no horizon")
- English Ā has ⊣ C (the article treated it as horizonless)
- German adds ForceP as a distinct clause size above CP
- Vacuous probes derived from bilateral labeling (§3.5)
- HLT (279) derived as emergent property, not stipulated

## Architecture

The theory-layer infrastructure (`ProbeProfile`, `transparentTo`,
`transparentToLabel`, `upward_entailment`, `height_locality_connection`)
lives in `Theories/Syntax/Minimalism/Core/Probe.lean`. This file
imports those definitions and verifies the paper's empirical predictions
as concrete theorems using the simplified fValue model.
-/

namespace Phenomena.Agreement.Studies.Keine2019

open Minimalism (ProbeProfile keinePhiProbe keineAProbe keineWhLicensing
  keineĀProbe fValue ClauseSpine Cat)

-- ============================================================================
-- § 1: The Transparency Table (@cite{keine-2019} (58))
-- ============================================================================

/-! ### Table (58): Transparency (✓) and opacity (*) by clause type and operation

| Operation     | Probe location | CP (finite) | TP (nonfinite) | vP (nonfinite) |
|---------------|---------------|-------------|----------------|----------------|
| φ-agreement   | T⁰            | *           | *              | ✓              |
| A-movement    | T⁰            | *           | *              | ✓              |
| wh-licensing  | C⁰            | *           | ✓              | ✓              |
| Ā-movement    | C⁰            | ✓           | ✓              | ✓              |

The table captures the central empirical discovery: selective opacity is
not a binary phenomenon. There are at least three distinct locality types,
corresponding to different probe–horizon pairings. -/

-- ────────────────────────────────────────────────────────────────
-- φ-agreement (probe on T⁰, horizon C): opaque to CP and TP, transparent to vP
-- ────────────────────────────────────────────────────────────────

theorem phi_opaque_to_cp : keinePhiProbe.transparentTo .C = false := by decide
theorem phi_opaque_to_tp : keinePhiProbe.transparentTo .T = false := by decide
theorem phi_transparent_to_vp : keinePhiProbe.transparentTo .v = true := by decide

-- ────────────────────────────────────────────────────────────────
-- A-movement (probe on T⁰, horizon C): same locality as φ-agreement
-- ────────────────────────────────────────────────────────────────

theorem a_opaque_to_cp : keineAProbe.transparentTo .C = false := by decide
theorem a_opaque_to_tp : keineAProbe.transparentTo .T = false := by decide
theorem a_transparent_to_vp : keineAProbe.transparentTo .v = true := by decide

-- ────────────────────────────────────────────────────────────────
-- wh-licensing (probe on C⁰, horizon C): opaque to CP, transparent to TP and vP
-- ────────────────────────────────────────────────────────────────

theorem wh_opaque_to_cp : keineWhLicensing.transparentTo .C = false := by decide
theorem wh_transparent_to_tp : keineWhLicensing.transparentTo .T = true := by decide
theorem wh_transparent_to_vp : keineWhLicensing.transparentTo .v = true := by decide

-- ────────────────────────────────────────────────────────────────
-- Ā-movement (probe on C⁰, no horizon): transparent to everything
-- ────────────────────────────────────────────────────────────────

theorem ābar_transparent_to_cp : keineĀProbe.transparentTo .C = true := by decide
theorem ābar_transparent_to_tp : keineĀProbe.transparentTo .T = true := by decide
theorem ābar_transparent_to_vp : keineĀProbe.transparentTo .v = true := by decide

-- ============================================================================
-- § 2: Hindi Generalizations
-- ============================================================================

/-! ### Generalization (21): A-extraction renders clause transparent for LDA

If A-movement of *any* element out of an embedded clause has applied,
that clause is obligatorily transparent for LDA. Agreement is hence
obligatory and default agreement is impossible, regardless of whether
the agreement controller moves or not. Ā-movement has no such effect.

This is captured by the shared locality of A-movement and φ-agreement:
both are probes on T⁰ with horizon C. If A-movement can penetrate a
clause (= clause is transparent to the A-probe), φ-agreement can too. -/

/-- A-movement and φ-agreement share the same horizon and probe location.
    This is the structural reason A-extraction entails LDA transparency:
    whatever is transparent to [•A•] is transparent to [*φ*]. -/
theorem a_phi_same_profile :
    keineAProbe.probeHead = keinePhiProbe.probeHead ∧
    keineAProbe.horizon = keinePhiProbe.horizon := ⟨rfl, rfl⟩

/-- Consequence: for any clause head, A-transparency implies φ-transparency.
    This derives generalization (21) — if A-movement can enter a clause,
    φ-agreement can too, making LDA obligatory. -/
theorem a_transparency_implies_phi (c : Cat)
    (h : keineAProbe.transparentTo c = true) :
    keinePhiProbe.transparentTo c = true := h

/-! ### Generalization (23): finite clauses are selectively opaque

Finite clauses (CP) are opaque to A-movement and φ-agreement, but
transparent to Ā-movement. This is a direct consequence of the
probe–horizon pairings: A-probes and φ-probes have C as their horizon,
so CP blocks them. Ā-probes have no horizon, so nothing blocks them. -/

/-- The full (23): CP is selectively opaque — blocks A-movement and
    φ-agreement but not Ā-movement. -/
theorem finite_clause_selective_opacity :
    keineAProbe.transparentTo .C = false ∧
    keinePhiProbe.transparentTo .C = false ∧
    keineĀProbe.transparentTo .C = true := ⟨by decide, by decide, by decide⟩

-- ============================================================================
-- § 3: Height-Locality Instantiations
-- ============================================================================

/-! ### Generalization (33)/(62): Height-Locality Connection

The higher the structural position of a probe, the more kinds of
structures it can search into.

This is verified concretely: the Ā-probe (on C⁰, fValue 6) can search
into strictly more clause types than the A-probe (on T⁰, fValue 2).
The Height-Locality Connection is not a stipulation — it is derived as
a theorem in `Agree.lean` from the monotonicity of horizons within
extended projections. -/

/-- Ā-probes are higher than A-probes in the functional sequence. -/
theorem ābar_higher_than_a :
    fValue keineĀProbe.probeHead > fValue keineAProbe.probeHead := by decide

/-- The Ā-probe can search into everything the A-probe can, and more.
    For all three clause sizes, Ā-transparency ≥ A-transparency. -/
theorem ābar_subsumes_a :
    (keineAProbe.transparentTo .v = true → keineĀProbe.transparentTo .v = true) ∧
    (keineAProbe.transparentTo .T = true → keineĀProbe.transparentTo .T = true) ∧
    (keineAProbe.transparentTo .C = true → keineĀProbe.transparentTo .C = true) :=
  ⟨fun _ => by decide, fun _ => by decide, fun _ => by decide⟩

-- ============================================================================
-- § 4: Upward Entailment Instantiations
-- ============================================================================

/-! ### Generalization (40): Upward Entailment

If a clause of a given size is opaque for a probe, all larger clauses
are also opaque. Verified concretely for the A-probe: vP is transparent,
TP is opaque, and CP is opaque. The transition from transparent to opaque
happens once and never reverses. -/

/-- A-probe: opacity increases monotonically along the functional sequence.
    vP (F1) ✓ → T (F2) * → C (F6) *. Once opaque, always opaque. -/
theorem a_probe_monotonic_opacity :
    keineAProbe.transparentTo .v = true ∧
    keineAProbe.transparentTo .T = false ∧
    keineAProbe.transparentTo .C = false := ⟨by decide, by decide, by decide⟩

-- ============================================================================
-- § 5: ClauseSpine Bridge
-- ============================================================================

/-! ### Clause spine integration

The named spines from `ClauseSpine.lean` connect to probe transparency
via `fLevel`: a spine's F-level determines which probes can search into
clauses of that size. -/

/-- vP-sized clauses are transparent to all four probes. -/
theorem vP_transparent_all :
    keinePhiProbe.transparentTo ClauseSpine.vP.highestHead = true ∧
    keineAProbe.transparentTo ClauseSpine.vP.highestHead = true ∧
    keineWhLicensing.transparentTo ClauseSpine.vP.highestHead = true ∧
    keineĀProbe.transparentTo ClauseSpine.vP.highestHead = true :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- CP-sized clauses are transparent only to the Ā-probe. -/
theorem cP_transparent_only_ābar :
    keinePhiProbe.transparentTo ClauseSpine.cP.highestHead = false ∧
    keineAProbe.transparentTo ClauseSpine.cP.highestHead = false ∧
    keineWhLicensing.transparentTo ClauseSpine.cP.highestHead = false ∧
    keineĀProbe.transparentTo ClauseSpine.cP.highestHead = true :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- TP-sized clauses are transparent to wh-licensing and Ā-movement
    but opaque to φ-agreement and A-movement. -/
theorem tP_transparency :
    keinePhiProbe.transparentTo ClauseSpine.tP.highestHead = false ∧
    keineAProbe.transparentTo ClauseSpine.tP.highestHead = false ∧
    keineWhLicensing.transparentTo ClauseSpine.tP.highestHead = true ∧
    keineĀProbe.transparentTo ClauseSpine.tP.highestHead = true :=
  ⟨by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- § 6: Hyperraising (@cite{keine-2019} §4.2.3)
-- ============================================================================

/-! ### English hyperraising is blocked by CP

A-movement (hyperraising) out of a finite clause is impossible in
English because the A-probe ([•A•] on T⁰) has C as its horizon.
The CP boundary blocks the A-probe's search, ruling out
`*John seems [CP t likes oatmeal]`. -/

/-- Hyperraising blocked: A-probe cannot search into CP. -/
theorem hyperraising_blocked :
    keineAProbe.transparentTo .C = false := by decide

/-- Ā-extraction is fine: Ā-probe has no horizon blocking CP.
    `Who do you think [CP t eats oatmeal]?` is grammatical. -/
theorem ābar_extraction_ok :
    keineĀProbe.transparentTo .C = true := by decide

end Phenomena.Agreement.Studies.Keine2019
