import Linglib.Theories.Syntax.Minimalism.Core.Probe
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine

/-!
# Probes and Their Horizons @cite{keine-2020}

*Probes and Their Horizons*. MIT Press, LI Monograph 81.

## Summary

@cite{keine-2020} is the monograph expansion of @cite{keine-2019}.
It develops a comprehensive theory of selective opacity — where the same
domain is opaque to some operations but transparent to others — based
on probe-specific *horizons* and *bilateral labeling*.

## Core Contributions Formalized

1. **Bilateral labeling** (ch. 3): within an extended projection, both head
   and complement project labels. CP's label is `[C, T, v, V]`. A probe's
   search terminates when the horizon category appears in the label.
   This *derives* Upward Entailment as an emergent property.

2. **Language-parameterized probes**: Hindi, English, German, Itelmen,
   and Tsez have different probe–horizon pairings (`LanguageProbeConfig`).

3. **NmlzP ≱ CP** (ch. 2): Hindi has four clause sizes (vP, TP, NmlzP, CP)
   that are NOT linearly ordered — NmlzP is opaque to Ā but transparent
   to wh, while CP is the reverse.

4. **ForceP** (ch. 4): German V2 clauses are structurally larger than
   V-final CPs — they project ForceP.

5. **vP is not a phase** (ch. 5): φ-Agree crosses unboundedly many vPs
   but not CPs; selective opacity creates intractable problems for vP
   phases; previous arguments can be reanalyzed.

6. **Default horizon** (307): for probe [*F*] on X⁰, default horizon = X.

7. **Horizons + phases coexist** (ch. 4): horizons determine selective
   opacity (probe-specific); CP phases impose absolute opacity (all
   operations). These are orthogonal constraints.

8. **Vacuous probes** (§3.5, (274)–(278)): a probe whose sister's bilateral
   label contains the horizon category is vacuous — its search terminates
   at the sister, leaving no searchable domain.

9. **Height-Locality Theorem** ((279)): location→horizon and horizon→location
   constraints emerge from bilateral labeling + vacuity filtering.

10. **Ban on Improper Movement** (§3.4.1–3.4.2): Ā-movement cannot feed
    A-movement — derived from horizons, not stipulated.

11. **A-movement–Agreement Generalization** ((231)): A-extraction forces
    obligatory LDA — A-probes and φ-probes share horizons in Hindi.

12. **Movement–agreement mismatches** (§3.4.5): Itelmen and Tsez show that
    φ-agreement and A-movement can have different horizons in *opposite*
    directions, via @cite{bobaljik-wurmbrand-2005} and
    @cite{polinsky-potsdam-2001}.

13. **Smuggling constraints** (§3.4.3, (248)–(259)): A-movement out of
    Ā-moved constituents is blocked by horizons (CP encapsulates);
    Ā-movement out of A-moved constituents is not blocked.

14. **Crosslinguistic A-movement typology** (§3.6, (300)): three attested
    settings (Lubukusu ⊣ ∅, English ⊣ C, Hindi ⊣ T) form an entailment
    chain.

15. **Phase–horizon orthogonality** (ch. 4): phases provide absolute
    opacity (Spell-Out), horizons provide selective opacity (search
    termination). These are orthogonal constraints.

## Architecture

This file imports `Probe.lean` (for `ProbeProfile`, `LanguageProbeConfig`,
`transparentToLabel`) and `ClauseSpine.lean` (for clause spines with
bilateral labels). It verifies the book's predictions as theorems.
-/

namespace Keine2020

open Minimalism (ProbeProfile LanguageProbeConfig ClauseSpine Cat fValue english_extr
  lubukusuAProbe)

-- ============================================================================
-- § 1: Hindi Transparency Table (@cite{keine-2020} (168))
-- ============================================================================

/-! ### Hindi 4×4 Transparency Table

| Operation     | vP | TP | NmlzP | CP |
|---------------|----|----|-------|----|
| φ-agreement   | ✓  | *  | *     | *  |
| A-movement    | ✓  | *  | *     | *  |
| wh-licensing  | ✓  | ✓  | ✓     | *  |
| Ā-movement    | ✓  | ✓  | *     | ✓  |

The key discovery: NmlzP and CP are NOT linearly ordered.
NmlzP blocks Ā but not wh; CP blocks wh but not Ā. -/

private def hindiCfg := LanguageProbeConfig.hindi

-- Bilateral labels for Hindi clause types
private def vPLabel  : List Cat := ClauseSpine.vP.projectedHeads
private def tPLabel  : List Cat := ClauseSpine.tP.projectedHeads
private def nmlzPLabel : List Cat := ClauseSpine.nmlzP.projectedHeads
private def cPLabel  : List Cat := ClauseSpine.cP.projectedHeads

-- ────────────────────────────────────────────────────────────────
-- φ-agreement (T⁰, ⊣ T): transparent to vP only
-- ────────────────────────────────────────────────────────────────

theorem hindi_phi_transparent_vP :
    hindiCfg.phi.transparentToLabel vPLabel = true := by decide
theorem hindi_phi_opaque_tP :
    hindiCfg.phi.transparentToLabel tPLabel = false := by decide
theorem hindi_phi_opaque_nmlzP :
    hindiCfg.phi.transparentToLabel nmlzPLabel = false := by decide
theorem hindi_phi_opaque_cP :
    hindiCfg.phi.transparentToLabel cPLabel = false := by decide

-- ────────────────────────────────────────────────────────────────
-- A-movement (T⁰, ⊣ T): same as φ
-- ────────────────────────────────────────────────────────────────

theorem hindi_a_transparent_vP :
    hindiCfg.aMove.transparentToLabel vPLabel = true := by decide
theorem hindi_a_opaque_tP :
    hindiCfg.aMove.transparentToLabel tPLabel = false := by decide
theorem hindi_a_opaque_nmlzP :
    hindiCfg.aMove.transparentToLabel nmlzPLabel = false := by decide
theorem hindi_a_opaque_cP :
    hindiCfg.aMove.transparentToLabel cPLabel = false := by decide

-- ────────────────────────────────────────────────────────────────
-- wh-licensing (C⁰, ⊣ C): transparent to vP, TP, NmlzP; opaque to CP
-- ────────────────────────────────────────────────────────────────

theorem hindi_wh_transparent_vP :
    hindiCfg.wh.transparentToLabel vPLabel = true := by decide
theorem hindi_wh_transparent_tP :
    hindiCfg.wh.transparentToLabel tPLabel = true := by decide
theorem hindi_wh_transparent_nmlzP :
    hindiCfg.wh.transparentToLabel nmlzPLabel = true := by decide
theorem hindi_wh_opaque_cP :
    hindiCfg.wh.transparentToLabel cPLabel = false := by decide

-- ────────────────────────────────────────────────────────────────
-- Ā-movement (C⁰, ⊣ Nmlz): transparent to vP, TP, CP; opaque to NmlzP
-- ────────────────────────────────────────────────────────────────

theorem hindi_ābar_transparent_vP :
    hindiCfg.ābar.transparentToLabel vPLabel = true := by decide
theorem hindi_ābar_transparent_tP :
    hindiCfg.ābar.transparentToLabel tPLabel = true := by decide
theorem hindi_ābar_opaque_nmlzP :
    hindiCfg.ābar.transparentToLabel nmlzPLabel = false := by decide
theorem hindi_ābar_transparent_cP :
    hindiCfg.ābar.transparentToLabel cPLabel = true := by decide

-- ============================================================================
-- § 2: NmlzP ≱ CP (@cite{keine-2020} ch. 2)
-- ============================================================================

/-- NmlzP and CP are incomparable: each is opaque to one probe but
    transparent to the other. This cannot be captured by a linear
    fValue ordering — it requires bilateral labeling. -/
theorem nmlzP_cp_incomparable :
    -- NmlzP transparent to wh, CP opaque to wh
    hindiCfg.wh.transparentToLabel nmlzPLabel = true ∧
    hindiCfg.wh.transparentToLabel cPLabel = false ∧
    -- CP transparent to Ā, NmlzP opaque to Ā
    hindiCfg.ābar.transparentToLabel cPLabel = true ∧
    hindiCfg.ābar.transparentToLabel nmlzPLabel = false := by decide

/-- NmlzP and CP have the same number of projected heads — their
    difference is qualitative (which heads), not quantitative (how many). -/
theorem nmlzP_cP_same_spine_size :
    ClauseSpine.nmlzP.size = ClauseSpine.cP.size := by decide

/-- The bilateral labels of NmlzP and CP differ precisely in their
    topmost head: Nmlz vs C. -/
theorem nmlzP_has_nmlz_not_c :
    ClauseSpine.nmlzP.projects .Nmlz = true ∧
    ClauseSpine.nmlzP.projects .C = false := by decide

theorem cP_has_c_not_nmlz :
    ClauseSpine.cP.projects .C = true ∧
    ClauseSpine.cP.projects .Nmlz = false := by decide

-- ============================================================================
-- § 3: German Transparency Table (@cite{keine-2020} ch. 4)
-- ============================================================================

/-! ### German 4×4 Transparency Table

| Operation       | vP | TP | CP (V-final) | ForceP (V2) |
|-----------------|----|----|-------------|-------------|
| scrambling      | ✓  | *  | *           | *           |
| relativization  | ✓  | ✓  | *           | *           |
| wh-movement     | ✓  | ✓  | ✓           | *           |
| topicalization  | ✓  | ✓  | ✓           | ✓           |
-/

private def germanCfg := LanguageProbeConfig.german
private def forcePLabel : List Cat := ClauseSpine.forceP.projectedHeads

-- ────────────────────────────────────────────────────────────────
-- scrambling (T⁰, ⊣ T): transparent to vP only
-- ────────────────────────────────────────────────────────────────

theorem german_scr_transparent_vP :
    germanCfg.phi.transparentToLabel vPLabel = true := by decide
theorem german_scr_opaque_tP :
    germanCfg.phi.transparentToLabel tPLabel = false := by decide
theorem german_scr_opaque_cP :
    germanCfg.phi.transparentToLabel cPLabel = false := by decide
theorem german_scr_opaque_forceP :
    germanCfg.phi.transparentToLabel forcePLabel = false := by decide

-- ────────────────────────────────────────────────────────────────
-- relativization (C⁰, ⊣ C): transparent to vP, TP
-- ────────────────────────────────────────────────────────────────

theorem german_rel_transparent_vP :
    germanCfg.wh.transparentToLabel vPLabel = true := by decide

-- Note: German rel uses the wh field with horizon Force (same structural
-- position C⁰). For relativization specifically (horizon C), we test directly:
private def germanRelProbe : ProbeProfile := ⟨.C, some .C⟩

theorem german_rel_transparent_tP :
    germanRelProbe.transparentToLabel tPLabel = true := by decide
theorem german_rel_opaque_cP :
    germanRelProbe.transparentToLabel cPLabel = false := by decide
theorem german_rel_opaque_forceP :
    germanRelProbe.transparentToLabel forcePLabel = false := by decide

-- ────────────────────────────────────────────────────────────────
-- wh-movement (C⁰, ⊣ Force): transparent to vP, TP, CP
-- ────────────────────────────────────────────────────────────────

theorem german_wh_transparent_vP :
    germanCfg.wh.transparentToLabel vPLabel = true := by decide
theorem german_wh_transparent_tP :
    germanCfg.wh.transparentToLabel tPLabel = true := by decide
theorem german_wh_transparent_cP :
    germanCfg.wh.transparentToLabel cPLabel = true := by decide
theorem german_wh_opaque_forceP :
    germanCfg.wh.transparentToLabel forcePLabel = false := by decide

-- ────────────────────────────────────────────────────────────────
-- topicalization (Force⁰, ⊣ ∅): transparent to everything
-- ────────────────────────────────────────────────────────────────

theorem german_top_transparent_vP :
    germanCfg.ābar.transparentToLabel vPLabel = true := by decide
theorem german_top_transparent_tP :
    germanCfg.ābar.transparentToLabel tPLabel = true := by decide
theorem german_top_transparent_cP :
    germanCfg.ābar.transparentToLabel cPLabel = true := by decide
theorem german_top_transparent_forceP :
    germanCfg.ābar.transparentToLabel forcePLabel = true := by decide

-- ============================================================================
-- § 4: English Opacity (@cite{keine-2020} (241))
-- ============================================================================

private def englishCfg := LanguageProbeConfig.english

/-- English hyperraising blocked: A-probe (T⁰, ⊣ C) cannot search into CP. -/
theorem english_hyperraising_blocked :
    englishCfg.aMove.transparentToLabel cPLabel = false := by decide

/-- English wh-extraction OK: wh-probe (C⁰, ⊣ ∅) has no horizon. -/
theorem english_wh_extraction_ok :
    englishCfg.wh.transparentToLabel cPLabel = true := by decide

-- ============================================================================
-- § 5: Hindi Generalizations
-- ============================================================================

/-- Generalization (21): A-extraction renders clause transparent for LDA.
    A-movement and φ-agreement share the same probe settings in Hindi:
    both on T⁰ with horizon T. -/
theorem hindi_a_phi_same :
    hindiCfg.aMove = hindiCfg.phi := rfl

/-- Generalization (23): finite clauses (CP) are opaque to A-movement
    and φ-agreement but transparent to Ā-movement. -/
theorem hindi_finite_selective_opacity :
    hindiCfg.aMove.transparentToLabel cPLabel = false ∧
    hindiCfg.phi.transparentToLabel cPLabel = false ∧
    hindiCfg.ābar.transparentToLabel cPLabel = true := by decide

-- ============================================================================
-- § 6: Default Horizon (@cite{keine-2020} (307))
-- ============================================================================

/-- Hindi φ and A probes use the default horizon: probe on T⁰ with
    horizon T (= its own head). -/
theorem hindi_phi_uses_default :
    hindiCfg.phi = ProbeProfile.defaultHorizon .T := rfl

/-- German scrambling probe uses the default horizon: probe on T⁰
    with horizon T. -/
theorem german_scr_uses_default :
    germanCfg.phi = ProbeProfile.defaultHorizon .T := rfl

-- ============================================================================
-- § 7: Four Distinct Locality Types (Hindi)
-- ============================================================================

/-- Hindi exhibits four distinct locality types — one per operation.
    Using bilateral labeling, each probe produces a unique 4-tuple
    of transparency values across (vP, TP, NmlzP, CP). -/
def hindiProfile (p : ProbeProfile) : Bool × Bool × Bool × Bool :=
  ( p.transparentToLabel vPLabel,
    p.transparentToLabel tPLabel,
    p.transparentToLabel nmlzPLabel,
    p.transparentToLabel cPLabel )

theorem hindi_four_locality_types :
    -- All four probes produce different profiles
    hindiProfile hindiCfg.phi ≠ hindiProfile hindiCfg.wh ∧
    hindiProfile hindiCfg.phi ≠ hindiProfile hindiCfg.ābar ∧
    hindiProfile hindiCfg.wh ≠ hindiProfile hindiCfg.ābar := by decide

-- ============================================================================
-- § 8: Horizon Category Matters (@cite{keine-2020} §3.6)
-- ============================================================================

/-- Under bilateral labeling, the specific horizon category matters.
    Hindi wh (horizon C) and Ā (horizon Nmlz) are both on C⁰ but
    have different transparency profiles — proving that the A/Ā
    distinction is not strictly derived from probe height. -/
theorem same_head_different_locality :
    hindiCfg.wh.probeHead = hindiCfg.ābar.probeHead ∧
    hindiProfile hindiCfg.wh ≠ hindiProfile hindiCfg.ābar := by decide

-- ============================================================================
-- § 9: ForceP is Structurally Larger than CP
-- ============================================================================

/-- ForceP projects all the heads that CP does, plus Force. -/
theorem forceP_superset_cP :
    ClauseSpine.forceP.projects .V = true ∧
    ClauseSpine.forceP.projects .v = true ∧
    ClauseSpine.forceP.projects .T = true ∧
    ClauseSpine.forceP.projects .C = true ∧
    ClauseSpine.forceP.projects .Force = true := by decide

/-- ForceP is strictly larger than CP in spine size. -/
theorem forceP_larger_than_cP :
    ClauseSpine.cP.size < ClauseSpine.forceP.size := by decide

-- ============================================================================
-- § 10: Vacuous Probes (@cite{keine-2020} §3.5, (274)–(278))
-- ============================================================================

/-! ### Vacuous probes: bilateral-labeling-derived

A probe is vacuous when its sister's bilateral label already contains the
horizon category — the probe's search terminates at the sister, leaving
no domain to search. Vacuous probes are undetectable: they cannot
trigger movement or agreement.

Example: a probe on C⁰ with horizon T is vacuous, because the sister
of C⁰ is TP, whose label `[V, Appl, v, Voice, T]` contains T. -/

/-- Standard vacuous examples: C⁰ ⊣ T, C⁰ ⊣ v, C⁰ ⊣ V are all vacuous. -/
theorem vacuous_C_with_T :
    (ProbeProfile.mk .C (some .T)).isVacuous = true := by decide
theorem vacuous_C_with_v :
    (ProbeProfile.mk .C (some .v)).isVacuous = true := by decide
theorem vacuous_C_with_V :
    (ProbeProfile.mk .C (some .V)).isVacuous = true := by decide

/-- Hindi Ā (C⁰ ⊣ Nmlz) is NOT vacuous: Nmlz is not in TP's label. -/
theorem hindi_ābar_not_vacuous :
    hindiCfg.ābar.isVacuous = false := by decide

/-- All Hindi probes are nonvacuous — each produces observable effects. -/
theorem hindi_all_nonvacuous :
    hindiCfg.phi.isVacuous = false ∧
    hindiCfg.aMove.isVacuous = false ∧
    hindiCfg.wh.isVacuous = false ∧
    hindiCfg.ābar.isVacuous = false := by decide

/-- All German probes are nonvacuous. -/
theorem german_all_nonvacuous :
    germanCfg.phi.isVacuous = false ∧
    germanCfg.aMove.isVacuous = false ∧
    germanCfg.wh.isVacuous = false ∧
    germanCfg.ābar.isVacuous = false := by decide

-- ============================================================================
-- § 11: Height-Locality Theorem (@cite{keine-2020} (279))
-- ============================================================================

/-! ### HLT: Location→Horizon and Horizon→Location constraints

The HLT emerges from bilateral labeling + vacuity. Only nonvacuous
probe–horizon pairings produce observable dependencies:

**(279a)** A probe on C⁰ cannot have T, v, or V as horizon (vacuous).
It CAN have C, Nmlz, or Force.

**(279b)** A probe with horizon T cannot be on C⁰ or Force⁰ (vacuous).
It can be on T⁰ (default horizon). -/

/-- HLT (279a) for Hindi: the attested probes on C⁰ (wh ⊣ C, Ā ⊣ Nmlz)
    are exactly the nonvacuous options. -/
theorem hindi_hlt_C_probes :
    -- Attested and nonvacuous
    hindiCfg.wh.isVacuous = false ∧
    hindiCfg.ābar.isVacuous = false ∧
    -- Unattested alternatives would be vacuous
    (ProbeProfile.mk .C (some .T)).isVacuous = true ∧
    (ProbeProfile.mk .C (some .v)).isVacuous = true := by decide

/-- HLT (279b) for Hindi: φ and A probes use T⁰ ⊣ T (nonvacuous),
    but ⊣ T on C⁰ or Force⁰ would be vacuous. -/
theorem hindi_hlt_T_horizon :
    hindiCfg.phi.isVacuous = false ∧
    (ProbeProfile.mk .C (some .T)).isVacuous = true ∧
    (ProbeProfile.mk .Force (some .T)).isVacuous = true := by decide

-- ============================================================================
-- § 12: Ban on Improper Movement (@cite{keine-2020} §3.4.1–3.4.2)
-- ============================================================================

/-! ### BIM: Ā cannot feed A

Ā-movement places DP in [Spec,CP], creating a CP. A-probes have horizons
that make CP opaque. Therefore the A-probe cannot reach an Ā-moved
element — improper movement is blocked.

Conversely, A-movement feeds Ā-movement freely: Ā-probes can search
into CP (Hindi Ā: C⁰ ⊣ Nmlz, CP lacks Nmlz). -/

/-- BIM premise: CPs are opaque to A-probes in all three languages. -/
theorem bim_hindi :
    hindiCfg.aMove.transparentToLabel cPLabel = false := by decide
theorem bim_english :
    LanguageProbeConfig.english.aMove.transparentToLabel cPLabel = false := by decide
theorem bim_german :
    germanCfg.aMove.transparentToLabel cPLabel = false := by decide

/-- Proper movement (A feeds Ā) is permitted: Ā-probes can enter CP. -/
theorem proper_movement_hindi :
    hindiCfg.ābar.transparentToLabel cPLabel = true := by decide
theorem proper_movement_english :
    LanguageProbeConfig.english.ābar.transparentToLabel cPLabel = true := by decide

-- ============================================================================
-- § 13: A-movement–Agreement Generalization (@cite{keine-2020} (231))
-- ============================================================================

/-! ### (231): A-extraction forces obligatory LDA

If A-movement of any element out of an embedded clause has taken place,
that clause is obligatorily transparent for LDA. This is derived from
horizons: A-movement and φ-agreement share the same probe settings in
Hindi (both T⁰ ⊣ T), so anything transparent to one is transparent to
the other. Ā-movement has a DIFFERENT horizon (C⁰ ⊣ Nmlz), so
Ā-extraction does not force agreement. -/

/-- A-probes and φ-probes are identical in Hindi — same head, same horizon. -/
theorem generalization_231_same_probes :
    hindiCfg.aMove = hindiCfg.phi := rfl

/-- CP transparent to Ā (C⁰ ⊣ Nmlz) but opaque to φ (T⁰ ⊣ T):
    Ā-extraction does not force agreement. -/
theorem generalization_231_ābar_no_agreement :
    hindiCfg.ābar.transparentToLabel cPLabel = true ∧
    hindiCfg.phi.transparentToLabel cPLabel = false := by decide

-- ============================================================================
-- § 14: English Extraposition (@cite{keine-2020} (241))
-- ============================================================================

/-! ### English has three probes, including extraposition

English extraposition ([*extr*] on T⁰ ⊣ T) is more local than
A-movement (T⁰ ⊣ C): it cannot cross even TP boundaries. -/

/-- Extraposition is blocked by TP; A-movement is not. -/
theorem english_extr_more_local :
    english_extr.transparentToLabel tPLabel = false ∧
    englishCfg.aMove.transparentToLabel tPLabel = true := by decide

/-- Extraposition uses the default horizon for T⁰. -/
theorem english_extr_is_default :
    english_extr = ProbeProfile.defaultHorizon .T := rfl

-- ============================================================================
-- § 15: Movement–Agreement Mismatches (@cite{keine-2020} §3.4.5)
-- ============================================================================

/-! ### Itelmen and Tsez: φ-agreement ≠ A-movement

@cite{keine-2020} §3.4.5 discusses languages where φ-agreement and
A-movement have different locality — the A-movement–Agreement
Generalization ((231)) is Hindi-specific, not universal.

The two languages show *opposite* mismatch directions:

- **Itelmen** (@cite{bobaljik-wurmbrand-2005}, (269)): A-movement out of
  a nonfinite clause forces obligatory high scope, but there are
  locality constraints on agreement that do not apply to movement.
  A-movement is *more permissive* than φ-agreement.

- **Tsez** (@cite{polinsky-potsdam-2001}, (271)): LDA into an embedded
  clause is possible, but crossclausal movement is blocked.
  φ-agreement is *more permissive* than A-movement.

This demonstrates that there is no inherent directionality to
movement–agreement mismatches. -/

/-- Itelmen (269): A-movement can probe into TP, φ-agreement cannot.
    Movement is more permissive than agreement. -/
theorem itelmen_movement_more_permissive :
    LanguageProbeConfig.itelmen.aMove.transparentToLabel tPLabel = true ∧
    LanguageProbeConfig.itelmen.phi.transparentToLabel tPLabel = false := by decide

/-- Tsez (271): φ can probe into TP, A-movement cannot.
    Agreement is more permissive than movement — the inverse of Itelmen. -/
theorem tsez_agreement_more_permissive :
    LanguageProbeConfig.tsez.phi.transparentToLabel tPLabel = true ∧
    LanguageProbeConfig.tsez.aMove.transparentToLabel tPLabel = false := by decide

/-- In Hindi, by contrast, φ and A-movement are IDENTICAL — no mismatch. -/
theorem hindi_no_mismatch :
    hindiCfg.phi = hindiCfg.aMove := rfl

/-- Itelmen and Tsez have *opposite* mismatch directions: in Itelmen
    movement is more permissive, in Tsez agreement is more permissive.
    Their configs are genuinely different. -/
theorem itelmen_tsez_opposite_mismatch :
    LanguageProbeConfig.itelmen.phi ≠ LanguageProbeConfig.tsez.phi ∧
    LanguageProbeConfig.itelmen.aMove ≠ LanguageProbeConfig.tsez.aMove := by decide

-- ============================================================================
-- § 16: Smuggling Constraints (@cite{keine-2020} §3.4.3, (248)–(259))
-- ============================================================================

/-! ### Smuggling: selective opacity in nonidentity movement

@cite{keine-2020} §3.4.3 shows that smuggling derivations (where XP is
Ā-moved to [Spec,CP], then YP is A-subextracted from XP) exhibit
selective-opacity effects. The horizon account derives these without any
special constraint on movement sequences:

1. **A-movement out of Ā-moved constituent**: BLOCKED.
   Ā-movement creates a CP structure around the moved constituent.
   The A-probe has C (or T) as its horizon, so CP is opaque.
   Example: `*Oscar is known [CP how likely [to win]] it was tᴬ tᴬ̄`

2. **Ā-movement out of A-moved constituent**: OK.
   A-movement does not create an opaque boundary for the Ā-probe.
   Example: `Which movie do you think [the first part of tᴬ̄] is likely tᴬ to create a scandal?`

The key insight is that these constraints are domain-based (the CP
created by Ā-movement is opaque to the A-probe), not item-based
(no reference to the movement history of the DP). -/

/-- Smuggling: Ā-movement creates CP, which blocks the A-probe.
    In all three languages, A-probes cannot search into CP — this is
    exactly the BIM premise, which also derives smuggling restrictions. -/
theorem smuggling_blocked_by_cp :
    -- Hindi: A ⊣ T, CP contains T → opaque
    hindiCfg.aMove.transparentToLabel cPLabel = false ∧
    -- English: A ⊣ C, CP contains C → opaque
    englishCfg.aMove.transparentToLabel cPLabel = false ∧
    -- German: A ⊣ T, CP contains T → opaque
    germanCfg.aMove.transparentToLabel cPLabel = false := by decide

/-- Smuggling: A-movement does NOT create an opaque boundary for
    Ā-probes. The Ā-probe can still search into the domain because
    TP (the landing site of A-movement) does not contain the Ā-probe's
    horizon. -/
theorem smuggling_ābar_not_blocked :
    -- Hindi Ā ⊣ Nmlz: TP label lacks Nmlz → transparent
    hindiCfg.ābar.transparentToLabel tPLabel = true ∧
    -- English wh ⊣ ∅: no horizon → transparent to everything
    englishCfg.wh.transparentToLabel tPLabel = true := by decide

-- ============================================================================
-- § 17: Crosslinguistic A-Movement Typology (@cite{keine-2020} (300))
-- ============================================================================

/-! ### Three attested A-movement horizons

@cite{keine-2020} §3.6, (300) identifies three crosslinguistically
attested A-movement probe settings:

| Language       | Horizon | Hyperraising? |
|----------------|---------|---------------|
| Lubukusu       | ⊣ ∅    | Yes (finite)  |
| English        | ⊣ C    | No (CP blocks)|
| Hindi/Russian  | ⊣ T    | No (TP blocks)|

These form an entailment chain: anything transparent to Hindi's
A-probe is transparent to English's, and anything transparent to
English's is transparent to Lubukusu's. -/

/-- The three A-movement settings verified against clause types. -/
theorem crosslinguistic_a_movement :
    -- Lubukusu (⊣ ∅): CP transparent
    Minimalism.lubukusuAProbe.transparentToLabel cPLabel = true ∧
    -- English (⊣ C): CP opaque, TP transparent
    englishCfg.aMove.transparentToLabel cPLabel = false ∧
    englishCfg.aMove.transparentToLabel tPLabel = true ∧
    -- Hindi (⊣ T): TP opaque, vP transparent
    hindiCfg.aMove.transparentToLabel tPLabel = false ∧
    hindiCfg.aMove.transparentToLabel vPLabel = true := by decide

-- ============================================================================
-- § 18: Phase + Horizon Orthogonality (@cite{keine-2020} ch. 4)
-- ============================================================================

/-! ### Horizons and CP phases coexist

@cite{keine-2020} ch. 4 argues that horizons and CP phases are
orthogonal constraints on syntactic locality:

- **Horizons** determine *selective opacity*: which operations can
  cross a given boundary. Probe-specific — different probes see
  different boundaries.

- **CP phases** determine *absolute opacity*: all material inside
  the phase complement is removed from the workspace (Spell-Out).
  This affects ALL operations uniformly, but leaves the phase edge
  (specifier) accessible.

The division of labor:
- Ā-extraction is possible but must proceed successive-cyclically
  (enforced by phases, not horizons)
- A-extraction is categorically blocked (enforced by horizons,
  not phases — [Spec,CP] is at the phase edge but still beyond
  the A-probe's horizon) -/

/-- Phase-horizon division of labor for English:
    - Phases allow Ā-extraction via successive cyclicity
      ([Spec,CP] is accessible to Ā-probe)
    - Horizons block A-extraction even from [Spec,CP]
      (CP contains C, which is [*A*]'s horizon) -/
theorem english_phase_horizon_division :
    -- Ā: CP transparent (probe can see [Spec,CP])
    englishCfg.ābar.transparentToLabel cPLabel = true ∧
    -- A: CP opaque (probe blocked by horizon)
    englishCfg.aMove.transparentToLabel cPLabel = false := by decide

/-- Hindi shows the same division: Ā can enter CP, A cannot. -/
theorem hindi_phase_horizon_division :
    hindiCfg.ābar.transparentToLabel cPLabel = true ∧
    hindiCfg.aMove.transparentToLabel cPLabel = false := by decide

end Keine2020
