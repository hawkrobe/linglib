import Linglib.Theories.Phonology.Autosegmental.RegisterTier
import Linglib.Fragments.Drubea.Prosody
import Linglib.Phenomena.Tone.Studies.Hyman2006

/-!
# Lionnet (2025): Tonal Languages Without Tone
@cite{lionnet-2025}

Tonal languages without tone: downstep in Drubea and Numèè
(Oceanic, New Caledonia). *Phonology* 42, e23, 1–43.

## Key claims formalized

1. The word-prosodic system of Drubea and Numèè consists entirely of
   register features — underlying downstep (`l`) and postlexical
   upstep (`h`) — with **no tone features**.

2. The register-bearing unit (RBU) is the **mora**, not the syllable,
   evidenced by the CV⁺V three-way contrast.

3. **Culminativity**: each native stem contains at most one downstep.

4. Drubea/Numèè downstep satisfies the core definitional properties
   of downstep cross-linguistically (@cite{leben-2018}).

5. Tonal systems split into **tone-based** (paradigmatic) and
   **register-based** (syntagmatic), enriching @cite{hyman-2006}'s
   word-prosodic typology.

6. The register analysis is more parsimonious than the tonal
   alternative: 1 underlying primitive + 1 postlexical process
   vs. 3 + 2 (@cite{lionnet-2025} §5).
-/

namespace Lionnet2025

open Phonology.Autosegmental.RegisterTier
open Fragments.Drubea.Prosody

-- ============================================================================
-- § 1: Segmental Identity of Minimal Pairs
-- ============================================================================

/-- Every monosyllabic minimal pair shares the same segmental form.
    The contrast is **purely prosodic** — the register feature `l` is
    the only difference between the two members of each pair
    (@cite{lionnet-2025}: ex. 4). -/
theorem minimal_pairs_same_segments :
    monoMinimalPairs.all (fun (a, b) => a.form == b.form) = true := by
  native_decide

/-- The contrast in each minimal pair IS the register specification:
    one member is registerless, the other is σ1-downstepped. -/
theorem minimal_pairs_register_contrast :
    monoMinimalPairs.all (fun (a, b) =>
      a.pattern == .registerless && b.pattern == .σ1_downstepped) = true := by
  native_decide

-- ============================================================================
-- § 2: Culminativity
-- ============================================================================

/-- Every stem in the Drubea fragment satisfies culminativity:
    at most one `l` feature per stem (@cite{lionnet-2025} §3.10). -/
theorem all_stems_culminative :
    ∀ e ∈ allStems, IsCulminative e.specs := by
  decide

/-- Culminativity holds structurally for all three patterns at any
    mora count: each pattern places at most one `l`. -/
theorem pattern_culminative_0 (p : StemPattern) :
    IsCulminative (p.toSpecs 0) := by cases p <;> decide
theorem pattern_culminative_1 (p : StemPattern) :
    IsCulminative (p.toSpecs 1) := by cases p <;> decide
theorem pattern_culminative_2 (p : StemPattern) :
    IsCulminative (p.toSpecs 2) := by cases p <;> decide
theorem pattern_culminative_3 (p : StemPattern) :
    IsCulminative (p.toSpecs 3) := by cases p <;> decide
theorem pattern_culminative_4 (p : StemPattern) :
    IsCulminative (p.toSpecs 4) := by cases p <;> decide

-- ============================================================================
-- § 3: CV⁺V Three-Way Contrast (mora as RBU)
-- ============================================================================

/-- The three register patterns produce distinct mora-level specifications
    on bimoraic stems, confirming the mora as the RBU
    (@cite{lionnet-2025} §3.7, §4.2). -/
theorem cvPlusV_three_way_distinct :
    StemPattern.registerless.toSpecs 2 ≠ StemPattern.σ1_downstepped.toSpecs 2 ∧
    StemPattern.registerless.toSpecs 2 ≠ StemPattern.σ2_downstepped.toSpecs 2 ∧
    StemPattern.σ1_downstepped.toSpecs 2 ≠ StemPattern.σ2_downstepped.toSpecs 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- CVV registerless: both morae unspecified [∅, ∅]. -/
theorem cvv_registerless :
    StemPattern.registerless.toSpecs 2 = [none, none] := by rfl

/-- ⁺CVV: downstep on first mora [l, ∅]. -/
theorem cvv_σ1_downstepped :
    StemPattern.σ1_downstepped.toSpecs 2 = [some .l, none] := by rfl

/-- CV⁺V: downstep on second mora [∅, l]. -/
theorem cvPlusV_σ2_downstepped :
    StemPattern.σ2_downstepped.toSpecs 2 = [none, some .l] := by rfl

/-- With only 1 mora (monomoraic CV), only two patterns are distinct:
    registerless and σ1-downstepped. The σ2 pattern collapses to
    registerless (no second mora to host the `l`). -/
theorem monomoraic_two_way :
    StemPattern.σ2_downstepped.toSpecs 1 = StemPattern.registerless.toSpecs 1 := by rfl

-- ============================================================================
-- § 4: Terracing (Register Realization)
-- ============================================================================

/-- Four consecutive downstepped monosyllables produce terracing:
    each is realized one step lower than the preceding
    (cf. ex. 11: /⁺ɲi ⁺mwa ⁺ŋii ⁺me/ 'They said that…';
    ex. 12: /⁺mwa ⁺ŋii ⁺yoo ⁺ne/ in Figure 7).

    The theory-primary content is the delta sequence `[-1, -2, -3, -4]`:
    each downstep adds another step of cumulative descent. The offset-4
    realization below is just an arbitrary anchoring of those deltas. -/
theorem four_downsteps_deltas :
    pitchDeltas [some .l, some .l, some .l, some .l] = [-1, -2, -3, -4] := by
  decide

theorem four_downsteps_terrace :
    realizePitch 4
      [some .l, some .l, some .l, some .l] = [3, 2, 1, 0] := by
  decide

/-- Registerless syllables following a downstep maintain the lowered
    register — they are realized at the same pitch as the downstepped
    syllable (cf. ex. 7–8, Figures 3–4). -/
theorem registerless_maintains_lowered :
    realizePitch 4
      [some .l, none, none] = [3, 3, 3] := by
  native_decide

/-- A mixed sequence of downstepped and registerless syllables:
    each downstep creates a new lower plateau
    (cf. ex. 15: /⁺ne-⁺boo-V ⁺ya yaa ⁺me a-⁺te/). -/
theorem mixed_terracing :
    realizePitch 4
      [some .l, some .l, none, some .l, none, none, some .l] =
      [3, 2, 2, 1, 1, 1, 0] := by
  native_decide

-- ============================================================================
-- § 5: Pre-Downstep Raising (h-Epenthesis)
-- ============================================================================

/-- Abrupt h-epenthesis: insert `h` on the registerless RBU immediately
    preceding a downstep (cf. ex. 13b; @cite{lionnet-2025} §3.2, §4.4). -/
theorem h_epenthesis_abrupt :
    hEpenthesis [none, some .l, none] =
      [some .h, some .l, none] := by rfl

/-- After h-epenthesis, the raised RBU is realized above baseline,
    creating a sharper contrast with the following downstep
    (cf. Figure 8). -/
theorem h_epenthesis_pitch :
    realizePitch 4 (hEpenthesis [none, some .l, none]) = [5, 4, 4] := by
  native_decide

/-- Spreading h-epenthesis: raising extends over the entire sequence
    of registerless syllables before a downstep
    (cf. ex. 16: /⁺tã ⁺mwa ne-re ma⁺a/; @cite{lionnet-2025} §3.2). -/
theorem h_epenthesis_spreads :
    hEpenthesisSpread [none, none, none, some .l, none] =
      [some .h, some .h, some .h, some .l, none] := by rfl

/-- Registerless RBUs get h-epenthesis before a downstep;
    downstepped RBUs do NOT — they are already `l`-bearing
    (cf. ex. 32 vs 33; @cite{lionnet-2025} §4.5). -/
theorem registerless_gets_h_downstepped_does_not :
    hEpenthesis [none, some .l] = [some .h, some .l] ∧
    hEpenthesis [some .l, some .l] = [some .l, some .l] := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Utterance-Initial Neutralization
-- ============================================================================

/-- Utterance-initial downstep is not phonetically realized: there is
    no preceding register to contrast with
    (cf. ex. 30 vs 31; @cite{lionnet-2025} §3.5, §4.5). -/
theorem utt_initial_no_contrast :
    realizePitch 4 (uttInitialNeutralize [some .l, none]) =
    realizePitch 4 [none, none] := by
  native_decide

/-- The contrast between registerless and downstepped IS maintained
    when a downstepped syllable follows: the initial registerless
    syllable undergoes pre-downstep raising, the initial downstepped
    one does not (cf. ex. 32 vs 33; @cite{lionnet-2025} §3.5). -/
theorem utt_initial_contrast_with_following_downstep :
    -- /goo ⁺mie/ 'wet Hibbertia': registerless initial → h-epenthesis
    hEpenthesis [none, some .l] = [some .h, some .l] ∧
    -- /⁺goo ⁺mie/ 'wet tree': downstepped initial → no h-epenthesis
    hEpenthesis [some .l, some .l] = [some .l, some .l] := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Utterance-Final Prosody
-- ============================================================================

/-- Drubea utterance-final raising: h% docks onto the final
    registerless syllable (cf. ex. 20: /⁺taa bee pwi +⁺%/;
    @cite{lionnet-2025} §3.3, §4.8). -/
theorem drubea_final_raising :
    applyBoundary [some .l, none, none] .h_pct =
      [some .l, none, some .h] := by native_decide

/-- Numèè utterance-final lowering: l% docks onto final light CV
    syllable after a registerless syllable
    (cf. ex. 24–25; @cite{lionnet-2025} §3.4, §4.8). -/
theorem numee_final_lowering :
    applyBoundary [none, none] .l_pct =
      [none, some .l] := by native_decide

/-- Boundary l% after a downstepped syllable: the final registerless
    syllable acquires a boundary downstep, producing two consecutive
    pitch drops (@cite{lionnet-2025} §3.4, §4.8). -/
theorem boundary_after_downstep :
    realizePitch 4 (applyBoundary [some .l, none] .l_pct) =
      [3, 2] := by
  native_decide

-- ============================================================================
-- § 8: Downstep Properties (Leben 2018)
-- ============================================================================

/-- Drubea/Numèè downstep satisfies all three core definitional
    properties of downstep (@cite{leben-2018}: 2;
    @cite{lionnet-2025} §6.1):

    (a) affects the entire prosodic domain (not just one tone)
    (b) changes the register for what follows
    (c) cumulative: multiple downsteps stack -/
def drubeaDownstep : DownstepProperties where
  affectsDomain          := true
  changesRegister        := true
  isCumulative           := true
  uttInitialNeutral      := true   -- tendency (d)
  characteristicallyAffectsH := false  -- N/A: no H tones in the system
  functionsContrastively := true   -- tendency (f): lexical contrast

theorem drubea_core_properties :
    drubeaDownstep.affectsDomain ∧
    drubeaDownstep.changesRegister ∧
    drubeaDownstep.isCumulative := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 9: Register vs Tonal Analysis
-- ============================================================================

/-- The register analysis of Drubea/Numèè (@cite{lionnet-2025} §4):
    1 underlying primitive (the `l` feature) and
    1 postlexical process (h-epenthesis). -/
def registerAnalysis : AnalysisInventory where
  underlyingPrimitives := 1  -- just `l`
  postlexicalProcesses := 1  -- h-epenthesis

/-- The competing tonal analysis (@cite{lionnet-2025} §5):
    3 representational primitives (underlying L + epenthetic H +
    epenthetic downstep ⁺) and 2 postlexical processes (OCP-driven
    downstep insertion + H-spreading for pre-downstep raising).

    Additionally, the tonal analysis suffers from a duplication problem
    (both L and downstep encode the same pitch drop) and a conspiracy
    problem (raising of H before L and of L before ⁺L are analysed as
    unrelated despite the same phonetic effect). -/
def tonalAnalysis : AnalysisInventory where
  underlyingPrimitives := 3  -- underlying L + epenthetic H + epenthetic ⁺
  postlexicalProcesses := 2  -- OCP downstep insertion + H-spreading

/-- The register analysis is strictly more parsimonious. -/
theorem register_more_parsimonious :
    registerAnalysis.underlyingPrimitives < tonalAnalysis.underlyingPrimitives ∧
    registerAnalysis.postlexicalProcesses < tonalAnalysis.postlexicalProcesses :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 10: Typological Classification
-- ============================================================================

/-- Drubea is the first attested **register-only** word-prosodic system:
    tonal contrasts defined entirely syntagmatically, with no paradigmatic
    tone features (@cite{lionnet-2025} §6.2, Conclusion). -/
theorem drubea_is_register_based :
    wordProsodicType = .registerBased := rfl

-- ============================================================================
-- § 11: Connection to Hyman 2006
-- ============================================================================

/-- Drubea is +tone under @cite{hyman-2006}'s definition (3): pitch
    (via register features) enters into the lexical realization of
    morphemes. The minimal pairs in §1 demonstrate this directly. -/
theorem drubea_is_tonal_hyman :
    Hyman2006.isTonalUnderHyman wordProsodicType = true := rfl

/-- Drubea enriches Hyman's typology: it is a tonal system (by def. 3)
    that is register-based rather than tone-based — a sub-distinction
    within Hyman's tone prototype that he did not draw. -/
theorem drubea_enriches_hyman :
    Hyman2006.isTonalUnderHyman .registerBased = true ∧
    wordProsodicType = .registerBased := ⟨rfl, rfl⟩

/-- Drubea is +T, −SA under @cite{hyman-2006}'s 2×2 typology
    (same quadrant as Yoruba). -/
theorem drubea_quadrant :
    Hyman2006.drubea.quadrant = .toneOnly := rfl

-- ============================================================================
-- § 12: Culminativity — Register vs Stress
-- ============================================================================

/-- Drubea satisfies register culminativity: every stem in the fragment
    has at most one `l` feature. This is `IsCulminative` from
    RegisterTier, applied to all stems in §2.

    This is NOT @cite{hyman-2006}'s stress culminativity (def. 5b),
    which concerns primary stress per word. Drubea has no stress
    accent system — OBLHEAD does not apply. The two uses of
    "culminativity" are formally parallel but phonologically distinct
    (see `Hyman2006.CulminativityDomain`). -/
theorem drubea_register_culminative_not_stress :
    -- Register culminativity holds (Lionnet)
    (∀ e ∈ allStems, IsCulminative e.specs) ∧
    -- Stress accent is absent (Hyman)
    Hyman2006.drubea.hasStressAccent = false :=
  ⟨all_stems_culminative, rfl⟩

end Lionnet2025
