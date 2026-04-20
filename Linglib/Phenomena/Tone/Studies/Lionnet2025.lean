import Linglib.Theories.Phonology.Autosegmental.RegisterTier
import Linglib.Fragments.Drubea.Prosody
import Linglib.Fragments.Numee.Prosody
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
    (@cite{lionnet-2025}). -/
theorem minimal_pairs_same_segments :
    monoMinimalPairs.all (fun (a, b) => a.form == b.form) = true := by
  decide

/-- The contrast in each minimal pair IS the register specification:
    one member is registerless, the other is σ1-downstepped. -/
theorem minimal_pairs_register_contrast :
    monoMinimalPairs.all (fun (a, b) =>
      a.pattern == .registerless && b.pattern == .σ1_downstepped) = true := by
  decide

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
    StemPattern.registerless.toSpecs 2 = [TRN.empty, TRN.empty] := by rfl

/-- ⁺CVV: downstep on first mora [l, ∅]. -/
theorem cvv_σ1_downstepped :
    StemPattern.σ1_downstepped.toSpecs 2 = [TRN.downstep, TRN.empty] := by rfl

/-- CV⁺V: downstep on second mora [∅, l]. -/
theorem cvPlusV_σ2_downstepped :
    StemPattern.σ2_downstepped.toSpecs 2 = [TRN.empty, TRN.downstep] := by rfl

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
    pitchDeltas [TRN.downstep, TRN.downstep, TRN.downstep, TRN.downstep] = [-1, -2, -3, -4] := by
  decide

theorem four_downsteps_terrace :
    realizePitch 4
      [TRN.downstep, TRN.downstep, TRN.downstep, TRN.downstep] = [3, 2, 1, 0] := by
  decide

/-- Registerless syllables following a downstep maintain the lowered
    register — they are realized at the same pitch as the downstepped
    syllable. -/
theorem registerless_maintains_lowered :
    realizePitch 4
      [TRN.downstep, TRN.empty, TRN.empty] = [3, 3, 3] := by
  decide

/-- A mixed sequence of downstepped and registerless syllables:
    each downstep creates a new lower plateau, registerless RBUs
    inherit the current register. -/
theorem mixed_terracing :
    realizePitch 4
      [TRN.downstep, TRN.downstep, TRN.empty, TRN.downstep, TRN.empty, TRN.empty, TRN.downstep] =
      [3, 2, 2, 1, 1, 1, 0] := by
  decide

-- ============================================================================
-- § 5: Pre-Downstep Raising (h-Epenthesis)
-- ============================================================================

/-- Abrupt h-epenthesis: insert `h` on the registerless RBU immediately
    preceding a downstep (cf. ex. 13b; @cite{lionnet-2025} §3.2, §4.4). -/
theorem h_epenthesis_abrupt :
    hEpenthesis [TRN.empty, TRN.downstep, TRN.empty] =
      [TRN.upstep, TRN.downstep, TRN.empty] := by rfl

/-- Spreading h-epenthesis: raising extends over the entire sequence
    of registerless syllables before a downstep
    (@cite{lionnet-2025} §3.2). -/
theorem h_epenthesis_spreads :
    hEpenthesisSpread [TRN.empty, TRN.empty, TRN.empty, TRN.downstep, TRN.empty] =
      [TRN.upstep, TRN.upstep, TRN.upstep, TRN.downstep, TRN.empty] := by rfl

-- ============================================================================
-- § 6: Utterance-Initial Neutralization
-- ============================================================================

/-- Utterance-initial downstep is not phonetically realized: there is
    no preceding register to contrast with (@cite{lionnet-2025} §3.5,
    §4.5). The realized pitch sequence is indistinguishable from a
    registerless initial. -/
theorem utt_initial_no_contrast :
    realizePitchUtterance 4 [TRN.downstep, TRN.empty] =
    realizePitch 4 [TRN.empty, TRN.empty] := by
  decide

/-- The contrast between registerless and downstepped IS maintained
    when a downstepped syllable follows: the initial registerless
    syllable undergoes pre-downstep raising, the initial downstepped
    one does not (@cite{lionnet-2025} §3.5, §4.5). The minimal pair
    `/goo ⁺mie/` 'wet Hibbertia' (registerless initial → h-epenthesis)
    vs `/⁺goo ⁺mie/` 'wet tree' (downstepped initial → no h-epenthesis)
    is the diagnostic. -/
theorem utt_initial_contrast_with_following_downstep :
    hEpenthesis [TRN.empty, TRN.downstep] = [TRN.upstep, TRN.downstep] ∧
    hEpenthesis [TRN.downstep, TRN.downstep] = [TRN.downstep, TRN.downstep] := ⟨rfl, rfl⟩

/-- The reason the contrast survives utterance-initial neutralization:
    `realizePitchUtterance` only suppresses the *phonetic* drop, leaving
    the underlying `l` in place to block h-epenthesis on itself. The
    underlying form is still culminative-sensitive
    (@cite{lionnet-2025} §3.5). -/
theorem utt_initial_l_underlyingly_active :
    -- Phonetically flat utterance-initially…
    realizePitchUtterance 4 [TRN.downstep, TRN.downstep] = realizePitch 4 [TRN.empty, TRN.downstep] ∧
    -- …but the underlying `l` blocks h-epenthesis on itself.
    hEpenthesis [TRN.downstep, TRN.downstep] = [TRN.downstep, TRN.downstep] := by
  refine ⟨by decide, rfl⟩

-- ============================================================================
-- § 7: Drubea Utterance-Final Raising (h%)
-- ============================================================================

/-- Drubea utterance-final raising: `h%` docks onto the final
    registerless syllable (@cite{lionnet-2025} §3.3, §4.8). The
    Numèè utterance-final downstep `⁺%` is formalized separately
    in §13 because its eligibility conditions (light CV + registerless
    penult) require explicit syllable structure. -/
theorem drubea_final_raising :
    applyBoundary [TRN.downstep, TRN.empty, TRN.empty] .h_pct =
      [TRN.downstep, TRN.empty, TRN.upstep] := by decide

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

/-- The `functionsContrastively` annotation on `drubeaDownstep` is not a
    free stipulation: it is *witnessed* by `monoMinimalPairs`. A pair of
    segmentally identical stems differing only in register (the form
    equality of `minimal_pairs_same_segments` plus the register
    contrast of `minimal_pairs_register_contrast`) is exactly what
    `functionsContrastively` claims for the lexical case
    (@cite{lionnet-2025} §3.10). -/
theorem drubea_contrastively_witnessed :
    drubeaDownstep.functionsContrastively = true ∧
    ∃ a b : StemEntry, a.form = b.form ∧ a.specs ≠ b.specs := by
  refine ⟨rfl, ?_⟩
  refine ⟨⟨"be", "death; to die", .registerless, 1⟩,
          ⟨"be", "niaouli tree", .σ1_downstepped, 1⟩, rfl, ?_⟩
  decide

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
  ⟨by decide, by decide⟩

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

-- ============================================================================
-- § 13: Numèè Boundary Downstep ⁺% (@cite{lionnet-2025} §3.4)
-- ============================================================================

/-! Numèè shares Drubea's underlying register inventory (registerless vs
    downstepped morae, no tone features) but diverges at the
    utterance-final boundary. The phenomenon, formalized in
    `Fragments/Numee/Prosody.lean`, has three properties worth pinning
    down here: it applies only to **light CV** finals, only when the
    **preceding syllable is registerless**, and produces a *stacked*
    double downstep when the final is itself underlyingly downstepped
    — preserving the registerless/downstepped contrast utterance-finally. -/

open Fragments.Numee.Prosody

/-- Boundary `⁺%` downsteps a registerless light CV final preceded by
    a registerless syllable (@cite{lionnet-2025} ex. 24). -/
theorem numee_registerless_final_single :
    numeeBoundaryEffect [jaa, niCoconut] = .single := by decide

/-- An *already-downstepped* light CV final receives a *second* downstep
    at the boundary — the stacked `⁺⁺` that preserves the underlying
    contrast in final position (@cite{lionnet-2025} ex. 25). The minimal
    pair `nĩ` 'coconut' (registerless) vs `⁺nĩ` 'breast' (downstepped)
    is realised utterance-finally as a one-step vs two-step pitch drop
    on the same surface segments. -/
theorem numee_downstepped_final_double :
    numeeBoundaryEffect [jaa, niBreast] = .double := by decide

/-- The boundary distinguishes the minimal pair: `niCoconut` triggers
    `single`, `niBreast` triggers `double`. This is the empirical
    signature that the underlying registerless/downstepped contrast
    survives the boundary process. -/
theorem numee_minimal_pair_distinguished :
    numeeBoundaryEffect [jaa, niCoconut] ≠ numeeBoundaryEffect [jaa, niBreast] := by
  decide

/-- A **heavy CVV** final blocks the boundary downstep — eligibility
    requires a light (monomoraic) final (@cite{lionnet-2025} ex. 26). -/
theorem numee_heavy_final_blocks :
    numeeBoundaryEffect [regCV, mii] = .none := by decide

/-- A **downstepped preceding syllable** blocks the boundary, even
    when the final is light CV and registerless
    (@cite{lionnet-2025} ex. 28: `⁺tĩĩ ku` 'three yams'). -/
theorem numee_after_downstepped_blocks :
    numeeBoundaryEffect [regCVV, beTii, ku] = .none := by decide

/-- Same blocking pattern with a different downstepped penult and
    different light CV final (@cite{lionnet-2025} ex. 29: `⁺paa kwɛ̃`
    'down sand'). -/
theorem numee_after_downstepped_blocks' :
    numeeBoundaryEffect [niCoconut, paa, kwe] = .none := by decide

/-- A bare light CV final with no preceding syllable does not trigger
    the boundary — the rule's structural description requires *two*
    syllables. -/
theorem numee_singleton_no_boundary :
    numeeBoundaryEffect [niCoconut] = .none := by decide

/-- Numèè syllables inherit the same register inventory as Drubea
    morphemes — the per-mora `TRN` list `niBreast` carries is
    `IsCulminative`, just like Drubea stems. The boundary process is
    *postlexical* and does not feed culminativity, which is a property
    of underlying lexical specifications. -/
theorem numee_lexical_culminative :
    IsCulminative niBreast.specs ∧
    IsCulminative beTii.specs ∧
    IsCulminative paa.specs := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Lionnet2025
