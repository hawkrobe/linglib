/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Tone.Register
import Linglib.Fragments.Drubea.Prosody
import Linglib.Fragments.Numee.Prosody
import Linglib.Studies.Hyman2006

/-!
# Lionnet (2025): tonal languages without tone

[lionnet-2025] analyses the word prosody of Drubea and Numèè (Oceanic, New Caledonia) as
consisting entirely of register features — an underlying downstep `l` and a postlexical
upstep `h` — with no tone features: the register-bearing unit is the mora, as the CV⁺V
three-way contrast shows; each native stem carries at most one downstep (culminativity);
the downstep meets [leben-2018]'s definitional properties; and the analysis is more
parsimonious than a tonal one (§5). Tone systems thereby split into tone-based and
register-based, enriching [hyman-2006]'s word-prosodic typology.

The register-only apparatus — culminativity, pre-downstep h-epenthesis in its abrupt and
spreading variants, and utterance-initial neutralisation — is the paper's; the terracing
realization it rides on is `Tone.Register`.
-/

namespace Lionnet2025

open Tone Drubea.Prosody

/-! ### The register-only apparatus -/

/-- **Register culminativity** (§3.10): at most one `[-raised]` node per stem. -/
abbrev IsCulminative (ts : List TRN) : Prop :=
  ts.countP (fun t => t.raised == some false) ≤ 1

/-- **Pre-downstep h-epenthesis** (§3.2, §4.4): an upstep replaces the registerless node
immediately before a downstep. An underlying downstep blocks the rule on itself — the
diagnostic that survives utterance-initial neutralisation. -/
def hEpenthesis : List TRN → List TRN
  | [] => []
  | [t] => [t]
  | TRN.empty :: TRN.downstep :: rest => TRN.upstep :: TRN.downstep :: hEpenthesis rest
  | t :: rest => t :: hEpenthesis rest

/-- **Spreading h-epenthesis** (§3.2): every registerless node before a downstep is
raised. -/
def hEpenthesisSpread : List TRN → List TRN
  | [] => []
  | TRN.downstep :: rest => TRN.downstep :: hEpenthesisSpread rest
  | TRN.upstep :: rest => TRN.upstep :: hEpenthesisSpread rest
  | TRN.empty :: rest =>
      let rest' := hEpenthesisSpread rest
      match rest' with
      | TRN.downstep :: _ | TRN.upstep :: _ => TRN.upstep :: rest'
      | _ => TRN.empty :: rest'
  | t :: rest => t :: hEpenthesisSpread rest

/-- **Utterance-initial neutralisation** (§3.5, §4.5): an initial `[-raised]` node is
realized at the baseline, there being no preceding register to contrast with. The feature
stays in the underlying form, blocking h-epenthesis on itself. -/
def realizePitchUtterance (level : Int) : List TRN → List Int
  | [] => []
  | t :: rest =>
      if t.raised = some false ∧ t.upper = none then level :: realizePitch level rest
      else realizePitch level (t :: rest)

/-! ### Segmental identity of minimal pairs -/

/-- Every monosyllabic minimal pair shares its segmental form: the contrast is the register
feature `l` alone. -/
theorem minimal_pairs_same_segments :
    monoMinimalPairs.all (fun (a, b) => a.form == b.form) = true := by
  decide

/-- The contrast in each minimal pair is the register specification: one member is
registerless, the other σ1-downstepped. -/
theorem minimal_pairs_register_contrast :
    monoMinimalPairs.all (fun (a, b) =>
      a.pattern == .registerless && b.pattern == .σ1_downstepped) = true := by
  decide

/-! ### Culminativity -/

/-- Every stem in the Drubea fragment is culminative: at most one `l` per stem (§3.10). -/
theorem all_stems_culminative :
    ∀ e ∈ allStems, IsCulminative e.specs := by
  decide

/-- Culminativity holds structurally for all three patterns at any mora count: each
pattern places at most one `l`. -/
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

/-! ### The CV⁺V three-way contrast: the mora as register-bearing unit -/

/-- The three register patterns give distinct mora-level specifications on bimoraic stems
(§3.7, §4.2). -/
theorem cvPlusV_three_way_distinct :
    StemPattern.registerless.toSpecs 2 ≠ StemPattern.σ1_downstepped.toSpecs 2 ∧
    StemPattern.registerless.toSpecs 2 ≠ StemPattern.σ2_downstepped.toSpecs 2 ∧
    StemPattern.σ1_downstepped.toSpecs 2 ≠ StemPattern.σ2_downstepped.toSpecs 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- CVV registerless: both morae unspecified. -/
theorem cvv_registerless :
    StemPattern.registerless.toSpecs 2 = [TRN.empty, TRN.empty] := by rfl

/-- ⁺CVV: downstep on the first mora. -/
theorem cvv_σ1_downstepped :
    StemPattern.σ1_downstepped.toSpecs 2 = [TRN.downstep, TRN.empty] := by rfl

/-- CV⁺V: downstep on the second mora. -/
theorem cvPlusV_σ2_downstepped :
    StemPattern.σ2_downstepped.toSpecs 2 = [TRN.empty, TRN.downstep] := by rfl

/-- On a monomoraic stem only two patterns are distinct: the σ2 pattern collapses to
registerless, there being no second mora to host the `l`. -/
theorem monomoraic_two_way :
    StemPattern.σ2_downstepped.toSpecs 1 = StemPattern.registerless.toSpecs 1 := by rfl

/-! ### Terracing -/

/-- Four consecutive downstepped monosyllables terrace, each one step lower than the last
(ex. 11, ex. 12): the deltas `[-1, -2, -3, -4]`; a baseline only anchors them. -/
theorem four_downsteps_deltas :
    pitchDeltas [TRN.downstep, TRN.downstep, TRN.downstep, TRN.downstep] = [-1, -2, -3, -4] := by
  decide

theorem four_downsteps_terrace :
    realizePitch 4 [TRN.downstep, TRN.downstep, TRN.downstep, TRN.downstep] = [3, 2, 1, 0] := by
  decide

/-- Registerless syllables after a downstep keep the lowered register. -/
theorem registerless_maintains_lowered :
    realizePitch 4 [TRN.downstep, TRN.empty, TRN.empty] = [3, 3, 3] := by
  decide

/-- Each downstep opens a new lower plateau; registerless morae inherit the current one. -/
theorem mixed_terracing :
    realizePitch 4
      [TRN.downstep, TRN.downstep, TRN.empty, TRN.downstep, TRN.empty, TRN.empty, TRN.downstep] =
      [3, 2, 2, 1, 1, 1, 0] := by
  decide

/-! ### Pre-downstep raising -/

/-- Abrupt h-epenthesis: `h` on the registerless mora immediately before a downstep
(ex. 13b). -/
theorem h_epenthesis_abrupt :
    hEpenthesis [TRN.empty, TRN.downstep, TRN.empty] =
      [TRN.upstep, TRN.downstep, TRN.empty] := by rfl

/-- The raised mora is realized above the baseline. -/
theorem h_epenthesis_raises_pitch :
    realizePitch 4 (hEpenthesis [TRN.empty, TRN.downstep, TRN.empty]) = [5, 4, 4] := by
  decide

/-- Spreading h-epenthesis: raising extends over the whole registerless stretch before a
downstep (§3.2). -/
theorem h_epenthesis_spreads :
    hEpenthesisSpread [TRN.empty, TRN.empty, TRN.empty, TRN.downstep, TRN.empty] =
      [TRN.upstep, TRN.upstep, TRN.upstep, TRN.downstep, TRN.empty] := by rfl

/-! ### Utterance-initial neutralisation -/

/-- An utterance-initial downstep is not realized: the pitch sequence is that of a
registerless initial (§3.5, §4.5). -/
theorem utt_initial_no_contrast :
    realizePitchUtterance 4 [TRN.downstep, TRN.empty] =
    realizePitch 4 [TRN.empty, TRN.empty] := by
  decide

/-- Only the first node is neutralised: a later downstep still drops the pitch. -/
theorem utt_initial_only_first :
    realizePitchUtterance 4 [TRN.downstep, TRN.downstep, TRN.empty] = [4, 3, 3] := by
  decide

/-- The contrast survives when a downstep follows: a registerless initial undergoes
pre-downstep raising, a downstepped one does not — `/goo ⁺mie/` 'wet Hibbertia' vs
`/⁺goo ⁺mie/` 'wet tree' (§3.5, §4.5). -/
theorem utt_initial_contrast_with_following_downstep :
    hEpenthesis [TRN.empty, TRN.downstep] = [TRN.upstep, TRN.downstep] ∧
    hEpenthesis [TRN.downstep, TRN.downstep] = [TRN.downstep, TRN.downstep] := ⟨rfl, rfl⟩

/-- Why it survives: neutralisation suppresses only the phonetic drop, and the underlying
`l` still blocks h-epenthesis on itself (§3.5). -/
theorem utt_initial_l_underlyingly_active :
    realizePitchUtterance 4 [TRN.downstep, TRN.downstep] =
        realizePitch 4 [TRN.empty, TRN.downstep] ∧
    hEpenthesis [TRN.downstep, TRN.downstep] = [TRN.downstep, TRN.downstep] := by
  refine ⟨by decide, rfl⟩

/-! ### Drubea utterance-final raising -/

/-- Drubea's `h%` docks onto the final registerless syllable (§3.3, §4.8); Numèè's
utterance-final downstep `⁺%` is below, its conditions needing syllable structure. -/
theorem drubea_final_raising :
    applyBoundary [TRN.downstep, TRN.empty, TRN.empty] .h_pct =
      [TRN.downstep, TRN.empty, TRN.upstep] := by decide

/-! ### Downstep properties -/

/-- [leben-2018]'s properties of downstep, as refined in §6.1: (a)–(c) definitional,
(d)–(f) cross-linguistic tendencies. -/
structure DownstepProperties where
  /-- (a) Affects the whole prosodic domain, not a single tone. -/
  affectsDomain : Bool
  /-- (b) Changes the register for what follows. -/
  changesRegister : Bool
  /-- (c) Cumulative: downsteps stack. -/
  isCumulative : Bool
  /-- (d) Utterance-initially, no phonetic contrast with the undownstepped. -/
  uttInitialNeutral : Bool
  /-- (e) Characteristically affects H tones. -/
  characteristicallyAffectsH : Bool
  /-- (f) Functions contrastively. -/
  functionsContrastively : Bool
  deriving Repr

/-- Drubea/Numèè downstep meets the three definitional properties ([leben-2018]: 2; §6.1).
Property (e) does not apply: the system has no H tones. -/
def drubeaDownstep : DownstepProperties where
  affectsDomain := true
  changesRegister := true
  isCumulative := true
  uttInitialNeutral := true
  characteristicallyAffectsH := false
  functionsContrastively := true

theorem drubea_core_properties :
    drubeaDownstep.affectsDomain ∧ drubeaDownstep.changesRegister ∧
      drubeaDownstep.isCumulative := ⟨rfl, rfl, rfl⟩

/-- `functionsContrastively` is witnessed by `monoMinimalPairs`: two stems with the same
segments and different register specifications (§3.10). -/
theorem drubea_contrastively_witnessed :
    drubeaDownstep.functionsContrastively = true ∧
    ∃ a b : StemEntry, a.form = b.form ∧ a.specs ≠ b.specs := by
  refine ⟨rfl, ?_⟩
  refine ⟨⟨"be", "death; to die", .registerless, 1⟩,
          ⟨"be", "niaouli tree", .σ1_downstepped, 1⟩, rfl, ?_⟩
  decide

/-! ### Register versus tonal analysis -/

/-- The primitives of an analysis (§4–§5): underlying primitives and postlexical
processes. -/
structure AnalysisInventory where
  underlyingPrimitives : Nat
  postlexicalProcesses : Nat
  deriving Repr, DecidableEq

/-- The register analysis (§4): one underlying primitive, `l`, and one postlexical
process, h-epenthesis. -/
def registerAnalysis : AnalysisInventory where
  underlyingPrimitives := 1
  postlexicalProcesses := 1

/-- The tonal alternative (§5): underlying L, epenthetic H and epenthetic downstep, with
OCP-driven downstep insertion and H-spreading — and a duplication (L and downstep both
encode the drop) and a conspiracy (two unrelated raisings with one phonetic effect). -/
def tonalAnalysis : AnalysisInventory where
  underlyingPrimitives := 3
  postlexicalProcesses := 2

/-- The register analysis is strictly more parsimonious. -/
theorem register_more_parsimonious :
    registerAnalysis.underlyingPrimitives < tonalAnalysis.underlyingPrimitives ∧
    registerAnalysis.postlexicalProcesses < tonalAnalysis.postlexicalProcesses :=
  ⟨by decide, by decide⟩

/-! ### Typology

Drubea is tonal by [hyman-2006]'s definition (3) — register enters lexical realization, as
the minimal pairs show — yet register-based rather than tone-based: a sub-distinction
within Hyman's tone prototype that he did not draw (§6.2). Its culminativity is register
culminativity, at most one `l` per stem, not Hyman's stress culminativity (definition (5b)),
which it lacks along with stress accent. -/

/-- Drubea is the first attested register-only word-prosodic system (§6.2): no stem
specifies `[upper]`. -/
theorem drubea_register_only : ∀ e ∈ allStems, IsRegisterOnly e.specs := by decide

/-- Tonal by definition (3), without stress accent: +T, −SA, the cell of Yoruba. -/
theorem drubea_tone_only :
    wordProsody.tone = true ∧ Hyman2006.quadrant wordProsody = .toneOnly ∧
      Hyman2006.quadrant wordProsody = Hyman2006.quadrant Hyman2006.yoruba := ⟨rfl, rfl, rfl⟩

/-- Register culminativity holds while stress accent, hence Hyman's culminativity, is
absent. -/
theorem drubea_register_culminative_not_stress :
    (∀ e ∈ allStems, IsCulminative e.specs) ∧ wordProsody.stressAccent = false :=
  ⟨all_stems_culminative, rfl⟩

/-! ### Numèè boundary downstep

Numèè shares Drubea's register inventory but diverges at the utterance-final boundary
(§3.4): the boundary downstep `⁺%` applies only to a light CV final after a registerless
syllable, and stacks a second downstep on a final that is itself downstepped, preserving
the contrast utterance-finally. The process is `Fragments/Numee/Prosody`. -/

open Numee.Prosody

/-- `⁺%` downsteps a registerless light CV final after a registerless syllable (ex. 24). -/
theorem numee_registerless_final_single :
    numeeBoundaryEffect [jaa, niCoconut] = .single := by decide

/-- A downstepped light CV final receives a second downstep — the stacked `⁺⁺` (ex. 25):
`nĩ` 'coconut' vs `⁺nĩ` 'breast' surface as a one-step vs two-step drop. -/
theorem numee_downstepped_final_double :
    numeeBoundaryEffect [jaa, niBreast] = .double := by decide

/-- The boundary distinguishes the minimal pair. -/
theorem numee_minimal_pair_distinguished :
    numeeBoundaryEffect [jaa, niCoconut] ≠ numeeBoundaryEffect [jaa, niBreast] := by
  decide

/-- A heavy CVV final blocks the boundary downstep (ex. 26). -/
theorem numee_heavy_final_blocks :
    numeeBoundaryEffect [regCV, mii] = .none := by decide

/-- A downstepped preceding syllable blocks it, even before a light registerless final
(ex. 28, `⁺tĩĩ ku` 'three yams'). -/
theorem numee_after_downstepped_blocks :
    numeeBoundaryEffect [regCVV, beTii, ku] = .none := by decide

/-- The same, with another downstepped penult (ex. 29, `⁺paa kwɛ̃` 'down sand'). -/
theorem numee_after_downstepped_blocks' :
    numeeBoundaryEffect [niCoconut, paa, kwe] = .none := by decide

/-- A lone light CV final does not trigger the boundary: its structural description needs
two syllables. -/
theorem numee_singleton_no_boundary :
    numeeBoundaryEffect [niCoconut] = .none := by decide

/-- Numèè syllables carry the same culminative register inventory as Drubea stems; the
boundary process is postlexical and does not feed culminativity. -/
theorem numee_lexical_culminative :
    IsCulminative niBreast.specs ∧ IsCulminative beTii.specs ∧ IsCulminative paa.specs := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Lionnet2025
