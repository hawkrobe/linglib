import Linglib.Core.Prosody
import Linglib.Theories.Phonology.Autosegmental.RegisterTier
import Linglib.Theories.Syntax.CCG.Intonation
import Linglib.Theories.Semantics.Focus.KratzerSelkirk2020

/-!
# Beckman & Pierrehumbert (1986) @cite{beckman-pierrehumbert-1986}

Intonational Structure in Japanese and English. *Phonology Yearbook* 3: 255–309.

## Core Contributions

This paper establishes the prosodic hierarchy above the word — accentual
phrase (AP), intermediate phrase (ip), intonation phrase (IP) — via
cross-linguistic comparison of Japanese and English intonation. It
introduced three key analytical innovations:

1. **Accentual phrase**: the domain of pitch accent distribution, delimited
   by a phrasal H and boundary L in Japanese. At most one pitch accent
   per AP (culminativity at the phrasal level).

2. **Catathesis**: pitch range compression triggered by bitonal pitch accents.
   The domain is the intermediate phrase. Blocked by ip boundaries.
   Chaining produces descending F0 staircases.

3. **Intermediate phrase**: the domain of catathesis. In Japanese, 1–3 APs,
   bounded by pause or glottalization + L boundary tone. In English,
   decomposed from @cite{pierrehumbert-1980}'s single "phrase accent" into
   an ip-terminal tone (phrase accent) distinct from the IP boundary tone.

The paper also demonstrates that Japanese tonal patterns are much sparser
than earlier autosegmental accounts assumed — closer to English in their
distribution of tones to tone-bearing units.

## Bridge to RegisterTier

Catathesis is formalized as register-based downstep applied to the
intonation domain: each bitonal pitch accent within an intermediate
phrase contributes a register `l` feature, producing cumulative terracing
via `realizePitch` (@cite{snider-1999}, @cite{lionnet-2025}). The ip
boundary resets the register, preventing catathesis from propagating
across phrases.
-/

namespace Phenomena.Intonation.Studies.BeckmanPierrehumbert1986

open Core.Prosody
open Phonology.Autosegmental.RegisterTier

-- ============================================================================
-- § 1: Accentual Phrase (§2.2)
-- ============================================================================

/-- An accentual phrase: the lowest level of prosodic phrasing defined
    by the intonation pattern.

    In Japanese, delimited by a phrasal H and boundary L tone. Contains
    at most one pitch accent. An unaccented AP has the rising pitch shape
    (L → phrasal H) but no accent HL fall (§2.2).

    In English, the AP is less firmly established. It corresponds to the
    domain of a single pitch accent plus the surrounding material up to
    the next accent or phrase boundary (§2.4).

    Accentedness is derived from the accent field: an AP is accented iff
    its accent is non-null. -/
structure AccentualPhrase where
  /-- Pitch accent type (null if unaccented) -/
  accent : PitchAccent
  /-- Number of words grouped in this phrase -/
  nWords : Nat
  deriving Repr, DecidableEq

/-- An AP is accented iff it has a non-null accent. -/
def AccentualPhrase.isAccented (ap : AccentualPhrase) : Bool :=
  ap.accent != .null

-- **Culminativity at the AP level** (§2.2, §2.3): an accentual phrase
-- contains at most one pitch accent. Enforced structurally —
-- `AccentualPhrase` has a single `accent` field. When two lexically
-- accented words are grouped in the same AP, one accent must be deleted.

-- ============================================================================
-- § 2: Catathesis as Register Downstep (§3)
-- ============================================================================

/-- Convert a sequence of APs into register specifications.

    Each bitonal accent contributes a register `l` (downstep) feature;
    non-bitonal or null accents contribute no register feature (registerless).
    This bridges catathesis to @cite{snider-1999}'s RegisterTier: the
    descending staircase in catathesis chains (Fig. 11) is the same
    terracing effect produced by cumulative register `l` features. -/
def catathesisToRegisterSpecs (aps : List AccentualPhrase) : List RegisterSpec :=
  aps.map (λ ap => if ap.accent.isBitonal then some .l else none)

/-- **Catathesis produces terracing** (§3, Fig. 11): a sequence of
    bitonal accents within an ip produces a descending staircase.
    This follows from `realizePitch` applied to the register specs. -/
theorem catathesis_terracing (n : Nat) :
    realizePitch n [some .l, some .l] = [n - 1, n - 1 - 1] := by
  simp [realizePitch]

/-- Catathesis lowers pitch: after one bitonal accent, the pitch is
    strictly lower than the starting level (for nonzero baseline). -/
theorem catathesis_lowers (n : Nat) :
    (realizePitch n [some .l]).head? = some (n - 1) := by
  simp [realizePitch]

/-- Count catathesis applications in a sequence of APs. -/
def catathesisCount (aps : List AccentualPhrase) : Nat :=
  aps.filter (·.accent.isBitonal) |>.length

/-- An ip with no bitonal accents has zero catathesis — no pitch
    compression occurs. -/
theorem no_bitonal_no_catathesis (aps : List AccentualPhrase)
    (h : ∀ ap ∈ aps, ap.accent.isBitonal = false) :
    catathesisCount aps = 0 := by
  simp only [catathesisCount]
  rw [List.filter_eq_nil_iff.mpr (by intro a ha; simp [h a ha])]
  simp

-- ============================================================================
-- § 3: Catathesis ≠ Downdrift (§3.1)
-- ============================================================================

-- @cite{beckman-pierrehumbert-1986} §3.1: catathesis differs fundamentally
-- from downdrift in African tone languages. Downdrift is triggered by any
-- H L H sequence; catathesis is triggered specifically by the HL of the
-- *accent*. In Japanese, every unaccented AP has a phrasal H + boundary L,
-- but only accented APs trigger catathesis.

/-- Catathesis is triggered by the accent HL, not by any HL sequence.
    An unaccented AP (with phrasal H + boundary L) does NOT trigger
    catathesis (§3.1). -/
theorem unaccented_no_catathesis :
    PitchAccent.null.isBitonal = false := rfl

-- ============================================================================
-- § 4: Intermediate Phrase — Domain of Catathesis (§4)
-- ============================================================================

/-- An intermediate phrase: a sequence of accentual phrases terminated
    by a phrase accent.

    @cite{beckman-pierrehumbert-1986} §4.1: in Japanese, the ip is the
    domain of catathesis. It can be as short as a single AP and seldom
    contains more than three. Its boundary is marked by pause or
    glottalization, and the phrase-final L tone provides evidence for
    disjuncture.

    §4.3: in English, the ip is reanalyzed from @cite{pierrehumbert-1980}'s
    framework. The phrase accent (H or L) is terminal to the ip, while
    the boundary tone is terminal to the IP. -/
structure IntermediatePhrase where
  /-- Accentual phrases within this ip -/
  aps : List AccentualPhrase
  /-- Phrase accent: terminal tone of the ip -/
  phraseAccent : PhraseAccent
  /-- Non-empty: an ip contains at least one AP -/
  aps_nonempty : aps ≠ [] := by decide
  deriving Repr

/-- An intonation phrase: one or more intermediate phrases terminated
    by a boundary tone (§4.2). -/
structure IntonationPhrase where
  /-- Intermediate phrases within this IP -/
  ips : List IntermediatePhrase
  /-- Boundary tone: terminal tone of the IP -/
  boundaryTone : BoundaryTone
  /-- Non-empty -/
  ips_nonempty : ips ≠ [] := by decide
  deriving Repr

/-- The terminal contour of an IP is composed from the phrase accent
    of its final ip and the IP boundary tone. This is the structural
    decomposition that @cite{beckman-pierrehumbert-1986} §4.2–4.3
    establish and that @cite{steedman-2000} uses in the CCG `Tune` type. -/
def IntonationPhrase.terminalContour (ip : IntonationPhrase) : TerminalContour :=
  let lastIp := ip.ips.getLast ip.ips_nonempty
  ⟨lastIp.phraseAccent, ip.boundaryTone⟩

/-- Register specs within a single ip: catathesis chains. -/
def ipRegisterSpecs (ip : IntermediatePhrase) : List RegisterSpec :=
  catathesisToRegisterSpecs ip.aps

/-- Register specs across an IP: each ip resets the register.
    This is the structural basis for "catathesis is blocked by ip
    boundaries" (§4.1, §4.4, Figs. 17–18 vs. 12–13).

    Each ip gets independent register specs — the `l` features from
    one ip do not propagate into the next. -/
def ipRegisterSpecsAcrossIps (ips : List IntermediatePhrase)
    : List (List RegisterSpec) :=
  ips.map ipRegisterSpecs


-- ============================================================================
-- § 5: Cross-linguistic Comparison (§2.5, §3.3, §6)
-- ============================================================================

/-- Where catathesis takes effect relative to the triggering accent.

    @cite{beckman-pierrehumbert-1986} §3.3: in Japanese, catathesis
    applies within the accent itself (affecting the trailing L). In
    English, catathesis applies after the second tone of the triggering
    bitonal accent. -/
inductive CatathesisTiming where
  | withinAccent  -- Japanese: affects the L of H*+L
  | afterAccent   -- English: affects tones after the bitonal accent
  deriving Repr, DecidableEq

/-- Language-specific intonation system parameters.

    @cite{beckman-pierrehumbert-1986} §6: Japanese and English share the
    same prosodic hierarchy but differ in how accents relate to the lexicon,
    the size of the pitch accent inventory, and whether unaccented phrases
    are possible. -/
structure IntonationSystem where
  /-- How accents are specified (lexical vs postlexical) -/
  accentSpec : AccentSpecification
  /-- The set of contrastive pitch accent shapes (excluding null) -/
  accentShapes : List PitchAccent
  /-- Whether lexically unaccented words/phrases exist -/
  hasUnaccented : Bool
  /-- Whether the accentual phrase boundary L is always present -/
  apBoundaryLAlwaysPresent : Bool
  /-- When catathesis applies relative to the triggering accent (§3.3) -/
  catathesisTiming : CatathesisTiming
  deriving Repr

/-- Number of contrastive accent shapes — derived, not stipulated. -/
def IntonationSystem.accentInventorySize (sys : IntonationSystem) : Nat :=
  sys.accentShapes.length

/-- Japanese intonation system (§2, §6):
    - Accent location is lexical (H*+L at specified mora)
    - Single accent shape
    - Unaccented words exist (and are common)
    - Boundary L is always present -/
def japanese : IntonationSystem :=
  { accentSpec := .lexical
    accentShapes := [.H_star_plus_L]
    hasUnaccented := true
    apBoundaryLAlwaysPresent := true
    catathesisTiming := .withinAccent }

/-- English intonation system (§2, §6):
    - Accent shape is postlexical (chosen by intonation)
    - Six contrastive accent shapes
    - Every content word has an accentable syllable
    - AP boundary is less clearly defined -/
def english : IntonationSystem :=
  { accentSpec := .postlexical
    accentShapes := [.H_star, .L_star, .H_star_plus_L,
                     .H_plus_L_star, .L_star_plus_H, .L_plus_H_star]
    hasUnaccented := false
    apBoundaryLAlwaysPresent := false
    catathesisTiming := .afterAccent }

/-- Japanese has lexical accent specification. -/
theorem japanese_lexical : japanese.accentSpec = .lexical := rfl

/-- English has postlexical accent specification. -/
theorem english_postlexical : english.accentSpec = .postlexical := rfl

/-- Japanese has fewer accent shapes than English (derived from
    the actual accent lists, not a stipulated number). -/
theorem japanese_smaller_inventory :
    japanese.accentInventorySize < english.accentInventorySize := by decide

/-- Japanese uses exactly one accent shape. -/
theorem japanese_one_accent : japanese.accentInventorySize = 1 := rfl

/-- English uses exactly six accent shapes. -/
theorem english_six_accents : english.accentInventorySize = 6 := rfl

/-- All Japanese accents are bitonal (and therefore trigger catathesis). -/
theorem japanese_accents_all_bitonal :
    japanese.accentShapes.all (·.isBitonal) = true := rfl

/-- Not all English accents are bitonal — H* and L* are monotonal. -/
theorem english_has_monotonal :
    english.accentShapes.all (·.isBitonal) = false := rfl

-- @cite{beckman-pierrehumbert-1986} §5: two supra-phrasal processes operate
-- above the ip level. **Final lowering** compresses pitch range near the end
-- of a declarative utterance; its domain appears to be discourse-controlled
-- (not a fixed phonological unit). **Declination** is a gradual time-dependent
-- lowering (~10 Hz/sec), independent of prosodic structure. Both exist in
-- Japanese and (probably) English. Neither is catathesis — catathesis is
-- structurally bounded by the ip; these operate above it.

-- ============================================================================
-- § 6: Worked Examples
-- ============================================================================

/-- An accented AP (e.g., *uma'i* 'delicious', Fig. 6a). -/
def accentedAP : AccentualPhrase := ⟨.H_star_plus_L, 1⟩

/-- An unaccented AP (e.g., *mame* 'beans', Fig. 6). -/
def unaccentedAP : AccentualPhrase := ⟨.null, 1⟩

/-- Two-AP ip: accented + unaccented (Figs. 3, 5). Catathesis
    applies once — the unaccented AP is in a lower pitch range. -/
def twoAP_ip : IntermediatePhrase :=
  { aps := [accentedAP, unaccentedAP], phraseAccent := .L }

/-- The register specs for this ip show one downstep. -/
theorem twoAP_ip_specs :
    ipRegisterSpecs twoAP_ip = [some .l, none] := rfl

/-- Pitch realization: from baseline 4, the accented AP is at 3
    (downstepped by catathesis) and the unaccented AP stays at 3. -/
theorem twoAP_ip_pitch :
    realizePitch 4 (ipRegisterSpecs twoAP_ip) = [3, 3] := by decide

/-- Three-AP ip: accented + accented + unaccented (staircase, Fig. 11). -/
def threeAP_ip : IntermediatePhrase :=
  { aps := [accentedAP, accentedAP, unaccentedAP], phraseAccent := .L }

/-- Two downsteps produce a two-level staircase. -/
theorem threeAP_ip_specs :
    ipRegisterSpecs threeAP_ip = [some .l, some .l, none] := rfl

/-- Pitch realization: 4 → 3 → 2 → 2 (descending staircase). -/
theorem threeAP_ip_pitch :
    realizePitch 4 (ipRegisterSpecs threeAP_ip) = [3, 2, 2] := by decide

/-- Catathesis blocking: same APs split across two ips. The second ip
    starts at full pitch range, not at the compressed level. -/
def split_ips : List IntermediatePhrase :=
  [{ aps := [accentedAP], phraseAccent := .L },
   { aps := [accentedAP, unaccentedAP], phraseAccent := .L }]

/-- The register specs are independent per ip. -/
theorem split_ips_specs :
    ipRegisterSpecsAcrossIps split_ips = [[some .l], [some .l, none]] := rfl

/-- Each ip starts from its own baseline — catathesis does not leak
    across the ip boundary. The first ip has pitch [3] (from baseline 4);
    the second ip independently has [3, 3]. -/
theorem split_ips_pitch_independent :
    (split_ips.map (realizePitch 4 ∘ ipRegisterSpecs))
    = [[3], [3, 3]] := by decide

/-- Compare: if there were no ip boundary, all three APs would be in
    one catathesis chain, producing [3, 2, 2] instead of [3] + [3, 3].
    The second AP is at pitch 3 (not 2) because the boundary resets
    the register. -/
theorem catathesis_without_boundary :
    realizePitch 4 (catathesisToRegisterSpecs [accentedAP, accentedAP, unaccentedAP])
    = [3, 2, 2] := by decide

-- ============================================================================
-- § 7: Bridge to CCG Intonation (@cite{steedman-2000})
-- ============================================================================

open CCG.Intonation

/-- Construct a CCG Tune from a B&P IntonationPhrase and a pitch accent.
    The tune's terminal contour is the IP's terminal contour —
    the same phrase accent + boundary tone decomposition that
    @cite{steedman-2000} uses for prosodic CCG categories. -/
def ipToTune (ip : IntonationPhrase) (accent : PitchAccent) : Tune :=
  ⟨accent, ip.terminalContour⟩

/-- The terminal contour of a CCG Tune constructed from a B&P IP
    is exactly the B&P terminal contour — @cite{steedman-2000}'s
    Tune decomposition and B&P's IP decomposition produce the same
    `TerminalContour` by construction. -/
theorem tune_terminal_eq_bp_terminal (ip : IntonationPhrase) (accent : PitchAccent) :
    (ipToTune ip accent).terminal = ip.terminalContour := rfl

/-- A declarative IP (L phrase accent, L% boundary tone). -/
def declarativeIP : IntonationPhrase :=
  { ips := [{ aps := [accentedAP], phraseAccent := .L }], boundaryTone := .L_pct }

/-- A continuation-rise IP (L phrase accent, H% boundary tone). -/
def continuationIP : IntonationPhrase :=
  { ips := [{ aps := [accentedAP], phraseAccent := .L }], boundaryTone := .H_pct }

/-- A declarative IP has the same terminal contour as
    @cite{steedman-2000}'s rheme tune (H* L L%). -/
theorem declarative_ip_matches_rheme_terminal :
    declarativeIP.terminalContour = rhemeTune.terminal := by decide

/-- A continuation-rise IP has the same terminal contour as
    @cite{steedman-2000}'s theme tune (L+H* L H%). -/
theorem continuation_ip_matches_theme_terminal :
    continuationIP.terminalContour = themeTune.terminal := by decide

-- ============================================================================
-- § 8: Bridge to Kratzer & Selkirk 2020 — ip as Focus-Prosody Domain
-- ============================================================================

open Semantics.Focus.KratzerSelkirk2020

/-- The ip/φ domain serves two independent functions:
    1. **Catathesis domain** (B&P §4): register resets at ip boundaries
    2. **Focus-prosody domain** (@cite{kratzer-selkirk-2020} §7):
       [FoC] = φ-Level-Head

    Whether focus marking triggers catathesis depends on the accent
    inventory: guaranteed in Japanese (all accents are bitonal),
    not guaranteed in English (H* is monotonal). -/
theorem ip_dual_function :
    PitchAccent.H_star_plus_L.isBitonal = true ∧
    PitchAccent.H_star.isBitonal = false := ⟨rfl, rfl⟩

/-- In Japanese, [FoC] spellout at φ-level always triggers catathesis:
    the only accent shape (H*+L) is bitonal. Focus-marking and catathesis
    are inseparable in the Japanese system.

    Proof chain: [FoC] → φ-Level-Head (K&S 34) → pitch accent (head =
    most prominent) → bitonal (Japanese has only H*+L) → catathesis
    (B&P §3). -/
theorem japanese_foc_always_triggers_catathesis :
    japanese.accentShapes.all (·.isBitonal) = true := rfl

/-- In English, [FoC] spellout at φ-level does NOT guarantee catathesis:
    the default rheme accent H* is monotonal, so catathesis only occurs
    when the speaker selects a bitonal accent shape (H*+L, H+L*, L*+H,
    L+H*). -/
theorem english_foc_may_not_trigger_catathesis :
    PitchAccent.H_star.isBitonal = false := rfl


-- ============================================================================
-- § 9: Monotonicity of Catathesis
-- ============================================================================

/-- More catathesis (more bitonal accents) produces lower pitch: replacing
    a registerless AP with a bitonal-accented one produces pointwise
    lower-or-equal pitch realization. -/
theorem more_catathesis_lower_pitch :
    pointwiseLE
      (realizePitch 4 [some .l, some .l, none])
      (realizePitch 4 [some .l, none, none]) := by decide

/-- **Catathesis blocking**: realizing the second ip from the original
    baseline produces pointwise higher pitch than continuing from the
    compressed level. When an ip boundary resets the register to
    baseline `n`, subsequent pitches are higher than if catathesis had
    continued from `n - k`.

    Direct application of `realizePitch_baseline_mono`. -/
theorem catathesis_blocking (specs : List RegisterSpec) (n k : Nat) :
    pointwiseLE (realizePitch (n - k) specs) (realizePitch n specs) :=
  realizePitch_baseline_mono specs (Nat.sub_le n k)

/-- Concrete catathesis blocking: after one downstep from baseline 4,
    the second ip starting from 4 (reset) produces higher pitches [3, 3]
    than continuing from 3 (no reset) which gives [2, 2]. -/
theorem catathesis_blocking_concrete :
    pointwiseLE
      (realizePitch 3 [some .l, none])
      (realizePitch 4 [some .l, none]) := by decide

/-- Catathesis register specs only contain `none` (maintain) or `some .l`
    (lower) — never `some .h` (raise). This ensures catathesis is
    monotonically compressive. -/
theorem catathesis_specs_no_raising (aps : List AccentualPhrase)
    (s : RegisterSpec) (hs : s ∈ catathesisToRegisterSpecs aps) :
    s = none ∨ s = some .l := by
  simp only [catathesisToRegisterSpecs, List.mem_map] at hs
  obtain ⟨ap, _, rfl⟩ := hs
  rcases Bool.eq_false_or_eq_true (ap.accent.isBitonal) with h | h <;> simp [h]

/-- Japanese catathesis timing: catathesis applies within the accent. -/
theorem japanese_catathesis_timing :
    japanese.catathesisTiming = .withinAccent := rfl

/-- English catathesis timing: catathesis applies after the accent. -/
theorem english_catathesis_timing :
    english.catathesisTiming = .afterAccent := rfl

end Phenomena.Intonation.Studies.BeckmanPierrehumbert1986
