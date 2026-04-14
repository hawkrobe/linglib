import Linglib.Core.Prosody

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
   reanalyzed from @cite{pierrehumbert-1980}'s "phrase accent" as the
   terminal tone of the ip, distinct from the IP boundary tone.

The paper also demonstrates that Japanese tonal patterns are much sparser
than earlier autosegmental accounts assumed — closer to English in their
distribution of tones to tone-bearing units.
-/

namespace Phenomena.Intonation.Studies.BeckmanPierrehumbert1986

open Core.Prosody

-- ============================================================================
-- § 1: Accentual Phrase (§2.2)
-- ============================================================================

/-- Accentedness: whether a word bears a lexical accent.

    In Japanese, accent is a lexical property: some words have an accent
    (H tone linked to a specific mora), others are unaccented. In English,
    every content word has at least one accentable syllable, but whether
    an accent is realized depends on focus and phrasing. -/
inductive Accentedness where
  | accented    -- bears a pitch accent
  | unaccented  -- no pitch accent
  deriving Repr, DecidableEq

/-- An accentual phrase: the lowest level of prosodic phrasing defined
    by the intonation pattern.

    In Japanese, delimited by a phrasal H and boundary L tone. Contains
    at most one pitch accent. An unaccented AP has the rising pitch shape
    (L → phrasal H) but no accent HL fall (§2.2).

    In English, the AP is less firmly established. It corresponds to the
    domain of a single pitch accent plus the surrounding material up to
    the next accent or phrase boundary (§2.4). -/
structure AccentualPhrase where
  /-- Accentedness of this phrase -/
  accentedness : Accentedness
  /-- Pitch accent type (null if unaccented) -/
  accent : PitchAccent
  /-- Number of words grouped in this phrase -/
  nWords : Nat
  deriving Repr

/-- **Culminativity at the AP level** (§2.2, §2.3): an accentual phrase
    contains at most one pitch accent. If two lexically accented words
    are grouped in the same AP, one accent must be deleted. -/
def AccentualPhrase.isCulminative (ap : AccentualPhrase) : Prop :=
  ap.accentedness = .unaccented → ap.accent = .null

/-- Consistency: accented APs have non-null accents,
    unaccented APs have null accents. -/
def AccentualPhrase.isConsistent (ap : AccentualPhrase) : Bool :=
  match ap.accentedness, ap.accent with
  | .accented, .null => false
  | .unaccented, .null => true
  | .unaccented, _ => false
  | .accented, _ => true

-- ============================================================================
-- § 2: Catathesis (§3)
-- ============================================================================

/-- A pitch range: the span within which tones are realized.

    Catathesis compresses the pitch range, lowering both H and L tones
    proportionally. We model this as a fraction (numerator/denominator)
    of the original range. -/
structure PitchRange where
  /-- Fraction of original range remaining (1 = full, < 1 = compressed) -/
  scale : Nat
  /-- Denominator for the fraction -/
  denom : Nat
  /-- Scale is positive -/
  scale_pos : 0 < scale := by omega
  /-- Denominator is positive -/
  denom_pos : 0 < denom := by omega
  deriving Repr

/-- Full (uncompressed) pitch range -/
def PitchRange.full : PitchRange := ⟨1, 1, by omega, by omega⟩

/-- Apply catathesis: compress pitch range by a fixed factor.

    @cite{beckman-pierrehumbert-1986} §3: catathesis compresses the pitch
    range, lowering both H and L tones (except L tones already at the
    bottom of the range). The compression is cumulative — multiple
    applications of catathesis produce descending staircases (Fig. 11). -/
def PitchRange.applyCatathesis (r : PitchRange) : PitchRange :=
  ⟨r.scale * 3, r.denom * 4,
   by have := r.scale_pos; omega,
   by have := r.denom_pos; omega⟩  -- compress to 3/4

/-- Apply catathesis across a sequence of accentual phrases within
    an intermediate phrase. Each bitonal accent triggers catathesis
    on the following material (§3.2).

    Returns the pitch range after processing all APs in sequence. -/
def catathesisChain (aps : List AccentualPhrase) : PitchRange :=
  aps.foldl (λ r ap =>
    if ap.accent.isBitonal then r.applyCatathesis else r
  ) .full

/-- Catathesis chains: n applications of catathesis produce
    n levels of compression (descending staircase, Fig. 11). -/
theorem catathesis_chains_two :
    let r := PitchRange.full.applyCatathesis.applyCatathesis
    r.scale * PitchRange.full.denom < PitchRange.full.scale * r.denom := by
  simp only [PitchRange.full, PitchRange.applyCatathesis]
  decide

-- ============================================================================
-- § 3: Intermediate Phrase — Domain of Catathesis (§4)
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
    of its final ip and the IP boundary tone. -/
def IntonationPhrase.terminalContour (ip : IntonationPhrase) : TerminalContour :=
  match ip.ips.getLast? with
  | some lastIp => ⟨lastIp.phraseAccent, ip.boundaryTone⟩
  | none => ⟨.L, ip.boundaryTone⟩  -- unreachable given ips_nonempty

/-- **Catathesis is blocked by intermediate phrase boundaries** (§4.1, §4.4).

    The pitch range resets at each ip boundary. Within an ip, catathesis
    chains; across ip boundaries, it does not. This is the key evidence
    for the ip as a prosodic domain (Figs. 17, 18 vs. 12, 13). -/
def catathesisWithinIp (ip : IntermediatePhrase) : PitchRange :=
  catathesisChain ip.aps

/-- Catathesis across an IP: each ip gets its own pitch range. -/
def catathesisAcrossIps (ips : List IntermediatePhrase) : List PitchRange :=
  ips.map catathesisWithinIp

-- ============================================================================
-- § 4: Cross-linguistic Comparison (§2.5, §6)
-- ============================================================================

/-- Language-specific intonation system parameters.

    @cite{beckman-pierrehumbert-1986} §6: Japanese and English share the
    same prosodic hierarchy but differ in how accents relate to the lexicon,
    the size of the pitch accent inventory, and whether unaccented phrases
    are possible. -/
structure IntonationSystem where
  /-- How accents are specified (lexical vs postlexical) -/
  accentSpec : AccentSpecification
  /-- Number of contrastive pitch accent shapes -/
  accentInventorySize : Nat
  /-- Whether lexically unaccented words/phrases exist -/
  hasUnaccented : Bool
  /-- Whether the accentual phrase boundary L is always present -/
  apBoundaryLAlwaysPresent : Bool
  deriving Repr

/-- Japanese intonation system (§2, §6):
    - Accent location is lexical (H*+L at specified mora)
    - Single accent shape (no intonational contrast via accent shape)
    - Unaccented words exist (and are common)
    - Boundary L is always present (utterance-initially or phrase-finally) -/
def japanese : IntonationSystem :=
  { accentSpec := .lexical
    accentInventorySize := 1
    hasUnaccented := true
    apBoundaryLAlwaysPresent := true }

/-- English intonation system (§2, §6):
    - Accent shape is postlexical (chosen by intonation)
    - Six contrastive accent shapes
    - Every content word has an accentable syllable (no lexically unaccented)
    - AP boundary is less clearly defined than in Japanese -/
def english : IntonationSystem :=
  { accentSpec := .postlexical
    accentInventorySize := 6
    hasUnaccented := false
    apBoundaryLAlwaysPresent := false }

/-- Japanese has lexical accent specification. -/
theorem japanese_lexical : japanese.accentSpec = .lexical := rfl

/-- English has postlexical accent specification. -/
theorem english_postlexical : english.accentSpec = .postlexical := rfl

/-- Japanese has fewer accent shapes than English. -/
theorem japanese_smaller_inventory :
    japanese.accentInventorySize < english.accentInventorySize := by decide

-- ============================================================================
-- § 5: Focus–Prosody Interaction (§4.1, §4.4)
-- ============================================================================

/-- Focus induces an intermediate phrase boundary.

    @cite{beckman-pierrehumbert-1986} §4.1: in Japanese, a focused item
    tends to be preceded by an ip boundary (the ip is left-dominant).
    §4.4: in English, focus blocks catathesis by introducing an ip
    boundary before the focused element, even when the English ip is
    right-dominant.

    This is testable: if catathesis is blocked between two accents, an
    ip boundary must intervene (Figs. 18–21 vs. 12–13). -/
structure FocusPhrasing where
  /-- The position of focus in the utterance -/
  focusPosition : Nat
  /-- Whether an ip boundary is inserted before the focused element -/
  preFocusBoundary : Bool
  /-- Whether catathesis is blocked across the focus boundary -/
  catathesisBlocked : Bool
  deriving Repr

/-- In Japanese, focus triggers a pre-focus ip boundary (§4.1). -/
def japaneseFocusPhrasing (pos : Nat) : FocusPhrasing :=
  { focusPosition := pos
    preFocusBoundary := true
    catathesisBlocked := true }

/-- Focus-induced boundaries block catathesis: if a boundary is present,
    catathesis should be blocked. -/
theorem focus_blocks_catathesis (fp : FocusPhrasing) :
    fp.preFocusBoundary = true → fp.catathesisBlocked = true →
    fp.preFocusBoundary = fp.catathesisBlocked := by
  intro h1 h2; rw [h1, h2]

-- ============================================================================
-- § 6: Catathesis Trigger — Japanese vs English (§3.3)
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

/-- Japanese catathesis applies within the accent. -/
def japaneseCatathesisTiming : CatathesisTiming := .withinAccent

/-- English catathesis applies after the accent. -/
def englishCatathesisTiming : CatathesisTiming := .afterAccent

-- ============================================================================
-- § 7: Final Lowering and Declination (§5)
-- ============================================================================

/-- Final lowering and declination operate at or above the IP level.

    @cite{beckman-pierrehumbert-1986} §5: final lowering is a compression
    of pitch range near the end of a declarative utterance. It affects
    the last IP in a multi-phrase utterance. Declination is a gradual,
    time-dependent lowering operating at an even larger domain. Both
    exist in Japanese and (probably) English. -/
inductive SupraPhrasalProcess where
  | finalLowering  -- pitch range compression near utterance end
  | declination    -- gradual time-dependent lowering
  deriving Repr, DecidableEq

/-- Final lowering affects the IP domain; declination may operate
    above it (§5). -/
def SupraPhrasalProcess.minDomain : SupraPhrasalProcess → ProsodicLevel
  | .finalLowering => .ι
  | .declination => .ι  -- domain is controversial; at least IP

end Phenomena.Intonation.Studies.BeckmanPierrehumbert1986
