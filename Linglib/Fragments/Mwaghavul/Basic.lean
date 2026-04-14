import Linglib.Theories.Phonology.Autosegmental.RegisterTier
import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone

/-!
# Mwaghavul Phonological Fragment
@cite{akinbo-fwangwar-2026} @cite{fwangwar-2018}

Mwaghavul (ISO 639-3: sur, Glottocode: mwag1236) is an A3 West Chadic
(Afro-Asiatic) language spoken by more than 700,000 people in Plateau State,
Nigeria (@cite{crozier-blench-1992}).

## Tone system

Mwaghavul contrasts three level tones — high (H), mid (M), and low (L) —
plus an LH rising contour. The tone-bearing unit (TBU) is the syllable.
All tonal co-occurrences on bisyllabic roots are attested except M-LH
(@cite{akinbo-fwangwar-2026} Table 3).

## Ideophones

Mwaghavul has a rich inventory of ideophones — "an open class of marked words
that depict sensory imagery" (@cite{dingemanse-2019}:16). Ideophones share the
same grammatical classes as nonideophonic words (nouns, verbs, adjectives,
adverbs) and occur in comparable morphosyntactic environments.

## Verbalisation

All tonally derived verbs in Mwaghavul have ideophonic bases. The verb
formation is morphophonologically marked through one of two lexically
determined tonal alternations triggered by segmentally null verbalisers:

1. **M verbaliser** (VBZ₁): overwrites every TBU with M
2. **M-H verbaliser** (VBZ₂): overwrites nonfinal TBUs with M, final with H

The M-H melody is attested only in derived verbs — no underived verb has
this pattern. Data from @cite{akinbo-fwangwar-2026} and
@cite{fwangwar-2018}.
-/

namespace Fragments.Mwaghavul

open Theories.Phonology.Autosegmental.RegisterTier (ToneFeature TBUKind
  WordProsodicType)
open Theories.Phonology.Autosegmental.GrammaticalTone (TBU Spec ValuationWindow)

-- ============================================================================
-- S 1: Phonological Inventory
-- ============================================================================

/-- Mwaghavul is a three-level tone language with syllable TBUs. -/
def wordProsodicType : WordProsodicType := .toneBased
def tbuKind : TBUKind := .syllable

-- ============================================================================
-- S 2: Verbaliser Allomorphs
-- ============================================================================

/-- The two lexically specific suppletive allomorphs of the verbaliser
    morpheme (@cite{akinbo-fwangwar-2026} (17)). -/
inductive VerbalizerChoice where
  | m   -- VBZ₁: M melody (targets unreduplicated ideophones only)
  | mh  -- VBZ₂: M-H melody (targets both unreduplicated and reduplicated)
  deriving DecidableEq, Repr

/-- The M-tone verbaliser (VBZ₁): targets only unreduplicated ideophones.
    Overwrites every TBU of the host with M. -/
def verbM : Spec :=
  { name := "VBZ₁"
    melody := [.M]
    window := .whole }

/-- The M-H verbaliser (VBZ₂): targets both unreduplicated and
    reduplicated ideophones. Nonfinal TBUs get M, final gets H. -/
def verbMH : Spec :=
  { name := "VBZ₂"
    melody := [.M, .H]
    window := .nonfinalFinal }

-- ============================================================================
-- S 3: Ideophone Data
-- ============================================================================

/-- An ideophone entry: base form, gloss, lexical tones, and which
    verbaliser it selects. Tone pattern is listed left-to-right matching
    syllable order.

    Whether an ideophone undergoes M or M-H alternation is lexically
    determined and not predictable from syllable structure or tone
    (@cite{akinbo-fwangwar-2026} §3.1). -/
structure Ideophone where
  form     : String
  gloss    : String
  tones    : List ToneFeature
  verbType : VerbalizerChoice
  deriving Repr

/-- Number of syllables, derived from the tone list. -/
def Ideophone.nSyl (i : Ideophone) : Nat := i.tones.length

-- M-tone verbaliser ideophones from (7a)
def zut     : Ideophone := ⟨"zùt",    "how solid substance ejects", [.L],     .m⟩
def diis    : Ideophone := ⟨"dìːs",   "blood sucking",              [.L],     .m⟩
def kwaaj   : Ideophone := ⟨"kwàj",   "bubbling hot water",         [.L],     .m⟩
def vjaar   : Ideophone := ⟨"vjàr",   "pouring of urine",          [.L],     .m⟩
def shweer  : Ideophone := ⟨"ʃwèr",   "how water falls",           [.L],     .m⟩
def wuulash : Ideophone := ⟨"wùlàʃ",  "wide open",                 [.L, .L], .m⟩

-- M-tone verbaliser ideophones from (7b)
def fooyoop : Ideophone := ⟨"fɔ̀yɔ̀p", "oily",                     [.L, .L], .m⟩
def vjayaap : Ideophone := ⟨"vjàyàp", "liquid ejects from a fruit", [.L, .L], .m⟩

-- M-H verbaliser ideophones from (8a)
def bishool  : Ideophone := ⟨"bìʃɔ̀l",  "shabbily dressed",         [.L, .L], .mh⟩
def kitiif   : Ideophone := ⟨"kìtíf",   "untidy",                   [.L, .H], .mh⟩
def kodzoong : Ideophone := ⟨"kɔ̀dʒɔ̀ŋ", "walking effortfully",     [.L, .L], .mh⟩
def kitfor   : Ideophone := ⟨"kìtʃɔ̀r",  "old-sounding vehicle",    [.L, .L], .mh⟩

-- M-H verbaliser ideophones from (8b)
def korjong  : Ideophone := ⟨"kɔ̀rjɔ̀ŋ", "crooked",                 [.L, .L], .mh⟩
def mondos   : Ideophone := ⟨"mɔ̀ndɔ̀s",  "big nose",                [.L, .L], .mh⟩
def vwaplas  : Ideophone := ⟨"vwàplàs",  "oversized",               [.L, .L], .mh⟩
def jalpat   : Ideophone := ⟨"jàlpàt",   "hanging loose",           [.L, .L], .mh⟩

-- M-H verbaliser ideophones from (8c)
def hanlayap : Ideophone := ⟨"háŋláyáp", "light-weighted",          [.H, .H, .H], .mh⟩
def hamhoyof : Ideophone := ⟨"hámhɔ̀yɔ̀ʃ","dryness of cracked feet", [.H, .L, .L], .mh⟩

-- ============================================================================
-- S 4: Derivation via tonalOverwrite
-- ============================================================================

/-- A toned Mwaghavul syllable. -/
structure Syl where
  ipa : String
  deriving DecidableEq, Repr

/-- Convenience: a toned Mwaghavul syllable. -/
abbrev TSyl := TBU Syl

/-- Build a toned syllable from IPA and tone. -/
def mkTSyl (ipa : String) (t : ToneFeature) : TSyl :=
  ⟨⟨ipa⟩, t⟩

/-- Derive a verb from an ideophone using its verbaliser spec.
    Returns the output tonal pattern. -/
def deriveVerb (base : Ideophone) : List ToneFeature :=
  let spec := match base.verbType with
    | .m  => verbM
    | .mh => verbMH
  let host := base.tones.map λ t => mkTSyl base.form t
  (Theories.Phonology.Autosegmental.GrammaticalTone.tonalOverwrite host spec).map TBU.tone

-- M-tone verbaliser: wùlàʃ [L L] → wūlāʃ [M M]
theorem wuulash_verb : deriveVerb wuulash = [.M, .M] := by native_decide

-- M-tone verbaliser on monosyllable: dìːs [L] → dīːs [M]
theorem diis_verb : deriveVerb diis = [.M] := by native_decide

-- M-H verbaliser: bìʃɔ̀l [L L] → bīʃɔ́l [M H]
theorem bishool_verb : deriveVerb bishool = [.M, .H] := by native_decide

-- M-H verbaliser on trisyllable: háŋláyáp [H H H] → hāŋlāyáp [M M H]
theorem hanlayap_verb : deriveVerb hanlayap = [.M, .M, .H] := by native_decide

-- M-H verbaliser: kìtíf [L H] → kītíf [M H]
theorem kitiif_verb : deriveVerb kitiif = [.M, .H] := by native_decide

-- M-H verbaliser: jàlpàt [L L] → jālpát [M H]
theorem jalpat_verb : deriveVerb jalpat = [.M, .H] := by native_decide

-- ============================================================================
-- S 5: Empirical Generalizations (@cite{akinbo-fwangwar-2026} (13))
-- ============================================================================

/-- All M-tone derived verbs produce uniform M across all TBUs (13a). -/
theorem m_verb_uniform (i : Ideophone) (h : i.verbType = .m) :
    deriveVerb i = i.tones.map (λ _ => ToneFeature.M) := by
  simp [deriveVerb, h, verbM,
    Theories.Phonology.Autosegmental.GrammaticalTone.tonalOverwrite,
    List.map_map]

/-- M-H derived verbs have M on nonfinal TBUs and H on the final TBU.
    Verified on bisyllabic bases. -/
theorem mh_verb_bisyllabic_pattern (i : Ideophone)
    (h : i.verbType = .mh) (h2 : i.tones.length = 2) :
    deriveVerb i = [.M, .H] := by
  simp [deriveVerb, h, verbMH]
  match i, h2 with
  | ⟨_, _, [_, _], _⟩, _ =>
    simp [Theories.Phonology.Autosegmental.GrammaticalTone.tonalOverwrite]

end Fragments.Mwaghavul
