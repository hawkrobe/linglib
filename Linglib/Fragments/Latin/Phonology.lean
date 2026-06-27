import Linglib.Phonology.Segmental.Basic

/-!
# Latin Phonology — Fragment

Synchronic segmental inventory of Classical Latin, anchored on
[cser-2020] (the most recent comprehensive synchronic phonology of the
language). [sen-2015] is the complementary diachronic anchor for study
files that explain *why* the inventory has this shape (clear and dark /l/
allophony, inverse compensatory lengthening, syllabification).

The Fragment provides the consensus consonant and vowel inventory plus
enumeration lists. Natural-class membership reuses the substrate predicates
from `Phonology.Segment` (`Segment.IsVowel`,
`Segment.IsConsonant`, …); theoretical apparatus (moraic encoding,
tier projections, conjugation classes) lives downstream in study files
that consume this Fragment.

## Main declarations

* `a`, `e`, `i`, `o`, `u`: five short vowels.
* `p`, `b`, `t`, `d`, `k`, `g`: the six oral stops.
* `f`, `s`: voiceless fricatives.
* `m`, `n`: nasals.
* `l`, `r`: liquids.
* `v`: the labio-velar glide (orthographic ⟨v⟩, phonetically [w]).
* `vowels`, `consonants`, `allSegments`: enumeration lists.

## Implementation notes

**Vowel length is prosodic, not segmental.** The `[long]` feature is not
in the `Phonology.Features` inventory (which follows
[hayes-2009]'s decision to treat duration as a syllable-level
property). Long vowels are encoded as two morae in `Prosody`'s moraic layer
rather than as distinct segments; consumers needing a surface short-vs-long
contrast construct it at the syllable level.

**Clear vs dark /l/ is allophonic.** [sen-2015] ch. 2 treats both
[l] and [ɫ] as positional realizations of a single /l/ phoneme (clear
before /i/ and in geminates, dark elsewhere). The Fragment supplies one
`l` segment; the clear and dark variants surface in a Sen 2015 study file
that derives them from positional context.

**Orthographic ⟨v⟩ is the glide [w].** [belth-2026] encodes ⟨v⟩ as
[-consonantal] so that the tier projection of *pluv-* in `pluvaris` picks
up the preceding /l/ rather than /v/ — the choice the Fragment adopts. A
later study that needs the consonantal-fricative realization /β/ of late
Latin would either add a separate segment or override the spec.

**Namespace shadowing.** Because the file's namespace ends with `.Phonology`,
`open Phonology (...)` would resolve to the current namespace
(`Latin.Phonology`) rather than the substrate root. The
`_root_.` prefix forces resolution to the top-level `Phonology`.

**Deferred:** the labio-velars /kʷ/ ⟨qu⟩, /gʷ/ ⟨gu⟩; the rare /h/ and /y/;
diphthongs ⟨ae⟩, ⟨oe⟩, ⟨au⟩; onset and coda phonotactic predicates. These
land when the first consumer needs them.

## Todo

* `lDark` allophone and the contextual mapping ([sen-2015] ch. 2).
* Long-vowel surface notation if a consumer outside the moraic framework
  needs it.
* Frequency table from [cser-2020] Appendix 1.
* Onset and coda phonotactic predicates.
* Labio-velars /kʷ/, /gʷ/; rare segments /h/, /y/; diphthongs.
-/

namespace Latin.Phonology

open _root_.Phonology (Segment Feature)

/-! ### Vowels -/

/-- /a/ — low vowel. -/
def a : Segment := .ofSpecs
  [(.syllabic, true), (.consonantal, false), (.sonorant, true),
   (.approximant, true), (.voice, true),
   (.low, true), (.high, false)]

/-- /e/ — mid front vowel. -/
def e : Segment := .ofSpecs
  [(.syllabic, true), (.consonantal, false), (.sonorant, true),
   (.approximant, true), (.voice, true),
   (.front, true), (.back, false),
   (.high, false), (.low, false), (.round, false)]

/-- /i/ — high front vowel. -/
def i : Segment := .ofSpecs
  [(.syllabic, true), (.consonantal, false), (.sonorant, true),
   (.approximant, true), (.voice, true),
   (.front, true), (.back, false),
   (.high, true), (.low, false), (.round, false)]

/-- /o/ — mid back rounded vowel. -/
def o : Segment := .ofSpecs
  [(.syllabic, true), (.consonantal, false), (.sonorant, true),
   (.approximant, true), (.voice, true),
   (.back, true), (.front, false),
   (.high, false), (.low, false), (.round, true)]

/-- /u/ — high back rounded vowel. -/
def u : Segment := .ofSpecs
  [(.syllabic, true), (.consonantal, false), (.sonorant, true),
   (.approximant, true), (.voice, true),
   (.back, true), (.front, false),
   (.high, true), (.low, false), (.round, true)]

/-! ### Oral stops -/

/-- /p/ — voiceless bilabial stop. -/
def p : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, false), (.delayedRelease, false),
   (.voice, false), (.labial, true)]

/-- /b/ — voiced bilabial stop. -/
def b : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, false), (.delayedRelease, false),
   (.voice, true), (.labial, true)]

/-- /t/ — voiceless alveolar stop. -/
def t : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, false), (.delayedRelease, false),
   (.voice, false), (.coronal, true), (.anterior, true)]

/-- /d/ — voiced alveolar stop. -/
def d : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, false), (.delayedRelease, false),
   (.voice, true), (.coronal, true), (.anterior, true)]

/-- /k/ — voiceless velar stop (orthographic ⟨c⟩, ⟨k⟩, also ⟨q⟩ before /u/). -/
def k : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, false), (.delayedRelease, false),
   (.voice, false), (.dorsal, true)]

/-- /g/ — voiced velar stop. -/
def g : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, false), (.delayedRelease, false),
   (.voice, true), (.dorsal, true)]

/-! ### Fricatives -/

/-- /f/ — voiceless labiodental fricative. -/
def f : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, true), (.voice, false),
   (.labial, true), (.labiodental, true)]

/-- /s/ — voiceless alveolar fricative. -/
def s : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, true), (.strident, true), (.voice, false),
   (.coronal, true), (.anterior, true)]

/-! ### Nasals -/

/-- /m/ — bilabial nasal. -/
def m : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, true),
   (.nasal, true), (.voice, true), (.labial, true)]

/-- /n/ — alveolar nasal. -/
def n : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, true),
   (.nasal, true), (.voice, true),
   (.coronal, true), (.anterior, true)]

/-! ### Liquids -/

/-- /l/ — alveolar lateral. [sen-2015] ch. 2 treats clear [l] and
dark [ɫ] as positional allophones of this single phoneme; the Fragment
exposes just /l/, with the allophonic split derived in a Sen 2015 study
file. -/
def l : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, true),
   (.approximant, true), (.continuant, true),
   (.lateral, true), (.voice, true),
   (.coronal, true), (.anterior, true)]

/-- /r/ — alveolar trill ([cser-2020] §2). [sen-2015] §4.3
discusses /r/'s behaviour in vowel reduction before TR clusters. -/
def r : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, true),
   (.continuant, true), (.trill, true), (.voice, true),
   (.coronal, true), (.anterior, true)]

/-! ### Glides -/

/-- /w/ — labio-velar glide, written orthographic ⟨v⟩ in Classical Latin.
[belth-2026] treats this as [-consonantal] so that the tier projection
of *pluv-* in `pluvaris` picks up the preceding /l/ rather than /v/. -/
def v : Segment := .ofSpecs
  [(.syllabic, false), (.consonantal, false), (.sonorant, true),
   (.approximant, true), (.voice, true),
   (.back, true), (.round, true), (.labial, true)]

/-! ### Enumeration -/

/-- The five short vowels of Classical Latin. -/
def vowels : List Segment := [a, e, i, o, u]

/-- The thirteen consonant segments covered by the Fragment.
Labio-velars /kʷ/, /gʷ/, the rare /h/, and the palatal glide /j/ are
deferred. -/
def consonants : List Segment := [p, b, t, d, k, g, f, s, m, n, l, r, v]

/-- All segments currently provided by the Fragment. -/
def allSegments : List Segment := vowels ++ consonants

/-! ### Sanity theorems

Natural-class predicates (`IsVowel`, `IsConsonant`, …) come from
`Phonology.Segment`. The theorems below confirm
the Fragment's segments inhabit the expected classes. -/

/-- The five vowel segments satisfy `Segment.IsVowel`. -/
theorem all_vowels_are_vowels : ∀ s ∈ vowels, s.IsVowel := by decide

/-- The thirteen consonant segments do not satisfy `Segment.IsVowel`. -/
theorem no_consonant_is_vowel : ∀ s ∈ consonants, ¬ s.IsVowel := by decide

/-- The six oral stops satisfy `Segment.IsStop`. -/
theorem stops_are_stops : ∀ s ∈ ([p, b, t, d, k, g] : List Segment), s.IsStop := by
  decide

/-- The two fricatives satisfy `Segment.IsFricative`. -/
theorem fricatives_are_fricatives :
    ∀ x ∈ ([f, s] : List Segment), x.IsFricative := by decide

/-- The two nasals satisfy `Segment.IsNasal`. -/
theorem nasals_are_nasals :
    ∀ s ∈ ([m, n] : List Segment), s.IsNasal := by decide

/-- The two liquids satisfy `Segment.IsLiquid`. -/
theorem liquids_are_liquids :
    ∀ s ∈ ([l, r] : List Segment), s.IsLiquid := by decide

/-- The glide `v` (orthographic ⟨v⟩, phonetically [w]) satisfies
`Segment.IsGlide`. -/
theorem v_is_glide : v.IsGlide := by decide

end Latin.Phonology
