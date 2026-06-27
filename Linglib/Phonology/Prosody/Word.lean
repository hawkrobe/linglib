import Linglib.Phonology.Prosody.Foot
import Linglib.Features.Prosody

/-!
# Prosodic Word (Word)
[selkirk-1984]

The prosodic word (Word, ω) is the prosodic constituent immediately
above the foot in the prosodic hierarchy:

    σ < f < **ω** < φ < ι

Word is the domain for a cluster of phonological processes:
- **Stress assignment** and metrical parsing
- **Vowel harmony** (progressive harmony in Telugu)
- **Minimal word constraints** (bimoraic minimum)
- **Obligatory hiatus resolution** (within Word; optional across Word)

## Morphosyntax-Prosody Mapping

Not all morphological elements are Word-internal. The mapping from
morphosyntactic structure to prosodic structure determines which
elements fall within the Word and which form their own domain:

| Morphological status | Word membership | Example (Telugu)     |
|----------------------|-----------------|----------------------|
| Root                 | Internal        | samudr-              |
| Derivational suffix  | Internal        | (not shown)          |
| Inflectional suffix  | Internal        | -am, -ni, -ki        |
| Agreement suffix     | Internal        | -ni (1SG), -vi (2SG) |
| Postposition         | **External**    | -lō, -tō, -gurinci  |

This boundary is diagnosed by vowel harmony scope, minimal word
effects, and obligatory vs optional hiatus resolution
([aitha-2026] §3.2).

## Connection to Linglib

`Features.Prosody` defines the prosodic hierarchy levels (σ, f, ω, φ, ι)
and intonational structure. This module provides the *internal
structure* of the prosodic word: syllable constituency, weight
profiles, minimal word constraints, and the morphosyntax-prosody
mapping that determines Word boundaries.
-/

namespace Prosody


/-! ### Morphological status and Word membership -/

/-- Morphological status of an element relative to the prosodic word,
    decomposed into **orthogonal Boolean axes** rather than a flat
    enumeration of named cases. The previous inductive design with cases
    `root | derivational | ... | clitic` conflated three independent
    dimensions and made it impossible to add new combinations (e.g., a
    "free" vs. "bound" N2 in a Japanese compound, which is the moderator
    in [breiss-katsuda-kawahara-2026]) without doubling the case
    enumeration.

    The three axes:

    - `prWdInternal` — is this element parsed inside the prosodic word
      with the stem? Empirically diagnosed by vowel-harmony scope,
      minimal-word effects, and hiatus-resolution obligation
      ([aitha-2026] §3.2).
    - `free` — can this element stand alone as a wordform? Roots and
      free morphemes are `true`; bound roots, inflectional suffixes,
      and most clitics are `false`. **The Breiss N2 free-vs-bound
      distinction lives on this axis.**
    - `affixal` — is this element morphologically bound to a stem
      (vs. a separate lexical word)? Roots are `false`; affixes,
      clitics, and bound morphemes are `true`.

    Named constructors below recover the old enum cases. -/
structure MorphStatus where
  prWdInternal : Bool
  free         : Bool
  affixal      : Bool
  deriving DecidableEq, Repr

namespace MorphStatus

/-- Root morpheme: Word-internal, free-standing, not affixal. -/
def root         : MorphStatus := ⟨true,  true,  false⟩
/-- Derivational affix: Word-internal with the stem, bound, affixal. -/
def derivational : MorphStatus := ⟨true,  false, true⟩
/-- Inflectional affix (case, number, tense): Word-internal, bound. -/
def inflectional : MorphStatus := ⟨true,  false, true⟩
/-- Agreement marker: Word-internal (crucially, for Telugu nominal
    predicative agreement; [aitha-2026] §3.1). -/
def agreement    : MorphStatus := ⟨true,  false, true⟩
/-- Postposition: forms a **separate** Word. Evidence: not subject to
    progressive vowel harmony, obeys minimal word constraint
    independently, hiatus resolution across boundary is optional
    ([aitha-2026] §3.2). Free-standing in many languages. -/
def postposition : MorphStatus := ⟨false, true,  false⟩
/-- Clitic: Word-external boundary element; phonologically bound but
    syntactically not an affix. -/
def clitic       : MorphStatus := ⟨false, false, true⟩

/-- Bound free-standing morpheme that occurs only inside compounds —
    e.g., the "bound" N2 in Japanese compound nominals. Word-internal,
    not free, not strictly affixal (it's a stem-class member, just one
    that never surfaces alone). -/
def boundStem    : MorphStatus := ⟨true,  false, false⟩

end MorphStatus

/-- Is this morphological element parsed inside the Word with the stem?
    Direct projection of the `prWdInternal` axis. -/
def MorphStatus.isPrWdInternal (s : MorphStatus) : Bool := s.prWdInternal

/-! ### Prosodic word structure -/

/-- A prosodic word: a sequence of syllables (by weight) that forms a
    single domain for stress assignment and phonological processes.

    The `syllables` field gives the weight profile in linear order.
    For example, Telugu *samudram* 'ocean' has profile [L, L, H]
    (sa.mu.dram). -/
structure Word where
  syllables : List Syllable.Weight
  deriving DecidableEq, Repr

/-- The weight profile of a sequence of fully-moraified syllables — the bridge
    from the structural σ level (`Syllable`) up to the prosodic word. -/
def Word.ofSyllables (σs : List Syllable) : Word := ⟨σs.map Syllable.weight⟩

/-- Total mora count of a prosodic word (each weight *is* a mora count). -/
def Word.moraCount (w : Word) : Nat :=
  w.syllables.foldl (· + ·) 0

/-- Number of syllables. -/
def Word.syllableCount (w : Word) : Nat :=
  w.syllables.length

/-! ### Minimal word constraint -/

/-- Does a prosodic word satisfy the minimal word constraint?

    [mccarthy-prince-1993]: the smallest prosodic word must
    contain at least one foot, which requires at least two morae
    (for moraic trochee languages) or two syllables (for syllabic
    trochee languages).

    Telugu requires a bimoraic minimum ([aitha-2026] §3.2):
    the shortest standalone words are informal 2SG imperatives like
    *rā* 'come' (CVV = 2μ) and *pō* 'go' (CVV = 2μ). No word
    consists of a single light syllable. -/
abbrev Word.satisfiesMinWord (w : Word) (minMorae : Nat := 2) : Prop :=
  w.moraCount ≥ minMorae

/-! ### Morphological element -/

/-- A morphological element with its prosodic properties.
    Used to determine how it interacts with the stem's Word. -/
structure MorphElement where
  /-- Surface form (for documentation). -/
  form : String
  /-- Morphological status (determines Word membership). -/
  status : MorphStatus
  /-- Weight of the initial syllable. Relevant for the Telugu weak
      alternation: the long form is triggered when a *light* initial
      syllable follows within the Word ([aitha-2026] §3.2). -/
  initialWeight : Syllable.Weight
  deriving DecidableEq, Repr

/-- Does this element trigger the long stem form in Telugu weak nouns?

    The long form (-āni) surfaces when the element is:
    1. Word-internal (inflectional suffix or agreement marker), AND
    2. Its initial syllable is light (CV = 1μ)

    Postpositions never trigger the long form, even if they begin with
    a light syllable (e.g., *-gurinci* 'about', *-eduru* 'in front of'),
    because they are Word-external. -/
abbrev MorphElement.triggersLongForm (m : MorphElement) : Prop :=
  m.status.isPrWdInternal ∧ m.initialWeight = .light

/-! ### Word-sensitive phonological processes -/

/-- Hiatus resolution obligation: within a Word, hiatus resolution
    is **obligatory**; across Word boundaries, it is **optional**.

    [aitha-2026] §3.2: Telugu *koṭṭu* 'to hit' + *-āli* 'OBLIG'
    → *koṭṭāli* (obligatory deletion of /u/ word-internally), but
    *kukka eduru* 'in front of the dog' allows optional retention. -/
inductive HiatusObligation where
  | obligatory   -- within Word
  | optional     -- across Word boundary
  deriving DecidableEq, Repr

/-- Determine hiatus resolution obligation from the morphological
    status of the following element. -/
def hiatusObligation (following : MorphStatus) : HiatusObligation :=
  if following.isPrWdInternal then .obligatory else .optional

/-! ### Worked examples

Anonymous `example`s lock in the morphological-status classification, the
minimal-word constraint, and the Telugu long-form trigger;
`agr_1sg_triggers_long` is named because it is reused elsewhere. -/

-- Morphological status: roots/inflection/agreement are Word-internal,
-- postpositions external.
example : MorphStatus.root.isPrWdInternal = true := rfl
example : MorphStatus.inflectional.isPrWdInternal = true := rfl
example : MorphStatus.agreement.isPrWdInternal = true := rfl
example : MorphStatus.postposition.isPrWdInternal = false := rfl

-- Minimal word (bimoraic): a heavy, or two lights, satisfies it; a single
-- light does not. Telugu postpositions satisfy it independently — *-lō*
-- (CVV = 2μ), *-kinda* (3μ).
example : (Word.mk [.heavy]).satisfiesMinWord := by decide
example : ¬ (Word.mk [.light]).satisfiesMinWord := by decide
example : (Word.mk [.light, .light]).satisfiesMinWord := by decide
example : (Word.mk [.heavy, .light]).satisfiesMinWord := by decide

-- Hiatus obligation: obligatory Word-internally, optional across a boundary.
example : hiatusObligation .inflectional = .obligatory := rfl
example : hiatusObligation .postposition = .optional := rfl

-- Long-form trigger: Word-internal + light initial triggers it (ACC *-ni*,
-- DAT *-ki*); postpositions never do, even *-gurinci* (light initial *gu-*).
example : (MorphElement.mk "-ni" .inflectional .light).triggersLongForm := by decide
example : (MorphElement.mk "-ki" .inflectional .light).triggersLongForm := by decide
example : ¬ (MorphElement.mk "-lō" .postposition .heavy).triggersLongForm := by decide
example : ¬ (MorphElement.mk "-gurinci" .postposition .light).triggersLongForm := by decide

/-- 1SG *-ni*: Word-internal (agreement), light → triggers the long form. Named
    because it is reused (the Telugu predicative-agreement argument). -/
theorem agr_1sg_triggers_long :
    (MorphElement.mk "-ni" .agreement .light).triggersLongForm := by decide

end Prosody
