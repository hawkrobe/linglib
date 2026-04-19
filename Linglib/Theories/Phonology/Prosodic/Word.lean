import Linglib.Theories.Phonology.Prosodic.Syllable.Foot
import Linglib.Core.Prosody

/-!
# Prosodic Word (PrWd)
@cite{selkirk-1984}

The prosodic word (PrWd, ω) is the prosodic constituent immediately
above the foot in the prosodic hierarchy:

    σ < f < **ω** < φ < ι

PrWd is the domain for a cluster of phonological processes:
- **Stress assignment** and metrical parsing
- **Vowel harmony** (progressive harmony in Telugu)
- **Minimal word constraints** (bimoraic minimum)
- **Obligatory hiatus resolution** (within PrWd; optional across PrWd)

## Morphosyntax-Prosody Mapping

Not all morphological elements are PrWd-internal. The mapping from
morphosyntactic structure to prosodic structure determines which
elements fall within the PrWd and which form their own domain:

| Morphological status | PrWd membership | Example (Telugu)     |
|----------------------|-----------------|----------------------|
| Root                 | Internal        | samudr-              |
| Derivational suffix  | Internal        | (not shown)          |
| Inflectional suffix  | Internal        | -am, -ni, -ki        |
| Agreement suffix     | Internal        | -ni (1SG), -vi (2SG) |
| Postposition         | **External**    | -lō, -tō, -gurinci  |

This boundary is diagnosed by vowel harmony scope, minimal word
effects, and obligatory vs optional hiatus resolution
(@cite{aitha-2026} §3.2).

## Connection to Linglib

`Core.Prosody` defines the prosodic hierarchy levels (σ, f, ω, φ, ι)
and intonational structure. This module provides the *internal
structure* of the prosodic word: syllable constituency, weight
profiles, minimal word constraints, and the morphosyntax-prosody
mapping that determines PrWd boundaries.
-/

namespace Phonology.ProsodicWord

open Phonology.Syllable

-- ============================================================================
-- § 1: Morphological Status and PrWd Membership
-- ============================================================================

/-- The morphological status of an element relative to the prosodic word.
    Determines whether the element is parsed inside the PrWd with the
    stem or forms a separate prosodic domain. -/
inductive MorphStatus where
  /-- Root morpheme: always PrWd-internal. -/
  | root
  /-- Derivational affix: PrWd-internal with the stem. -/
  | derivational
  /-- Inflectional affix (case, number, tense): PrWd-internal. -/
  | inflectional
  /-- Agreement marker: PrWd-internal (crucially, for Telugu nominal
      predicative agreement; @cite{aitha-2026} §3.1). -/
  | agreement
  /-- Postposition: forms a **separate** PrWd. Evidence: not subject to
      progressive vowel harmony, obeys minimal word constraint
      independently, hiatus resolution across boundary is optional
      (@cite{aitha-2026} §3.2). -/
  | postposition
  /-- Clitic: may be PrWd-internal or -external depending on the
      language and the specific clitic. -/
  | clitic
  deriving DecidableEq, Repr

/-- Is this morphological element parsed inside the PrWd with the stem?

    The boundary between PrWd-internal and PrWd-external elements is
    empirically diagnosed by:
    1. **Vowel harmony**: progressive harmony in Telugu affects only
       PrWd-internal suffixes, not postpositions
    2. **Minimal word constraint**: postpositions independently satisfy
       the bimoraic minimum; inflectional suffixes do not
    3. **Hiatus resolution**: obligatory within PrWd, optional across
       PrWd boundaries -/
def MorphStatus.isPrWdInternal : MorphStatus → Bool
  | .root | .derivational | .inflectional | .agreement => true
  | .postposition | .clitic => false

-- ============================================================================
-- § 2: Prosodic Word Structure
-- ============================================================================

/-- A prosodic word: a sequence of syllables (by weight) that forms a
    single domain for stress assignment and phonological processes.

    The `syllables` field gives the weight profile in linear order.
    For example, Telugu *samudram* 'ocean' has profile [L, L, H]
    (sa.mu.dram). -/
structure PrWd where
  syllables : List SyllWeight
  deriving DecidableEq, Repr

/-- Total mora count of a prosodic word. -/
def PrWd.moraCount (w : PrWd) : Nat :=
  w.syllables.foldl (· + ·.morae) 0

/-- Number of syllables. -/
def PrWd.syllableCount (w : PrWd) : Nat :=
  w.syllables.length

-- ============================================================================
-- § 3: Minimal Word Constraint
-- ============================================================================

/-- Does a prosodic word satisfy the minimal word constraint?

    @cite{mccarthy-prince-1993}: the smallest prosodic word must
    contain at least one foot, which requires at least two morae
    (for moraic trochee languages) or two syllables (for syllabic
    trochee languages).

    Telugu requires a bimoraic minimum (@cite{aitha-2026} §3.2):
    the shortest standalone words are informal 2SG imperatives like
    *rā* 'come' (CVV = 2μ) and *pō* 'go' (CVV = 2μ). No word
    consists of a single light syllable. -/
def PrWd.satisfiesMinWord (w : PrWd) (minMorae : Nat := 2) : Bool :=
  w.moraCount ≥ minMorae

-- ============================================================================
-- § 4: Morphological Element
-- ============================================================================

/-- A morphological element with its prosodic properties.
    Used to determine how it interacts with the stem's PrWd. -/
structure MorphElement where
  /-- Surface form (for documentation). -/
  form : String
  /-- Morphological status (determines PrWd membership). -/
  status : MorphStatus
  /-- Weight of the initial syllable. Relevant for the Telugu weak
      alternation: the long form is triggered when a *light* initial
      syllable follows within the PrWd (@cite{aitha-2026} §3.2). -/
  initialWeight : SyllWeight
  deriving DecidableEq, Repr

/-- Does this element trigger the long stem form in Telugu weak nouns?

    The long form (-āni) surfaces when the element is:
    1. PrWd-internal (inflectional suffix or agreement marker), AND
    2. Its initial syllable is light (CV = 1μ)

    Postpositions never trigger the long form, even if they begin with
    a light syllable (e.g., *-gurinci* 'about', *-eduru* 'in front of'),
    because they are PrWd-external. -/
def MorphElement.triggersLongForm (m : MorphElement) : Bool :=
  m.status.isPrWdInternal && m.initialWeight == .light

-- ============================================================================
-- § 5: PrWd-Sensitive Phonological Processes
-- ============================================================================

/-- Hiatus resolution obligation: within a PrWd, hiatus resolution
    is **obligatory**; across PrWd boundaries, it is **optional**.

    @cite{aitha-2026} §3.2: Telugu *koṭṭu* 'to hit' + *-āli* 'OBLIG'
    → *koṭṭāli* (obligatory deletion of /u/ word-internally), but
    *kukka eduru* 'in front of the dog' allows optional retention. -/
inductive HiatusObligation where
  | obligatory   -- within PrWd
  | optional     -- across PrWd boundary
  deriving DecidableEq, Repr

/-- Determine hiatus resolution obligation from the morphological
    status of the following element. -/
def hiatusObligation (following : MorphStatus) : HiatusObligation :=
  if following.isPrWdInternal then .obligatory else .optional

-- ============================================================================
-- § 6: Verification
-- ============================================================================

-- Morphological status classification

theorem root_is_internal : MorphStatus.root.isPrWdInternal = true := rfl
theorem infl_is_internal : MorphStatus.inflectional.isPrWdInternal = true := rfl
theorem agr_is_internal : MorphStatus.agreement.isPrWdInternal = true := rfl
theorem postp_is_external : MorphStatus.postposition.isPrWdInternal = false := rfl

-- Minimal word examples

/-- A single heavy syllable (CVV or CVC) = 2μ: satisfies bimoraic min. -/
theorem heavy_satisfies_min : (PrWd.mk [.heavy]).satisfiesMinWord = true := rfl

/-- A single light syllable (CV) = 1μ: violates bimoraic min. -/
theorem light_violates_min : (PrWd.mk [.light]).satisfiesMinWord = false := rfl

/-- Two light syllables (CV.CV) = 2μ: satisfies bimoraic min. -/
theorem ll_satisfies_min : (PrWd.mk [.light, .light]).satisfiesMinWord = true := rfl

-- Telugu postpositions satisfy min word independently

/-- *-lō* 'in' (CVV = 2μ): satisfies min word as a separate PrWd. -/
theorem lo_satisfies_min : (PrWd.mk [.heavy]).satisfiesMinWord = true := rfl

/-- *-kinda* 'below' (CVC.CV = 3μ): satisfies min word. -/
theorem kinda_satisfies_min : (PrWd.mk [.heavy, .light]).satisfiesMinWord = true := rfl

-- Hiatus obligation

theorem infl_hiatus_obligatory :
    hiatusObligation .inflectional = .obligatory := rfl

theorem postp_hiatus_optional :
    hiatusObligation .postposition = .optional := rfl

-- Triggering the long form

/-- ACC *-ni*: PrWd-internal, light → triggers long form. -/
theorem acc_ni_triggers_long :
    (MorphElement.mk "-ni" .inflectional .light).triggersLongForm = true := rfl

/-- DAT *-ki*: PrWd-internal, light → triggers long form. -/
theorem dat_ki_triggers_long :
    (MorphElement.mk "-ki" .inflectional .light).triggersLongForm = true := rfl

/-- 1SG *-ni*: PrWd-internal (agreement), light → triggers long form. -/
theorem agr_1sg_triggers_long :
    (MorphElement.mk "-ni" .agreement .light).triggersLongForm = true := rfl

/-- P *-lō* 'in': PrWd-external → does NOT trigger long form. -/
theorem postp_lo_no_long :
    (MorphElement.mk "-lō" .postposition .heavy).triggersLongForm = false := rfl

/-- P *-gurinci* 'about': PrWd-external → does NOT trigger long form,
    even though its initial syllable *gu-* is light. -/
theorem postp_gurinci_no_long :
    (MorphElement.mk "-gurinci" .postposition .light).triggersLongForm = false := rfl

end Phonology.ProsodicWord
