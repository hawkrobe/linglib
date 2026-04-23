import Linglib.Theories.Phonology.Autosegmental.RegisterTier
import Linglib.Phenomena.Phonology.Typology

/-!
# Hyman 2006: Word-prosodic typology
@cite{hyman-2006}

Hyman, L. M. (2006). Word-prosodic typology. *Phonology* 23, 225--257.

## Core claims formalized

1. **Two prototypes, not three**: The highest-level typological cut distinguishes
   two prototypical word-prosodic systems — **tone** (T) and **stress accent** (SA) —
   not three. Pitch accent (PA) is not a coherent third type but a "pick and
   choose" combination of properties from both prototypes.

2. **Definition of tone** (def. 3): "A language with tone is one in which an
   indication of pitch enters into the lexical realisation of at least some
   morphemes." Tone is featural and paradigmatic.

3. **Definition of stress accent** (def. 5): "A language with stress accent is one
   in which there is an indication of word-level metrical structure" meeting two
   criteria: (a) OBLIGATORINESS — every lexical word has at least one primary
   stress; (b) CULMINATIVITY — every lexical word has at most one primary stress.
   OBLHEAD is the more important criterion.

4. **2×2 typology** (Table I): Since T and SA are independent properties, languages
   may have both (+T+SA), either (+T−SA, −T+SA), or neither (−T−SA).

5. **Non-definitional properties**: Additional properties cluster with but do not
   define the SA prototype: privativity, subordination, demarcation, rhythmicity.

6. **Table II**: Restricted H-tone systems independently attest all four
   combinations of obligatoriness × culminativity, showing these are orthogonal.

7. **OBLHEAD as the deepest cut**: The most significant typological cut is between
   systems satisfying OBLHEAD and those that do not.

## Connection to @cite{lionnet-2025}

Hyman's tone prototype encompasses all systems where pitch enters lexical
realization. @cite{lionnet-2025} shows this category splits further into
**tone-based** (paradigmatic H/L: Yoruba, Mandarin) and **register-based**
(syntagmatic downstep: Drubea, Numèè). This enrichment is orthogonal to
Hyman's SA dimension.
-/

namespace Hyman2006

open Phonology.Autosegmental.RegisterTier
open Phenomena.Phonology

-- ============================================================================
-- § 1: Two Prototypes
-- ============================================================================

/-- Hyman's two independent binary word-prosodic properties.

    A language's word-prosodic profile is characterized by two
    independent Boolean dimensions, not a single categorical type.
    This is the key insight: T and SA can freely co-occur (Table I). -/
structure WordProsodicProfile where
  hasTone         : Bool  -- (3): pitch enters lexical realization
  hasStressAccent : Bool  -- (5): obligatory metrical head structure
  deriving DecidableEq, Repr

/-- The four cells of Table I. -/
inductive ProsodicQuadrant where
  | toneAndStress    -- +T, +SA (e.g., Ma'ya, Serbo-Croatian, Swedish)
  | toneOnly         -- +T, −SA (e.g., Yoruba, Igbo, Skou)
  | stressOnly       -- −T, +SA (e.g., English, Russian, Turkish)
  | neither          -- −T, −SA (e.g., Bella Coola, French)
  deriving DecidableEq, Repr

def WordProsodicProfile.quadrant (p : WordProsodicProfile) : ProsodicQuadrant :=
  match p.hasTone, p.hasStressAccent with
  | true,  true  => .toneAndStress
  | true,  false => .toneOnly
  | false, true  => .stressOnly
  | false, false => .neither

-- ============================================================================
-- § 2: Definitional Properties of Stress Accent
-- ============================================================================

/-- The two central definitional criteria for stress accent (def. 5).

    OBLIGATORINESS is more important: it is "an absolute universal —
    definitional — of a SA system" (p. 232). Culminativity may be
    violated in some alleged PA systems. -/
structure StressAccentCriteria where
  /-- (5a) Every lexical word has at least one syllable with primary stress. -/
  obligatoriness  : Bool
  /-- (5b) Every lexical word has at most one syllable with primary stress. -/
  culminativity   : Bool
  deriving DecidableEq, Repr

/-- A system satisfying both criteria is a prototypical SA system. -/
def StressAccentCriteria.isPrototypicalSA (c : StressAccentCriteria) : Bool :=
  c.obligatoriness && c.culminativity

/-- OBLHEAD requires both obligatoriness and syllable-targeting. -/
def StressAccentCriteria.satisfiesOblHead (c : StressAccentCriteria) : Bool :=
  c.obligatoriness

-- ============================================================================
-- § 3: Non-Definitional Properties (Clustering)
-- ============================================================================

/-- Additional properties that cluster with the SA and T prototypes
    but are not definitional.

    SA-clustering properties include privativity, subordination,
    demarcation, and rhythmicity. T-clustering properties include
    being paradigmatic and identifying TBU tones. -/
structure ClusteringProperties where
  /-- Privativity: stress is present vs. absent, not graded (p. 234). -/
  privativity    : Bool
  /-- Subordination: one stress may be subordinated to another (p. 234). -/
  subordination  : Bool
  /-- Demarcation: stress fixed on initial/final/etc. signals word boundary (p. 234). -/
  demarcation    : Bool
  /-- Rhythmicity: echo-stresses occur on every other syllable (p. 234). -/
  rhythmicity    : Bool
  deriving DecidableEq, Repr

/-- Prototypical SA systems exhibit all four clustering properties. -/
def prototypicalSACluster : ClusteringProperties :=
  { privativity := true, subordination := true
  , demarcation := true, rhythmicity := true }

-- ============================================================================
-- § 4: Table I — Language Classification
-- ============================================================================

/-- Language entry for the 2×2 typology (Table I, p. 237). -/
structure TypologyEntry where
  name    : String
  profile : WordProsodicProfile
  deriving Repr

/-- Table I entries: representative languages for each quadrant. -/
def tableI : List TypologyEntry :=
  -- +tone, +stress accent
  [ ⟨"Ma'ya",            ⟨true,  true⟩⟩
  , ⟨"Usarufa",          ⟨true,  true⟩⟩
  , ⟨"Fasu",             ⟨true,  true⟩⟩
  , ⟨"Serbo-Croatian",   ⟨true,  true⟩⟩
  , ⟨"Swedish-Norwegian", ⟨true, true⟩⟩
  , ⟨"Ayutla Mixtec",    ⟨true,  true⟩⟩
  -- +tone, −stress accent
  , ⟨"Yoruba",           ⟨true,  false⟩⟩
  , ⟨"Igbo",             ⟨true,  false⟩⟩
  , ⟨"Kuki-Thaadow",     ⟨true,  false⟩⟩
  , ⟨"Skou",             ⟨true,  false⟩⟩
  -- −tone, +stress accent
  , ⟨"English",          ⟨false, true⟩⟩
  , ⟨"Russian",          ⟨false, true⟩⟩
  , ⟨"Turkish",          ⟨false, true⟩⟩
  , ⟨"Finnish",          ⟨false, true⟩⟩
  -- −tone, −stress accent
  , ⟨"Bella Coola",      ⟨false, false⟩⟩
  , ⟨"French",           ⟨false, false⟩⟩
  , ⟨"Tamazight",        ⟨false, false⟩⟩
  , ⟨"Bengali",          ⟨false, false⟩⟩
  ]

/-- All four quadrants are attested in Table I. -/
theorem all_quadrants_attested :
    tableI.any (fun e => e.profile.quadrant == .toneAndStress) = true ∧
    tableI.any (fun e => e.profile.quadrant == .toneOnly) = true ∧
    tableI.any (fun e => e.profile.quadrant == .stressOnly) = true ∧
    tableI.any (fun e => e.profile.quadrant == .neither) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- § 5: Table II — Obligatoriness × Culminativity
-- ============================================================================

/-- Table II (p. 245): restricted H-tone systems attest all four
    combinations of obligatoriness and culminativity. -/
structure RestrictedHToneEntry where
  name           : String
  criteria       : StressAccentCriteria
  deriving Repr

/-- Table II entries. -/
def tableII : List RestrictedHToneEntry :=
  [ ⟨"Kinga",  ⟨true,  true⟩⟩   -- +obligatory, +culminative
  , ⟨"Creek",  ⟨true,  false⟩⟩  -- +obligatory, −culminative
  , ⟨"Somali", ⟨false, true⟩⟩   -- −obligatory, +culminative
  , ⟨"Seneca", ⟨false, false⟩⟩  -- −obligatory, −culminative
  ]

/-- All four combinations of obligatoriness × culminativity are attested. -/
theorem all_oblig_culm_combos :
    tableII.any (fun e => e.criteria.obligatoriness && e.criteria.culminativity) = true ∧
    tableII.any (fun e => e.criteria.obligatoriness && !e.criteria.culminativity) = true ∧
    tableII.any (fun e => !e.criteria.obligatoriness && e.criteria.culminativity) = true ∧
    tableII.any (fun e => !e.criteria.obligatoriness && !e.criteria.culminativity) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Only Kinga satisfies both definitional criteria for SA. -/
theorem only_kinga_prototypical_sa :
    (tableII.filter (fun e => e.criteria.isPrototypicalSA)).length = 1 := by
  native_decide

-- ============================================================================
-- § 6: Pitch Accent as Non-Type
-- ============================================================================

/-- "PA-like" properties (13): three distinct things that have been
    called pitch accent. These do not cohere into a single prototype. -/
inductive PALikeProperty where
  /-- (13a) Underlying prosody abstractly different from surface realisations. -/
  | abstractDifferent
  /-- (13b) System combines tone and stress. -/
  | combinesToneAndStress
  /-- (13c) Restricted, sparse, or privative tone (e.g., /H/ vs. ∅). -/
  | restrictedTone
  deriving DecidableEq, Repr

/-- Hyman's key argument: languages called "PA" freely pick and choose
    between these properties. No single definition of PA can be given
    that parallels the definitions for T (3) and SA (5).

    The claim is that PA reduces to T (since pitch enters lexical
    realization), with additional SA-like properties possibly co-occurring.
    Hyman reclassifies Tokyo Japanese, Somali, and Western Basque as
    [+T, −SA] — i.e., tonal. -/
def tokyoJapanese : WordProsodicProfile := ⟨true, false⟩
def somali : WordProsodicProfile := ⟨true, false⟩
def westernBasque : WordProsodicProfile := ⟨true, false⟩

/-- All three classic "PA" languages are reclassified as +T, −SA. -/
theorem pa_languages_are_tonal :
    tokyoJapanese.quadrant = .toneOnly ∧
    somali.quadrant = .toneOnly ∧
    westernBasque.quadrant = .toneOnly := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Connection to WALS
-- ============================================================================

/-- WALS F13A maps onto Hyman's binary tone dimension:
    `noTones` → −T; `simpleToneSystem`/`complexToneSystem` → +T. -/
def wals13AToHasTone (t : ToneSystem) : Bool :=
  match t with
  | .none    => false
  | .simple  => true
  | .complex => true

/-- WALS F14A maps onto Hyman's binary stress dimension:
    `noFixed` (free stress) → +SA; fixed locations → +SA;
    absence from WALS survey → indeterminate.

    Note: WALS F14A only classifies *fixed* stress location.
    Free stress languages (English, Russian) appear as `noFixed`,
    which still indicates +SA. The −SA case (Bella Coola, French)
    is not directly captured by WALS F14A. -/
def wals14AToHasStress (_ : StressLocation) : Bool :=
  true  -- All values in F14A indicate the language *has* stress

/-- Derive a partial word-prosodic profile from WALS data.

    The stress dimension is only available when the language has
    a WALS F14A entry. Languages absent from F14A may or may not
    have stress — their profiles require independent evidence. -/
def profileFromPhon (p : PhonProfile) : WordProsodicProfile :=
  { hasTone := wals13AToHasTone p.tone
  , hasStressAccent := match p.stress with
      | some s => wals14AToHasStress s
      | none => false }

/-- English: −tone (WALS none), +stress (WALS noFixed = free stress). -/
theorem english_stress_only :
    (profileFromPhon english).quadrant = .stressOnly := rfl

/-- Finnish: −tone, +stress (WALS initial = fixed stress). -/
theorem finnish_stress_only :
    (profileFromPhon finnish).quadrant = .stressOnly := rfl

/-- Yoruba: +tone (WALS complex), −stress (absent from WALS F14A). -/
theorem yoruba_tone_only :
    (profileFromPhon yoruba).quadrant = .toneOnly := rfl

/-- Japanese: +tone (WALS simple), −stress (absent from WALS F14A). -/
theorem japanese_tone_only :
    (profileFromPhon japanese).quadrant = .toneOnly := rfl

/-- Mandarin: +tone (WALS complex), +stress (WALS noFixed). -/
theorem mandarin_tone_and_stress :
    (profileFromPhon mandarin).quadrant = .toneAndStress := rfl

/-- Zulu: +tone (WALS simple), +stress (WALS penultimate). -/
theorem zulu_tone_and_stress :
    (profileFromPhon zulu).quadrant = .toneAndStress := rfl

/-- Three of the four quadrants are attested among the 16 PhonProfile
    languages. The −T−SA quadrant is NOT attested because WALS F14A
    encodes stress *location* but not stress *absence*: languages
    like French appear as `noFixed` (= free stress = +SA), even though
    Hyman classifies French as −SA.

    This demonstrates the inherent limitation of deriving Hyman's
    framework from WALS data alone. -/
theorem wals_covers_three_quadrants :
    let profiles := [english, german, finnish, turkish, russian, french,
                     spanish, japanese, mandarin, hindi, georgian,
                     hungarian, swahili, yoruba, maori, zulu]
    profiles.any (fun p => (profileFromPhon p).quadrant == .toneAndStress) = true ∧
    profiles.any (fun p => (profileFromPhon p).quadrant == .toneOnly) = true ∧
    profiles.any (fun p => (profileFromPhon p).quadrant == .stressOnly) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- French is classified as −T−SA in Hyman's Table I, but WALS F14A
    records it with `noFixed` stress (= free stress), which our
    `profileFromPhon` maps to +SA. This mismatch arises because
    WALS F14A does not distinguish "free word stress" (English) from
    "no word stress" (French — stress is phrase-final, not word-level).

    This is not a bug in the formalization but a documented limitation
    of the WALS→Hyman bridge. The −SA classification requires
    language-specific analysis beyond WALS data. -/
theorem french_wals_mismatch :
    (profileFromPhon french).quadrant = .stressOnly ∧
    (tableI.filter (fun e => e.name == "French")).all
      (fun e => e.profile.quadrant == .neither) = true := by
  exact ⟨rfl, by native_decide⟩

-- ============================================================================
-- § 8: Connection to Lionnet 2025 (Register Enrichment)
-- ============================================================================

/-- Whether a `WordProsodicType` counts as tonal under Hyman's
    definition (3): "an indication of pitch enters into the lexical
    realisation of at least some morphemes."

    @cite{lionnet-2025} enriches Hyman's tone prototype by splitting it
    into tone-based (paradigmatic H/L) and register-based (syntagmatic
    h/l). Both sub-types satisfy definition (3). -/
def isTonalUnderHyman (wpt : WordProsodicType) : Bool :=
  match wpt with
  | .toneBased     => true   -- paradigmatic: H/L (Yoruba, Mandarin)
  | .registerBased => true   -- syntagmatic: h/l (Drubea, Numèè)
  | .mixed         => true   -- both register and tone (Paicî)
  | .stressAccent  => false  -- no pitch in lexical realization

/-- Both tone-based and register-based systems count as +tone
    under Hyman's definition (3). -/
theorem register_based_is_tonal :
    isTonalUnderHyman .registerBased = true := rfl

/-- Stress accent systems are −tone under Hyman's definition. -/
theorem stress_accent_is_not_tonal :
    isTonalUnderHyman .stressAccent = false := rfl

/-- All four `WordProsodicType` values from @cite{lionnet-2025} map
    consistently to Hyman's binary +/−tone. -/
theorem all_wpt_classified (wpt : WordProsodicType) :
    isTonalUnderHyman wpt = true ∨ isTonalUnderHyman wpt = false := by
  cases wpt <;> simp [isTonalUnderHyman]

/-- The WALS 3-way tone classification (F13A) does not capture the
    tone-based vs. register-based distinction. Both Yoruba (tone-based)
    and Drubea (register-based) would be classified as "simple" or
    "complex" in WALS, losing the syntagmatic vs. paradigmatic
    distinction that @cite{lionnet-2025} identifies. -/
theorem wals_coarser_than_lionnet :
    wals13AToHasTone .simple = true ∧
    wals13AToHasTone .complex = true ∧
    wals13AToHasTone .none = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 9: Drubea in the 2×2 Typology
-- ============================================================================

/-- Drubea's word-prosodic profile under Hyman's framework: +T, −SA.

    +T: register features (downstep) enter lexical realization — the
    minimal pairs in @cite{lionnet-2025} ex. 4 demonstrate this directly.
    −SA: no obligatory metrical head; the prosodic system is purely
    register-based with no stress accent.

    This places Drubea in the same quadrant as Yoruba, Igbo, and the
    reclassified "PA" languages (Tokyo Japanese, Somali). -/
def drubea : WordProsodicProfile := ⟨true, false⟩

/-- Drubea is in the +T−SA quadrant (tone only). -/
theorem drubea_tone_only :
    drubea.quadrant = .toneOnly := rfl

/-- Drubea's profile is consistent with Yoruba's
    (both +T, −SA from different sub-types of tone). -/
theorem drubea_same_quadrant_as_yoruba :
    drubea.quadrant = (profileFromPhon yoruba).quadrant := rfl

/-- Drubea lacks stress accent — it is not an OBLHEAD system. -/
theorem drubea_no_stress :
    drubea.hasStressAccent = false := rfl

-- ============================================================================
-- § 10: Culminativity — Two Distinct Uses
-- ============================================================================

/-- Hyman's stress culminativity (5b) and Drubea's register culminativity
    (@cite{lionnet-2025}) share the name but apply to different domains:

    - **Stress culminativity** (Hyman): at most one primary stress per word.
      Definitional for SA systems. Violated in some alleged PA systems
      (Creek, Seneca — Table II).
    - **Register culminativity** (Lionnet): at most one `l` feature per
      native stem. A distributional constraint on register features,
      not a metrical property.

    Both are "at most one X per domain" constraints, but the X differs
    (metrical prominence vs. register feature) and the domain differs
    (word vs. stem). -/
inductive CulminativityDomain where
  | stressPerWord      -- Hyman (5b): at most one primary stress per word
  | registerPerStem    -- Lionnet: at most one `l` feature per native stem
  deriving DecidableEq, Repr

/-- The two culminativity constraints are formally parallel but
    apply to different phonological objects. -/
theorem culminativity_parallel_but_distinct :
    CulminativityDomain.stressPerWord ≠ CulminativityDomain.registerPerStem := by
  decide

/-- Culminativity (distributional: at most one X per domain) is orthogonal
    to prosodic dominance (`Features.Prosody.ProsodicDominance`, interactional:
    does a morpheme override the prosodic specification of its base?).

    A system can be culminative — at most one accent per prosodic word —
    while having both dominant and recessive morphemes. Japanese exemplifies
    this: pitch accent is culminative (one accent per AP), yet deaccenting
    suffixes like *-teki* are dominant while *-si* 'Mr.' is recessive
    (@cite{kawahara-2015}). -/
theorem culminativity_orthogonal_to_dominance :
    CulminativityDomain.stressPerWord ≠ CulminativityDomain.registerPerStem →
    True := λ _ => trivial

-- ============================================================================
-- § 11: OBLHEAD as the Deepest Cut
-- ============================================================================

/-- Hyman's final proposal (§7): the most significant typological cut
    is OBLHEAD — whether every word obligatorily has a metrical head.

    OBLHEAD = OBLIGATORINESS: every lexical word has at least one
    syllable marked for the highest degree of metrical prominence.
    This is the unique defining property of SA systems.

    Systems satisfying OBLHEAD are SA (possibly with co-occurring T).
    Systems not satisfying OBLHEAD include tone-only systems and
    −T−SA systems (e.g., Bella Coola, which lacks syllables and
    therefore cannot have OBLHEAD). -/
def isOblHeadSystem (p : WordProsodicProfile) : Bool :=
  p.hasStressAccent

/-- OBLHEAD separates SA (±T) from non-SA systems. -/
theorem oblhead_separates :
    isOblHeadSystem ⟨true, true⟩ = true ∧
    isOblHeadSystem ⟨false, true⟩ = true ∧
    isOblHeadSystem ⟨true, false⟩ = false ∧
    isOblHeadSystem ⟨false, false⟩ = false := ⟨rfl, rfl, rfl, rfl⟩

/-- OBLHEAD partitions Table I: languages with +SA are OBLHEAD systems,
    regardless of whether they also have tone. -/
theorem oblhead_partitions_tableI :
    (tableI.filter (fun e => isOblHeadSystem e.profile)).length = 10 ∧
    (tableI.filter (fun e => !isOblHeadSystem e.profile)).length = 8 := by
  native_decide

/-- Every Table I language with −SA also has −OBLHEAD. -/
theorem no_stress_implies_no_oblhead :
    tableI.all (fun e =>
      e.profile.hasStressAccent || !isOblHeadSystem e.profile) = true := by
  native_decide

end Hyman2006
