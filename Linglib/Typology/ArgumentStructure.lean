import Linglib.Data.WALS.Features.F100A
import Linglib.Data.WALS.Features.F105A
import Linglib.Data.WALS.Features.F106A
import Linglib.Data.WALS.Features.F107A
import Linglib.Data.WALS.Features.F108A
import Linglib.Data.WALS.Features.F108B
import Linglib.Data.WALS.Features.F109A
import Linglib.Data.WALS.Features.F109B
import Linglib.Data.WALS.Features.F110A
import Linglib.Data.WALS.Features.F111A
import Linglib.Features.Case.Basic

/-!
# Typology.ArgumentStructure
[maslova-nedjalkov-2013] [siewierska-2013]
[haspelmath-2013-ditransitive]
[polinsky-2013-antipassive] [polinsky-2013-applicative]
[song-2013-periphrastic] [song-2013-nonperiphrastic]
[nordlinger-2023]
[konig-kokutani-2006] [siloni-2008] [siloni-2012]

Per-language typological substrate for valence and voice constructions,
covering WALS chapters 105--111:

- **Ch 105** ([haspelmath-2013-ditransitive]): Ditransitive constructions ('give') --
  alignment of R (recipient) and T (theme) with monotransitive P.
- **Ch 106** ([maslova-nedjalkov-2013]): Reciprocal constructions and
  their relationship to reflexives.
- **Ch 107** ([siewierska-2013]): Passive constructions -- presence/absence.
- **Ch 108** ([polinsky-2013-antipassive]): Antipassive constructions.
- **Ch 109** ([polinsky-2013-applicative]): Applicative constructions.
- **Ch 110** ([song-2013-periphrastic]): Periphrastic causative constructions.
- **Ch 111** ([song-2013-nonperiphrastic]): Nonperiphrastic causative
  constructions (morphological vs compound).

Mirrors the `Linglib/Typology/{Possession,Negation,Comparison,Coordination,
Modality,Gender,Alignment}` substrate-extension pattern. Fragment-importable.

## What lives here

- `ReciprocalType` (4-way), `RecipStrategy` (7-way), `RecipValency` (2-way),
  `RecipFormation` (2-way) reciprocal classifications.
- `PassivePresence` (Ch 107).
- `AntipassiveType` + `AntipassiveProductivity` (Ch 108).
- `DitransitiveType` (Ch 105).
- `ApplicativeBase` × `AppliedObjectRole` × `ApplicativeType` (Ch 109).
- `PeriphrasticCausativeType` (Ch 110), `NonperiphrCausativeType` (Ch 111).
- `ValenceProfile` per-language struct (Ch 106--109 + Ch 111).
- `AlignmentType` abbreviation pointing at `Features.AlignmentFamily` (the
  accusative/ergative dichotomy used for the antipassive correlation;
  the richer 5-way typology lives in `Alignment.AlignmentType`).
- WALS converters `fromWALS{105A,106A,108A,109A,109B,111A}`.
- WALS aggregate sample-size + corpus-only theorems.

## Theory-laden caveats

- `RecipStrategy.isNominal` follows König & Kokutani (2006)'s primary
  typological distinction; clitics are classified non-nominal because
  their valence behavior is verbal (e.g. French/Czech `se` reduces valence).
- `RecipFormation.allowsDiscontinuous` encodes Siloni 2008/2012's empirical
  prediction: only lexically-formed reciprocals license discontinuous
  ("John kissed with Mary") forms.

## Out of scope

Per-language WALS data is in `Data/WALS/Features/F106A.lean` etc., with
converters above (`fromWALS106A`, `fromWALS108A`, `fromWALS109A`,
`fromWALS111A`). Pylkkänen's structural Appl typology and its WALS
divergence are in `Studies/Pylkkanen2008.lean`. Nordlinger's extended
reciprocal apparatus (`RecipProfile`, strategy/valency correlations) is
in `Studies/Nordlinger2023.lean`. Song's morphological-causative
morpheme examples are in `Studies/Song2013.lean`.
-/

set_option autoImplicit false

namespace Typology.ArgumentStructure

private abbrev f100a := Data.WALS.F100A.allData
private abbrev f105a := Data.WALS.F105A.allData
private abbrev f106a := Data.WALS.F106A.allData
private abbrev f107a := Data.WALS.F107A.allData
private abbrev f108a := Data.WALS.F108A.allData
private abbrev f108b := Data.WALS.F108B.allData
private abbrev f109a := Data.WALS.F109A.allData
private abbrev f109b := Data.WALS.F109B.allData
private abbrev f110a := Data.WALS.F110A.allData
private abbrev f111a := Data.WALS.F111A.allData

-- ============================================================================
-- §1. Reciprocal Constructions (Ch 106 + Nordlinger 2023 strategy/valency)
-- ============================================================================

/-- WALS Ch 106: How reciprocal situations are encoded relative to reflexives.

    The four values follow [maslova-nedjalkov-2013]'s classification:

    - `noDedicated`: "There are no non-iconic reciprocal constructions" --
      the language lacks a dedicated grammatical reciprocal marker.
    - `distinctFromReflexive`: "All reciprocal constructions are formally
      distinct from reflexive constructions" (e.g. English "each other" vs
      "themselves").
    - `mixed`: "There are both reflexive and non-reflexive reciprocal
      constructions" -- the language has both a reflexive-identical strategy
      and a formally distinct one (e.g. German "sich" + "einander").
      Common in Europe.
    - `identicalToReflexive`: "The reciprocal and reflexive constructions
      are formally identical" (e.g. Imbabura Quechua "-ri",
      West Greenlandic "-ssin-"). -/
inductive ReciprocalType where
  | noDedicated
  | distinctFromReflexive
  | mixed
  | identicalToReflexive
  deriving DecidableEq, Repr

instance : Inhabited ReciprocalType := ⟨.noDedicated⟩

/-- Morphosyntactic strategy for encoding reciprocity.

    [nordlinger-2023] summarizes the structural typologies of
    König & Kokutani (2006), Nedjalkov (2007a), and Evans (2008), which
    classify reciprocal constructions by the morphosyntactic locus
    of the reciprocal marking:

    - `bipartiteNP`: Bipartite quantifier NP -- English "each other",
      Icelandic "hvor...annad" (two independently inflected parts).
    - `recipPronoun`: Reciprocal pronoun -- Russian "drug druga",
      Hausa "jùnan-mù". Free-standing pronominal form in object position.
    - `recipClitic`: Reciprocal clitic -- French/Czech "se",
      Wambaya "-ngg-" (RR morpheme in auxiliary). Intermediate between
      pronoun and affix; functionally verbal (valence-reducing in most
      cases, though Wambaya retains bivalent syntax via ergative case).
    - `verbalAffix`: Morphological marking on the verb -- Swahili "-ana",
      Hungarian "-oz-", Chicheŵa "-an-". Derives an intransitive
      (monovalent) verb from a transitive base.
    - `verbalAuxiliary`: Reciprocal auxiliary -- Warrwa "wanji-" replaces
      the regular transitive auxiliary.
    - `lexical`: Inherently reciprocal predicate -- English "quarrel",
      "meet". The symmetric meaning is part of the verb's lexical semantics.
    - `compoundVerb`: Compound verb -- Mandarin "dǎ-lái-dǎ-qù"
      (beat-come-beat-go = 'beat each other'). -/
inductive RecipStrategy where
  | bipartiteNP
  | recipPronoun
  | recipClitic
  | verbalAffix
  | verbalAuxiliary
  | lexical
  | compoundVerb
  deriving DecidableEq, Repr

/-- Whether the strategy marks the NP/argument position (nominal strategy)
    or the verb/predicate (verbal strategy).
    König & Kokutani (2006)'s primary typological distinction.

    Clitics are classified as non-nominal: Evans (2008) treats them as
    intermediate, but their valence behavior is typically verbal --
    French/Czech "se" reduces valence (monovalent), and even Wambaya
    "-ngg-" is morphologically bound to the auxiliary. -/
def RecipStrategy.isNominal : RecipStrategy → Bool
  | .bipartiteNP     => true
  | .recipPronoun    => true
  | .recipClitic     => false
  | .verbalAffix     => false
  | .verbalAuxiliary => false
  | .lexical         => false
  | .compoundVerb    => false

/-- Valency effect of reciprocal construction on the base predicate.

    Maslova (2008) distinguishes "unary" and "binary" reciprocals;
    [nordlinger-2023] discusses how NP/argument strategies tend to
    preserve valency while verb-marked strategies tend to reduce it. The
    correlation is a tendency, not absolute -- Malagasy verb-marked
    reciprocals retain full valency at f-structure (Hurst 2006, 2012). -/
inductive RecipValency where
  | bivalent    -- two syntactic arguments preserved
  | monovalent  -- verb becomes intransitive (single subject NP)
  deriving DecidableEq, Repr

/-- Where reciprocal verbs are formed, per Siloni (2008, 2012).

    [nordlinger-2023] discusses Siloni's distinction:
    - `lexical`: formed in the lexicon through "bundling" -- two thematic
      roles (agent, patient) merge into a single complex role. Produces
      verbs with inherently symmetric semantics. Can license discontinuous
      reciprocal constructions (subject + comitative argument).
    - `syntactic`: formed in the syntax via an operation that creates
      the symmetric reading. Cannot license discontinuous reciprocals.

    Key empirical prediction: discontinuous reciprocals ("John kissed
    with Mary") are possible only with lexically-formed reciprocal verbs. -/
inductive RecipFormation where
  | lexical
  | syntactic
  deriving DecidableEq, Repr

/-- Can the reciprocal construction appear in discontinuous form
    (reciprocants split across subject and comitative argument)?
    [nordlinger-2023] §3.3. -/
def RecipFormation.allowsDiscontinuous : RecipFormation → Bool
  | .lexical   => true
  | .syntactic => false

-- ============================================================================
-- §2. Passive Constructions (Ch 107)
-- ============================================================================

/-- WALS Ch 107: Whether a language has passive constructions.

    Siewierska defines a passive as having five properties: (i) contrasts
    with active, (ii) active subject demoted or suppressed, (iii) active
    object promoted to subject (if personal passive), (iv) pragmatically
    restricted, (v) special verbal morphology. Includes both personal and
    impersonal passives, both synthetic (Swahili `-w-`) and periphrastic
    (English "be + past participle", Polish `zostac + participle`).

    - `present`: The language has at least one passive construction.
    - `absent`: No passive construction (agent demotion achieved by other
      means: subject omission, impersonal pronoun, 3pl verb form, etc.). -/
inductive PassivePresence where
  | present
  | absent
  deriving DecidableEq, Repr

-- ============================================================================
-- §3. Antipassive Constructions (Ch 108)
-- ============================================================================

/-- WALS Ch 108: Antipassive construction type.

    An antipassive is a derived detransitivized construction: the patient-like
    argument is either suppressed or demoted to an oblique. The term indicates
    the mirror image of the passive: in the passive the agent is demoted, in
    the antipassive the patient.

    - `implicitPatient`: Patient-like argument left implicit (unexpressed).
    - `obliquePatient`: Patient-like argument expressed as oblique complement
      (e.g. Chukchi instrumental `kimitw-e` in antipassive vs absolutive
      `kimitw-xn` in transitive).
    - `noAntipassive`: No antipassive construction. -/
inductive AntipassiveType where
  | implicitPatient
  | obliquePatient
  | noAntipassive
  deriving DecidableEq, Repr

/-- Does this value represent the presence of an antipassive? -/
def AntipassiveType.hasAntipassive : AntipassiveType → Bool
  | .implicitPatient => true
  | .obliquePatient  => true
  | .noAntipassive   => false

/-- WALS Ch 108 inset map: Productivity of the antipassive.

    - `productive`: Antipassive applies to a wide range of transitive verbs.
    - `partiallyProductive`: Restricted to certain subsets of transitives.
    - `notProductive`: Very limited (lexically specified). -/
inductive AntipassiveProductivity where
  | productive
  | partiallyProductive
  | notProductive
  deriving DecidableEq, Repr

/-- Morphological alignment system (simplified for antipassive correlation).
    The canonical accusative/ergative dichotomy lives in `Features.AlignmentFamily`;
    this file uses that type directly rather than re-declaring it. A richer
    typology (active-stative, tripartite, hierarchical, etc.) is available in
    `Alignment.AlignmentType`. -/
abbrev AlignmentType := Features.AlignmentFamily

-- ============================================================================
-- §4. Ditransitive Constructions (Ch 105)
-- ============================================================================

/-- WALS Ch 105: How ditransitive verbs (prototypically 'give') encode
    the recipient (R) and theme (T) arguments relative to the monotransitive
    patient (P).

    - `indirectObject`: R is treated differently from P (R gets a
      preposition or dative case: "give the book TO Mary").
    - `doubleObject`: R is treated the same as P (both bare NPs:
      "give Mary the book").
    - `secondaryObject`: T is treated differently from P (T gets
      special marking: Ainu, Lakhota).
    - `mixed`: More than one construction type is available. -/
inductive DitransitiveType where
  | indirectObject
  | doubleObject
  | secondaryObject
  | mixed
  deriving DecidableEq, Repr

-- ============================================================================
-- §5. Applicative Constructions (Ch 109)
-- ============================================================================

/-- WALS Ch 109: Transitivity of the base verb for applicative formation.

    - `bothBases`: Applicatives formed from both transitive and intransitive
      bases (most common pattern when applicatives exist).
    - `transitiveOnly`: Only from transitive bases.
    - `intransitiveOnly`: Only from intransitive bases (rare: Fijian, Wambaya). -/
inductive ApplicativeBase where
  | bothBases
  | transitiveOnly
  | intransitiveOnly
  deriving DecidableEq, Repr

/-- WALS Ch 109: Semantic role of the applied object.

    - `benefactiveOnly`: Applied object restricted to benefactive role.
    - `benefactiveAndOther`: Benefactive plus instrument, locative, etc.
    - `nonbenefactiveOnly`: No benefactive; only instrument, locative, etc. -/
inductive AppliedObjectRole where
  | benefactiveOnly
  | benefactiveAndOther
  | nonbenefactiveOnly
  deriving DecidableEq, Repr

/-- WALS Ch 109: Full applicative type combining base and role.
    `none` for languages without applicative constructions. -/
inductive ApplicativeType where
  | applicative (base : ApplicativeBase) (role : AppliedObjectRole)
  | noApplicative
  deriving DecidableEq, Repr

/-- Does this value represent the presence of an applicative? -/
def ApplicativeType.hasApplicative : ApplicativeType → Bool
  | .applicative .. => true
  | .noApplicative  => false

-- ============================================================================
-- §6. Causative Types (Ch 110--111)
-- ============================================================================

/-- WALS Ch 110: Periphrastic causative type. -/
inductive PeriphrasticCausativeType where
  | sequentialOnly
  | purposiveOnly
  | both
  deriving DecidableEq, Repr

/-- WALS Ch 111: Nonperiphrastic (morphological/compound) causative type. -/
inductive NonperiphrCausativeType where
  | neither
  | morphologicalOnly
  | compoundOnly
  | both
  deriving DecidableEq, Repr

/-- Does this value represent a morphological causative? -/
def NonperiphrCausativeType.hasMorphological : NonperiphrCausativeType → Bool
  | .morphologicalOnly => true
  | .both              => true
  | _                  => false

-- ============================================================================
-- §7. ValenceProfile (Fragment-side joint)
-- ============================================================================

/-- A cross-linguistic valence/voice profile for a single language.

    Covers WALS Ch 106--109 directly, plus Ch 111 causative morphology for
    the applicative-causative correlation. Ch 110 (periphrastic causatives)
    is omitted from profiles since most WALS sources do not report it. -/
structure ValenceProfile where
  language : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Ch 106: Reciprocal construction type -/
  reciprocal : ReciprocalType
  /-- Ch 107: Passive presence -/
  passive : PassivePresence
  /-- Ch 108: Antipassive type -/
  antipassive : AntipassiveType
  /-- Ch 108: Morphological alignment (relevant for antipassive correlation) -/
  alignment : AlignmentType
  /-- Ch 109: Applicative type -/
  applicative : ApplicativeType
  /-- Ch 111: Nonperiphrastic causative type -/
  causative : NonperiphrCausativeType
  deriving Repr, DecidableEq

/-- Whether the profile records a passive. -/
def ValenceProfile.hasPassive (p : ValenceProfile) : Bool :=
  p.passive == .present

-- ============================================================================
-- §8. WALS converters
-- ============================================================================

/-- Convert WALS 105A value to `DitransitiveType`. -/
def fromWALS105A : Data.WALS.F105A.DitransitiveConstructionsTheVerbGive → DitransitiveType
  | .indirectObjectConstruction  => .indirectObject
  | .doubleObjectConstruction    => .doubleObject
  | .secondaryObjectConstruction => .secondaryObject
  | .mixed                       => .mixed

/-- Convert WALS 106A value to `ReciprocalType`. -/
def fromWALS106A : Data.WALS.F106A.ReciprocalType → ReciprocalType
  | .noReciprocalConstruction => .noDedicated
  | .distinctFromReflexive    => .distinctFromReflexive
  | .mixed                    => .mixed
  | .identicalToReflexive     => .identicalToReflexive

/-- Convert WALS 108A value to `AntipassiveType`. -/
def fromWALS108A : Data.WALS.F108A.AntipassiveType → AntipassiveType
  | .implicitPatient => .implicitPatient
  | .obliquePatient  => .obliquePatient
  | .noAntipassive   => .noAntipassive

/-- Convert WALS 109A value to `ApplicativeType`. The WALS enum encodes
    base-transitivity and semantic role together; we decompose into
    `ApplicativeBase` × `AppliedObjectRole`. -/
def fromWALS109A : Data.WALS.F109A.ApplicativeType → ApplicativeType
  | .benefactiveBothBases         => .applicative .bothBases .benefactiveOnly
  | .benefactiveTransOnly         => .applicative .transitiveOnly .benefactiveOnly
  | .benefactiveAndOtherBothBases => .applicative .bothBases .benefactiveAndOther
  | .benefactiveAndOtherTransOnly => .applicative .transitiveOnly .benefactiveAndOther
  | .nonBenefactiveBothBases      => .applicative .bothBases .nonbenefactiveOnly
  | .nonBenefactiveTransOnly      => .applicative .transitiveOnly .nonbenefactiveOnly
  | .nonBenefactiveIntransOnly    => .applicative .intransitiveOnly .nonbenefactiveOnly
  | .noApplicative                => .noApplicative

/-- Convert WALS 109B value to an optional `AppliedObjectRole`.
    Returns `none` for languages without applicative constructions, since
    there is no applied object whose role could be classified.
    Instrument, locative, and instrument-and-locative all map to
    `.nonbenefactiveOnly`; the finer distinction is preserved in the WALS
    source data. -/
def fromWALS109B : Data.WALS.F109B.AppliedObjectRole → Option AppliedObjectRole
  | .instrument            => some .nonbenefactiveOnly
  | .locative              => some .nonbenefactiveOnly
  | .instrumentAndLocative => some .nonbenefactiveOnly
  | .onlyBenefactive       => some .benefactiveOnly
  | .noApplicative         => none

/-- Convert WALS 111A value to `NonperiphrCausativeType`. -/
def fromWALS111A : Data.WALS.F111A.NonperiphrCausativeType → NonperiphrCausativeType
  | .neither           => .neither
  | .morphologicalOnly => .morphologicalOnly
  | .compoundOnly      => .compoundOnly
  | .both              => .both


-- ============================================================================
-- §10. Theory-neutral WALS distribution facts
-- ============================================================================

/-- Ch 105: indirect-object alignment is the modal ditransitive pattern. -/
theorem ch105_indirectObject_modal :
    let indir := (f105a.filter (·.value == .indirectObjectConstruction)).length
    indir > (f105a.filter (·.value == .doubleObjectConstruction)).length ∧
    indir > (f105a.filter (·.value == .secondaryObjectConstruction)).length ∧
    indir > (f105a.filter (·.value == .mixed)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Ch 107: more than a third of WALS-sampled languages have a passive. -/
theorem passives_substantial_minority :
    let present := (f107a.filter (·.value == .present)).length
    present * 3 > f107a.length := by native_decide

/-- Ch 108: in [polinsky-2013-antipassive]'s sample, more languages have
    oblique-patient antipassives than implicit-patient antipassives, and the
    majority have no antipassive at all. -/
theorem antipassive_distribution :
    let oblique := (f108a.filter (·.value == .obliquePatient)).length
    let implicit := (f108a.filter (·.value == .implicitPatient)).length
    let none_ := (f108a.filter (·.value == .noAntipassive)).length
    oblique > implicit ∧ none_ > oblique + implicit := by native_decide

/-- Ch 111: morphological causatives appear in more than 80% of WALS-sampled
    languages (~90% in [song-2013-nonperiphrastic]'s tally). This dwarfs
    periphrastic causatives in frequency. -/
theorem morphological_causative_dominant :
    let morphOnly := (f111a.filter (·.value == .morphologicalOnly)).length
    let both := (f111a.filter (·.value == .both)).length
    (morphOnly + both) * 10 > f111a.length * 8 := by native_decide

/-- Ch 106: [nordlinger-2023] reports that of the 175 languages in
    [maslova-nedjalkov-2013]'s sample, polysemous reflexive/reciprocal
    constructions are present in 60 (34%). In WALS terms, polysemy corresponds
    to Values 3 (mixed) and 4 (identical to reflexive). -/
theorem polysemy_count :
    let mixed := (f106a.filter (·.value == .mixed)).length
    let identical := (f106a.filter (·.value == .identicalToReflexive)).length
    mixed + identical = 60 := by native_decide

/-- 60 out of 175 = 34.3%: more than a third but less than half. -/
theorem polysemy_percentage :
    let polysemous := (f106a.filter
        (fun d => d.value == .mixed || d.value == .identicalToReflexive)).length
    polysemous * 3 > f106a.length ∧ polysemous * 2 < f106a.length := by
  native_decide

/-- [polinsky-2013-antipassive]'s headline data: WALS data refutes any
    biconditional between antipassive (F108A) and ergative verbal person
    marking (F100A). Lango (`laj`) is accusative-aligned and has an
    implicit-patient antipassive — refuting "antipassive ⟹ ergative".
    Abkhaz (`abk`) is ergative-aligned and has no antipassive — refuting
    "ergative ⟹ antipassive". Cf. [silverstein-1976]. -/
theorem antipassive_alignment_independence :
    (Data.WALS.F100A.lookupISO "laj").map (·.value) = some .accusative ∧
    (Data.WALS.F108A.lookupISO "laj").map (·.value) = some .implicitPatient ∧
    (Data.WALS.F100A.lookupISO "abk").map (·.value) = some .ergative ∧
    (Data.WALS.F108A.lookupISO "abk").map (·.value) = some .noAntipassive := by
  decide

/-- [song-2013-periphrastic]: in WALS Ch 110, the purposive type
    (effect clause marked by future/irrealis or purposive particle) is
    the dominant periphrastic causative strategy, more common than the
    sequential type (cause and effect clauses in fixed temporal order). -/
theorem periphrastic_purposive_dominant :
    let sequential := (f110a.filter (·.value == .sequentialOnly)).length
    let purposive := (f110a.filter (·.value == .purposiveOnly)).length
    purposive > sequential := by decide

/-- [polinsky-2013-applicative]'s near-universal: applicatives formed
    only from intransitive bases (`.nonBenefactiveIntransOnly`) are
    vanishingly rare in WALS Ch 109, while applicatives on both bases
    dominate by more than 10:1. The exceptions are Fijian and Wambaya. -/
theorem applicative_both_dominates_intrans_only :
    let intransOnly := (f109a.filter (·.value == .nonBenefactiveIntransOnly)).length
    let bothBases := (f109a.filter fun d =>
      d.value == .benefactiveBothBases ||
      d.value == .benefactiveAndOtherBothBases ||
      d.value == .nonBenefactiveBothBases).length
    bothBases > 10 * intransOnly := by decide

end Typology.ArgumentStructure
