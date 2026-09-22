import Linglib.Fragments.Icelandic.Case
import Linglib.Syntax.Case.Source

/-!
# Icelandic verbs
[thrainsson-2007] [yip-maling-jackendoff-1987]
[zaenen-maling-thrainsson-1985]

## Case Frames ([thrainsson-2007] §4.1.2.2, ex. 4.48)

Of the 16 logically possible two-case combinations (4 × 4), only **5** are
reasonably common for dyadic verbs ([yip-maling-jackendoff-1987]):
NA, ND, NG, DN, AA. Two more (AN, GN) are extremely rare or restricted
to one construction each. Seven (DA, DD, DG, GA, GD, GG, and transitive
NN) do not occur at all.

## Quirky Subject Properties ([thrainsson-2007] §4.1.2.1)

Oblique subjects pass 9 of 10 subject diagnostics
([zaenen-maling-thrainsson-1985], [thrainsson-2007] §4.1.1):
1. Precede verb in default word order (§4.1.1.1)
2. Invert with verb in yes/no questions (§4.1.1.1)
3. Block expletive *það* constructions (§4.1.1.3)
4. Bind clause-internal reflexives *sig* (§4.1.1.4)
5. Bind long-distance reflexives (§4.1.1.5)
6. License conjunction reduction / subject ellipsis (§4.1.1.6)
7. Embed under ECM verbs, preserving case (§4.1.1.7)
8. Control PRO in infinitival complements (§4.1.1.8, limited)
9. Extract from embedded clauses (§4.1.1.9)

The ONE diagnostic they fail: **verb agreement**. The finite verb agrees
with the nominative argument (regardless of position), not the quirky
subject. When no nominative argument is present, the verb shows default
3sg agreement ([thrainsson-2007] ex. 4.47).

## Triadic (Ditransitive) Frames ([thrainsson-2007] §4.1.2.3, ex. 4.62)

Subject is always nominative in ditransitives. Six patterns are attested
for the two objects: NDA (>220 verbs), NAD (~40), NDG (~30), NDD (~30),
NAG (~20), NAA (~2).

## Case Assignment ([zaenen-maling-thrainsson-1985])

Quirky case is **lexical**: it is preserved under raising and is not
affected by passivization. Structural case (NOM, ACC in standard frames)
changes under passivization (ACC object → NOM subject in passive). The
distinction is the subject's case provenance, encoded as `Case.Source`
(`.inherent` vs `.structural`).

## The *-st* and *-na* verbs

Consensus lexical data for Icelandic verbs participating in the
*-st* / *-na* alternations made famous by [wood-2015]. Each
entry carries only the surface forms and a Boolean for whether an
active variant exists — every other piece of information about each
verb (the *-st* classification, the anticausative-marking morpheme,
the Voice cell) is paper-specific apparatus and lives in `Wood2015`,
where it can participate in further analysis without polluting the
Fragment schema.


Note on classification: in [wood-2015]'s analysis *-st* (historically
*sik* → *-sk* → *-st*) is **not** an exponent of Voice. It is a defective
`[−participant]` clitic — a featural subset of the reflexive pronoun —
that merges in a specifier/argument position and cliticizes to the verb.
It appears across the descriptive categories [wood-2015] distinguishes
(anticausative, generic middle, figure reflexive, reflexive, inherent,
subject-experiencer, reciprocal); the Voice/v exponents proper are *-na*
(Voice{∅}), *-Ø* (the elsewhere Voice exponent), and *-ka* (v), with
*-na*-marked anticausatives like *brotna*. The merge-site classification
and the *-st* / *-na* contrast are formalized in the Wood2015 study file,
not here.
-/

namespace Icelandic.Verbs

/-! #### Verb Case Frames -/

/-- A verb's case frame: the cases assigned to its arguments.
    Theory-neutral — records the morphological facts without committing
    to a particular analysis of WHY these cases appear.

    The two post-verbal argument slots follow **linear order**: `firstObject`
    is the first NP after the verb (typically IO in NDA frames),
    `secondObject` is the second (typically DO in NDA frames).
    [thrainsson-2007] §4.1.2.3 discusses the difficulty of labeling
    these as "direct" vs "indirect" in Icelandic. -/
structure VerbCaseFrame where
  /-- Icelandic citation form -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- Case of the subject (first argument) -/
  subjectCase : Case
  /-- Case of the first post-verbal argument, if any -/
  firstObject : Option Case := none
  /-- Case of the second post-verbal argument, if any -/
  secondObject : Option Case := none
  /-- Provenance of the subject's case: `.structural` (changes under
      passivization/raising) or `.inherent` (lexical/quirky — preserved
      under raising). Default: NOM → structural, all others → inherent. -/
  subjectCaseSource : Case.Source :=
    if subjectCase == .nom then .structural else .inherent
  deriving Repr, BEq

/-- Is the subject non-nominative (quirky)?
    Derived from the case frame, not stored redundantly. -/
def VerbCaseFrame.quirkySubject (v : VerbCaseFrame) : Bool :=
  v.subjectCase != .nom

/-! #### Dyadic Verb Data — Productive Patterns -/

-- § 2.1: NOM-ACC (NA) — default, most common

/-- *elska* 'love' — NA frame ([thrainsson-2007] ex. 4.56a).
    *Hann elskar hana.* 'He(N) loves her(A).' -/
def elska : VerbCaseFrame :=
  { form := "elska", gloss := "love"
    subjectCase := .nom, firstObject := some .acc }

/-- *lesa* 'read' — NA frame ([thrainsson-2007] ex. 4.56b).
    *Hún las bókina.* 'She(N) read book-the(A).' -/
def lesa : VerbCaseFrame :=
  { form := "lesa", gloss := "read"
    subjectCase := .nom, firstObject := some .acc }

-- § 2.2: NOM-DAT (ND) — ~750 verbs

/-- *hjálpa* 'help' — ND frame ([thrainsson-2007] ex. 4.57a).
    *Hún hjálpaði honum.* 'She(N) helped him(D).' -/
def hjalpa : VerbCaseFrame :=
  { form := "hjálpa", gloss := "help"
    subjectCase := .nom, firstObject := some .dat }

/-- *strauka* 'pet' — ND frame ([thrainsson-2007] ex. 4.57b).
    *Ég strauk kettinum.* 'I(N) petted cat-the(D).' -/
def strauka : VerbCaseFrame :=
  { form := "strauka", gloss := "pet"
    subjectCase := .nom, firstObject := some .dat }

/-- *kasta* 'throw' — ND frame ([thrainsson-2007] ex. 4.57c).
    *Hann kastaði boltanum.* 'He(N) threw ball-the(D).' -/
def kasta : VerbCaseFrame :=
  { form := "kasta", gloss := "throw"
    subjectCase := .nom, firstObject := some .dat }

-- § 2.3: NOM-GEN (NG) — less common

/-- *sakna* 'miss' — NG frame ([thrainsson-2007] ex. 4.58a).
    *Hann saknar hennar.* 'He(N) misses her(G).' -/
def sakna : VerbCaseFrame :=
  { form := "sakna", gloss := "miss"
    subjectCase := .nom, firstObject := some .gen }

/-- *krefja* 'demand' — NG frame ([thrainsson-2007] ex. 4.58b).
    *Ég krefst bóta.* 'I(N) demand compensation(G).' -/
def krefja : VerbCaseFrame :=
  { form := "krefja", gloss := "demand"
    subjectCase := .nom, firstObject := some .gen }

-- § 2.4: DAT-NOM (DN) — quirky dative subject, common

/-- *líka* 'like' — DN frame ([thrainsson-2007] ex. 4.61b).
    *Henni líkuðu hestarnir.* 'Her(D) liked(pl.) horses-the(Npl.).'
    Verb agrees with NOM object *hestarnir*, not DAT subject *henni*. -/
def lika : VerbCaseFrame :=
  { form := "líka", gloss := "like"
    subjectCase := .dat, firstObject := some .nom }

/-- *batna* 'get better' — DN frame ([thrainsson-2007] ex. 4.61c).
    *Barninu batnaði veikin.* 'Child-the(D) got-better sickness(N).' -/
def batna : VerbCaseFrame :=
  { form := "batna", gloss := "get better/recover"
    subjectCase := .dat, firstObject := some .nom }

/-- *leiðast* 'be bored' — DN frame ([thrainsson-2007] ex. 4.61d).
    *Stráknum leiddust kennararnir.* 'Boy-the(D) bored(pl.) teachers-the(Npl.).'
    Also an -st verb (see Verbs.lean). -/
def leidastCF : VerbCaseFrame :=
  { form := "leiðast", gloss := "be bored"
    subjectCase := .dat, firstObject := some .nom }

/-- *áskotnast* 'get by luck' — DN frame ([thrainsson-2007] ex. 4.61a).
    *Mér áskotnuðust peningar.* 'Me(D) lucked-onto(pl.) money(Npl.).' -/
def askotnast : VerbCaseFrame :=
  { form := "áskotnast", gloss := "get by luck"
    subjectCase := .dat, firstObject := some .nom }

-- § 2.5: ACC-ACC (AA) — quirky accusative subject, not very stable

/-- *vanta* 'lack/need' — AA frame ([thrainsson-2007] ex. 4.60a).
    *Hana vantar vinnu.* 'Her(A) lacks work(A).' -/
def vanta : VerbCaseFrame :=
  { form := "vanta", gloss := "lack/need"
    subjectCase := .acc, firstObject := some .acc }

/-- *dreyma* 'dream' — AA frame ([thrainsson-2007] ex. 4.60b).
    *Mig dreymdi draum.* 'Me(A) dreamt dream(A).' -/
def dreyma : VerbCaseFrame :=
  { form := "dreyma", gloss := "dream"
    subjectCase := .acc, firstObject := some .acc }

/-- *bresta* 'fail (of courage)' — AA frame ([thrainsson-2007] ex. 4.60c).
    *Harald brast kjark.* 'Harold(A) failed courage(A).' -/
def bresta : VerbCaseFrame :=
  { form := "bresta", gloss := "fail (of courage)"
    subjectCase := .acc, firstObject := some .acc }

/-! #### Rare / Marginal Dyadic Patterns -/

/-- ACC-NOM impersonal — extremely rare, possibly one construction
    ([thrainsson-2007] ex. 4.52a, parenthesized in ex. 4.48 grid).
    *Hana hefur líklega sótt syfja.* 'Her(A) has probably sought sleepiness(N).'
    The ACC experiencer occupies subject position; the NOM theme *syfja*
    'sleepiness' is a nominative noun, not a verb. The verbal predicate
    in this construction is *sækja* (pp. *sótt*). -/
def syfja : VerbCaseFrame :=
  { form := "syfja", gloss := "sleepiness (ACC-NOM impersonal)"
    subjectCase := .acc, firstObject := some .nom }

/-- GEN-NOM — extremely restricted, all examples involve the copula *vera*
    and a fixed predicative noun ([thrainsson-2007] ex. 4.54-4.55).
    *Þess var þá enginn kostur.* 'Of-that(G) was then no(N) choice(N).'
    'That was not possible then.' -/
def vera_kostur : VerbCaseFrame :=
  { form := "vera (kostur)", gloss := "be an option (copula + pred. noun)"
    subjectCase := .gen, firstObject := some .nom }

/-! #### Triadic (Ditransitive) Verb Data -/

/-- *gefa* 'give' — NDA frame ([thrainsson-2007] ex. 4.63a).
    *María gaf Haraldi bókina.* 'Mary(N) gave Harold(D) book-the(A).'
    Most common ditransitive pattern (>220 verbs). -/
def gefa : VerbCaseFrame :=
  { form := "gefa", gloss := "give"
    subjectCase := .nom, firstObject := some .dat, secondObject := some .acc }

/-- *segja* 'tell' — NDA frame ([thrainsson-2007] ex. 4.62). -/
def segja : VerbCaseFrame :=
  { form := "segja", gloss := "tell"
    subjectCase := .nom, firstObject := some .dat, secondObject := some .acc }

/-- *svipta* 'deprive' — NAD frame ([thrainsson-2007] ex. 4.65a).
    *Lögreglan svipti hann ökuleyfinu.* 'Police-the(N) deprived him(A)
    driver's-licence-the(D).' -/
def svipta : VerbCaseFrame :=
  { form := "svipta", gloss := "deprive"
    subjectCase := .nom, firstObject := some .acc, secondObject := some .dat }

/-- *leyna* 'conceal' — NAD frame ([thrainsson-2007] ex. 4.65b).
    *Þeir leyndu hana sannleikanum.* 'They(N) concealed her(A)
    truth-the(D).' -/
def leyna : VerbCaseFrame :=
  { form := "leyna", gloss := "conceal"
    subjectCase := .nom, firstObject := some .acc, secondObject := some .dat }

/-- *lofa* 'promise' — NDD frame ([thrainsson-2007] ex. 4.72a).
    *Ég lofaði henni því.* 'I(N) promised her(D) it(D).' -/
def lofa : VerbCaseFrame :=
  { form := "lofa", gloss := "promise"
    subjectCase := .nom, firstObject := some .dat, secondObject := some .dat }

/-- *skila* 'return' — NDD frame ([thrainsson-2007] ex. 4.72b).
    *Hún skilaði mér bókinni.* 'She(N) returned me(D) book-the(D).' -/
def skila : VerbCaseFrame :=
  { form := "skila", gloss := "return"
    subjectCase := .nom, firstObject := some .dat, secondObject := some .dat }

/-- *spyrja* 'ask' — NAG frame ([thrainsson-2007] ex. 4.70a).
    *Þeir spurðu hana margra spurninga.* 'They(N) asked her(A) many
    questions(G).' -/
def spyrja : VerbCaseFrame :=
  { form := "spyrja", gloss := "ask"
    subjectCase := .nom, firstObject := some .acc, secondObject := some .gen }

/-- *óska* 'wish' — NDG frame ([thrainsson-2007] ex. 4.69a).
    *Ég óska þér velfarnaðar.* 'I(N) wish you(D) well-being(G).' -/
def oska : VerbCaseFrame :=
  { form := "óska", gloss := "wish"
    subjectCase := .nom, firstObject := some .dat, secondObject := some .gen }

/-- *kosta* 'cost' — NAA frame ([thrainsson-2007] ex. 4.74).
    *Maturinn kostaði mig fjóra dollara.* 'Food-the(N) cost me(A) four
    dollars(A).' Extremely rare pattern (~2 verbs). -/
def kosta : VerbCaseFrame :=
  { form := "kosta", gloss := "cost"
    subjectCase := .nom, firstObject := some .acc, secondObject := some .acc }

/-! #### Subject Diagnostics -/

/-- The 10 standard subject diagnostics for Icelandic
    ([thrainsson-2007] §4.1.1, [zaenen-maling-thrainsson-1985]). -/
inductive SubjectDiagnostic where
  | defaultPosition        -- precedes verb in declaratives (§4.1.1.1)
  | yesNoInversion         -- inverts with verb in questions (§4.1.1.1)
  | blockExpletive         -- blocks expletive *það* (§4.1.1.3)
  | reflexiveBinding       -- antecedent of clause-internal *sig* (§4.1.1.4)
  | longDistanceReflexive  -- antecedent of long-distance *sig* (§4.1.1.5)
  | conjunctionReduction   -- subject ellipsis under coordination (§4.1.1.6)
  | ecmEmbedding           -- embeds under ECM verbs preserving case (§4.1.1.7)
  | proControl             -- controls PRO in infinitival complements (§4.1.1.8)
  | extraction             -- extracts from embedded clauses (§4.1.1.9)
  | verbAgreement          -- triggers person/number agreement on verb
  deriving DecidableEq, Repr

/-- Does a quirky (non-nominative) subject pass this diagnostic?
    Quirky subjects pass all diagnostics EXCEPT verb agreement
    ([thrainsson-2007] §4.1.2.1). -/
def SubjectDiagnostic.passedByQuirkySubject : SubjectDiagnostic → Bool
  | .verbAgreement => false
  | _              => true

/-! #### Agreement -/

/-- Which argument does the finite verb agree with?
    In Icelandic, the verb agrees with the **nominative** argument,
    regardless of whether it is the subject or the object
    ([thrainsson-2007] §4.1.2.1, ex. 4.47).
    When no nominative argument is present, default 3sg appears. -/
inductive AgreementTarget where
  | nominativeArg  -- verb agrees with whichever NP bears nominative
  | default3sg     -- no nominative argument → default 3sg
  deriving DecidableEq, Repr

/-- Determine the agreement target for a verb's case frame.
    If any argument is nominative, the verb agrees with it.
    Otherwise, default 3sg. -/
def VerbCaseFrame.agreementTarget (v : VerbCaseFrame) : AgreementTarget :=
  if v.subjectCase == .nom then .nominativeArg
  else if v.firstObject == some .nom then .nominativeArg
  else if v.secondObject == some .nom then .nominativeArg
  else .default3sg

/-! #### Verb Collections -/

/-- Dyadic verbs with nominative subjects. -/
def nomSubjectVerbs : List VerbCaseFrame :=
  [elska, lesa, hjalpa, strauka, kasta, sakna, krefja]

/-- Dyadic verbs with quirky (non-nominative) subjects. -/
def quirkySubjectVerbs : List VerbCaseFrame :=
  [lika, batna, leidastCF, askotnast, vanta, dreyma, bresta, syfja, vera_kostur]

/-- All dyadic verb entries. -/
def allDyadicVerbs : List VerbCaseFrame :=
  nomSubjectVerbs ++ quirkySubjectVerbs

/-- Ditransitive verb entries. -/
def ditransitiveVerbs : List VerbCaseFrame :=
  [gefa, segja, svipta, leyna, lofa, skila, spyrja, oska, kosta]

/-! #### Case Frame Typology -/

/-- The 5 productive dyadic case patterns in Icelandic
    ([thrainsson-2007] §4.1.2.2, [yip-maling-jackendoff-1987]).
    Out of 16 logically possible combinations (4 cases × 4 cases),
    7 do not occur (DA, DD, DG, GA, GD, GG, transitive NN) and
    4 are very rare (AN, AG, GN, NN-copular). -/
def productiveDyadicPatterns : List (Case × Case) :=
  [(.nom, .acc), (.nom, .dat), (.nom, .gen), (.dat, .nom), (.acc, .acc)]

theorem five_of_sixteen_productive :
    productiveDyadicPatterns.length = 5 := rfl

/-- Every verb in the fragment uses one of the 7 attested patterns
    (5 productive + AN + GN). -/
theorem all_verbs_use_attested_pattern :
    let attested := productiveDyadicPatterns ++ [(.acc, .nom), (.gen, .nom)]
    allDyadicVerbs.all (fun v =>
      match v.firstObject with
      | some o => attested.contains (v.subjectCase, o)
      | none => false) = true := by decide

/-! #### Verification Theorems -/

-- § 9.1: Quirky subject identification

/-- All verbs in the quirky list have non-nominative subjects. -/
theorem quirky_verbs_are_quirky :
    quirkySubjectVerbs.all (·.quirkySubject) = true := by decide

/-- No verb in the nominative-subject list has a quirky subject. -/
theorem nom_verbs_not_quirky :
    nomSubjectVerbs.all (fun v => !v.quirkySubject) = true := by decide

-- § 9.2: Case assignment

/-- Quirky subjects bear inherent (lexical) case. -/
theorem quirky_subjects_inherent :
    quirkySubjectVerbs.all
      (fun v => v.subjectCaseSource == .inherent) = true := by decide

/-- Nominative subjects bear structural case. -/
theorem nom_subjects_structural :
    nomSubjectVerbs.all
      (fun v => v.subjectCaseSource == .structural) = true := by decide

-- § 9.3: Agreement

/-- NA verbs: agreement target is the nominative subject. -/
theorem na_agrees_with_subject :
    elska.agreementTarget = .nominativeArg := rfl

/-- DN verbs: agreement target is the nominative OBJECT (not the
    dative subject). This is the key quirky-case agreement fact. -/
theorem dn_agrees_with_object :
    lika.agreementTarget = .nominativeArg ∧
    batna.agreementTarget = .nominativeArg ∧
    leidastCF.agreementTarget = .nominativeArg := ⟨rfl, rfl, rfl⟩

/-- AA verbs (no nominative argument): default 3sg agreement. -/
theorem aa_default_agreement :
    vanta.agreementTarget = .default3sg ∧
    dreyma.agreementTarget = .default3sg ∧
    bresta.agreementTarget = .default3sg := ⟨rfl, rfl, rfl⟩

/-- AN verbs: agreement target is the nominative object. -/
theorem an_agrees_with_object :
    syfja.agreementTarget = .nominativeArg := rfl

/-- Comprehensive: quirky verbs with NOM objects agree with that object. -/
theorem quirky_with_nom_object_agrees :
    (quirkySubjectVerbs.filter (fun v => v.firstObject == some .nom)).all
      (fun v => v.agreementTarget == .nominativeArg) = true := by decide

/-- Comprehensive: quirky verbs without any NOM argument default to 3sg. -/
theorem quirky_without_nom_defaults :
    (quirkySubjectVerbs.filter (fun v => v.firstObject != some .nom)).all
      (fun v => v.agreementTarget == .default3sg) = true := by decide

-- § 9.4: Subject diagnostics

/-- Quirky subjects pass 9 of 10 diagnostics. -/
theorem quirky_passes_nine :
    let diagnostics := [SubjectDiagnostic.defaultPosition,
                        .yesNoInversion, .blockExpletive,
                        .reflexiveBinding, .longDistanceReflexive,
                        .conjunctionReduction, .ecmEmbedding,
                        .proControl, .extraction, .verbAgreement]
    (diagnostics.filter SubjectDiagnostic.passedByQuirkySubject).length = 9 := rfl

/-- Verb agreement is the only diagnostic quirky subjects fail. -/
theorem quirky_fails_only_agreement :
    SubjectDiagnostic.passedByQuirkySubject .verbAgreement = false ∧
    SubjectDiagnostic.passedByQuirkySubject .defaultPosition = true ∧
    SubjectDiagnostic.passedByQuirkySubject .reflexiveBinding = true ∧
    SubjectDiagnostic.passedByQuirkySubject .extraction = true :=
  ⟨rfl, rfl, rfl, rfl⟩

-- § 9.5: Ditransitive patterns

/-- All ditransitive verbs have nominative subjects. -/
theorem ditrans_nom_subjects :
    ditransitiveVerbs.all (fun v => v.subjectCase == .nom) = true := by
  decide

/-- All 6 attested ditransitive object patterns are represented. -/
theorem six_ditrans_patterns :
    let patterns := ditransitiveVerbs.map
      (fun v => (v.firstObject, v.secondObject))
    patterns.contains (some .dat, some .acc) ∧  -- NDA: gefa, segja
    patterns.contains (some .acc, some .dat) ∧  -- NAD: svipta, leyna
    patterns.contains (some .dat, some .dat) ∧  -- NDD: lofa, skila
    patterns.contains (some .dat, some .gen) ∧  -- NDG: óska
    patterns.contains (some .acc, some .gen) ∧  -- NAG: spyrja
    patterns.contains (some .acc, some .acc)     -- NAA: kosta
    := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- § 9.6: Counts

theorem dyadic_verb_count : allDyadicVerbs.length = 16 := rfl
theorem ditransitive_verb_count : ditransitiveVerbs.length = 9 := rfl

-- § 9.7: Cross-reference with -st fragment

/-- *leiðast* 'be bored' is both an -st verb AND a quirky-subject verb
    (DAT-NOM frame). The form and gloss match between this fragment
    and Verbs.lean — verified by inspection (structural link
    requires a study file that imports both). -/
theorem leidast_is_quirky_dn :
    leidastCF.subjectCase = .dat ∧
    leidastCF.firstObject = some .nom ∧
    leidastCF.quirkySubject = true ∧
    leidastCF.subjectCaseSource = .inherent := ⟨rfl, rfl, rfl, rfl⟩

/-! ### The *-st* verbs -/

/-! #### Verb Entry -/

/-- A lexical entry for an Icelandic verb participating in the
    *-st* / *-na* alternation. Carries only consensus surface data. -/
structure IcelandicStVerb where
  /-- Active / bare form, if one exists. `none` for inherent *-st*
      verbs (*nálgast*, *minnast*) and the subject-experiencer
      *leiðast*. -/
  activeForm : Option String
  /-- The intransitive form: typically suffixed with *-st*, with
      *-na* on `brotna` and friends, or identical to the active when
      the alternation is unmarked. -/
  stForm : String
  /-- English gloss for human readers. -/
  gloss : String
  /-- Whether an active variant exists (must agree with
      `activeForm.isSome`; the redundancy is a sanity check used by
      the consistency theorem below). -/
  hasActiveVariant : Bool
  deriving Repr, BEq, DecidableEq

/-! #### Verb Data -/

/-- *opna* / *opnast* 'open'. -/
def opnast : IcelandicStVerb :=
  { activeForm := some "opna"
    stForm := "opnast"
    gloss := "open"
    hasActiveVariant := true }

/-- *splundra* / *splundrast* 'shatter'. -/
def splundrast : IcelandicStVerb :=
  { activeForm := some "splundra"
    stForm := "splundrast"
    gloss := "shatter"
    hasActiveVariant := true }

/-- *brjóta* / *brotna* 'break' — the canonical *-na*-marked
    anticausative (cf. *opnast* / *splundrast* with *-st*). -/
def brotna : IcelandicStVerb :=
  { activeForm := some "brjóta"
    stForm := "brotna"
    gloss := "break"
    hasActiveVariant := true }

/-- *selja* / *seljast* 'sell'. -/
def seljast : IcelandicStVerb :=
  { activeForm := some "selja"
    stForm := "seljast"
    gloss := "sell"
    hasActiveVariant := true }

/-- *lesa* / *lesast* 'read'. -/
def lesast : IcelandicStVerb :=
  { activeForm := some "lesa"
    stForm := "lesast"
    gloss := "read"
    hasActiveVariant := true }

/-- *setja* / *setjast* 'sit down' — a posture verb. -/
def setjast : IcelandicStVerb :=
  { activeForm := some "setja"
    stForm := "setjast"
    gloss := "sit down"
    hasActiveVariant := true }

/-- *klæða* / *klæðast* 'dress'. -/
def klaedast : IcelandicStVerb :=
  { activeForm := some "klæða"
    stForm := "klæðast"
    gloss := "dress"
    hasActiveVariant := true }

/-- *nálgast* 'approach' — no active variant; *-st* is lexicalized. -/
def nalgast : IcelandicStVerb :=
  { activeForm := none
    stForm := "nálgast"
    gloss := "approach"
    hasActiveVariant := false }

/-- *minnast* 'remember' — no active variant. -/
def minnast : IcelandicStVerb :=
  { activeForm := none
    stForm := "minnast"
    gloss := "remember"
    hasActiveVariant := false }

/-- *leiðast* 'be bored' — subject-experiencer; no active variant.
    *Mér leiðist í skólanum* 'I am bored in school'. -/
def leidast : IcelandicStVerb :=
  { activeForm := none
    stForm := "leiðast"
    gloss := "be bored"
    hasActiveVariant := false }

/-- *kyssa* / *kyssast* 'kiss' — used in reciprocal contexts:
    *Þau kyssast* 'They kissed (each other)'. -/
def kyssast : IcelandicStVerb :=
  { activeForm := some "kyssa"
    stForm := "kyssast"
    gloss := "kiss"
    hasActiveVariant := true }

/-- All *-st*-marked verb entries (excludes *-na*-marked verbs like
    *brotna*). -/
def allStVerbs : List IcelandicStVerb :=
  [opnast, splundrast, seljast, lesast, setjast, klaedast,
   nalgast, minnast, leidast, kyssast]

/-! #### Self-Consistency -/

/-- Sanity check: every verb whose `hasActiveVariant` is true also
    has `activeForm.isSome`. Catches schema drift in either field. -/
theorem alternating_have_active :
    (allStVerbs.filter (·.hasActiveVariant)).all
      (fun v => v.activeForm.isSome) = true := by decide

end Icelandic.Verbs
