import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Semantics.ArgumentStructure.DiathesisAlternation

/-!
# The property tables of the Levin classes

The `Properties` table of every class page of [levin-1993] Part II: each property Levin
lists, an alternation of Part One or one of the further properties the pages name (derived
nominals, sentential complements, cognate and reaction objects, and so on), with the diacritic
the page gives it, an asterisk for a property the class lacks and a question mark for a
marginal one, and the scope qualifier of the entry where the page has one ("some verbs",
"most verbs", "a few verbs"). The alternation profile of a class is read off the table:
`LevinClass.alternations` are the alternations attested without diacritic and
`LevinClass.starredAlternations` the starred ones, with `LevinClass.Participates` the attested
relation.

## Implementation notes

The tables are transcribed from the class pages mechanically; a property Levin phrases as a
denial ("Unintentional interpretation not available", "Coreferential interpretation of
pronouns not possible") is the corresponding alternation starred. The Introduction's component
prediction agrees with Part II on the quadruple *break*, *cut*, *hit*, *touch*
(`quadruple_prediction_matches`) and overshoots elsewhere (`prediction_not_sound`).

## References

* [levin-1993]
-/

namespace ArgumentStructure

/-- A property a class page of [levin-1993] Part II lists: an alternation of Part One or one
of the further properties the pages name. -/
inductive LevinProperty where
  /-- An alternation or construction of Part One. -/
  | alternation (a : DiathesisAlternation)
  /-- Zero-related nominal. -/
  | zeroRelatedNominal
  /-- -er nominal. -/
  | erNominal
  /-- -ing nominal. -/
  | ingNominal
  /-- Process nominal. -/
  | processNominal
  /-- Result nominal. -/
  | resultNominal
  /-- Derived nominal with the active interpretation only. -/
  | derivedNominalActiveOnly
  /-- Derived nominal with the passive interpretation only. -/
  | derivedNominalPassiveOnly
  /-- -able adjective. -/
  | ableAdjective
  /-- Zero-related adjective. -/
  | zeroRelatedAdjective
  /-- Sentential complement. -/
  | sententialComplement
  /-- Sentential complement with goal object. -/
  | sententialComplementWithGoalObject
  /-- Sentential complement with goal to phrase. -/
  | sententialComplementWithGoalToPhrase
  /-- Sentential complement with optional goal object. -/
  | sententialComplementWithOptionalGoalObject
  /-- Sentential complement with optional goal to phrase. -/
  | sententialComplementWithOptionalGoalToPhrase
  /-- Sentential complement without goal phrase. -/
  | sententialComplementWithoutGoalPhrase
  /-- Extraposition of sentential complements. -/
  | extraposition
  /-- Direct speech. -/
  | directSpeech
  /-- Parenthetical use of the verb. -/
  | parentheticalUse
  /-- Infinitival copular clause. -/
  | infinitivalCopularClause
  /-- Measure phrase. -/
  | measurePhrase
  /-- Path phrase. -/
  | pathPhrase
  /-- Depictive phrase. -/
  | depictivePhrase
  /-- Substance object. -/
  | substanceObject
  /-- Body-part object. -/
  | bodyPartObject
  /-- Collective NP subject. -/
  | collectiveNPSubject
  /-- Impersonal passive. -/
  | impersonalPassive
  /-- Choice of preposition in the passive depends on the verb. -/
  | passivePrepositionChoice
  /-- Most verbs allow a from phrase. -/
  | fromPhrase
  /-- With alternates with in. -/
  | withAlternatesWithIn
  /-- Of alternates with out with a few verbs. -/
  | ofAlternatesWithOut
  /-- Unspecified object plus locative PP. -/
  | unspecifiedObjectPlusLocativePP
  /-- Acceptability of a coreferential interpretation of pronouns varies. -/
  | coreferentialPronounsVary
  deriving DecidableEq, Repr

/-- The alternation a property is, if it is one. -/
def LevinProperty.alternation? : LevinProperty → Option DiathesisAlternation
  | .alternation a => some a
  | _ => none

/-- The diacritic a class page gives a property: none, an asterisk, or a question mark. -/
inductive Attestation where
  | attested | starred | marginal
  deriving DecidableEq, Repr

/-- The scope qualifier of a property entry. -/
inductive PropertyScope where
  | all | most | some | few
  deriving DecidableEq, Repr

/-- One line of a class page's property table. -/
structure ClassProperty where
  property : LevinProperty
  attestation : Attestation := .attested
  scope : PropertyScope := .all
  deriving DecidableEq, Repr

namespace LevinClass

/-- The property table of the class page, in the page's order. -/
def properties : LevinClass → List ClassProperty
  | .put =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .putInSpatialConfiguration =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .funnel =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .putDirection =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .dative, .starred, .all⟩,
     ⟨.alternation .middle, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .pour =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .middle, .starred, .all⟩, ⟨.alternation .causative, .attested, .all⟩,
     ⟨.alternation .boundNonreflexiveAnaphor, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .few⟩]
  | .coil =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causativeInchoative, .attested, .all⟩, ⟨.alternation .middle, .attested, .all⟩,
     ⟨.alternation .boundNonreflexiveAnaphor, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .sprayLoad =>
    [⟨.alternation .locative, .attested, .all⟩, ⟨.alternation .causative, .attested, .some⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .conative, .attested, .some⟩,
     ⟨.alternation .boundNonreflexiveAnaphor, .attested, .some⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .fill =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .locatumSubject, .attested, .all⟩, ⟨.withAlternatesWithIn, .attested, .some⟩]
  | .butter =>
    [⟨.alternation .cognatePrepositionalPhrase, .attested, .all⟩,
     ⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .pocket =>
    [⟨.alternation .cognatePrepositionalPhrase, .starred, .all⟩,
     ⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩]
  | .remove =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .banish =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .clear =>
    [⟨.alternation .locative, .attested, .all⟩, ⟨.alternation .locative, .attested, .all⟩,
     ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causativeInchoative, .attested, .all⟩,
     ⟨.alternation .resultative, .starred, .all⟩, ⟨.zeroRelatedAdjective, .attested, .some⟩,
     ⟨.alternation .adjectivalPassive, .attested, .all⟩]
  | .wipeManner =>
    [⟨.alternation .locative, .attested, .all⟩, ⟨.alternation .conative, .attested, .some⟩,
     ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .unspecifiedObject, .attested, .some⟩,
     ⟨.unspecifiedObjectPlusLocativePP, .attested, .some⟩,
     ⟨.alternation .resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .wipeInstrument =>
    [⟨.alternation .locative, .attested, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .unspecifiedObject, .attested, .some⟩,
     ⟨.unspecifiedObjectPlusLocativePP, .attested, .some⟩,
     ⟨.alternation .resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .steal =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .benefactive, .starred, .all⟩,
     ⟨.alternation .conative, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩]
  | .cheat =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.ofAlternatesWithOut, .attested, .all⟩]
  | .pit =>
    [⟨.alternation .cognatePrepositionalPhrase, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .debone =>
    [⟨.alternation .cognatePrepositionalPhrase, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .mine =>
    [⟨.alternation .cognatePrepositionalPhrase, .attested, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .send =>
    [⟨.alternation .dative, .attested, .some⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .boundNonreflexiveAnaphor, .starred, .all⟩]
  | .slide =>
    [⟨.alternation .dative, .attested, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causativeInchoative, .attested, .all⟩, ⟨.alternation .middle, .attested, .all⟩,
     ⟨.coreferentialPronounsVary, .attested, .all⟩]
  | .bringTake =>
    [⟨.alternation .dative, .attested, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .resultative, .starred, .all⟩,
     ⟨.alternation .boundNonreflexiveAnaphor, .attested, .all⟩]
  | .carry =>
    [⟨.alternation .dative, .attested, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.coreferentialPronounsVary, .attested, .all⟩]
  | .drive =>
    [⟨.alternation .dative, .marginal, .some⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .boundNonreflexiveAnaphor, .starred, .all⟩]
  | .pushPull =>
    [⟨.alternation .conative, .attested, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .wayObject, .attested, .some⟩,
     ⟨.alternation .boundNonreflexiveAnaphor, .attested, .all⟩,
     ⟨.alternation .resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .give =>
    [⟨.alternation .dative, .attested, .all⟩, ⟨.alternation .fulfilling, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .contribute =>
    [⟨.alternation .dative, .starred, .all⟩, ⟨.alternation .fulfilling, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .futureHaving =>
    [⟨.alternation .dative, .attested, .all⟩, ⟨.alternation .fulfilling, .attested, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .fulfilling => [⟨.alternation .fulfilling, .attested, .all⟩]
  | .equip => [⟨.alternation .fulfilling, .starred, .all⟩, ⟨.alternation .dative, .starred, .all⟩]
  | .get =>
    [⟨.fromPhrase, .attested, .all⟩, ⟨.alternation .benefactive, .attested, .all⟩,
     ⟨.alternation .dative, .starred, .all⟩, ⟨.alternation .locative, .starred, .all⟩,
     ⟨.alternation .sumOfMoneySubject, .attested, .some⟩]
  | .obtain =>
    [⟨.fromPhrase, .attested, .all⟩, ⟨.alternation .benefactive, .starred, .all⟩,
     ⟨.alternation .dative, .starred, .all⟩, ⟨.alternation .locative, .starred, .all⟩,
     ⟨.alternation .sumOfMoneySubject, .attested, .few⟩]
  | .exchange =>
    [⟨.alternation .dative, .starred, .all⟩, ⟨.alternation .benefactive, .starred, .all⟩]
  | .berry => []
  | .learn => []
  | .hold =>
    [⟨.alternation .conative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .attested, .some⟩]
  | .keep => [⟨.alternation .locative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .conceal => [⟨.alternation .locative, .starred, .all⟩]
  | .throw =>
    [⟨.alternation .directionalPhrase, .attested, .all⟩, ⟨.alternation .dative, .attested, .most⟩,
     ⟨.alternation .withAgainst, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .pelt =>
    [⟨.alternation .directionalPhrase, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .withAgainst, .starred, .all⟩, ⟨.alternation .dative, .starred, .all⟩,
     ⟨.alternation .middle, .starred, .all⟩]
  | .hit =>
    [⟨.alternation .withAgainst, .attested, .all⟩, ⟨.alternation .throughWith, .starred, .all⟩,
     ⟨.alternation .conative, .attested, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .attested, .all⟩,
     ⟨.alternation .togetherReciprocal, .attested, .all⟩,
     ⟨.alternation .simpleReciprocal, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .middle, .starred, .all⟩, ⟨.alternation .instrumentSubject, .attested, .all⟩,
     ⟨.alternation .unintentionalInterpretation, .attested, .some⟩,
     ⟨.alternation .resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .swat =>
    [⟨.alternation .withAgainst, .starred, .all⟩, ⟨.alternation .throughWith, .starred, .all⟩,
     ⟨.alternation .conative, .attested, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .attested, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .instrumentSubject, .starred, .all⟩,
     ⟨.alternation .resultative, .attested, .some⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .spank =>
    [⟨.alternation .withAgainst, .starred, .all⟩, ⟨.alternation .throughWith, .starred, .all⟩,
     ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .attested, .some⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .instrumentSubject, .starred, .all⟩,
     ⟨.alternation .resultative, .attested, .all⟩, ⟨.ingNominal, .attested, .most⟩]
  | .nonAgentiveImpact =>
    [⟨.alternation .simpleReciprocalIntransitive, .starred, .all⟩,
     ⟨.alternation .togetherReciprocalIntransitive, .attested, .some⟩]
  | .poke =>
    [⟨.alternation .throughWith, .attested, .all⟩, ⟨.alternation .withAgainst, .starred, .all⟩,
     ⟨.alternation .conative, .attested, .some⟩,
     ⟨.alternation .bodyPartPossessorAscension, .attested, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .touch =>
    [⟨.alternation .withAgainst, .starred, .all⟩, ⟨.alternation .throughWith, .starred, .all⟩,
     ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .attested, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩,
     ⟨.alternation .unintentionalInterpretation, .starred, .all⟩,
     ⟨.alternation .resultative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .cut =>
    [⟨.alternation .conative, .attested, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .attested, .some⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .attested, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩,
     ⟨.alternation .characteristicPropertyOfInstrument, .attested, .some⟩,
     ⟨.alternation .unintentionalInterpretation, .attested, .some⟩,
     ⟨.pathPhrase, .attested, .some⟩, ⟨.alternation .resultative, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .carve =>
    [⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .attested, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩,
     ⟨.alternation .characteristicPropertyOfInstrument, .attested, .some⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .mix =>
    [⟨.alternation .simpleReciprocal, .attested, .all⟩,
     ⟨.alternation .simpleReciprocalIntransitive, .attested, .most⟩,
     ⟨.alternation .togetherReciprocal, .attested, .all⟩,
     ⟨.alternation .togetherReciprocalIntransitive, .attested, .most⟩,
     ⟨.alternation .causativeInchoative, .attested, .most⟩, ⟨.alternation .middle, .attested, .all⟩]
  | .amalgamate =>
    [⟨.alternation .simpleReciprocal, .attested, .all⟩,
     ⟨.alternation .simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .togetherReciprocal, .starred, .all⟩,
     ⟨.alternation .togetherReciprocalIntransitive, .starred, .all⟩,
     ⟨.alternation .causativeInchoative, .attested, .most⟩, ⟨.alternation .middle, .attested, .all⟩]
  | .shake =>
    [⟨.alternation .togetherReciprocal, .attested, .all⟩,
     ⟨.alternation .simpleReciprocal, .starred, .all⟩, ⟨.alternation .causative, .starred, .few⟩,
     ⟨.alternation .middle, .attested, .all⟩]
  | .tape =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .simpleReciprocal, .starred, .all⟩,
     ⟨.alternation .togetherReciprocal, .attested, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .attested, .all⟩,
     ⟨.alternation .resultative, .attested, .all⟩,
     ⟨.alternation .cognatePrepositionalPhrase, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .cling =>
    [⟨.alternation .simpleReciprocalIntransitive, .starred, .all⟩,
     ⟨.alternation .togetherReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .separate =>
    [⟨.alternation .simpleReciprocal, .attested, .all⟩,
     ⟨.alternation .simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .apartReciprocal, .starred, .all⟩,
     ⟨.alternation .apartReciprocalIntransitive, .starred, .all⟩,
     ⟨.alternation .causativeInchoative, .attested, .some⟩,
     ⟨.alternation .middle, .attested, .all⟩, ⟨.alternation .locative, .starred, .all⟩]
  | .split =>
    [⟨.alternation .simpleReciprocal, .starred, .all⟩,
     ⟨.alternation .simpleReciprocalIntransitive, .starred, .all⟩,
     ⟨.alternation .apartReciprocal, .attested, .all⟩,
     ⟨.alternation .apartReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .causativeInchoative, .attested, .most⟩, ⟨.alternation .middle, .attested, .all⟩]
  | .disassemble =>
    [⟨.alternation .simpleReciprocal, .starred, .all⟩,
     ⟨.alternation .apartReciprocal, .starred, .all⟩, ⟨.alternation .causative, .starred, .few⟩,
     ⟨.alternation .middle, .attested, .all⟩]
  | .differ =>
    [⟨.alternation .simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .apartReciprocalIntransitive, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .color =>
    [⟨.alternation .resultative, .attested, .all⟩,
     ⟨.alternation .cognatePrepositionalPhrase, .attested, .all⟩]
  | .imageImpression =>
    [⟨.alternation .imageImpression, .attested, .all⟩,
     ⟨.alternation .unspecifiedObject, .attested, .all⟩, ⟨.processNominal, .attested, .all⟩,
     ⟨.resultNominal, .attested, .all⟩]
  | .scribble =>
    [⟨.alternation .imageImpression, .starred, .all⟩,
     ⟨.alternation .unspecifiedObject, .attested, .some⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .illustrate =>
    [⟨.alternation .imageImpression, .starred, .all⟩, ⟨.processNominal, .attested, .some⟩,
     ⟨.resultNominal, .attested, .some⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .transcribe =>
    [⟨.alternation .imageImpression, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .build =>
    [⟨.alternation .materialProduct, .attested, .all⟩,
     ⟨.alternation .totalTransformation, .starred, .all⟩,
     ⟨.alternation .unspecifiedObject, .attested, .all⟩,
     ⟨.alternation .benefactive, .attested, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .rawMaterialSubject, .attested, .some⟩,
     ⟨.alternation .sumOfMoneySubject, .attested, .few⟩]
  | .grow =>
    [⟨.alternation .materialProductIntransitive, .attested, .all⟩,
     ⟨.alternation .totalTransformationIntransitive, .starred, .all⟩,
     ⟨.alternation .causativeInchoative, .attested, .all⟩]
  | .prepare =>
    [⟨.alternation .materialProduct, .starred, .all⟩, ⟨.alternation .benefactive, .attested, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩]
  | .create =>
    [⟨.alternation .materialProduct, .starred, .all⟩, ⟨.alternation .benefactive, .starred, .most⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .rawMaterialSubject, .starred, .all⟩]
  | .knead =>
    [⟨.alternation .materialProduct, .starred, .all⟩,
     ⟨.alternation .causativeInchoative, .attested, .some⟩,
     ⟨.alternation .rawMaterialSubject, .starred, .all⟩,
     ⟨.alternation .totalTransformation, .starred, .all⟩]
  | .turn =>
    [⟨.alternation .totalTransformation, .attested, .all⟩,
     ⟨.alternation .totalTransformationIntransitive, .attested, .most⟩,
     ⟨.alternation .causativeInchoative, .attested, .most⟩,
     ⟨.alternation .materialProduct, .starred, .all⟩,
     ⟨.alternation .materialProductIntransitive, .starred, .all⟩]
  | .performance =>
    [⟨.alternation .dative, .attested, .some⟩, ⟨.alternation .benefactive, .attested, .some⟩,
     ⟨.alternation .unspecifiedObject, .attested, .all⟩, ⟨.alternation .causative, .starred, .all⟩]
  | .engender => [⟨.alternation .causative, .starred, .all⟩]
  | .calve => []
  | .appoint =>
    [⟨.alternation .as, .attested, .all⟩, ⟨.alternation .dative, .starred, .all⟩,
     ⟨.infinitivalCopularClause, .attested, .some⟩]
  | .characterize =>
    [⟨.alternation .as, .starred, .all⟩, ⟨.infinitivalCopularClause, .attested, .few⟩]
  | .dub =>
    [⟨.alternation .as, .starred, .all⟩, ⟨.alternation .dative, .starred, .all⟩,
     ⟨.infinitivalCopularClause, .starred, .all⟩]
  | .declare =>
    [⟨.alternation .as, .starred, .all⟩, ⟨.alternation .dative, .starred, .all⟩,
     ⟨.infinitivalCopularClause, .attested, .all⟩]
  | .conjecture =>
    [⟨.alternation .as, .starred, .all⟩, ⟨.infinitivalCopularClause, .attested, .all⟩]
  | .masquerade => []
  | .orphan => [⟨.alternation .verbalPassive, .attested, .all⟩]
  | .captain => []
  | .see =>
    [⟨.alternation .middle, .starred, .all⟩, ⟨.alternation .possessorObject, .starred, .all⟩,
     ⟨.alternation .attributeObject, .attested, .all⟩]
  | .sight => [⟨.alternation .middle, .starred, .all⟩]
  | .peer => []
  | .stimulusSubjectPerception => [⟨.alternation .verbalPassive, .starred, .all⟩]
  | .amuse =>
    [⟨.alternation .causative, .starred, .most⟩, ⟨.alternation .middle, .attested, .most⟩,
     ⟨.alternation .proArbObject, .attested, .all⟩, ⟨.extraposition, .attested, .all⟩,
     ⟨.passivePrepositionChoice, .attested, .all⟩, ⟨.alternation .resultative, .attested, .all⟩,
     ⟨.derivedNominalPassiveOnly, .attested, .all⟩, ⟨.erNominal, .attested, .some⟩,
     ⟨.ableAdjective, .attested, .some⟩]
  | .admire =>
    [⟨.alternation .middle, .starred, .all⟩, ⟨.alternation .possessorObject, .attested, .all⟩,
     ⟨.alternation .attributeObject, .attested, .all⟩, ⟨.alternation .as, .starred, .all⟩,
     ⟨.sententialComplement, .attested, .some⟩, ⟨.extraposition, .attested, .some⟩,
     ⟨.derivedNominalActiveOnly, .attested, .all⟩, ⟨.ableAdjective, .attested, .all⟩,
     ⟨.erNominal, .attested, .all⟩]
  | .marvel => [⟨.alternation .verbalPassive, .attested, .some⟩]
  | .appeal => [⟨.alternation .verbalPassive, .starred, .all⟩]
  | .want =>
    [⟨.alternation .possessorObject, .attested, .all⟩,
     ⟨.alternation .attributeObject, .starred, .all⟩, ⟨.alternation .as, .starred, .all⟩,
     ⟨.alternation .verbalPassive, .marginal, .all⟩]
  | .long => [⟨.alternation .verbalPassive, .marginal, .all⟩]
  | .judgment =>
    [⟨.alternation .middle, .starred, .all⟩, ⟨.alternation .possessorObject, .attested, .all⟩,
     ⟨.alternation .attributeObject, .starred, .all⟩, ⟨.alternation .as, .attested, .some⟩,
     ⟨.processNominal, .attested, .some⟩]
  | .assessment =>
    [⟨.alternation .possessorObject, .attested, .all⟩,
     ⟨.alternation .attributeObject, .starred, .all⟩]
  | .hunt => [⟨.alternation .unspecifiedObject, .attested, .all⟩]
  | .search => []
  | .stalk => []
  | .investigate => []
  | .rummage => []
  | .ferret => []
  | .correspond =>
    [⟨.collectiveNPSubject, .attested, .all⟩,
     ⟨.alternation .simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .understoodReciprocalObject, .starred, .all⟩,
     ⟨.alternation .withPrepositionDrop, .starred, .all⟩]
  | .marry =>
    [⟨.alternation .simpleReciprocalIntransitive, .starred, .all⟩,
     ⟨.alternation .understoodReciprocalObject, .attested, .all⟩,
     ⟨.alternation .withPrepositionDrop, .starred, .all⟩]
  | .meet =>
    [⟨.alternation .simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .understoodReciprocalObject, .attested, .all⟩,
     ⟨.alternation .withPrepositionDrop, .attested, .all⟩]
  | .transferOfMessage => [⟨.alternation .dative, .attested, .most⟩]
  | .tell =>
    [⟨.alternation .dative, .attested, .all⟩,
     ⟨.sententialComplementWithGoalObject, .attested, .all⟩,
     ⟨.sententialComplementWithGoalToPhrase, .starred, .all⟩,
     ⟨.sententialComplementWithoutGoalPhrase, .starred, .all⟩, ⟨.directSpeech, .attested, .all⟩,
     ⟨.parentheticalUse, .attested, .all⟩, ⟨.alternation .verbalPassive, .attested, .all⟩,
     ⟨.impersonalPassive, .starred, .all⟩, ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .mannerOfSpeaking =>
    [⟨.alternation .dative, .starred, .all⟩,
     ⟨.sententialComplementWithOptionalGoalToPhrase, .attested, .all⟩,
     ⟨.directSpeech, .attested, .all⟩, ⟨.parentheticalUse, .attested, .all⟩,
     ⟨.alternation .verbalPassive, .starred, .all⟩,
     ⟨.alternation .reactionObject, .attested, .all⟩,
     ⟨.alternation .cognateObject, .marginal, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .instrumentOfCommunication =>
    [⟨.alternation .dative, .attested, .all⟩,
     ⟨.sententialComplementWithOptionalGoalObject, .attested, .all⟩,
     ⟨.sententialComplementWithOptionalGoalToPhrase, .attested, .all⟩,
     ⟨.directSpeech, .attested, .all⟩, ⟨.parentheticalUse, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .talk =>
    [⟨.sententialComplement, .starred, .all⟩,
     ⟨.alternation .simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .togetherReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .understoodReciprocalObject, .starred, .all⟩,
     ⟨.alternation .withPrepositionDrop, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .chitchat =>
    [⟨.sententialComplement, .starred, .all⟩,
     ⟨.alternation .simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.alternation .togetherReciprocalIntransitive, .starred, .all⟩,
     ⟨.alternation .understoodReciprocalObject, .starred, .all⟩,
     ⟨.alternation .withPrepositionDrop, .starred, .all⟩]
  | .say => [⟨.alternation .dative, .starred, .all⟩]
  | .complain =>
    [⟨.sententialComplementWithOptionalGoalToPhrase, .attested, .all⟩,
     ⟨.directSpeech, .attested, .all⟩, ⟨.parentheticalUse, .attested, .all⟩,
     ⟨.alternation .cognateObject, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .advise =>
    [⟨.alternation .proArbObject, .attested, .all⟩,
     ⟨.sententialComplementWithOptionalGoalObject, .attested, .all⟩,
     ⟨.directSpeech, .attested, .all⟩, ⟨.parentheticalUse, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .starred, .most⟩]
  | .animalSound =>
    [⟨.alternation .directionalPhrase, .starred, .all⟩,
     ⟨.alternation .reactionObject, .attested, .all⟩, ⟨.alternation .resultative, .attested, .all⟩]
  | .eat =>
    [⟨.alternation .unspecifiedObject, .attested, .all⟩, ⟨.alternation .conative, .attested, .all⟩,
     ⟨.alternation .instrumentSubject, .starred, .all⟩,
     ⟨.alternation .resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .chew =>
    [⟨.alternation .unspecifiedObject, .attested, .all⟩, ⟨.alternation .conative, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .gobble =>
    [⟨.alternation .unspecifiedObject, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .devour =>
    [⟨.alternation .unspecifiedObject, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .dine =>
    [⟨.alternation .unspecifiedObject, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩]
  | .gorge =>
    [⟨.alternation .unspecifiedObject, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩]
  | .feed => [⟨.alternation .dative, .attested, .all⟩]
  | .hiccup =>
    [⟨.alternation .cognateObject, .marginal, .all⟩, ⟨.alternation .resultative, .marginal, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .breathe =>
    [⟨.alternation .cognateObject, .attested, .few⟩, ⟨.substanceObject, .attested, .most⟩,
     ⟨.alternation .resultative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .exhale =>
    [⟨.alternation .cognateObject, .starred, .all⟩, ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .nonverbalExpression =>
    [⟨.alternation .cognateObject, .attested, .some⟩,
     ⟨.alternation .reactionObject, .attested, .all⟩,
     ⟨.alternation .resultative, .attested, .most⟩, ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .wink =>
    [⟨.alternation .understoodBodyPartObject, .attested, .all⟩,
     ⟨.alternation .verbalPassive, .starred, .all⟩, ⟨.alternation .cognateObject, .starred, .all⟩,
     ⟨.alternation .reactionObject, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .crane =>
    [⟨.alternation .understoodBodyPartObject, .attested, .all⟩,
     ⟨.alternation .cognateObject, .starred, .all⟩, ⟨.alternation .verbalPassive, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .curtsey =>
    [⟨.alternation .cognateObject, .starred, .all⟩,
     ⟨.alternation .reactionObject, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .snooze =>
    [⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .cognateObject, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .flinch =>
    [⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .cognateObject, .starred, .all⟩,
     ⟨.alternation .reactionObject, .starred, .all⟩]
  | .bodyInternalStateOfExistence => [⟨.alternation .causative, .starred, .all⟩]
  | .suffocate =>
    [⟨.alternation .causative, .attested, .all⟩, ⟨.alternation .middle, .marginal, .all⟩,
     ⟨.alternation .resultative, .attested, .some⟩]
  | .pain =>
    [⟨.alternation .cognateObject, .starred, .all⟩, ⟨.alternation .verbalPassive, .starred, .all⟩]
  | .tingle => [⟨.alternation .cognateObject, .starred, .all⟩]
  | .hurt => []
  | .changeOfBodilyState =>
    [⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .cognateObject, .starred, .all⟩]
  | .dress =>
    [⟨.alternation .causative, .attested, .all⟩,
     ⟨.alternation .understoodReflexiveObject, .attested, .all⟩]
  | .groom => [⟨.alternation .understoodReflexiveObject, .starred, .all⟩]
  | .floss =>
    [⟨.alternation .understoodReflexiveObject, .starred, .all⟩,
     ⟨.alternation .understoodBodyPartObject, .attested, .all⟩]
  | .braid =>
    [⟨.alternation .understoodBodyPartObject, .starred, .all⟩,
     ⟨.alternation .understoodReflexiveObject, .starred, .all⟩]
  | .simpleDressing => [⟨.alternation .understoodReflexiveObject, .starred, .all⟩]
  | .dressingWell => [⟨.alternation .adjectivalPassive, .attested, .all⟩]
  | .beingDressed => [⟨.alternation .understoodReflexiveObject, .starred, .all⟩]
  | .murder =>
    [⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .instrumentSubject, .starred, .all⟩,
     ⟨.alternation .resultative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .poison =>
    [⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .resultative, .attested, .some⟩, ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .lightEmission =>
    [⟨.alternation .locative, .attested, .all⟩, ⟨.alternation .locativeInversion, .attested, .all⟩,
     ⟨.alternation .thereInsertion, .attested, .all⟩, ⟨.alternation .causative, .attested, .some⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .attested, .all⟩, ⟨.erNominal, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .soundEmission =>
    [⟨.alternation .locative, .attested, .most⟩,
     ⟨.alternation .locativeInversion, .attested, .some⟩,
     ⟨.alternation .thereInsertion, .attested, .some⟩, ⟨.alternation .causative, .attested, .all⟩,
     ⟨.alternation .directionalPhrase, .attested, .all⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩, ⟨.erNominal, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .smellEmission =>
    [⟨.alternation .locative, .attested, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .substanceEmission =>
    [⟨.alternation .causative, .attested, .some⟩, ⟨.alternation .substanceSource, .attested, .all⟩,
     ⟨.alternation .locative, .attested, .some⟩,
     ⟨.alternation .locativeInversion, .attested, .some⟩,
     ⟨.alternation .thereInsertion, .attested, .some⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩, ⟨.erNominal, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .destroy =>
    [⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .middle, .starred, .all⟩,
     ⟨.alternation .materialProduct, .starred, .all⟩,
     ⟨.alternation .totalTransformation, .starred, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .resultative, .starred, .all⟩, ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .break_ =>
    [⟨.alternation .causativeInchoative, .attested, .all⟩, ⟨.alternation .middle, .attested, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩,
     ⟨.alternation .withAgainst, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .starred, .all⟩,
     ⟨.alternation .unintentionalInterpretation, .attested, .some⟩,
     ⟨.alternation .resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .bend =>
    [⟨.alternation .causativeInchoative, .attested, .all⟩, ⟨.alternation .middle, .attested, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩,
     ⟨.alternation .withAgainst, .starred, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .bodyPartPossessorAscension, .starred, .all⟩,
     ⟨.alternation .resultative, .attested, .some⟩, ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .cooking =>
    [⟨.alternation .causativeInchoative, .attested, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .cognateObject, .starred, .all⟩, ⟨.alternation .resultative, .attested, .all⟩,
     ⟨.alternation .adjectivalPassive, .attested, .all⟩]
  | .otherChangeOfState =>
    [⟨.alternation .causativeInchoative, .attested, .all⟩, ⟨.alternation .middle, .attested, .all⟩,
     ⟨.alternation .instrumentSubject, .attested, .all⟩, ⟨.alternation .conative, .starred, .all⟩,
     ⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .locative, .starred, .all⟩,
     ⟨.alternation .locativeInversion, .starred, .all⟩,
     ⟨.alternation .thereInsertion, .starred, .all⟩, ⟨.alternation .cognateObject, .starred, .all⟩,
     ⟨.alternation .resultative, .attested, .all⟩,
     ⟨.alternation .adjectivalPassive, .attested, .all⟩]
  | .entitySpecificChangeOfState =>
    [⟨.alternation .causative, .starred, .all⟩, ⟨.alternation .cognateObject, .starred, .all⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .attested, .some⟩]
  | .calibratableChangeOfState =>
    [⟨.alternation .causative, .attested, .all⟩, ⟨.alternation .thereInsertion, .starred, .all⟩,
     ⟨.alternation .locativeInversion, .starred, .all⟩,
     ⟨.alternation .cognateObject, .starred, .all⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩]
  | .lodge =>
    [⟨.alternation .thereInsertion, .starred, .all⟩,
     ⟨.alternation .locativeInversion, .starred, .all⟩, ⟨.alternation .locative, .starred, .all⟩,
     ⟨.alternation .causative, .attested, .some⟩,
     ⟨.alternation .adjectivalPassive, .starred, .all⟩, ⟨.erNominal, .attested, .some⟩]
  | .exist =>
    [⟨.alternation .thereInsertion, .attested, .all⟩,
     ⟨.alternation .locativeInversion, .attested, .all⟩, ⟨.alternation .locative, .starred, .all⟩,
     ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩]
  | .entitySpecificModeOfBeing =>
    [⟨.alternation .thereInsertion, .attested, .some⟩,
     ⟨.alternation .locativeInversion, .attested, .some⟩,
     ⟨.alternation .locative, .attested, .some⟩, ⟨.alternation .causative, .starred, .few⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩, ⟨.erNominal, .starred, .all⟩]
  | .modeOfBeingInvolvingMotion =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .thereInsertion, .attested, .some⟩,
     ⟨.alternation .locativeInversion, .attested, .some⟩,
     ⟨.alternation .causative, .attested, .some⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩]
  | .soundExistence =>
    [⟨.alternation .locative, .attested, .all⟩, ⟨.alternation .thereInsertion, .attested, .all⟩,
     ⟨.alternation .locativeInversion, .attested, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩, ⟨.erNominal, .starred, .all⟩]
  | .swarm =>
    [⟨.alternation .locative, .attested, .all⟩, ⟨.alternation .locativeInversion, .attested, .all⟩,
     ⟨.alternation .thereInsertion, .attested, .all⟩, ⟨.alternation .causative, .starred, .all⟩]
  | .herd =>
    [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .causative, .attested, .some⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .bulge => [⟨.alternation .locative, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩]
  | .spatialConfiguration =>
    [⟨.alternation .thereInsertion, .attested, .all⟩,
     ⟨.alternation .locativeInversion, .attested, .all⟩,
     ⟨.alternation .causative, .attested, .some⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩]
  | .meander =>
    [⟨.alternation .locativeInversion, .attested, .all⟩,
     ⟨.alternation .thereInsertion, .attested, .all⟩]
  | .contiguousLocation =>
    [⟨.alternation .adjectivalPassive, .attested, .all⟩,
     ⟨.alternation .understoodReciprocalObject, .attested, .some⟩]
  | .appear =>
    [⟨.alternation .thereInsertion, .attested, .most⟩,
     ⟨.alternation .locativeInversion, .attested, .most⟩,
     ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .attested, .all⟩]
  | .reflexiveAppearance =>
    [⟨.alternation .thereInsertion, .starred, .all⟩,
     ⟨.alternation .locativeInversion, .starred, .all⟩,
     ⟨.alternation .reflexiveOfAppearance, .attested, .all⟩]
  | .disappearance =>
    [⟨.alternation .thereInsertion, .marginal, .all⟩,
     ⟨.alternation .locativeInversion, .marginal, .all⟩, ⟨.alternation .causative, .starred, .all⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .attested, .all⟩]
  | .occurrence =>
    [⟨.alternation .thereInsertion, .attested, .all⟩,
     ⟨.alternation .locativeInversion, .attested, .all⟩, ⟨.alternation .causative, .starred, .all⟩]
  | .bodyInternalMotion =>
    [⟨.alternation .causative, .starred, .all⟩, ⟨.bodyPartObject, .starred, .all⟩,
     ⟨.alternation .resultative, .attested, .some⟩,
     ⟨.alternation .directionalPhrase, .attested, .all⟩]
  | .assumePosition =>
    [⟨.alternation .thereInsertion, .starred, .all⟩,
     ⟨.alternation .locativeInversion, .starred, .all⟩]
  | .inherentlyDirectedMotion =>
    [⟨.alternation .locativePrepositionDrop, .attested, .some⟩,
     ⟨.alternation .causative, .starred, .all⟩, ⟨.measurePhrase, .starred, .all⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .attested, .all⟩,
     ⟨.depictivePhrase, .attested, .all⟩, ⟨.alternation .resultative, .starred, .all⟩]
  | .leave => [⟨.alternation .adjectivalPassive, .attested, .some⟩]
  | .roll =>
    [⟨.alternation .causativeInchoative, .attested, .most⟩,
     ⟨.alternation .locativePrepositionDrop, .starred, .all⟩,
     ⟨.alternation .resultative, .attested, .all⟩,
     ⟨.alternation .adjectivalPassive, .attested, .all⟩]
  | .run =>
    [⟨.alternation .inducedAction, .attested, .some⟩,
     ⟨.alternation .locativePrepositionDrop, .attested, .some⟩,
     ⟨.alternation .thereInsertion, .attested, .all⟩,
     ⟨.alternation .locativeInversion, .attested, .all⟩, ⟨.measurePhrase, .attested, .some⟩,
     ⟨.alternation .resultative, .attested, .all⟩,
     ⟨.alternation .adjectivalPassive, .attested, .some⟩,
     ⟨.alternation .adjectivalPerfectParticiple, .starred, .all⟩,
     ⟨.alternation .cognateObject, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .vehicleName =>
    [⟨.alternation .inducedAction, .attested, .some⟩,
     ⟨.alternation .locativePrepositionDrop, .attested, .some⟩,
     ⟨.alternation .resultative, .attested, .all⟩]
  | .nonVehicleName =>
    [⟨.alternation .inducedAction, .attested, .some⟩,
     ⟨.alternation .locativePrepositionDrop, .attested, .some⟩,
     ⟨.alternation .resultative, .attested, .all⟩]
  | .waltz =>
    [⟨.alternation .inducedAction, .attested, .all⟩, ⟨.alternation .resultative, .attested, .all⟩,
     ⟨.alternation .cognateObject, .attested, .all⟩]
  | .chase => [⟨.alternation .causative, .starred, .all⟩]
  | .accompany => [⟨.alternation .causative, .starred, .all⟩]
  | .avoid => []
  | .linger => [⟨.alternation .causative, .starred, .all⟩]
  | .rush => [⟨.alternation .causative, .attested, .all⟩]
  | .register =>
    [⟨.alternation .verbalPassive, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩]
  | .cost =>
    [⟨.alternation .verbalPassive, .starred, .all⟩, ⟨.alternation .causative, .starred, .all⟩]
  | .fit => []
  | .price => [⟨.alternation .causative, .starred, .all⟩]
  | .bill => [⟨.alternation .dative, .starred, .all⟩, ⟨.alternation .as, .starred, .all⟩]
  | .begin => [⟨.alternation .causative, .attested, .some⟩]
  | .complete => [⟨.alternation .causative, .starred, .all⟩]
  | .weekend => []
  | .weather => []

/-- The alternations the class page lists with the given diacritic. -/
def alternationsWith (c : LevinClass) (m : Attestation) : Finset DiathesisAlternation :=
  (c.properties.filterMap fun p ↦
    match p.property with
    | .alternation a => if p.attestation = m then some a else none
    | _ => none).toFinset

/-- The alternations the class page attests. -/
def alternations (c : LevinClass) : Finset DiathesisAlternation := c.alternationsWith .attested

/-- The alternations the class page stars. -/
def starredAlternations (c : LevinClass) : Finset DiathesisAlternation :=
  c.alternationsWith .starred

/-- The class shows the alternation in [levin-1993] Part II: its page attests it, or attests
the section grouping it, as a page attesting the causative alternations attests the
causative/inchoative one. -/
def Participates (c : LevinClass) (a : DiathesisAlternation) : Prop :=
  a ∈ c.alternations ∨ ∃ p ∈ a.parent?, p ∈ c.alternations

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Participates a) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The class lacks the alternation in [levin-1993] Part II: its page stars it, or stars the
section grouping it. -/
def Stars (c : LevinClass) (a : DiathesisAlternation) : Prop :=
  a ∈ c.starredAlternations ∨ ∃ p ∈ a.parent?, p ∈ c.starredAlternations

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Stars a) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The class page tests the alternation, attesting or starring it. -/
def Tests (c : LevinClass) (a : DiathesisAlternation) : Prop := c.Participates a ∨ c.Stars a

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Tests a) :=
  inferInstanceAs (Decidable (_ ∨ _))

end LevinClass

/-! ### The Introduction's quadruple

*break*, *cut*, *hit* and *touch* are told apart by the four diagnostic alternations, and on
these four classes the component prediction agrees with Part II. -/

/-- The four diagnostic alternations of the Introduction. -/
def diagnosticAlternations : List DiathesisAlternation :=
  [.causativeInchoative, .middle, .conative, .bodyPartPossessorAscension]

/-- The quadruple takes four distinct profiles over the diagnostic alternations. -/
theorem quadruple_profiles_distinct :
    ([LevinClass.break_, .cut, .hit, .touch].map fun c ↦
      diagnosticAlternations.map fun a ↦ decide (c.Participates a)).Pairwise (· ≠ ·) := by
  decide +kernel

/-- On the quadruple, the component prediction matches Part II for every diagnostic
alternation. -/
theorem quadruple_prediction_matches :
    ∀ c ∈ [LevinClass.break_, .cut, .hit, .touch], ∀ a ∈ diagnosticAlternations,
      c.meaningComponents.predictedAlternation a = decide (c.Participates a) := by
  decide +kernel

/-- The prediction is not sound in general: destroy verbs are change-of-state causatives that
Part II stars for the causative alternations. -/
theorem prediction_not_sound :
    LevinClass.destroy.meaningComponents.predictedAlternation .causativeInchoative = true ∧
      LevinClass.destroy.Stars .causativeInchoative := by
  decide +kernel

end ArgumentStructure
