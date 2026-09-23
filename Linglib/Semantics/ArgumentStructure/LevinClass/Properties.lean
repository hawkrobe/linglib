import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Semantics.ArgumentStructure.LevinProperty

/-!
# The property tables of the Levin classes

The `Properties` table of every class in [levin-1993] Part II: each property Levin tests the
class for (`LevinProperty`), with the diacritic she gives it, an asterisk for a property the
class lacks and a question mark for a marginal one, and the scope qualifier of the line where
there is one ("some verbs", "most verbs", "a few verbs"). The profile of a class is read off
the table: `LevinClass.Participates` holds of the properties the class attests,
`LevinClass.Stars` of those it stars, and `LevinClass.Tests` of either.

## Implementation notes

The tables are transcribed from the class entries mechanically; a property Levin phrases as
a denial ("Unintentional interpretation not available", "Coreferential interpretation of
pronouns not possible") is the corresponding property starred. A generic label is read at the
grain of the Part One subsection the entry's example instantiates: "Causative Alternations",
attested or starred, is the causative/inchoative alternation for every class, and "Locative
Alternation" is the spray/load alternation for the putting classes, the transitive clear
alternation for the removal and obtaining classes, the wipe alternation for the wipe classes,
and the swarm alternation for the emission and existence classes, smell emission included by
Levin's remark that its *of* form is the intransitive form of the alternation. The spray/load
class has the causative alternation twice, attested for the locative variant and starred for
the *with* variant, and those are two properties. The appear class's "many verbs" is the
scope `most`. No class has one property with two diacritics (`attestation_unique`).

## References

* [levin-1993]
-/

namespace ArgumentStructure

/-- The diacritic Levin gives a property of a class: none, an asterisk, or a question mark. -/
inductive Attestation where
  | attested | starred | marginal
  deriving DecidableEq, Repr

/-- The scope qualifier of a property entry. -/
inductive PropertyScope where
  | all | most | some | few
  deriving DecidableEq, Repr

/-- One line of a class's property table. -/
structure ClassProperty where
  property : LevinProperty
  attestation : Attestation := .attested
  scope : PropertyScope := .all
  deriving DecidableEq, Repr

namespace LevinClass

/-- The property table of the class, in Levin's order. -/
def properties : LevinClass → List ClassProperty
  | .put =>
    [⟨.sprayLoad, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .putInSpatialConfiguration =>
    [⟨.sprayLoad, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .funnel =>
    [⟨.sprayLoad, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .putDirection =>
    [⟨.sprayLoad, .starred, .all⟩, ⟨.dative, .starred, .all⟩,
     ⟨.middle, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .pour =>
    [⟨.sprayLoad, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.middle, .starred, .all⟩, ⟨.causativeInchoative, .attested, .all⟩,
     ⟨.boundNonreflexiveAnaphor, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .few⟩]
  | .coil =>
    [⟨.sprayLoad, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .attested, .all⟩, ⟨.middle, .attested, .all⟩,
     ⟨.boundNonreflexiveAnaphor, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .sprayLoad =>
    [⟨.sprayLoad, .attested, .all⟩, ⟨.causativeInchoativeLocativeVariant, .attested, .some⟩,
     ⟨.causativeInchoativeWithVariant, .starred, .all⟩, ⟨.conative, .attested, .some⟩,
     ⟨.boundNonreflexiveAnaphor, .attested, .some⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .fill =>
    [⟨.sprayLoad, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.locatumSubject, .attested, .all⟩, ⟨.withAlternatesWithIn, .attested, .some⟩]
  | .butter =>
    [⟨.cognatePrepositionalPhrase, .attested, .all⟩,
     ⟨.sprayLoad, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .pocket =>
    [⟨.cognatePrepositionalPhrase, .starred, .all⟩,
     ⟨.sprayLoad, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩]
  | .remove =>
    [⟨.clearTransitive, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .banish =>
    [⟨.clearTransitive, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .clear =>
    [⟨.clearTransitive, .attested, .all⟩,
     ⟨.clearIntransitive, .attested, .all⟩,
     ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .attested, .all⟩,
     ⟨.resultative, .starred, .all⟩, ⟨.zeroRelatedAdjective, .attested, .some⟩,
     ⟨.adjectivalPassive, .attested, .all⟩]
  | .wipeManner =>
    [⟨.wipe, .attested, .all⟩, ⟨.conative, .attested, .some⟩,
     ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.unspecifiedObject, .attested, .some⟩,
     ⟨.unspecifiedObjectPlusLocativePP, .attested, .some⟩,
     ⟨.resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .wipeInstrument =>
    [⟨.wipe, .attested, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.unspecifiedObject, .attested, .some⟩,
     ⟨.unspecifiedObjectPlusLocativePP, .attested, .some⟩,
     ⟨.resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .steal =>
    [⟨.clearTransitive, .starred, .all⟩, ⟨.benefactive, .starred, .all⟩,
     ⟨.conative, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩]
  | .cheat =>
    [⟨.clearTransitive, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.ofAlternatesWithOut, .attested, .all⟩]
  | .pit =>
    [⟨.cognatePrepositionalPhrase, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .debone =>
    [⟨.cognatePrepositionalPhrase, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .mine =>
    [⟨.cognatePrepositionalPhrase, .attested, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .send =>
    [⟨.dative, .attested, .some⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.boundNonreflexiveAnaphor, .starred, .all⟩]
  | .slide =>
    [⟨.dative, .attested, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .attested, .all⟩, ⟨.middle, .attested, .all⟩,
     ⟨.coreferentialPronounsVary, .attested, .all⟩]
  | .bringTake =>
    [⟨.dative, .attested, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.resultative, .starred, .all⟩,
     ⟨.boundNonreflexiveAnaphor, .attested, .all⟩]
  | .carry =>
    [⟨.dative, .attested, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.coreferentialPronounsVary, .attested, .all⟩]
  | .drive =>
    [⟨.dative, .marginal, .some⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.boundNonreflexiveAnaphor, .starred, .all⟩]
  | .pushPull =>
    [⟨.conative, .attested, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.wayObject, .attested, .some⟩,
     ⟨.boundNonreflexiveAnaphor, .attested, .all⟩,
     ⟨.resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .give =>
    [⟨.dative, .attested, .all⟩, ⟨.fulfilling, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .contribute =>
    [⟨.dative, .starred, .all⟩, ⟨.fulfilling, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .futureHaving =>
    [⟨.dative, .attested, .all⟩, ⟨.fulfilling, .attested, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .fulfilling => [⟨.fulfilling, .attested, .all⟩]
  | .equip => [⟨.fulfilling, .starred, .all⟩, ⟨.dative, .starred, .all⟩]
  | .get =>
    [⟨.fromPhrase, .attested, .all⟩, ⟨.benefactive, .attested, .all⟩,
     ⟨.dative, .starred, .all⟩, ⟨.clearTransitive, .starred, .all⟩,
     ⟨.sumOfMoneySubject, .attested, .some⟩]
  | .obtain =>
    [⟨.fromPhrase, .attested, .all⟩, ⟨.benefactive, .starred, .all⟩,
     ⟨.dative, .starred, .all⟩, ⟨.clearTransitive, .starred, .all⟩,
     ⟨.sumOfMoneySubject, .attested, .few⟩]
  | .exchange =>
    [⟨.dative, .starred, .all⟩, ⟨.benefactive, .starred, .all⟩]
  | .berry => []
  | .learn => []
  | .hold =>
    [⟨.conative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.bodyPartPossessorAscension, .attested, .some⟩]
  | .keep => [⟨.sprayLoad, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .conceal => [⟨.clearTransitive, .starred, .all⟩]
  | .throw =>
    [⟨.directionalPhrase, .attested, .all⟩, ⟨.dative, .attested, .most⟩,
     ⟨.withAgainst, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .pelt =>
    [⟨.directionalPhrase, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.withAgainst, .starred, .all⟩, ⟨.dative, .starred, .all⟩,
     ⟨.middle, .starred, .all⟩]
  | .hit =>
    [⟨.withAgainst, .attested, .all⟩, ⟨.throughWith, .starred, .all⟩,
     ⟨.conative, .attested, .all⟩,
     ⟨.bodyPartPossessorAscension, .attested, .all⟩,
     ⟨.togetherReciprocal, .attested, .all⟩,
     ⟨.simpleReciprocal, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.middle, .starred, .all⟩, ⟨.instrumentSubject, .attested, .all⟩,
     ⟨.unintentionalInterpretation, .attested, .some⟩,
     ⟨.resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .swat =>
    [⟨.withAgainst, .starred, .all⟩, ⟨.throughWith, .starred, .all⟩,
     ⟨.conative, .attested, .all⟩,
     ⟨.bodyPartPossessorAscension, .attested, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.instrumentSubject, .starred, .all⟩,
     ⟨.resultative, .attested, .some⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .spank =>
    [⟨.withAgainst, .starred, .all⟩, ⟨.throughWith, .starred, .all⟩,
     ⟨.conative, .starred, .all⟩,
     ⟨.bodyPartPossessorAscension, .attested, .some⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.instrumentSubject, .starred, .all⟩,
     ⟨.resultative, .attested, .all⟩, ⟨.ingNominal, .attested, .most⟩]
  | .nonAgentiveImpact =>
    [⟨.simpleReciprocalIntransitive, .starred, .all⟩,
     ⟨.togetherReciprocalIntransitive, .attested, .some⟩]
  | .poke =>
    [⟨.throughWith, .attested, .all⟩, ⟨.withAgainst, .starred, .all⟩,
     ⟨.conative, .attested, .some⟩,
     ⟨.bodyPartPossessorAscension, .attested, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .touch =>
    [⟨.withAgainst, .starred, .all⟩, ⟨.throughWith, .starred, .all⟩,
     ⟨.conative, .starred, .all⟩,
     ⟨.bodyPartPossessorAscension, .attested, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩,
     ⟨.unintentionalInterpretation, .starred, .all⟩,
     ⟨.resultative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .cut =>
    [⟨.conative, .attested, .all⟩,
     ⟨.bodyPartPossessorAscension, .attested, .some⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .attested, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩,
     ⟨.characteristicPropertyOfInstrument, .attested, .some⟩,
     ⟨.unintentionalInterpretation, .attested, .some⟩,
     ⟨.pathPhrase, .attested, .some⟩, ⟨.resultative, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .carve =>
    [⟨.conative, .starred, .all⟩,
     ⟨.bodyPartPossessorAscension, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .attested, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩,
     ⟨.characteristicPropertyOfInstrument, .attested, .some⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .mix =>
    [⟨.simpleReciprocal, .attested, .all⟩,
     ⟨.simpleReciprocalIntransitive, .attested, .most⟩,
     ⟨.togetherReciprocal, .attested, .all⟩,
     ⟨.togetherReciprocalIntransitive, .attested, .most⟩,
     ⟨.causativeInchoative, .attested, .most⟩, ⟨.middle, .attested, .all⟩]
  | .amalgamate =>
    [⟨.simpleReciprocal, .attested, .all⟩,
     ⟨.simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.togetherReciprocal, .starred, .all⟩,
     ⟨.togetherReciprocalIntransitive, .starred, .all⟩,
     ⟨.causativeInchoative, .attested, .most⟩, ⟨.middle, .attested, .all⟩]
  | .shake =>
    [⟨.togetherReciprocal, .attested, .all⟩,
     ⟨.simpleReciprocal, .starred, .all⟩, ⟨.causativeInchoative, .starred, .few⟩,
     ⟨.middle, .attested, .all⟩]
  | .tape =>
    [⟨.sprayLoad, .starred, .all⟩, ⟨.simpleReciprocal, .starred, .all⟩,
     ⟨.togetherReciprocal, .attested, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .attested, .all⟩,
     ⟨.resultative, .attested, .all⟩,
     ⟨.cognatePrepositionalPhrase, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .cling =>
    [⟨.simpleReciprocalIntransitive, .starred, .all⟩,
     ⟨.togetherReciprocalIntransitive, .attested, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .separate =>
    [⟨.simpleReciprocal, .attested, .all⟩,
     ⟨.simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.apartReciprocal, .starred, .all⟩,
     ⟨.apartReciprocalIntransitive, .starred, .all⟩,
     ⟨.causativeInchoative, .attested, .some⟩,
     ⟨.middle, .attested, .all⟩, ⟨.clearTransitive, .starred, .all⟩]
  | .split =>
    [⟨.simpleReciprocal, .starred, .all⟩,
     ⟨.simpleReciprocalIntransitive, .starred, .all⟩,
     ⟨.apartReciprocal, .attested, .all⟩,
     ⟨.apartReciprocalIntransitive, .attested, .all⟩,
     ⟨.causativeInchoative, .attested, .most⟩, ⟨.middle, .attested, .all⟩]
  | .disassemble =>
    [⟨.simpleReciprocal, .starred, .all⟩,
     ⟨.apartReciprocal, .starred, .all⟩, ⟨.causativeInchoative, .starred, .few⟩,
     ⟨.middle, .attested, .all⟩]
  | .differ =>
    [⟨.simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.apartReciprocalIntransitive, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .color =>
    [⟨.resultative, .attested, .all⟩,
     ⟨.cognatePrepositionalPhrase, .attested, .all⟩]
  | .imageImpression =>
    [⟨.imageImpression, .attested, .all⟩,
     ⟨.unspecifiedObject, .attested, .all⟩, ⟨.processNominal, .attested, .all⟩,
     ⟨.resultNominal, .attested, .all⟩]
  | .scribble =>
    [⟨.imageImpression, .starred, .all⟩,
     ⟨.unspecifiedObject, .attested, .some⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .illustrate =>
    [⟨.imageImpression, .starred, .all⟩, ⟨.processNominal, .attested, .some⟩,
     ⟨.resultNominal, .attested, .some⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .transcribe =>
    [⟨.imageImpression, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .build =>
    [⟨.materialProduct, .attested, .all⟩,
     ⟨.totalTransformation, .starred, .all⟩,
     ⟨.unspecifiedObject, .attested, .all⟩,
     ⟨.benefactive, .attested, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.rawMaterialSubject, .attested, .some⟩,
     ⟨.sumOfMoneySubject, .attested, .few⟩]
  | .grow =>
    [⟨.materialProductIntransitive, .attested, .all⟩,
     ⟨.totalTransformationIntransitive, .starred, .all⟩,
     ⟨.causativeInchoative, .attested, .all⟩]
  | .prepare =>
    [⟨.materialProduct, .starred, .all⟩, ⟨.benefactive, .attested, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩]
  | .create =>
    [⟨.materialProduct, .starred, .all⟩, ⟨.benefactive, .starred, .most⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.rawMaterialSubject, .starred, .all⟩]
  | .knead =>
    [⟨.materialProduct, .starred, .all⟩,
     ⟨.causativeInchoative, .attested, .some⟩,
     ⟨.rawMaterialSubject, .starred, .all⟩,
     ⟨.totalTransformation, .starred, .all⟩]
  | .turn =>
    [⟨.totalTransformation, .attested, .all⟩,
     ⟨.totalTransformationIntransitive, .attested, .most⟩,
     ⟨.causativeInchoative, .attested, .most⟩,
     ⟨.materialProduct, .starred, .all⟩,
     ⟨.materialProductIntransitive, .starred, .all⟩]
  | .performance =>
    [⟨.dative, .attested, .some⟩, ⟨.benefactive, .attested, .some⟩,
     ⟨.unspecifiedObject, .attested, .all⟩, ⟨.causativeInchoative, .starred, .all⟩]
  | .engender => [⟨.causativeInchoative, .starred, .all⟩]
  | .calve => []
  | .appoint =>
    [⟨.as, .attested, .all⟩, ⟨.dative, .starred, .all⟩,
     ⟨.infinitivalCopularClause, .attested, .some⟩]
  | .characterize =>
    [⟨.as, .starred, .all⟩, ⟨.infinitivalCopularClause, .attested, .few⟩]
  | .dub =>
    [⟨.as, .starred, .all⟩, ⟨.dative, .starred, .all⟩,
     ⟨.infinitivalCopularClause, .starred, .all⟩]
  | .declare =>
    [⟨.as, .starred, .all⟩, ⟨.dative, .starred, .all⟩,
     ⟨.infinitivalCopularClause, .attested, .all⟩]
  | .conjecture =>
    [⟨.as, .starred, .all⟩, ⟨.infinitivalCopularClause, .attested, .all⟩]
  | .masquerade => []
  | .orphan => [⟨.verbalPassive, .attested, .all⟩]
  | .captain => []
  | .see =>
    [⟨.middle, .starred, .all⟩, ⟨.possessorObject, .starred, .all⟩,
     ⟨.attributeObject, .attested, .all⟩]
  | .sight => [⟨.middle, .starred, .all⟩]
  | .peer => []
  | .stimulusSubjectPerception => [⟨.verbalPassive, .starred, .all⟩]
  | .amuse =>
    [⟨.causativeInchoative, .starred, .most⟩, ⟨.middle, .attested, .most⟩,
     ⟨.proArbObject, .attested, .all⟩, ⟨.extraposition, .attested, .all⟩,
     ⟨.passivePrepositionChoice, .attested, .all⟩, ⟨.resultative, .attested, .all⟩,
     ⟨.derivedNominalPassiveOnly, .attested, .all⟩, ⟨.erNominal, .attested, .some⟩,
     ⟨.ableAdjective, .attested, .some⟩]
  | .admire =>
    [⟨.middle, .starred, .all⟩, ⟨.possessorObject, .attested, .all⟩,
     ⟨.attributeObject, .attested, .all⟩, ⟨.as, .starred, .all⟩,
     ⟨.sententialComplement, .attested, .some⟩, ⟨.extraposition, .attested, .some⟩,
     ⟨.derivedNominalActiveOnly, .attested, .all⟩, ⟨.ableAdjective, .attested, .all⟩,
     ⟨.erNominal, .attested, .all⟩]
  | .marvel => [⟨.verbalPassive, .attested, .some⟩]
  | .appeal => [⟨.verbalPassive, .starred, .all⟩]
  | .want =>
    [⟨.possessorObject, .attested, .all⟩,
     ⟨.attributeObject, .starred, .all⟩, ⟨.as, .starred, .all⟩,
     ⟨.verbalPassive, .marginal, .all⟩]
  | .long => [⟨.verbalPassive, .marginal, .all⟩]
  | .judgment =>
    [⟨.middle, .starred, .all⟩, ⟨.possessorObject, .attested, .all⟩,
     ⟨.attributeObject, .starred, .all⟩, ⟨.as, .attested, .some⟩,
     ⟨.processNominal, .attested, .some⟩]
  | .assessment =>
    [⟨.possessorObject, .attested, .all⟩,
     ⟨.attributeObject, .starred, .all⟩]
  | .hunt => [⟨.unspecifiedObject, .attested, .all⟩]
  | .search => []
  | .stalk => []
  | .investigate => []
  | .rummage => []
  | .ferret => []
  | .correspond =>
    [⟨.collectiveNPSubject, .attested, .all⟩,
     ⟨.simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.understoodReciprocalObject, .starred, .all⟩,
     ⟨.withPrepositionDrop, .starred, .all⟩]
  | .marry =>
    [⟨.simpleReciprocalIntransitive, .starred, .all⟩,
     ⟨.understoodReciprocalObject, .attested, .all⟩,
     ⟨.withPrepositionDrop, .starred, .all⟩]
  | .meet =>
    [⟨.simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.understoodReciprocalObject, .attested, .all⟩,
     ⟨.withPrepositionDrop, .attested, .all⟩]
  | .transferOfMessage => [⟨.dative, .attested, .most⟩]
  | .tell =>
    [⟨.dative, .attested, .all⟩,
     ⟨.sententialComplementWithGoalObject, .attested, .all⟩,
     ⟨.sententialComplementWithGoalToPhrase, .starred, .all⟩,
     ⟨.sententialComplementWithoutGoalPhrase, .starred, .all⟩, ⟨.directSpeech, .attested, .all⟩,
     ⟨.parentheticalUse, .attested, .all⟩, ⟨.verbalPassive, .attested, .all⟩,
     ⟨.impersonalPassive, .starred, .all⟩, ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .mannerOfSpeaking =>
    [⟨.dative, .starred, .all⟩,
     ⟨.sententialComplementWithOptionalGoalToPhrase, .attested, .all⟩,
     ⟨.directSpeech, .attested, .all⟩, ⟨.parentheticalUse, .attested, .all⟩,
     ⟨.verbalPassive, .starred, .all⟩,
     ⟨.reactionObject, .attested, .all⟩,
     ⟨.cognateObject, .marginal, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .instrumentOfCommunication =>
    [⟨.dative, .attested, .all⟩,
     ⟨.sententialComplementWithOptionalGoalObject, .attested, .all⟩,
     ⟨.sententialComplementWithOptionalGoalToPhrase, .attested, .all⟩,
     ⟨.directSpeech, .attested, .all⟩, ⟨.parentheticalUse, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .talk =>
    [⟨.sententialComplement, .starred, .all⟩,
     ⟨.simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.togetherReciprocalIntransitive, .attested, .all⟩,
     ⟨.understoodReciprocalObject, .starred, .all⟩,
     ⟨.withPrepositionDrop, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .chitchat =>
    [⟨.sententialComplement, .starred, .all⟩,
     ⟨.simpleReciprocalIntransitive, .attested, .all⟩,
     ⟨.togetherReciprocalIntransitive, .starred, .all⟩,
     ⟨.understoodReciprocalObject, .starred, .all⟩,
     ⟨.withPrepositionDrop, .starred, .all⟩]
  | .say => [⟨.dative, .starred, .all⟩]
  | .complain =>
    [⟨.sententialComplementWithOptionalGoalToPhrase, .attested, .all⟩,
     ⟨.directSpeech, .attested, .all⟩, ⟨.parentheticalUse, .attested, .all⟩,
     ⟨.cognateObject, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .advise =>
    [⟨.proArbObject, .attested, .all⟩,
     ⟨.sententialComplementWithOptionalGoalObject, .attested, .all⟩,
     ⟨.directSpeech, .attested, .all⟩, ⟨.parentheticalUse, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .starred, .most⟩]
  | .animalSound =>
    [⟨.directionalPhrase, .starred, .all⟩,
     ⟨.reactionObject, .attested, .all⟩, ⟨.resultative, .attested, .all⟩]
  | .eat =>
    [⟨.unspecifiedObject, .attested, .all⟩, ⟨.conative, .attested, .all⟩,
     ⟨.instrumentSubject, .starred, .all⟩,
     ⟨.resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .chew =>
    [⟨.unspecifiedObject, .attested, .all⟩, ⟨.conative, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .gobble =>
    [⟨.unspecifiedObject, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .devour =>
    [⟨.unspecifiedObject, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .dine =>
    [⟨.unspecifiedObject, .starred, .all⟩, ⟨.conative, .starred, .all⟩]
  | .gorge =>
    [⟨.unspecifiedObject, .starred, .all⟩, ⟨.conative, .starred, .all⟩]
  | .feed => [⟨.dative, .attested, .all⟩]
  | .hiccup =>
    [⟨.cognateObject, .marginal, .all⟩, ⟨.resultative, .marginal, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .breathe =>
    [⟨.cognateObject, .attested, .few⟩, ⟨.substanceObject, .attested, .most⟩,
     ⟨.resultative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .exhale =>
    [⟨.cognateObject, .starred, .all⟩, ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .nonverbalExpression =>
    [⟨.cognateObject, .attested, .some⟩,
     ⟨.reactionObject, .attested, .all⟩,
     ⟨.resultative, .attested, .most⟩, ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .wink =>
    [⟨.understoodBodyPartObject, .attested, .all⟩,
     ⟨.verbalPassive, .starred, .all⟩, ⟨.cognateObject, .starred, .all⟩,
     ⟨.reactionObject, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .crane =>
    [⟨.understoodBodyPartObject, .attested, .all⟩,
     ⟨.cognateObject, .starred, .all⟩, ⟨.verbalPassive, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .curtsey =>
    [⟨.cognateObject, .starred, .all⟩,
     ⟨.reactionObject, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .snooze =>
    [⟨.causativeInchoative, .starred, .all⟩, ⟨.cognateObject, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .flinch =>
    [⟨.causativeInchoative, .starred, .all⟩, ⟨.cognateObject, .starred, .all⟩,
     ⟨.reactionObject, .starred, .all⟩]
  | .bodyInternalStateOfExistence => [⟨.causativeInchoative, .starred, .all⟩]
  | .suffocate =>
    [⟨.causativeInchoative, .attested, .all⟩, ⟨.middle, .marginal, .all⟩,
     ⟨.resultative, .attested, .some⟩]
  | .pain =>
    [⟨.cognateObject, .starred, .all⟩, ⟨.verbalPassive, .starred, .all⟩]
  | .tingle => [⟨.cognateObject, .starred, .all⟩]
  | .hurt => []
  | .changeOfBodilyState =>
    [⟨.causativeInchoative, .starred, .all⟩, ⟨.cognateObject, .starred, .all⟩]
  | .dress =>
    [⟨.causativeInchoative, .attested, .all⟩,
     ⟨.understoodReflexiveObject, .attested, .all⟩]
  | .groom => [⟨.understoodReflexiveObject, .starred, .all⟩]
  | .floss =>
    [⟨.understoodReflexiveObject, .starred, .all⟩,
     ⟨.understoodBodyPartObject, .attested, .all⟩]
  | .braid =>
    [⟨.understoodBodyPartObject, .starred, .all⟩,
     ⟨.understoodReflexiveObject, .starred, .all⟩]
  | .simpleDressing => [⟨.understoodReflexiveObject, .starred, .all⟩]
  | .dressingWell => [⟨.adjectivalPassive, .attested, .all⟩]
  | .beingDressed => [⟨.understoodReflexiveObject, .starred, .all⟩]
  | .murder =>
    [⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.instrumentSubject, .starred, .all⟩,
     ⟨.resultative, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .poison =>
    [⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.resultative, .attested, .some⟩, ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .lightEmission =>
    [⟨.swarm, .attested, .all⟩, ⟨.locativeInversion, .attested, .all⟩,
     ⟨.thereInsertion, .attested, .all⟩, ⟨.causativeInchoative, .attested, .some⟩,
     ⟨.adjectivalPerfectParticiple, .attested, .all⟩, ⟨.erNominal, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .soundEmission =>
    [⟨.swarm, .attested, .most⟩,
     ⟨.locativeInversion, .attested, .some⟩,
     ⟨.thereInsertion, .attested, .some⟩, ⟨.causativeInchoative, .attested, .all⟩,
     ⟨.directionalPhrase, .attested, .all⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩, ⟨.erNominal, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .smellEmission =>
    [⟨.swarm, .attested, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .substanceEmission =>
    [⟨.causativeInchoative, .attested, .some⟩, ⟨.substanceSource, .attested, .all⟩,
     ⟨.swarm, .attested, .some⟩,
     ⟨.locativeInversion, .attested, .some⟩,
     ⟨.thereInsertion, .attested, .some⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩, ⟨.erNominal, .attested, .all⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .destroy =>
    [⟨.causativeInchoative, .starred, .all⟩, ⟨.middle, .starred, .all⟩,
     ⟨.materialProduct, .starred, .all⟩,
     ⟨.totalTransformation, .starred, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.resultative, .starred, .all⟩, ⟨.zeroRelatedNominal, .starred, .all⟩]
  | .break_ =>
    [⟨.causativeInchoative, .attested, .all⟩, ⟨.middle, .attested, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩,
     ⟨.withAgainst, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.bodyPartPossessorAscension, .starred, .all⟩,
     ⟨.unintentionalInterpretation, .attested, .some⟩,
     ⟨.resultative, .attested, .all⟩, ⟨.zeroRelatedNominal, .attested, .all⟩]
  | .bend =>
    [⟨.causativeInchoative, .attested, .all⟩, ⟨.middle, .attested, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩,
     ⟨.withAgainst, .starred, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.bodyPartPossessorAscension, .starred, .all⟩,
     ⟨.resultative, .attested, .some⟩, ⟨.zeroRelatedNominal, .attested, .most⟩]
  | .cooking =>
    [⟨.causativeInchoative, .attested, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.cognateObject, .starred, .all⟩, ⟨.resultative, .attested, .all⟩,
     ⟨.adjectivalPassive, .attested, .all⟩]
  | .otherChangeOfState =>
    [⟨.causativeInchoative, .attested, .all⟩, ⟨.middle, .attested, .all⟩,
     ⟨.instrumentSubject, .attested, .all⟩, ⟨.conative, .starred, .all⟩,
     ⟨.swarm, .starred, .all⟩, ⟨.sprayLoad, .starred, .all⟩,
     ⟨.locativeInversion, .starred, .all⟩,
     ⟨.thereInsertion, .starred, .all⟩, ⟨.cognateObject, .starred, .all⟩,
     ⟨.resultative, .attested, .all⟩,
     ⟨.adjectivalPassive, .attested, .all⟩]
  | .entitySpecificChangeOfState =>
    [⟨.causativeInchoative, .starred, .all⟩, ⟨.cognateObject, .starred, .all⟩,
     ⟨.adjectivalPerfectParticiple, .attested, .some⟩]
  | .calibratableChangeOfState =>
    [⟨.causativeInchoative, .attested, .all⟩, ⟨.thereInsertion, .starred, .all⟩,
     ⟨.locativeInversion, .starred, .all⟩,
     ⟨.cognateObject, .starred, .all⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩]
  | .lodge =>
    [⟨.thereInsertion, .starred, .all⟩,
     ⟨.locativeInversion, .starred, .all⟩, ⟨.swarm, .starred, .all⟩,
     ⟨.causativeInchoative, .attested, .some⟩,
     ⟨.adjectivalPassive, .starred, .all⟩, ⟨.erNominal, .attested, .some⟩]
  | .exist =>
    [⟨.thereInsertion, .attested, .all⟩,
     ⟨.locativeInversion, .attested, .all⟩, ⟨.swarm, .starred, .all⟩,
     ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩]
  | .entitySpecificModeOfBeing =>
    [⟨.thereInsertion, .attested, .some⟩,
     ⟨.locativeInversion, .attested, .some⟩,
     ⟨.swarm, .attested, .some⟩, ⟨.causativeInchoative, .starred, .few⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩, ⟨.erNominal, .starred, .all⟩]
  | .modeOfBeingInvolvingMotion =>
    [⟨.swarm, .starred, .all⟩, ⟨.thereInsertion, .attested, .some⟩,
     ⟨.locativeInversion, .attested, .some⟩,
     ⟨.causativeInchoative, .attested, .some⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩]
  | .soundExistence =>
    [⟨.swarm, .attested, .all⟩, ⟨.thereInsertion, .attested, .all⟩,
     ⟨.locativeInversion, .attested, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩, ⟨.erNominal, .starred, .all⟩]
  | .swarm =>
    [⟨.swarm, .attested, .all⟩, ⟨.locativeInversion, .attested, .all⟩,
     ⟨.thereInsertion, .attested, .all⟩, ⟨.causativeInchoative, .starred, .all⟩]
  | .herd =>
    [⟨.swarm, .starred, .all⟩, ⟨.causativeInchoative, .attested, .some⟩,
     ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .bulge => [⟨.swarm, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩]
  | .spatialConfiguration =>
    [⟨.thereInsertion, .attested, .all⟩,
     ⟨.locativeInversion, .attested, .all⟩,
     ⟨.causativeInchoative, .attested, .some⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩]
  | .meander =>
    [⟨.locativeInversion, .attested, .all⟩,
     ⟨.thereInsertion, .attested, .all⟩]
  | .contiguousLocation =>
    [⟨.adjectivalPassive, .attested, .all⟩,
     ⟨.understoodReciprocalObject, .attested, .some⟩]
  | .appear =>
    [⟨.thereInsertion, .attested, .most⟩,
     ⟨.locativeInversion, .attested, .most⟩,
     ⟨.causativeInchoative, .starred, .most⟩,
     ⟨.adjectivalPerfectParticiple, .attested, .all⟩]
  | .reflexiveAppearance =>
    [⟨.thereInsertion, .starred, .all⟩,
     ⟨.locativeInversion, .starred, .all⟩,
     ⟨.reflexiveOfAppearance, .attested, .all⟩]
  | .disappearance =>
    [⟨.thereInsertion, .marginal, .all⟩,
     ⟨.locativeInversion, .marginal, .all⟩, ⟨.causativeInchoative, .starred, .all⟩,
     ⟨.adjectivalPerfectParticiple, .attested, .all⟩]
  | .occurrence =>
    [⟨.thereInsertion, .attested, .all⟩,
     ⟨.locativeInversion, .attested, .all⟩, ⟨.causativeInchoative, .starred, .all⟩]
  | .bodyInternalMotion =>
    [⟨.causativeInchoative, .starred, .all⟩, ⟨.bodyPartObject, .starred, .all⟩,
     ⟨.resultative, .attested, .some⟩,
     ⟨.directionalPhrase, .attested, .all⟩]
  | .assumePosition =>
    [⟨.thereInsertion, .starred, .all⟩,
     ⟨.locativeInversion, .starred, .all⟩]
  | .inherentlyDirectedMotion =>
    [⟨.locativePrepositionDrop, .attested, .some⟩,
     ⟨.causativeInchoative, .starred, .all⟩, ⟨.measurePhrase, .starred, .all⟩,
     ⟨.adjectivalPerfectParticiple, .attested, .all⟩,
     ⟨.depictivePhrase, .attested, .all⟩, ⟨.resultative, .starred, .all⟩]
  | .leave => [⟨.adjectivalPassive, .attested, .some⟩]
  | .roll =>
    [⟨.causativeInchoative, .attested, .most⟩,
     ⟨.locativePrepositionDrop, .starred, .all⟩,
     ⟨.resultative, .attested, .all⟩,
     ⟨.adjectivalPassive, .attested, .all⟩]
  | .run =>
    [⟨.inducedAction, .attested, .some⟩,
     ⟨.locativePrepositionDrop, .attested, .some⟩,
     ⟨.thereInsertion, .attested, .all⟩,
     ⟨.locativeInversion, .attested, .all⟩, ⟨.measurePhrase, .attested, .some⟩,
     ⟨.resultative, .attested, .all⟩,
     ⟨.adjectivalPassive, .attested, .some⟩,
     ⟨.adjectivalPerfectParticiple, .starred, .all⟩,
     ⟨.cognateObject, .starred, .all⟩, ⟨.zeroRelatedNominal, .attested, .some⟩]
  | .vehicleName =>
    [⟨.inducedAction, .attested, .some⟩,
     ⟨.locativePrepositionDrop, .attested, .some⟩,
     ⟨.resultative, .attested, .all⟩]
  | .nonVehicleName =>
    [⟨.inducedAction, .attested, .some⟩,
     ⟨.locativePrepositionDrop, .attested, .some⟩,
     ⟨.resultative, .attested, .all⟩]
  | .waltz =>
    [⟨.inducedAction, .attested, .all⟩, ⟨.resultative, .attested, .all⟩,
     ⟨.cognateObject, .attested, .all⟩]
  | .chase => [⟨.causativeInchoative, .starred, .all⟩]
  | .accompany => [⟨.causativeInchoative, .starred, .all⟩]
  | .avoid => []
  | .linger => [⟨.causativeInchoative, .starred, .all⟩]
  | .rush => [⟨.causativeInchoative, .attested, .all⟩]
  | .register =>
    [⟨.verbalPassive, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩]
  | .cost =>
    [⟨.verbalPassive, .starred, .all⟩, ⟨.causativeInchoative, .starred, .all⟩]
  | .fit => []
  | .price => [⟨.causativeInchoative, .starred, .all⟩]
  | .bill => [⟨.dative, .starred, .all⟩, ⟨.as, .starred, .all⟩]
  | .begin => [⟨.causativeInchoative, .attested, .some⟩]
  | .complete => [⟨.causativeInchoative, .starred, .all⟩]
  | .weekend => []
  | .weather => []

variable (c : LevinClass) (p : LevinProperty)

/-- Some line of the class's table gives the property the diacritic `m`. -/
def Marks (m : Attestation) : Prop :=
  ∃ q ∈ c.properties, q.property = p ∧ q.attestation = m

instance (m : Attestation) : Decidable (c.Marks p m) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _ ∧ _))

/-- The class shows the property in [levin-1993] Part II: its table attests it. -/
abbrev Participates : Prop := c.Marks p .attested

/-- The class lacks the property in [levin-1993] Part II: its table stars it. -/
abbrev Stars : Prop := c.Marks p .starred

/-- The class is tested for the property, attesting or starring it. -/
def Tests : Prop := c.Participates p ∨ c.Stars p

instance : Decidable (c.Tests p) := inferInstanceAs (Decidable (_ ∨ _))

/-- No class has one property with two diacritics. -/
theorem attestation_unique :
    ∀ c : LevinClass, ∀ q ∈ c.properties, ∀ q' ∈ c.properties,
      q.property = q'.property → q.attestation = q'.attestation := by
  decide +kernel

end LevinClass

end ArgumentStructure
