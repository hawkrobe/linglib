module

/-!
# The properties of the Levin classes

The properties [levin-1993] Part II tests a class for, one constructor per label its entries
use: the alternations and constructions of Part One that some class attests or stars, located
by their Part One section, and the further properties the entries name (derived nominals,
sentential complements, phrases the verb takes, and so on). A generic label is read at the
grain of the Part One subsection the entry's example instantiates, so the causative
alternations a class stars are the causative/inchoative alternation and the locative
alternation a class shows is the spray/load, clear, wipe or swarm alternation of its variant.
Which classes have which properties is `LevinClass.properties` in
`LevinClass/Properties.lean`, and the English frame pair an alternation is, where it is one, is
`English.Alternations`.

## References

* [levin-1993]
-/

@[expose] public section

namespace ArgumentStructure

/-- A property [levin-1993] Part II tests a class for: an alternation or construction of Part
One, or one of the further properties its entries name. -/
inductive LevinProperty where
  /-- §1.1.1, Middle Alternation. -/
  | middle
  /-- §1.1.2.1, Causative/Inchoative Alternation. -/
  | causativeInchoative
  /-- §1.1.2.1 based on the locative variant of §2.3.1, as Levin lists it for the spray/load
  class: *Jessica sprayed paint on the wall* ~ *Paint sprayed on the wall*. -/
  | causativeInchoativeLocativeVariant
  /-- §1.1.2.1 based on the *with* variant of §2.3.1, as Levin lists it for the spray/load
  class: *Jessica sprayed the wall with paint* ~ *The wall sprayed with paint*. -/
  | causativeInchoativeWithVariant
  /-- §1.1.2.2, Induced Action Alternation. -/
  | inducedAction
  /-- §1.1.3, Substance/Source Alternation. -/
  | substanceSource
  /-- §1.2.1, Unspecified Object Alternation. -/
  | unspecifiedObject
  /-- §1.2.2, Understood Body-Part Object Alternation. -/
  | understoodBodyPartObject
  /-- §1.2.3, Understood Reflexive Object Alternation. -/
  | understoodReflexiveObject
  /-- §1.2.4, Understood Reciprocal Object Alternation. -/
  | understoodReciprocalObject
  /-- §1.2.5, PRO-arb Object Alternation. -/
  | proArbObject
  /-- §1.2.6.2, Characteristic Property of Instrument Alternation. -/
  | characteristicPropertyOfInstrument
  /-- §1.2.7, Way Object Alternation. -/
  | wayObject
  /-- §1.3, Conative Alternation. -/
  | conative
  /-- §1.4.1, Locative Preposition Drop Alternation. -/
  | locativePrepositionDrop
  /-- §1.4.2, With Preposition Drop Alternation. -/
  | withPrepositionDrop
  /-- §2.1, Dative Alternation. -/
  | dative
  /-- §2.2, Benefactive Alternation. -/
  | benefactive
  /-- §2.3.1, Spray/Load Alternation. -/
  | sprayLoad
  /-- §2.3.2, Clear Alternation (transitive). -/
  | clearTransitive
  /-- §2.3.3, Wipe Alternation. -/
  | wipe
  /-- §2.3.4, Swarm Alternation. -/
  | swarm
  /-- §2.3.5, Clear Alternation (intransitive). -/
  | clearIntransitive
  /-- §2.4.1, Material/Product Alternation (transitive). -/
  | materialProduct
  /-- §2.4.2, Material/Product Alternation (intransitive). -/
  | materialProductIntransitive
  /-- §2.4.3, Total Transformation Alternation (transitive). -/
  | totalTransformation
  /-- §2.4.4, Total Transformation Alternation (intransitive). -/
  | totalTransformationIntransitive
  /-- §2.5.1, Simple Reciprocal Alternation (transitive). -/
  | simpleReciprocal
  /-- §2.5.2, Together Reciprocal Alternation (transitive). -/
  | togetherReciprocal
  /-- §2.5.3, Apart Reciprocal Alternation (transitive). -/
  | apartReciprocal
  /-- §2.5.4, Simple Reciprocal Alternation (intransitive). -/
  | simpleReciprocalIntransitive
  /-- §2.5.5, Together Reciprocal Alternation (intransitive). -/
  | togetherReciprocalIntransitive
  /-- §2.5.6, Apart Reciprocal Alternation (intransitive). -/
  | apartReciprocalIntransitive
  /-- §2.6, Fulfilling Alternation. -/
  | fulfilling
  /-- §2.7, Image Impression Alternation. -/
  | imageImpression
  /-- §2.8, With/Against Alternation. -/
  | withAgainst
  /-- §2.9, Through/With Alternation. -/
  | throughWith
  /-- §2.12, Body-Part Possessor Ascension Alternation. -/
  | bodyPartPossessorAscension
  /-- §2.13.1, Possessor Object. -/
  | possessorObject
  /-- §2.13.2, Attribute Object. -/
  | attributeObject
  /-- §2.14, As Alternation. -/
  | as
  /-- §3.3, Instrument Subject Alternation. -/
  | instrumentSubject
  /-- §3.5, Locatum Subject Alternation. -/
  | locatumSubject
  /-- §3.8, Raw Material Subject Alternation. -/
  | rawMaterialSubject
  /-- §3.9, Sum of Money Subject Alternation. -/
  | sumOfMoneySubject
  /-- §4.2, Reflexive of Appearance Alternation. -/
  | reflexiveOfAppearance
  /-- §5.1, Verbal Passive. -/
  | verbalPassive
  /-- §5.2, Prepositional Passive. -/
  | prepositionalPassive
  /-- §5.3, Adjectival Passive (transitive verbs). -/
  | adjectivalPassive
  /-- §5.4, Adjectival Perfect Participles (intransitive verbs). -/
  | adjectivalPerfectParticiple
  /-- §6.1, There-Insertion. -/
  | thereInsertion
  /-- §6.2, Locative Inversion. -/
  | locativeInversion
  /-- §7.1, Cognate Object Construction. -/
  | cognateObject
  /-- §7.2, Cognate Prepositional Phrase Construction. -/
  | cognatePrepositionalPhrase
  /-- §7.3, Reaction Object Construction. -/
  | reactionObject
  /-- §7.4, X's Way Construction. -/
  | wayConstruction
  /-- §7.5, Resultative Construction. -/
  | resultative
  /-- §7.6, Unintentional Interpretation of Object. -/
  | unintentionalInterpretation
  /-- §7.7, Bound Nonreflexive Anaphor as Prepositional Object. -/
  | boundNonreflexiveAnaphor
  /-- §7.8, Directional Phrases with Nondirected Motion Verbs. -/
  | directionalPhrase
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
  /-- Sentential complement with goal *to* phrase. -/
  | sententialComplementWithGoalToPhrase
  /-- Sentential complement with optional goal object. -/
  | sententialComplementWithOptionalGoalObject
  /-- Sentential complement with optional goal *to* phrase. -/
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
  /-- Most verbs allow a *from* phrase. -/
  | fromPhrase
  /-- *With* alternates with *in*. -/
  | withAlternatesWithIn
  /-- *Of* alternates with *out* with a few verbs. -/
  | ofAlternatesWithOut
  /-- Unspecified object plus locative PP. -/
  | unspecifiedObjectPlusLocativePP
  /-- Acceptability of a coreferential interpretation of pronouns varies. -/
  | coreferentialPronounsVary
  deriving DecidableEq, Repr

end ArgumentStructure
