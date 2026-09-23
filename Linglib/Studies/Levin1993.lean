import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
import Linglib.Semantics.ArgumentStructure.LevinClass.Members
import Linglib.Fragments.English.Alternations
import Linglib.Fragments.English.Verbs
import Linglib.Data.Examples.Levin1993

/-!
# Levin (1993): English Verb Classes and Alternations

This file formalizes the diagnostic of [levin-1993]: a verb's participation in diathesis
alternations follows from its meaning, so verbs fall into semantically coherent classes that
share an alternation profile (`ArgumentStructure.LevinClass.Participates`). The book's
opening quadruple *break*, *cut*, *hit*, *touch* takes four distinct profiles across the
causative/inchoative, middle, conative, and body-part possessor ascension alternations, one
class each (`quadruple_profiles_distinct`), and on the quadruple the Introduction's component
prediction agrees with the classes of Part II (`quadruple_prediction_matches`). Every
categorical alternation judgment among the book's examples in `Data/Examples/Levin1993.json`
agrees with the profile of the verb's class (`participation_matches_profile`). The
alternations that pair two argument frames are the English alternations of
`Fragments/English/Alternations.lean` (`schema?`), and every English fragment verb Levin lists
has a class whose profile its frames realize (`frames_realize_class`).

## Implementation notes

Rows record the verb's class by the book's section number and the alternation by name;
`classOf` and `alternationOf` read them into the substrate's enumerations. A row's
participation in its alternation is its judgment: an acceptable row attests the alternation, a
starred row denies it, and a marginal row is categorical in neither direction.

## References

* [levin-1993]
-/

namespace Levin1993

open Data.Examples ArgumentStructure

/-- The alternation named by a row's tag. -/
def alternationOfString : String → Option LevinProperty
  | "causativeInchoative" => some .causativeInchoative
  | "inducedAction" => some .inducedAction
  | "middle" => some .middle
  | "conative" => some .conative
  | "substanceSource" => some .substanceSource
  | "unspecifiedObject" => some .unspecifiedObject
  | "understoodBodyPartObject" => some .understoodBodyPartObject
  | "understoodReflexiveObject" => some .understoodReflexiveObject
  | "understoodReciprocalObject" => some .understoodReciprocalObject
  | "dative" => some .dative
  | "benefactive" => some .benefactive
  | "sprayLoad" => some .sprayLoad
  | "bodyPartPossessorAscension" => some .bodyPartPossessorAscension
  | "swarm" => some .swarm
  | "materialProduct" => some .materialProduct
  | "totalTransformation" => some .totalTransformation
  | "instrumentSubject" => some .instrumentSubject
  | "verbalPassive" => some .verbalPassive
  | "prepositionalPassive" => some .prepositionalPassive
  | "thereInsertion" => some .thereInsertion
  | "locativeInversion" => some .locativeInversion
  | "cognateObject" => some .cognateObject
  | "wayConstruction" => some .wayConstruction
  | "resultative" => some .resultative
  | "directionalPhrase" => some .directionalPhrase
  | _ => none

/-- The class recorded on a row, by the book's section number. -/
def classOf (e : LinguisticExample) : Option LevinClass :=
  (e.feature? "levin_class").bind LevinClass.ofNumberString?

/-- The alternation recorded on a row. -/
def alternationOf (e : LinguisticExample) : Option LevinProperty :=
  (e.feature? "alternation").bind alternationOfString

/-- Every categorical row whose alternation Part II tests the class for agrees with the
class's profile: the row is acceptable exactly when the alternation is in it. The passive, the
*way* construction and directional phrases are presented in Part One by verb list and are not
tested per class, so those rows fall outside the check. -/
theorem participation_matches_profile :
    ∀ e ∈ Examples.all, ∀ c ∈ classOf e, ∀ a ∈ alternationOf e, e.judgment ≠ .marginal →
      c.Tests a → (c.Participates a ↔ e.judgment = .acceptable) := by
  decide +kernel

/-! ### The Introduction's quadruple

*break*, *cut*, *hit* and *touch* are told apart by the four diagnostic alternations, and on
these four classes the Introduction's component prediction agrees with Part II. -/

/-- The four diagnostic alternations of the Introduction. -/
def diagnosticAlternations : List LevinProperty :=
  [.causativeInchoative, .middle, .conative, .bodyPartPossessorAscension]

/-- The quadruple takes pairwise distinct profiles over the diagnostic alternations, so it
instantiates four verb classes. -/
theorem quadruple_profiles_distinct :
    ([LevinClass.break_, .cut, .hit, .touch].map fun c ↦
      diagnosticAlternations.map fun a ↦ decide (c.Participates a)).Pairwise (· ≠ ·) := by
  decide +kernel

/-- On the quadruple, the Introduction's component prediction matches Part II for
every diagnostic alternation. -/
theorem quadruple_prediction_matches :
    ∀ p ∈ [(LevinClass.break_, MeaningComponents.break_), (.cut, .cut), (.hit, .hit),
      (.touch, .touch)], ∀ a ∈ diagnosticAlternations,
      p.2.predictedAlternation a = decide (p.1.Participates a) := by
  decide +kernel

/-! ### The frame pairs of the alternations

The properties of Part II that pair two argument frames are the English alternations
of `Fragments/English/Alternations.lean`; the middle, the passives, the postverbal-subject
alternations, the constructions of chapter 7 and the further properties are not pairs of
frames and have none. -/

open English.Alternations in
/-- The frame pair of a property, where it is an alternation with one. -/
def schema? : LevinProperty → Option Voice
  | .causativeInchoative => some causativeInchoative
  | .causativeInchoativeLocativeVariant => some causativeInchoativeLocativeVariant
  | .causativeInchoativeWithVariant => some causativeInchoativeWithVariant
  | .inducedAction => some inducedAction
  | .conative => some conative
  | .substanceSource => some substanceSource
  | .unspecifiedObject => some unspecifiedObject
  | .understoodBodyPartObject => some understoodBodyPartObject
  | .understoodReflexiveObject => some understoodReflexiveObject
  | .understoodReciprocalObject => some understoodReciprocalObject
  | .dative => some dative
  | .benefactive => some benefactive
  | .sprayLoad => some sprayLoad
  | .swarm => some swarm
  | .materialProduct => some materialProduct
  | .totalTransformation => some totalTransformation
  | .bodyPartPossessorAscension => some bodyPartPossessorAscension
  | .instrumentSubject => some instrumentSubject
  | _ => none

/-- The verb's frames realize the class's profile: they refine both frames of each
alternation attested for the whole class, and neither of any alternation starred for the whole
class. -/
def Realizes (v : Verb) (c : LevinClass) : Prop :=
  ∀ p ∈ c.properties, p.scope = .all → ∀ σ ∈ schema? p.property,
    (p.attestation = .attested → v.Alternates σ) ∧ (p.attestation = .starred → ¬ v.Alternates σ)

instance (v : Verb) (c : LevinClass) : Decidable (Realizes v c) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _ → ∀ _ ∈ _, _))

/-- The listed verbs whose entry has the inchoative frame every class listing them stars:
*lock* among the tape verbs and *quit* among the complete verbs, each with an intransitive use
(*The door locked*, *The engine quit*) that Levin's generalization over the class denies. -/
def starredInchoatives : List String := ["lock", "quit"]

/-- Every other fragment verb Levin lists has a listed class whose profile its frames realize. -/
theorem frames_realize_class :
    ∀ v ∈ English.verbs, v.levinClasses.Nonempty → v.form ∉ starredInchoatives →
      ∃ c ∈ v.levinClasses, Realizes v.toVerb c := by
  decide +kernel

/-- The excepted verbs alternate by the causative/inchoative alternation, and every class
listing them stars it. -/
theorem starredInchoatives_alternate :
    ∀ v ∈ English.verbs, v.form ∈ starredInchoatives →
      v.toVerb.Alternates English.Alternations.causativeInchoative ∧
        ∀ c ∈ v.levinClasses, c.Stars .causativeInchoative := by
  decide +kernel

end Levin1993
