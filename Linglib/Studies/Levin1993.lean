import Linglib.Semantics.ArgumentStructure.DiathesisAlternation
import Linglib.Data.Examples.Levin1993

/-!
# Levin (1993): English Verb Classes and Alternations

This file formalizes the diagnostic of [levin-1993]: a verb's participation in diathesis
alternations follows from its meaning, so verbs fall into semantically coherent classes that
share an alternation profile (`ArgumentStructure.LevinClass.participatesIn`). The book's
opening quadruple *break*, *cut*, *hit*, *touch* takes four distinct profiles across the
causative/inchoative, middle, conative, and body-part possessor ascension alternations, one
class each (`quadruple_profiles_distinct`), and every categorical alternation judgment among
the book's examples in `Data/Examples/Levin1993.json` agrees with the profile of the verb's
class (`participation_matches_profile`).

## Implementation notes

Rows record the verb's class by the book's section number and the alternation by name;
`classOf` and `alternationOf` read them into the substrate's enumerations, collapsing
subclasses to their representatives and leaving classes outside the enumerations' grain
unrepresented, on which the transfer theorem is vacuous. Marginal judgments carry no
categorical participation value.

## References

* [levin-1993]
-/

namespace Levin1993

open Data.Examples ArgumentStructure

/-- The class named by a section number of the book, subclasses collapsing to their
representatives. -/
def classOfString : String → Option LevinClass
  | "45.1" => some .break_
  | "21.1" => some .cut
  | "18.1" => some .hit
  | "20" => some .touch
  | "12" => some .pushPull
  | "9.7" => some .sprayLoad
  | "13.1" => some .give
  | "11.1" => some .send
  | "26.1" => some .build
  | "26.6" => some .turn
  | "43.4" => some .substanceEmission
  | "39.1" => some .eat
  | "39.4" => some .devour
  | "36.3" => some .socialInteraction
  | "48.1.1" => some .appear
  | "47.1" => some .exist
  | "47.5.1" => some .exist
  | "51.3" => some .mannerOfMotion
  | "51.3.2" => some .mannerOfMotion
  | "41.1.1" => some .dress
  | "37.3" => some .mannerOfSpeaking
  | "30.1" => some .see
  | "54.1" => some .measure
  | _ => none

/-- The alternation named by a row's tag. -/
def alternationOfString : String → Option DiathesisAlternation
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
  | "locative" => some .locative
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

/-- The class recorded on a row. -/
def classOf (e : LinguisticExample) : Option LevinClass :=
  (e.feature? "levin_class").bind classOfString

/-- The alternation recorded on a row. -/
def alternationOf (e : LinguisticExample) : Option DiathesisAlternation :=
  (e.feature? "alternation").bind alternationOfString

/-- The categorical participation recorded on a row, none for a marginal judgment. -/
def observed (e : LinguisticExample) : Option Bool :=
  match e.feature? "participates" with
  | some "true" => some true
  | some "false" => some false
  | _ => none

/-- Every categorical row with a representable class and alternation agrees with the class's
profile; in particular an inherently specified instrument requires an agent, which keeps
*cut* out of the inchoative. -/
theorem participation_matches_profile :
    ∀ e ∈ Examples.all, ∀ c ∈ classOf e, ∀ a ∈ alternationOf e, ∀ b ∈ observed e,
      c.participatesIn a = b := by
  decide

/-- The book's opening quadruple: *break*, *cut*, *hit*, and *touch* take pairwise distinct
profiles across the causative/inchoative, middle, conative, and body-part possessor ascension
alternations, so they instantiate four verb classes. -/
theorem quadruple_profiles_distinct :
    ([LevinClass.break_, .cut, .hit, .touch].map λ c =>
      [DiathesisAlternation.causativeInchoative, .middle, .conative,
        .bodyPartPossessorAscension].map c.participatesIn).Pairwise (· ≠ ·) := by
  decide

end Levin1993
