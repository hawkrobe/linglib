import Linglib.Semantics.ArgumentStructure.DiathesisAlternation
import Linglib.Syntax.Voice.Alternation
import Linglib.Fragments.English.Predicates
import Linglib.Fragments.English.Adposition
import Linglib.Data.Examples.Levin1993

/-!
# Levin (1993): English Verb Classes and Alternations

This file formalizes the diagnostic of [levin-1993]: a verb's participation in diathesis
alternations follows from its meaning, so verbs fall into semantically coherent classes that
share an alternation profile (`ArgumentStructure.LevinClass.Participates`). The book's
opening quadruple *break*, *cut*, *hit*, *touch* takes four distinct profiles across the
causative/inchoative, middle, conative, and body-part possessor ascension alternations, one
class each (`quadruple_profiles_distinct`), and every categorical alternation judgment among
the book's examples in `Data/Examples/Levin1993.json` agrees with the profile of the verb's
class (`participation_matches_profile`). The alternations that pair two argument frames are
frame-pair schemas (`schema?`), and the English fragment's verbs have the frames of their
class's attested alternations and none instantiating a starred one
(`frames_cover_profile`, `frames_respect_starred`).

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

/-- Every categorical row whose alternation the class's Part II page tests agrees with the
page: attested rows are in the class's profile and starred rows outside it. The passive, the
*way* construction, directional phrases and the swarm alternation are presented in Part One by
verb list and not tested on the class pages, so those rows fall outside the check. -/
theorem participation_matches_profile :
    ∀ e ∈ Examples.all, ∀ c ∈ classOf e, ∀ a ∈ alternationOf e, ∀ b ∈ observed e,
      a ∈ c.alternations ∪ c.starredAlternations → decide (c.Participates a) = b := by
  decide

/-! ### Frame-pair schemas of the alternations

The alternations of Part One as pairs of English argument frames with a slot correspondence,
the preposition fixed where the alternation's definition fixes it: *to* for the dative, *for*
for the benefactive, *at* for the conative, *with* for the *with* variant of the locative and
swarm alternations and for the instrument, *from* for the substance/source alternation, *out
of* and *into* for the material/product and total transformation alternations, *on* for
body-part possessor ascension. The locative variants of the locative and swarm alternations
fix only that the phrase is spatial. The middle, the passives, the postverbal-subject
alternations and the constructions of chapter 7 are not pairs of frames and have no schema. -/

open Voice English.Adpositions ArgumentFrame.Slot in
/-- The frame-pair schema of an alternation, where it has one. -/
def schema? : DiathesisAlternation → Option ValencyAlternation
  | .causativeInchoative => some decausativization
  | .inducedAction => some causativization
  | .conative => some { antipassivization with target := .pp (some at_) }
  | .substanceSource => some
      { source := .pp (some from_), target := .np,
        correspondence := [(external, complement 0), (complement 0, external)] }
  | .unspecifiedObject => some (objectDrop .indef)
  | .understoodBodyPartObject => some (objectDrop .bodyPart)
  | .understoodReflexiveObject => some (objectDrop .reflexive)
  | .understoodReciprocalObject => some (objectDrop .reciprocal)
  | .dative => some (toDoubleObject to_)
  | .benefactive => some (toDoubleObject for_)
  | .locative => some
      { source := ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
        target := .np_pp (some with_),
        correspondence := [(external, external), (complement 0, complement 1),
          (complement 1, complement 0)] }
  | .bodyPartPossessorAscension => some
      { source := .np, target := .np_pp (some on),
        correspondence := [(external, external), (complement 0, complement 1)] }
  | .swarm => some
      { source := .pp none, target := .np_pp (some with_),
        correspondence := [(external, complement 1), (complement 0, external)] }
  | .materialProduct => some
      { source := .np_pp (some outOf), target := .np_pp (some into),
        correspondence := [(external, external), (complement 0, complement 1),
          (complement 1, complement 0)] }
  | .totalTransformation => some
      { source := .np_pp (some into),
        target := ⟨some .nominal,
          [.nominal, .adpositional (some .spatial) (some from_),
            .adpositional (some .spatial) (some into)]⟩,
        correspondence := [(external, external), (complement 0, complement 0),
          (complement 1, complement 2)] }
  | .instrumentSubject => some
      { source := .np_pp (some with_), target := .np,
        correspondence := [(complement 0, complement 0), (complement 1, external)] }
  | .middle | .verbalPassive | .prepositionalPassive | .thereInsertion | .locativeInversion
  | .cognateObject | .wayConstruction | .resultative | .directionalPhrase => none
where
  /-- The unexpressed object alternations: the object dropped with interpretation `i`. -/
  objectDrop (i : ImplicitInterp) : ValencyAlternation :=
    { source := .np, target := .objectDrop (some i),
      correspondence := [(external, external), (complement 0, complement 0)] }
  /-- The dative and benefactive alternations: the *p* phrase becomes the first object. -/
  toDoubleObject (p : Adposition) : ValencyAlternation :=
    { source := .np_pp (some p), target := .np_np,
      correspondence := [(external, external), (complement 0, complement 1),
        (complement 1, complement 0)] }

/-- Every fragment verb Levin lists has a listed class whose profile its frames realize: frames
refining both frames of each schema the class attests, and none for a schema it stars. -/
theorem frames_realize_class :
    ∀ v ∈ English.verbs, v.levinClasses.Nonempty → ∃ c ∈ v.levinClasses,
      (∀ a ∈ c.alternations, ∀ σ ∈ schema? a, v.toVerb.Alternates σ) ∧
        ∀ a ∈ c.starredAlternations, ∀ σ ∈ schema? a, ¬ v.toVerb.Alternates σ := by
  decide +kernel

/-- The book's opening quadruple: *break*, *cut*, *hit*, and *touch* take pairwise distinct
profiles across the causative/inchoative, middle, conative, and body-part possessor ascension
alternations, so they instantiate four verb classes. -/
theorem quadruple_profiles_distinct :
    ([LevinClass.break_, .cut, .hit, .touch].map fun c ↦
      [DiathesisAlternation.causativeInchoative, .middle, .conative,
        .bodyPartPossessorAscension].map fun a ↦ decide (c.Participates a)).Pairwise (· ≠ ·) := by
  decide

end Levin1993
