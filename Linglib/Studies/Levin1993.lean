module

public import Mathlib.Order.UpperLower.Basic
public import Linglib.Core.Order.Interval
public import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
public import Linglib.Semantics.ArgumentStructure.LevinClass.Members
public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Adpositions
public import Linglib.Data.Examples.Levin1993

/-!
# Levin (1993): English Verb Classes and Alternations

This file formalizes the diagnostic of [levin-1993]: a verb's participation in diathesis
alternations follows from its meaning, so verbs fall into semantically coherent classes that
share an alternation profile (`ArgumentStructure.LevinClass.Participates`). The book's
opening quadruple *break*, *cut*, *hit*, *touch* takes four distinct profiles across the
causative/inchoative, middle, conative, and body-part possessor ascension alternations, one
class each (`quadruple_profiles_distinct`). The Introduction explains the profiles by four
components of verb meaning, "motion, contact, change of state, and causation"
(`MeaningComponent`), to which each of the four alternations is sensitive (`sensitivity`): the
body-part possessor ascension alternation needs contact and the conative contact and motion, the
middle causation of a change of state, and the causative/inchoative a pure change of state, one
whose meaning does not specify how the change comes about. Only the last condition is lost when a
meaning involves more components (`isUpperSet_sensitivity`,
`not_isUpperSet_sensitivity_causativeInchoative`), and the components of the Introduction's
characterizations of the four verbs meet the conditions exactly where the class pages of Part II
attest the alternations (`quadruple_mem_sensitivity_of_participates`,
`quadruple_prediction_matches`). Every
categorical alternation judgment among the book's examples in `Data/Examples/Levin1993.json`
agrees with the profile of the verb's class (`participation_matches_profile`). The
alternations that pair two argument frames are frame-pair schemas (`schema?`), and every
English fragment verb Levin lists has a class whose page its frames realize
(`frames_realize_class`).

## Implementation notes

Rows record the verb's class by the book's section number and the alternation by name;
`classOf` and `alternationOf` read them into the substrate's enumerations. A row's
participation in its alternation is its judgment: an acceptable row attests the alternation, a
starred row denies it, and a marginal row is categorical in neither direction.

The Introduction's conditions are necessary ones: a verb shows the body-part possessor ascension
alternation "only if its meaning involves the notion of contact" (p. 8), and the
causative/inchoative "is found only with verbs of pure change of state" (p. 10). Each is an
interval of sets of components, and an alternation for which the Introduction states no
condition has the whole lattice. A pure change of state may carry a cause, as *break* does "when
transitive" (p. 9), so the causative/inchoative's interval runs from the change of state to the
change of state with its cause.

## References

* [levin-1993]
-/

@[expose] public section

namespace Levin1993

open ArgumentStructure

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

/-- The class recorded on a row, by the book's section number. -/
def classOf (e : Datum) : Option LevinClass :=
  (e.feature? "levin_class").bind LevinClass.ofNumberString?

/-- The alternation recorded on a row. -/
def alternationOf (e : Datum) : Option DiathesisAlternation :=
  (e.feature? "alternation").bind alternationOfString

/-- Every categorical row whose alternation the class's Part II page tests agrees with the
page: the row is acceptable exactly when the alternation is in the class's profile. The
passive, the *way* construction, directional phrases and the swarm alternation are presented
in Part One by verb list and not tested on the class pages, so those rows fall outside the
check. -/
theorem participation_matches_profile :
    ∀ e ∈ Examples.all, ∀ c ∈ classOf e, ∀ a ∈ alternationOf e, e.judgment ≠ .marginal →
      c.Tests a → (c.Participates a ↔ e.judgment = .acceptable) := by
  decide +kernel

/-! ### The Introduction's quadruple

*break*, *cut*, *hit* and *touch* are told apart by the four diagnostic alternations (p. 7), and
the Introduction explains the difference by the components of their meanings (pp. 7–10). -/

/-- A component of verb meaning to which diathesis alternations are sensitive: "the notions of
motion, contact, change of state, and causation" (p. 10). -/
inductive MeaningComponent where
  | motion
  | contact
  | changeOfState
  | causation
  deriving DecidableEq, Fintype, Repr

open MeaningComponent

/-- The sets of meaning components of the verbs that can show an alternation (p. 10):
body-part possessor ascension "is sensitive to the notion of contact", the conative "to both
contact and motion", the middle "is found with verbs whose meaning involves causing a change of
state", and the causative/inchoative "is found only with verbs of pure change of state". -/
def sensitivity : DiathesisAlternation → NonemptyInterval (Finset MeaningComponent)
  | .bodyPartPossessorAscension => ⟨({contact}, ⊤), le_top⟩
  | .conative => ⟨({contact, motion}, ⊤), le_top⟩
  | .middle => ⟨({changeOfState, causation}, ⊤), le_top⟩
  | .causativeInchoative => ⟨({changeOfState}, {changeOfState, causation}), by decide⟩
  | _ => ⊤

/-- Every alternation but the causative/inchoative is open to a verb whose meaning involves more
components than one it is open to, as the middle is to verbs of causing a change of state
"whether or not their meaning also specifies how this change of state comes about" (p. 10). -/
theorem isUpperSet_sensitivity {a : DiathesisAlternation} (ha : a ≠ .causativeInchoative) :
    IsUpperSet (sensitivity a : Set (Finset MeaningComponent)) := by
  have : (sensitivity a).snd = ⊤ := by cases a <;> first | exact absurd rfl ha | rfl
  rw [NonemptyInterval.coe_def, this, Set.Icc_top]
  exact isUpperSet_Ici _

/-- The causative/inchoative is not open to a verb that adds a means, such as contact, to a pure
change of state (pp. 9–10). -/
theorem not_isUpperSet_sensitivity_causativeInchoative :
    ¬ IsUpperSet (sensitivity .causativeInchoative : Set (Finset MeaningComponent)) := fun h ↦
  absurd (SetLike.mem_coe.1 <| h (a := {changeOfState}) (b := {changeOfState, contact})
    (by decide) (SetLike.mem_coe.2 (by decide))) (by decide)

/-- The four diagnostic alternations of the Introduction. -/
def diagnosticAlternations : List DiathesisAlternation :=
  [.causativeInchoative, .middle, .conative, .bodyPartPossessorAscension]

/-- The quadruple takes pairwise distinct profiles over the diagnostic alternations, so it
instantiates four verb classes. -/
theorem quadruple_profiles_distinct :
    ([LevinClass.break_, .cut, .hit, .touch].map fun c ↦
      diagnosticAlternations.map fun a ↦ decide (c.Participates a)).Pairwise (· ≠ ·) := by
  decide +kernel

/-- The quadruple's classes with the meaning components of the Introduction's
characterizations (p. 10): "*touch* is a pure verb of contact, *hit* is a verb of contact by
motion, *cut* is a verb of causing a change of state by moving something into contact with the
entity that changes state, and *break* is a pure verb of change of state", with the notion of cause
it has "when transitive" (p. 9), since *cut* and *break* are "both verbs of causing a change of
state" (p. 9). -/
def quadruple : List (LevinClass × Finset MeaningComponent) :=
  [(.break_, {changeOfState, causation}), (.cut, {changeOfState, causation, contact, motion}),
    (.hit, {contact, motion}), (.touch, {contact})]

/-- The Introduction's conditions are necessary on the quadruple: every alternation a class
page of Part II attests is open to the class's meaning components. -/
theorem quadruple_mem_sensitivity_of_participates :
    ∀ p ∈ quadruple, ∀ a : DiathesisAlternation, p.1.Participates a → p.2 ∈ sensitivity a := by
  decide +kernel

/-- On the diagnostic alternations the conditions also suffice: the quadruple's meaning
components predict the class pages exactly. -/
theorem quadruple_prediction_matches :
    ∀ p ∈ quadruple, ∀ a ∈ diagnosticAlternations, (p.2 ∈ sensitivity a ↔ p.1.Participates a) := by
  decide +kernel

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
def schema? : DiathesisAlternation → Option Voice
  | .causativeInchoative => some anticausative
  | .inducedAction => some causative
  | .conative => some { antipassive with target := .pp (some at_) }
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
  | _ => none
where
  /-- The unexpressed object alternations: the object dropped with interpretation `i`. -/
  objectDrop (i : ImplicitInterp) : Voice :=
    { source := .np, target := .objectDrop (some i),
      correspondence := [(external, external), (complement 0, complement 0)] }
  /-- The dative and benefactive alternations: the *p* phrase becomes the first object. -/
  toDoubleObject (p : Adposition) : Voice :=
    { source := .np_pp (some p), target := .np_np,
      correspondence := [(external, external), (complement 0, complement 1),
        (complement 1, complement 0)] }

/-- Every fragment verb Levin lists has a listed class whose page its frames realize: frames
refining both frames of each schema the page attests for the whole class, and none for a
schema it stars. -/
theorem frames_realize_class :
    ∀ v ∈ English.Verbs.verbs, v.levinClasses.Nonempty → ∃ c ∈ v.levinClasses,
      ∀ p ∈ c.properties, ∀ a ∈ p.alternation?, ∀ σ ∈ schema? a,
        (p.diacritic = .none → p.scope = .all → v.toVerb.Alternates σ) ∧
          (p.diacritic = .star → ¬ v.toVerb.Alternates σ) := by
  decide +kernel

end Levin1993
