import Linglib.Morphology.Word.Features
import Linglib.Syntax.Agreement.Bundle

/-!
# Universal Dependencies annotation of tokens

The bridge between the analytical inventories of person, number, gender and case and the
tags treebanks annotate. Each inventory realizes as a tag where one exists and each tag
ingests as a value: person's clusivity has no tag and collapses to the first person, so
ingestion after realization is coarsening; number's minimal, augmented and general values
have no tag, and the inverse, collective and count tags no value; the animacy genders have no
tag. A token's features realize as an annotation record and an annotation ingests as
features, and an annotation ingests as an agreement bundle.

## Main declarations

* `Person.toUD`, `Person.fromUD`: realization of a person as a tag, clusivity collapsing to
  the first person, and ingestion of a tag, with `Person.fromUD_toUD` showing ingestion after
  realization is coarsening.
* `Number.toUD`, `Number.fromUD`: the partial realization and ingestion of number, with
  `Number.roundtrip_fromUD_toUD` on the seven values that have a tag.
* `Gender.toUD`, `Gender.fromUD`: realization where a tag exists and total ingestion,
  `Gender.isPartialInv_fromUD_toUD` making realization a partial inverse.
* `Case.toUD`, `Case.fromUD`: the bijection between the two case inventories.
* `Morphology.Features.toUD`, `Morphology.Features.ofUD`: the annotation record a token's
  features realize as, and the features an annotation ingests as.
* `Agreement.Bundle.ofUD`: the agreement bundle an annotation ingests as.

## References

* [de-marneffe-zeman-2021]
-/

/-! ### Person -/

namespace Person

/-- Realize as an annotation: clusivity collapses to the first person. -/
def toUD : Person → UD.Person
  | .first | .firstInclusive | .firstExclusive => .first
  | .second => .second
  | .third => .third
  | .zero => .zero

/-- Ingest an annotation. -/
def fromUD : UD.Person → Person
  | .first => .first
  | .second => .second
  | .third => .third
  | .zero => .zero

@[simp] theorem toUD_fromUD (u : UD.Person) : (fromUD u).toUD = u := by cases u <;> rfl

/-- Ingestion after realization is coarsening: clusivity has no tag. -/
theorem fromUD_toUD (p : Person) : fromUD p.toUD = p.coarsen := by cases p <;> rfl

/-- The annotation conflates the clusivity values. -/
theorem ud_conflates_clusivity : Person.firstInclusive.toUD = Person.firstExclusive.toUD := rfl

end Person

/-! ### Number -/

namespace Number

/-- Realize as an annotation; general, minimal, augmented, unit augmented and global plural
have no tag. -/
def toUD : Number → Option UD.Number
  | .general => none
  | .singular => some .Sing
  | .dual => some .Dual
  | .trial => some .Tri
  | .paucal => some .Pauc
  | .plural => some .Plur
  | .greaterPaucal => some .Grpa
  | .greaterPlural => some .Grpl
  | .minimal => none
  | .augmented => none
  | .unitAugmented => none
  | .globalPlural => none

/-- Ingest an annotation; the inverse, collective and count tags have no value. -/
def fromUD : UD.Number → Option Number
  | .Sing => some .singular
  | .Plur => some .plural
  | .Dual => some .dual
  | .Tri => some .trial
  | .Pauc => some .paucal
  | .Grpa => some .greaterPaucal
  | .Grpl => some .greaterPlural
  | .Inv => none
  | .Coll => none
  | .Count => none

/-- The values with a tag round-trip. -/
theorem roundtrip_fromUD_toUD :
    ∀ v ∈ [Number.singular, .dual, .trial, .paucal, .plural, .greaterPaucal, .greaterPlural],
      v.toUD.bind fromUD = some v := by
  decide

end Number

/-! ### Gender -/

namespace Gender

/-- Realize as an annotation; the animacy labels have no tag. -/
def toUD : Gender → Option UD.Gender
  | .masculine => some .Masc
  | .feminine => some .Fem
  | .neuter => some .Neut
  | .common => some .Com
  | .animate => none
  | .inanimate => none

/-- Ingest an annotation. -/
def fromUD : UD.Gender → Gender
  | .Masc => .masculine
  | .Fem => .feminine
  | .Neut => .neuter
  | .Com => .common

/-- Realization is a partial inverse of ingestion. -/
theorem isPartialInv_fromUD_toUD : Function.IsPartialInv fromUD toUD :=
  fun x y ↦ by cases x <;> cases y <;> decide

@[simp] theorem toUD_fromUD (u : UD.Gender) : (fromUD u).toUD = some u :=
  isPartialInv_fromUD_toUD.eq u

/-- The labels with a tag round-trip. -/
theorem fromUD_of_toUD_eq_some {g : Gender} {u : UD.Gender} (h : g.toUD = some u) :
    fromUD u = g :=
  (isPartialInv_fromUD_toUD u g).1 h

end Gender

/-! ### Case -/

namespace Case

/-- Realize as an annotation. -/
def toUD : Case → UD.Case
  | .nom => .Nom
  | .acc => .Acc
  | .gen => .Gen
  | .dat => .Dat
  | .inst => .Ins
  | .loc => .Loc
  | .voc => .Voc
  | .abl => .Abl
  | .erg => .Erg
  | .abs => .Abs
  | .part => .Par
  | .ess => .Ess
  | .transl => .Tra
  | .com => .Com
  | .ade => .Ade
  | .ine => .Ine
  | .ill => .Ill
  | .ela => .Ela
  | .all => .All
  | .sub => .Sub
  | .sup => .Sup
  | .del => .Del
  | .ter => .Ter
  | .tem => .Tem
  | .caus => .Cau
  | .ben => .Ben
  | .perl => .Per
  | .abess => .Abe

/-- Ingest an annotation. -/
def fromUD : UD.Case → Case
  | .Nom => .nom
  | .Acc => .acc
  | .Gen => .gen
  | .Dat => .dat
  | .Ins => .inst
  | .Loc => .loc
  | .Voc => .voc
  | .Abl => .abl
  | .Erg => .erg
  | .Abs => .abs
  | .Par => .part
  | .Ess => .ess
  | .Tra => .transl
  | .Com => .com
  | .Ade => .ade
  | .Ine => .ine
  | .Ill => .ill
  | .Ela => .ela
  | .All => .all
  | .Sub => .sub
  | .Sup => .sup
  | .Del => .del
  | .Ter => .ter
  | .Tem => .tem
  | .Cau => .caus
  | .Ben => .ben
  | .Per => .perl
  | .Abe => .abess

/-- The inventories are in bijection. -/
theorem fromUD_toUD (c : Case) : fromUD c.toUD = c := by cases c <;> rfl

theorem toUD_fromUD (u : UD.Case) : (fromUD u).toUD = u := by cases u <;> rfl

end Case

/-! ### Tokens -/

namespace Morphology.Features

/-- The annotation of a token's features. -/
def toUD (f : Features) : UD.MorphFeatures where
  person := (f .person).map Person.toUD
  number := (f .number).bind Number.toUD
  gender := (f .gender).bind Gender.toUD
  case_ := (f .case).map Case.toUD
  definite := f .definiteness
  degree := f .degree
  pronType := f .pronType
  reflex := (f .reflex).isSome
  verbForm := f .verbForm
  tense := f .tense
  aspect := f .aspect
  mood := f .mood
  voice := f .voice
  polarity := f .polarity

/-- The features an annotation ingests as. -/
def ofUD (m : UD.MorphFeatures) : Features
  | .person => m.person.map Person.fromUD
  | .number => m.number.bind Number.fromUD
  | .gender => m.gender.map Gender.fromUD
  | .case => m.case_.map Case.fromUD
  | .definiteness => m.definite
  | .degree => m.degree
  | .pronType => m.pronType
  | .reflex => if m.reflex then some () else none
  | .verbForm => m.verbForm
  | .tense => m.tense
  | .aspect => m.aspect
  | .mood => m.mood
  | .voice => m.voice
  | .polarity => m.polarity

end Morphology.Features

/-- The agreement bundle an annotation ingests as. -/
def Agreement.Bundle.ofUD (m : UD.MorphFeatures) : Agreement.Bundle :=
  Agreement.Bundle.ofFeatures (Morphology.Features.ofUD m)
