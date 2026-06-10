import Linglib.Morphology.Gender

/-!
# Georgian Gender
[corbett-2013] [corbett-1991]

WALS [corbett-2013] F30A/31A/32A codes Georgian as **no gender** —
Georgian lacks noun-class affixes, and WALS applies a noun-side-marking
criterion. Corbett 1991 classifies Georgian's rationality/animacy split as
a 4-class non-sex-based gender system on the basis of pronominal and verbal
agreement targets. The Corbett 1991 view is a per-Study override at
`Studies/Corbett1991.lean`.
-/

namespace Georgian.Gender

open Morphology.Gender

/-- Georgian gender typology per WALS [corbett-2013]: no gender on the
    noun-side-marking criterion. -/
def genderTypology : GenderProfile :=
  .fromWALS "Georgian" "kat"
    (rawGenderCount := 0)

theorem genderTypology_iso639 : genderTypology.iso639 = "kat" := rfl

theorem genderTypology_name : genderTypology.name = "Georgian" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

end Georgian.Gender
