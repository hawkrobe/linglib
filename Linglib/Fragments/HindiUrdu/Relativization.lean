module

public import Linglib.Syntax.Clause.Relative

/-!
# Hindi-Urdu relative clauses

Hindi-Urdu relativizes with the relative pronoun *jo*, oblique *jis-*, which carries the same
postpositions as an ordinary noun phrase and so codes the relativized position. It occurs in two
constructions, a postnominal clause and the correlative *jo … vo*, in which the head noun
stands inside the relative clause and is picked up by *vo* in the main clause; the paper codes
the correlative as an internally headed strategy. Both relativize subjects through genitives,
and objects of comparison are treated as obliques governed by postpositions. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace HindiUrdu

open RelativeClause

/-- The postnominal clause with the relative pronoun *jo* relativizes subjects through genitives. -/
def relJo : Marker :=
  { form := "jo/jis-"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , placement := .postNominal
  , positions := {.subject, .directObject, .indirectObject, .oblique, .genitive} }

/-- The correlative *jo … vo* keeps the head inside the relative clause and relativizes subjects
through genitives. -/
def relCorrelative : Marker :=
  { form := "jo … vo"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , placement := .correlative
  , positions := {.subject, .directObject, .indirectObject, .oblique, .genitive} }

/-- The Hindi-Urdu relative-clause markers. -/
def relMarkers : List Marker := [relJo, relCorrelative]

end HindiUrdu
