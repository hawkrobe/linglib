module

public import Linglib.Syntax.Clause.Relative

/-!
# German relative clauses

German has two relative-clause strategies, the paper's opening illustration of a language with
more than one. The relative pronoun *der*, *die*, *das* declines for case and introduces a
postnominal clause, as in *der Mann, der in seinem Büro arbeitet* 'the man who is working in
his study'; it relativizes subjects through genitives, and objects of comparison cannot be
relativized. The participial construction precedes its head, as in *der in seinem Büro
arbeitende Mann* 'the man who is working in his study', and relativizes subjects only. The
data are [keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace German

open RelativeClause

/-- The relative pronoun *der*, *die*, *das* declines for the case of the relativized position
and relativizes subjects through genitives. -/
def relDer : Marker :=
  { form := "der/die/das"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , placement := .postNominal
  , positions := {.subject, .directObject, .indirectObject, .oblique, .genitive} }

/-- The prenominal participial construction leaves the relativized position empty and
relativizes subjects only. -/
def relParticiple : Marker :=
  { form := "participle"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject} }

/-- The German relative-clause markers. -/
def relMarkers : List Marker := [relDer, relParticiple]

end German
