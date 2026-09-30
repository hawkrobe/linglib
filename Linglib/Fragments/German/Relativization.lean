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

/-- The relative pronoun *der*, *die*, *das* declines for the case of the relativized position
and relativizes subjects through genitives. -/
def relDer : Relativizer where
  form := "der/die/das"
  placement := .postNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique | .genitive => {.relPronoun}
    | _ => ∅

/-- The prenominal participial construction leaves the relativized position empty and
relativizes subjects only. -/
def relParticiple : Relativizer where
  form := "participle"
  placement := .preNominal
  realize
    | .subject => {.gap}
    | _ => ∅

/-- The German relativizers. -/
def relativizers : List Relativizer := [relDer, relParticiple]

end German
