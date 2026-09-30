module

public import Linglib.Syntax.Clause.Relative

/-!
# Toba Batak relative clauses

Toba Batak has two postnominal relative-clause strategies and can relativize direct objects by
neither. The relativizer *na* introduces a clause with the relativized position left empty, as
in *boru-boru na manussi abit i* 'the woman who is washing clothes', and it relativizes subjects
only; a direct object must first be passivized into a subject. Noun phrases governed by
prepositions, indirect objects included, cannot be promoted, so a second strategy with the
marker *ima na* retains a personal pronoun in the relativized position, as in *dakdanak i, ima
na nipaboa ni si Rotua turi-turian i tu ibana* 'the child that Rotua told the story to'; it
relativizes indirect objects, obliques and genitives. The gap at the direct object is the
paper's reason for stating the Hierarchy Constraints per strategy. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace TobaBatak

/-- The relativizer *na* leaves the relativized position empty and relativizes subjects only. -/
def relNa : Relativizer where
  form := "na"
  placement := .postNominal
  realize
    | .subject => {.gap}
    | _ => ∅

/-- The relativizer *ima na*, with a personal pronoun retained in the relativized position,
relativizes indirect objects, obliques and genitives. -/
def relImaNa : Relativizer where
  form := "ima na"
  placement := .postNominal
  realize
    | .indirectObject | .oblique | .genitive => {.resumptive}
    | _ => ∅

/-- The Toba Batak relativizers. -/
def relativizers : List Relativizer := [relNa, relImaNa]

end TobaBatak
