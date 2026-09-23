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

open RelativeClause

/-- The relativizer *na* leaves the relativized position empty and relativizes subjects only. -/
def relGap : Marker :=
  { form := "na"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .postNominal
  , positions := {.subject} }

/-- The marker *ima na* with a retained personal pronoun relativizes indirect objects, obliques
and genitives. -/
def relResumptive : Marker :=
  { form := "ima na + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .postNominal
  , positions := {.indirectObject, .oblique, .genitive} }

/-- The Toba Batak relative-clause markers. -/
def relMarkers : List Marker := [relGap, relResumptive]

end TobaBatak
