module

public import Linglib.Syntax.Clause.Relative

/-!
# Hebrew relative clauses

Modern Hebrew forms its postnominal relative clauses with the complementizer *she-*, in two
ways. With the relativized position left empty, *she-* relativizes subjects and direct objects.
With a personal pronoun in the relativized position, the strategy Keenan and Comrie take as the
characteristic Semitic one, it relativizes everything from direct objects down to objects of
comparison: *ha-isha she-David natan la et ha-sefer* 'the woman that David gave the book to',
with the pronoun in *la* 'to her'. The direct object is shared between the two, subjects do not
retain a pronoun, and relative clauses on objects of comparison are only marginally
acceptable. The data are Keenan and Comrie's; Sichel's distinction between the optional
resumptive of direct objects, a bound pronoun, and the obligatory resumptive of prepositional
objects, a movement copy, is the matter of the studies of resumption.

## Main definitions

* `Hebrew.relSheGap`, `Hebrew.relSheResumptive`, `Hebrew.relMarkers`: the two strategies.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace Hebrew

open RelativeClause

/-- *she-* with the relativized position left empty, relativizing subjects and direct
objects. -/
def relSheGap : Marker :=
  { form := "she-", npRel := .gap, bearsCaseMarking := false, placement := .postNominal,
    positions := {.subject, .directObject} }

/-- *she-* with a personal pronoun in the relativized position, relativizing everything from
direct objects down to objects of comparison. -/
def relSheResumptive : Marker :=
  { form := "she-", npRel := .resumptive, bearsCaseMarking := true, placement := .postNominal,
    positions := {.directObject, .indirectObject, .oblique, .genitive, .objComparison} }

/-- The relative-clause markers. -/
def relMarkers : List Marker := [relSheGap, relSheResumptive]

end Hebrew
