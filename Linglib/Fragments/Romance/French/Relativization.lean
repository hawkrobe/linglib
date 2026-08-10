import Linglib.Syntax.RelativeClause.Basic

/-!
# French Relativization Fragment
[keenan-comrie-1977]

One relative clause marker: the case-coding relative pronoun system
*qui/que/dont/lequel* (+case, postnominal, covers SU–GEN; Table 1
leaves OCOMP blank).

Data from [keenan-comrie-1977] Table 1.
-/

namespace French

open RelativeClause

/-- Relative pronoun system *qui* (SU), *que* (DO), *dont* (GEN),
    *lequel* (with prepositions); postnominal RC. Covers SU–GEN
    (Table 1 p. 76; OCOMP blank). -/
def relQui : Marker :=
  { form := "qui/que/dont/lequel"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique, .genitive]
  , notes := "Case-coding relative pronoun system; OCOMP no data" }

/-- All French relative clause markers. -/
def relMarkers : List Marker := [relQui]

end French
