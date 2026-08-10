import Linglib.Syntax.RelativeClause.Basic

/-!
# Japanese Relativization Fragment
[keenan-comrie-1977]

Two relative clause markers, both prenominal and unmarked (no
relativizer, no relative pronoun):
- gap in NP_rel (-case, covers SU–GEN; OBL and GEN only for some NPs,
  OCOMP marginal)
- retained pronoun in NP_rel (+case, GEN only, and only for some NPs)

Data from [keenan-comrie-1977] Table 1 and Table 2.
-/

namespace Japanese

open RelativeClause

/-- Unmarked prenominal RC; NP_rel is deleted (gap). Covers SU–GEN
    (Table 1 p. 77: OBL and GEN carry split x/y entries — the strategy
    applies only for some NPs in those positions — and OCOMP is coded
    as not applying, though "the result is not judged too bad"). -/
def relGap : Marker :=
  { form := "∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique, .genitive]
  , notes := "Unmarked prenominal; OBL/GEN for some NPs only; OCOMP marginal" }

/-- Unmarked prenominal RC with a retained pronoun in NP_rel. GEN only,
    and only for some NPs (Table 1 p. 77; Table 2 codes Japanese
    retention as absent above GEN). -/
def relRetention : Marker :=
  { form := "∅ + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .preNominal
  , positions := [.genitive]
  , notes := "Retained pronoun; GEN only, for some NPs" }

/-- All Japanese relative clause markers. -/
def relMarkers : List Marker := [relGap, relRetention]

end Japanese
