import Linglib.Syntax.RelativeClause.Basic

/-!
# Turkish Relativization Fragment
[keenan-comrie-1977]

Two relative clause markers, both prenominal:
- Participles *-(y)En ~ -DIK* with gap in NP_rel (-case, covers SU–OBL)
- Participle with a retained pronoun in NP_rel (+case, covers GEN and,
  with reduced acceptability, OCOMP)

The Korean pattern (prenominal participial gap cutting off at OBL) plus
pronoun retention below the cut-off.

Data from [keenan-comrie-1977] Table 1 and Table 2.
-/

namespace Turkish

open RelativeClause

/-- Prenominal participial RC (subject participle *-(y)En*, non-subject
    participle *-DIK*); NP_rel is deleted. Covers SU–OBL
    (Table 1 p. 79). -/
def relParticiple : Marker :=
  { form := "-(y)En/-DIK"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique]
  , notes := "Participial; NP_rel deleted" }

/-- Prenominal participial RC with a retained pronoun in NP_rel. Covers
    GEN, and OCOMP with reduced acceptability (Table 1 p. 79; Table 2
    codes retention as normal at GEN and OCOMP). -/
def relRetention : Marker :=
  { form := "-(y)En/-DIK + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .preNominal
  , positions := [.genitive, .objComparison]
  , notes := "Retained pronoun; OCOMP with reduced acceptability" }

/-- All Turkish relative clause markers. -/
def relMarkers : List Marker := [relParticiple, relRetention]

end Turkish
