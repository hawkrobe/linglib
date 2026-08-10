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
    participle *-DIK*, RC subject in the genitive); NP_rel is deleted.
    Covers SU–OBL (Table 1 p. 79; [keenan-comrie-1979] p. 348
    exx. (117)-(118): *uyuy-an*, *ver-diğ-i*). -/
def relParticiple : Marker :=
  { form := "-(y)En/-DIK"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique]
  , notes := "Participial; NP_rel deleted" }

/-- Prenominal participial RC with a retained pronominal element in
    NP_rel: for an adnominal genitive, a possessive suffix retained on
    the head noun (ex. (119) *tavuğ-u* 'chicken-her'); for OCOMP, a
    stressed pronominal form (*kendisi*, ex. (120)), "although the
    result is not too natural" ([keenan-comrie-1979] p. 348; Table 1
    p. 79 codes OCOMP as +?). -/
def relRetention : Marker :=
  { form := "-(y)En/-DIK + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .preNominal
  , positions := [.genitive, .objComparison]
  , notes := "GEN: possessive suffix on head noun; OCOMP: stressed pronoun, marginal" }

/-- All Turkish relative clause markers. -/
def relMarkers : List Marker := [relParticiple, relRetention]

end Turkish
