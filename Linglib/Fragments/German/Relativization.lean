import Linglib.Syntax.RelativeClause.Basic

/-!
# German Relativization Fragment
[keenan-comrie-1977]

Two relative clause markers:
- Relative pronoun *der/die/das* (+case, postnominal, covers SU–GEN;
  Table 1 leaves OCOMP blank)
- Prenominal participial construction (-case, covers SU only), the
  paper's European example of a subjects-only participial strategy
  (§1.3.1 p. 70, alongside Russian and Polish)

Data from [keenan-comrie-1977] Table 1.
-/

namespace German

open RelativeClause

/-- Relative pronoun *der/die/das*, inflected for case; postnominal RC.
    Covers SU–GEN (Table 1 p. 77; OCOMP blank).
    The paper's ex. (1): "der Mann, der in seinem Büro arbeitet"
    'the man who is working in his study'; [keenan-comrie-1979] p. 337
    exx. (31)-(32) show the case contrast (*der* nom. vs *den* acc.). -/
def relDer : Marker :=
  { form := "der/die/das"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique, .genitive]
  , notes := "Case-inflected relative pronoun; OCOMP no data" }

/-- Prenominal participial construction; NP_rel is deleted (gap). Covers
    SU only — the subjects-only participial strategy of §1.3.1 p. 70.
    The paper's ex. (2): "der in seinem Büro arbeitende Mann"
    'the man who is working in his study'. -/
def relParticiple : Marker :=
  { form := "participle"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject]
  , notes := "Participial; subjects only" }

/-- All German relative clause markers. -/
def relMarkers : List Marker := [relDer, relParticiple]

end German
