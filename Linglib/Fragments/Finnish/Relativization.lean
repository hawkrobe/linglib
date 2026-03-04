import Linglib.Core.Relativization.Basic

/-!
# Finnish Relativization Fragment
@cite{keenan-comrie-1977}

Two relative clause markers:
- Relative pronoun *joka* (+case, postnominal, covers SU–GEN)
- Participial construction (-case, prenominal, covers SU/DO)

Finnish is notable because the +case strategy is the primary (broader) one,
covering 5 of 6 AH positions. OCOMP does not exist as a distinct
grammatical category in Finnish.

Data from @cite{keenan-comrie-1977} Table 1.
-/

namespace Fragments.Finnish

open Core

/-- Relative pronoun *joka*. Declines for case (agreeing with the role
    inside the RC). Postnominal RC. Covers SU–GEN.
    OCOMP does not exist as a distinct category in Finnish.
    E.g., "mies [joka lähti]" 'man [who left]',
    "kaupunki [jossa asuin]" 'city [where I-lived]'. -/
def relJoka : RelClauseMarker :=
  { form := "joka"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique, .genitive]
  , notes := "Relative pronoun; declines for case; OCOMP does not exist" }

/-- Participial construction. Prenominal RC formed with a participle.
    NP_rel is a gap. Covers SU and DO only.
    E.g., "[ _ lähtenyt] mies" '[ _ left] man'. -/
def relParticipial : RelClauseMarker :=
  { form := "participle"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject, .directObject]
  , notes := "Participial; prenominal; covers SU/DO only" }

/-- All Finnish relative clause markers. -/
def relMarkers : List RelClauseMarker := [relJoka, relParticipial]

end Fragments.Finnish
