import Linglib.Syntax.RelativeClause.Basic

/-!
# Hindi-Urdu Relativization Fragment
[keenan-comrie-1977]

Two relative clause markers, both built on the case-inflecting relative
pronoun *jo* (oblique *jis-*):
- Postnominal RC with *jo* (+case, covers SU–GEN)
- Correlative *jo … vo* (+case, covers SU–GEN), which [keenan-comrie-1977]
  Table 1 codes as their "internal" strategy — the paper's three-way
  surface typology (postnominal, prenominal, internal) has no separate
  correlative category, and the head NP occurs within the restricting
  clause (§1.4.1.2)

Both strategies are primary. OCOMP is starred in Table 1: objects of
comparison are treated as obliques governed by postpositions.

Data from [keenan-comrie-1977] Table 1 ("Hindi").
-/

namespace HindiUrdu

open RelativeClause

/-- Postnominal RC with the relative pronoun *jo* (oblique *jis-*),
    inflected for case. Covers SU–GEN (Table 1 p. 77; OCOMP treated as
    an oblique). -/
def relJo : Marker :=
  { form := "jo/jis-"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique, .genitive]
  , notes := "Case-inflected relative pronoun; OCOMP starred (treated as OBL)" }

/-- Correlative *jo … vo*: the *jo*-clause contains the head NP and is
    resumed by a correlate in the main clause. Coded "internal, +case"
    in Table 1 p. 77 (K&C's typology lacks a correlative category);
    covers SU–GEN. -/
def relCorrelative : Marker :=
  { form := "jo … vo"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , rcPosition := .correlative
  , positions := [.subject, .directObject, .indirectObject, .oblique, .genitive]
  , notes := "Correlative; K&C Table 1 codes as internal; OCOMP starred" }

/-- All Hindi-Urdu relative clause markers. -/
def relMarkers : List Marker := [relJo, relCorrelative]

end HindiUrdu
