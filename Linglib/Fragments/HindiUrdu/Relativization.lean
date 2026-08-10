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
    which "carries the same postpositions as ordinary NP's"; such RCs
    "often occur to the right of the matrix verb". Covers SU–GEN
    (Table 1 p. 77; [keenan-comrie-1979] p. 338, ex. (41) *jis se*). -/
def relJo : Marker :=
  { form := "jo/jis-"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique, .genitive]
  , notes := "Case-inflected relative pronoun; OCOMP starred (treated as OBL)" }

/-- Correlative *jo … vo*: "the head NP in the NP_rel position, still
    marked by the relativization marker, and cross-referenced in the
    'matrix' clause which follows the entire restricting clause"
    ([keenan-comrie-1979] p. 338, ex. (42) *jis caakuu … us caakuu*).
    Coded "internal, +case" in Table 1 p. 77 (K&C's typology lacks a
    correlative category); covers SU–GEN. -/
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
