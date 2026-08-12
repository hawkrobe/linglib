import Linglib.Features.Possession

/-!
# Irish possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Per-language possession values for Irish (Indo-European, ISO `gle`): forms
`ta leabhar agam`, `teach an fhir`; Celtic at-possession (ta X ag-PRON) with
genitive case on the possessor in adnominal possession. Substrate types
(`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming these
values live in `Studies/NicholsBickel2013.lean`.
-/

namespace Irish.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .dependentMarking

end Irish.Possession
