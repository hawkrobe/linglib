import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Dependent

/-!
# Yakut (Sakha) case

Sakha has an accusative-aligned system in which accusative and dative are dependent cases
while nominative and genitive are assigned under agreement with T and D; the genitive is
homophonous with the nominative except after a third-person possessive suffix.

## References

* [baker-vinokurova-2010]
-/

namespace Yakut.Case

open Syntax.Case

/-- The Sakha case system: dependent accusative and dative, nominative and genitive by
    Agree. -/
def yakutCaseConfig : CaseSystemConfig where
  langType := .accusative
  nomMode := .agreeT
  datMode := .dependent
  accMode := .dependent
  genMode := .agreeD

/-- The morphological case inventory: nominative, accusative, genitive, dative, ablative,
    instrumental, comitative and partitive. -/
def caseInventory : Finset Case := {.nom, .acc, .gen, .dat, .abl, .inst, .com, .part}

end Yakut.Case
