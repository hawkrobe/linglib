import Linglib.Features.Case.Basic
import Linglib.Syntax.Minimalist.Case.Dependent

/-!
# Yakut (Sakha) case

Sakha has an accusative-aligned system in which accusative and dative are dependent cases
while nominative and genitive are assigned under agreement with T and D; the genitive is
homophonous with the nominative except after a third-person possessive suffix.

## References

* [baker-vinokurova-2010]
-/

namespace Yakut.Case

open Minimalist

/-- The Sakha grammar of structural case: dative on the higher of two NPs in the verb phrase,
    accusative on the lower of two in the clause, nominative from T and genitive from D under
    Agree, and no elsewhere case in any domain. -/
def grammar : CaseGrammar where
  domains := [(.D, {}), (.v, { high := some .dat }), (.C, { low := some .acc })]
  agree := [(.T, .nom), (.D, .gen)]

/-- The morphological case inventory: nominative, accusative, genitive, dative, ablative,
    instrumental, comitative and partitive. -/
def caseInventory : Finset Case := {.nom, .acc, .gen, .dat, .abl, .inst, .com, .part}

end Yakut.Case
