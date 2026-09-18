import Linglib.Syntax.Case.Alignment
import Linglib.Semantics.Aspect.Basic

/-!
# Hindi case

Hindi marks seven case functions with postpositions: the unmarked nominative, the ergative
*-ne*, the accusative and dative, both *-ko*, the genitive *-ka* with its agreeing forms *-ke*
and *-ki*, the locative *-mem*, and the ablative and instrumental, both *-se*. The alignment is
split by aspect: in the perfective the transitive subject takes the ergative and the object
the unmarked form, while elsewhere the subject is unmarked and the object takes *-ko* when it
is marked at all ([blake-1994]).

## References

* [blake-1994]
-/

namespace Hindi.Case

/-- The case inventory, with the two syncretic pairs, accusative and dative and ablative and
instrumental, as distinct cases since they occupy different ranks of Blake's hierarchy. -/
def inventory : Finset Case := {.nom, .erg, .acc, .dat, .gen, .loc, .abl, .inst}

/-- The inventory is contiguous on Blake's hierarchy. -/
example : Case.IsValidInventory inventory := by decide

/-- The ablative and the instrumental, both *-se*, share a rank of Blake's hierarchy. -/
theorem abl_inst_same_tier : Case.hierarchyRank .abl = Case.hierarchyRank .inst := rfl

/-- The alignment by aspect: ergative in the perfective, where the transitive subject takes
*-ne*, and accusative otherwise. -/
def alignment : Aspect.Perfectivity → Alignment.AlignmentType
  | .perfective => .ergative
  | .imperfective => .accusative

end Hindi.Case
