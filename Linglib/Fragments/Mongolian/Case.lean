import Linglib.Features.Case.Basic
import Linglib.Syntax.Minimalist.Case.Dependent

/-!
# Mongolian case

Mongolian (Khalkha and Chakhar) has an accusative-aligned system in which accusative is a
dependent case, valued on the lower of two NPs in the clause, nominative is assigned by finite T
under Agree, and dative is nonstructural ([gong-2022], following [baker-vinokurova-2010]'s Sakha
but without its dependent dative). The morphological inventory lacks a dedicated locative, which
postpositions express.

## References

* [gong-2022]
* [baker-vinokurova-2010]
-/

namespace Mongolian.Case

open Minimalist _root_.Case

/-- The Mongolian grammar of structural case: accusative on the lower of two NPs in the
    clause, nominative from T and genitive from D under Agree, and no dependent dative. -/
def grammar : CaseGrammar where
  domains := [(.D, {}), (.v, {}), (.C, { low := some .acc })]
  agree := [(.T, .nom), (.D, .gen)]

/-- The morphological case inventory: nominative, accusative, genitive, dative, ablative,
    instrumental, and comitative. -/
def caseInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .abl, .inst, .com}

/-- A Mongolian ditransitive: the subject above the direct object, shifted to the clause
    edge, above the dative indirect object. -/
def ditransitive : List PhasedNP :=
  [{ label := "subject" }, { label := "DO", phase := .v, shifted := true },
   { label := "IO", phase := .v, lexicalCase := some .dat }]

/-- Its cases, with finite T probing the clause. -/
def ditransitiveCases : List (NP × Valuation) := grammar.assign [(.T, .C)] ditransitive

/-- The direct object is valued accusative by the dependent rule, the subject being the
    caseless NP above it. -/
theorem do_gets_dependent_acc :
    getCaseOf "DO" ditransitiveCases = some .acc ∧
    getMechanismOf "DO" ditransitiveCases = some .dependent := by decide

/-- The subject is valued nominative by T, not by a dependent rule. -/
theorem subject_gets_nom_by_agree :
    getCaseOf "subject" ditransitiveCases = some .nom ∧
    getMechanismOf "subject" ditransitiveCases = some .agree := by decide

/-- The indirect object keeps its lexical dative and neither competes for dependent case nor
    creates a case position. -/
theorem io_has_lexical_case : getMechanismOf "IO" ditransitiveCases = some .lexical := by decide

end Mongolian.Case
