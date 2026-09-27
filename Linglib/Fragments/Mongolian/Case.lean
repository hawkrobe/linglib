module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Minimalist.Case.Dependent

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

@[expose] public section

namespace Mongolian.Case

open Minimalist _root_.Case

/-- The Mongolian grammar of structural case: accusative on the lower of two NPs in the
    clause, nominative from T and genitive from D under Agree, and no dependent dative. -/
def grammar : CaseAssigners where
  domains := [(.D, {}), (.v, {}), (.C, { low := some .acc })]
  agree := [(.T, .nom), (.D, .gen)]

/-- The morphological case inventory: nominative, accusative, genitive, dative, ablative,
    instrumental, and comitative. -/
def inventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .abl, .inst, .com}

/-- The arguments of a ditransitive. -/
inductive DitransitiveArg
  | subject
  | directObject
  | indirectObject
  deriving DecidableEq, Repr

/-- Their positions in a Mongolian ditransitive: the subject above the direct object, shifted to
    the clause edge, above the dative indirect object. -/
def DitransitiveArg.position : DitransitiveArg → PhasedNP
  | .subject => {}
  | .directObject => { phase := .v, shifted := true }
  | .indirectObject => { phase := .v, lexicalCase := some .dat }

/-- A ditransitive's arguments, highest first. -/
def ditransitive : List DitransitiveArg := [.subject, .directObject, .indirectObject]

/-- Its cases, with finite T probing the clause. -/
def ditransitiveCases : Valuation DitransitiveArg (Case × Mechanism) :=
  grammar.assign DitransitiveArg.position [(.T, .C)] ditransitive

/-- The direct object is valued accusative by the dependent rule, the subject being the
    caseless NP above it. -/
theorem do_gets_dependent_acc :
    ditransitiveCases.valueOf .directObject = some (.acc, .dependent) := by decide

/-- The subject is valued nominative by T, not by a dependent rule. -/
theorem subject_gets_nom_by_agree :
    ditransitiveCases.valueOf .subject = some (.nom, .agree) := by decide

/-- The indirect object keeps its lexical dative and neither competes for dependent case nor
    creates a case position. -/
theorem io_has_lexical_case :
    ditransitiveCases.valueOf .indirectObject = some (.dat, .lexical) := by decide

end Mongolian.Case
