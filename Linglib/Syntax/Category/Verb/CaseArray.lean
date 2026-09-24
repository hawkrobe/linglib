module

public import Linglib.Syntax.Case.Basic

/-!
# Case arrays

This file defines the case array of a verb, the case of its subject and the cases of its objects
in their unmarked linear order. The array records which cases the arguments bear and nothing of
where they come from. Which cases a verb assigns lexically and which fall out of the
configuration is what accounts of case disagree about, and each study states its own.

## Main definitions

* `Verb.CaseArray`: the subject's case and the objects' cases
* `Verb.CaseArray.cases`: the array as a list
* `Verb.CaseArray.IsQuirky`: the subject is not nominative

## References

* [zaenen-maling-thrainsson-1985]
* [thrainsson-2007]
-/

@[expose] public section

/-- A verb's case array records the case of its subject and the cases of its objects in their
unmarked linear order. -/
structure Verb.CaseArray where
  /-- The subject bears this case. -/
  subject : Case := .nom
  /-- The objects bear these cases, in linear order. -/
  objects : List Case := []
  deriving DecidableEq, Repr

namespace Verb.CaseArray

/-- `a.cases` lists the subject's case, then the objects'. -/
def cases (a : CaseArray) : List Case := a.subject :: a.objects

/-- The subject is not nominative. -/
def IsQuirky (a : CaseArray) : Prop := a.subject ≠ .nom

instance (a : CaseArray) : Decidable a.IsQuirky := inferInstanceAs (Decidable (_ ≠ _))

end Verb.CaseArray
