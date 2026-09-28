module

public import Mathlib.Tactic.TypeStar

/-!
# Case arrays

This file defines the case array of a verb, the case of its subject and the cases of its objects
in their unmarked linear order, over the cases of a language. The array records which cases the
arguments bear and nothing of where they come from. Which cases a verb assigns lexically and
which fall out of the configuration is what accounts of case disagree about, and each study
states its own.

## Main definitions

* `Verb.CaseArray`: the subject's case and the objects' cases
* `Verb.CaseArray.cases`: the array as a list

## References

* [zaenen-maling-thrainsson-1985]
* [thrainsson-2007]
-/

@[expose] public section

/-- A verb's case array records the case of its subject and the cases of its objects in their
unmarked linear order, the cases being those of the language, `C`. -/
structure Verb.CaseArray (C : Type*) where
  /-- The subject bears this case. -/
  subject : C
  /-- The objects bear these cases, in linear order. -/
  objects : List C := []
  deriving DecidableEq, Repr

namespace Verb.CaseArray

variable {C : Type*}

/-- `a.cases` lists the subject's case, then the objects'. -/
def cases (a : CaseArray C) : List C := a.subject :: a.objects

end Verb.CaseArray
