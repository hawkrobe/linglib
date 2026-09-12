import Linglib.Data.Complementation.Noonan2007

/-!
# Noonan (2007): Complementation

This file formalizes the generalizations of the complementation chapter [noonan-2007]
over its sample of complement-taking predicates. Complement types are morphologically
reduced to the extent that they lack components of main clauses, and equi-deletion, the
deletion of a complement subject coreferential with a matrix argument, is confined to
predicates that take some reduced complement type (`equi_requires_reduced`). Negative
raising, the appearance of a complement's negation in the matrix without change of truth
value, is confined to propositional attitude, desiderative, and modal predicates
(`negative_raising_class_restriction`), so knowledge predicates such as *regret* never
support it (`knowledge_no_negative_raising`).

## Implementation notes

The rows are the generated sample of `Data/Complementation/Noonan2007`, seven languages
with the chapter's predicate classes, attested complement codings, and equi-deletion and
negative-raising behaviour; the predicate classes and their reality status live in the
substrate's complementation module.

## TODO

An earlier version of this file stated an implicational hierarchy from indicative
desiderative complements to indicative propositional-attitude complements; the chapter
states no such generalization and the theorem was dropped.

## References

* [noonan-2007]
-/

namespace Noonan2007

open Data.Complementation Data.Complementation.Noonan2007

/-- Equi-deletion occurs only with predicates attested with some reduced complement type. -/
theorem equi_requires_reduced :
    ∀ d ∈ all, d.hasEquiDeletion = true → ∃ c ∈ d.codings, c.isReduced = true := by
  decide

/-- Negative raising occurs only with propositional attitude, desiderative, and modal
predicates. -/
theorem negative_raising_class_restriction :
    ∀ d ∈ all, d.hasNegativeRaising = true →
      d.ctpClass = .propAttitude ∨ d.ctpClass = .desiderative ∨ d.ctpClass = .modal := by
  decide

/-- Knowledge predicates never support negative raising. -/
theorem knowledge_no_negative_raising :
    ∀ d ∈ all, d.ctpClass = .knowledge → d.hasNegativeRaising = false := by
  decide

end Noonan2007
