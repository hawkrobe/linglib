import Linglib.Semantics.Aspect.Stratified
import Linglib.Semantics.ArgumentStructure.VerbDenotation
import Linglib.Semantics.Plurality.Cover
import Linglib.Semantics.Plurality.Algebra
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Champollion 2017: distributivity as a bridge between aspect and measurement

This file formalizes results from *Parts of a Whole* ([champollion-2017]), which unifies
predicative distributivity, atelicity and pseudopartitive measurement under one property,
stratified reference: a predicate applies to an event exactly when that event divides
exhaustively into parts the predicate also applies to, along some dimension. The dimension is what
varies — thematic roles for distributivity, runtime for the *for*-adverbial, measure for the
pseudopartitive — and the substrate carries the property once (`Stratified.Reference`).

Two things are done here against that substrate. Lexical cumulativity, which the book assumes
throughout, entails Krifka's `CUM`; and atelicity in the runtime dimension is the existence of a
Schwarzschild cover into proper-subinterval parts, which is the book's own theorem relating
algebraic closure to covers. The per-verb distributivity facts — *see* distributing on both roles,
*kill* on its theme only, *meet* on neither — are meaning postulates in the book's sense, and are
recorded as such, over the Fragment verbs' denotations.

Vendler classes are not among the book's primitives; its atelicity diagnostic is the
subinterval-reference test, not a class label.

## Main definitions

* `Verb.StratifiesOver` — a verb's denotation has stratified distributive reference along a role
* `LexicallyCumulative` — a predicate is a fixed point of algebraic closure
* `ChampollionPostulates` — the per-verb distributivity postulates over Fragment verbs

## Main results

* `lexicallyCumulative_imp_cum` — lexical cumulativity entails Krifka's `CUM`
* `subintervalReference_iff_cover` — atelicity is a finite cover into proper-subinterval parts

## References

* [champollion-2017]
-/

namespace Verb

open Aspect.Stratified

/-! ### Verb distributivity

Whether a verb distributes over the atomic fillers of a thematic role is a property of its event
denotation, not a feature it carries. -/

variable {Entity State Time : Type*} [LinearOrder Time] [PartialOrder Entity]
  [SemilatticeSup (Event Time)]

/-- A verb **stratifies over** the atomic fillers of role `R`: for every
    argument assignment `(y, x)`, the verb's `CosModel` denotation has
    relational Stratified Distributive Reference along `R`
    (`RelationalDistributiveReference`). -/
def StratifiesOver (v : Verb) (M : CosModel Entity State Time)
    (R : Entity → Event Time → Prop) : Prop :=
  ∀ y x, RelationalDistributiveReferenceUniv R (M.denote v y x)

end Verb

namespace Champollion2017

open English.Predicates.Verbal
open _root_.Mereology
open Aspect.Stratified
open Plurality.Cover (IsFinCover algClosure_iff_exists_finCover)

/-! ### §2.7.2 algebraic substrate -/

section ThematicRolesAndCumulativity

/-- Champollion §2.7.2: lexical cumulativity of a predicate — `AlgClosure P = P`
    extensionally (`P` a fixed point of the `*`-operator). -/
def LexicallyCumulative {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  ∀ x, AlgClosure P x ↔ P x

/-- Lexical cumulativity entails Krifka's `CUM` (closure under binary join). -/
theorem lexicallyCumulative_imp_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (h : LexicallyCumulative P) : CUM P := by
  intro x hPx y hPy
  exact (h _).mp (AlgClosure.sum (AlgClosure.base hPx) (AlgClosure.base hPy))

end ThematicRolesAndCumulativity

/-! ### Distributivity as meaning postulates

The book's per-verb distributivity facts are lexical meaning postulates in Hoeksema's sense, not
theorems; they are stated here over the Fragment verbs' denotations. -/

section Distributivity
variable {Entity State Time : Type*} [LinearOrder Time] [PartialOrder Entity]
  [SemilatticeSup (Event Time)]

/-- The verb-distributivity postulates of [champollion-2017] Ch 4, over the Fragment verbs'
`CosModel` denotations and the model's agent and theme roles: *see* distributes on both, *kill*
on its theme only — a member of the posse need not have killed anyone — and *meet* on neither. -/
structure ChampollionPostulates (M : Verb.CosModel Entity State Time)
    (agentRole themeRole : Entity → Event Time → Prop) : Prop where
  see_distributes_agent : see.toVerb.StratifiesOver M agentRole
  see_distributes_theme : see.toVerb.StratifiesOver M themeRole
  kill_distributes_theme : kill.toVerb.StratifiesOver M themeRole
  kill_not_distributes_agent : ¬ kill.toVerb.StratifiesOver M agentRole
  meet_not_distributes_agent : ¬ meet.toVerb.StratifiesOver M agentRole

end Distributivity

/-! ### Atelicity as a Schwarzschild cover (§5.4) -/

/-- [champollion-2017] §5.4: a predicate `P` has stratified subinterval
    reference at `e` iff `e` has a finite Schwarzschild cover into
    proper-subinterval `P`-parts. The for-adverbial atelicity diagnostic
    *is* the existence of such a cover — his Theorem 14
    (`Cover.algClosure_iff_exists_finCover`) at the runtime dimension. The
    genuine consumer of `Semantics/Plurality/Cover.lean`. -/
theorem subintervalReference_iff_cover {Time : Type*} [LinearOrder Time]
    [SemilatticeSup (Event Time)] [DecidableEq (Event Time)]
    {P : Event Time → Prop} {e : Event Time} :
    SubintervalReference P e ↔
      ∃ (parts : Finset (Event Time)) (hne : parts.Nonempty),
        IsFinCover parts hne e ∧ ∀ p ∈ parts, P p ∧ p.runtime < e.runtime := by
  unfold SubintervalReference Reference SubintervalGranularity
  exact algClosure_iff_exists_finCover

end Champollion2017
