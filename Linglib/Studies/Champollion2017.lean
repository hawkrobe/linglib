import Linglib.Semantics.Aspect.Stratified
import Linglib.Semantics.ArgumentStructure.Verb
import Linglib.Semantics.Plurality.Algebra
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Studies.Krifka1998

/-!
# Champollion 2017: distributivity as a bridge between aspect and measurement

This file formalizes results from *Parts of a Whole* ([champollion-2017]), which unifies
predicative distributivity, atelicity and pseudopartitive measurement under one property,
stratified reference: a predicate applies to an event exactly when that event divides
exhaustively into parts the predicate also applies to, along some dimension. The dimension is what
varies — thematic roles for distributivity, runtime for the *for*-adverbial, measure for the
pseudopartitive — and the substrate carries the property once (`Aspect.StratifiedReference`).

Two things are done here against that substrate. Lexical cumulativity, which the book assumes
throughout, entails Krifka's `CUM`; and atelicity in the runtime dimension is the existence of a
Schwarzschild cover into proper-subinterval parts, which is the book's own theorem relating
algebraic closure to covers. The per-verb distributivity facts — *see* distributing on both roles,
*kill* on its theme only, *meet* on neither — are meaning postulates in the book's sense, and are
recorded as such, over the Fragment verbs' denotations.

Vendler classes are not among the book's primitives; its atelicity diagnostic is the
subinterval-reference test, not a class label.

Chapter 6 sets the book's strata-based account of *for*-adverbials against [krifka-1998]'s
subregion-based one, whose presupposition (28) requires every temporal part of the event to fall
under the predicate. On an event that splits into two temporally non-overlapping parts the
subregion presupposition yields stratified reference along the runtime
(`stratifiedReference_of_divisiveness`); the *push carts all the way to the store for fifty
minutes* scenario of Figure 6.2, on a model of eight legs of four trips, has stratified reference
but violates the presupposition at the halfway legs (`pushCarts_stratified`,
`pushCarts_not_subregion`), which is the chapter's case against divisive reference.

## Main definitions

* `Verb.StratifiesOver` — a verb's denotation has stratified distributive reference along a role
* `LexicallyCumulative` — a predicate is a fixed point of algebraic closure
* `ChampollionPostulates` — the per-verb distributivity postulates over Fragment verbs

## Main results

* `lexicallyCumulative_imp_cum` — lexical cumulativity entails Krifka's `CUM`
* `subintervalReference_iff_cover` — atelicity is a finite cover into proper-subinterval parts
* `stratifiedReference_of_divisiveness` — on a temporally separable event, Krifka's divisiveness
  clause gives stratified reference along the runtime
* `pushCarts_stratified`, `pushCarts_not_subregion` — the Figure 6.2 event has stratified
  reference and fails the subregion presupposition

## Implementation notes

* The runtime dimension of chapter 6 is any monotone map into a part order of times, so the
  stratified reference in play is the generic `StratifiedReference τ (· < ·)` rather than the
  interval-runtime `SubintervalReference`; runtimes of back-and-forth events are discontinuous
  (the chapter's footnote on the scenario), and the finite model takes them to be sets of
  instants.
* The presupposition (28) is stated as the chapter states it, with the universal clause over the
  temporal parts of the event; the reflexive case is the predicate at the event itself.

## References

* [champollion-2017]
-/

namespace Verb

open _root_.Aspect

/-! ### Verb distributivity

Whether a verb distributes over the atomic fillers of a thematic role is a property of its event
denotation, not a feature it carries. -/

variable {Entity State T : Type*} [LinearOrder T] [PartialOrder Entity]
  [SemilatticeSup (Event T)]

/-- A verb **stratifies over** the atomic fillers of role `R`: for every
    argument assignment `(y, x)`, the verb's `CosModel` denotation has
    relational Stratified Distributive Reference along `R`
    (`RelationalDistributiveReference`). -/
def StratifiesOver (v : Verb) (M : CosModel Entity State T)
    (R : Entity → Event T → Prop) : Prop :=
  ∀ y x, RelationalDistributiveReferenceUniv R (M.denote v y x)

end Verb

namespace Champollion2017

open English.Predicates.Verbal
open _root_.Mereology
open Aspect

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
variable {Entity State T : Type*} [LinearOrder T] [PartialOrder Entity]
  [SemilatticeSup (Event T)]

/-- The verb-distributivity postulates of [champollion-2017] Ch 4, over the Fragment verbs'
`CosModel` denotations and the model's agent and theme roles: *see* distributes on both, *kill*
on its theme only — a member of the posse need not have killed anyone — and *meet* on neither. -/
structure ChampollionPostulates (M : Verb.CosModel Entity State T)
    (agentRole themeRole : Entity → Event T → Prop) : Prop where
  see_distributes_agent : see.toVerb.StratifiesOver M agentRole
  see_distributes_theme : see.toVerb.StratifiesOver M themeRole
  kill_distributes_theme : kill.toVerb.StratifiesOver M themeRole
  kill_not_distributes_agent : ¬ kill.toVerb.StratifiesOver M agentRole
  meet_not_distributes_agent : ¬ meet.toVerb.StratifiesOver M agentRole

end Distributivity

/-! ### Atelicity as a Schwarzschild cover (§5.4) -/

/-- §5.4: a predicate `P` has stratified subinterval reference at `e` iff `e` is the sum of a
finite Schwarzschild cover into proper-subinterval `P`-parts, the book's Theorem 14 at the
runtime dimension. -/
theorem subintervalReference_iff_cover {T : Type*} [LinearOrder T]
    [SemilatticeSup (Event T)] {P : Event T → Prop} {e : Event T} :
    SubintervalReference P e ↔
      ∃ (parts : Finset (Event T)) (hne : parts.Nonempty),
        (∀ p ∈ parts, P p ∧ p.runtime < e.runtime) ∧ parts.sup' hne id = e := by
  unfold SubintervalReference StratifiedReference SubintervalGranularity
  exact algClosure_iff_exists_sup' _ _

/-! ### Aspect and space: the subregion and strata approaches (§6.3–6.4) -/

section Subregion

open Krifka1998

variable {α T : Type*} [SemilatticeSup α] [PartialOrder T] (τ : α → T) (P : α → Prop)

/-- The subregion presupposition (28) that the chapter attributes to [krifka-1998]'s
*for*-adverbial: the event has a temporal part, and every temporal part of it falls under the
predicate. -/
def SubregionPresup (e : α) : Prop :=
  (∃ e', IsTemporalPart τ e' e) ∧ ∀ e', IsTemporalPart τ e' e → P e'

variable {τ P}

/-- On an event that splits into two parts with non-overlapping, non-null runtimes, the
divisiveness clause of the subregion presupposition yields stratified reference along the
runtime: the two parts are each other's temporal siblings, so both fall under the predicate,
and each has a properly smaller runtime. -/
theorem stratifiedReference_of_divisiveness (hτ : Monotone τ) {a b : α}
    (hov : ¬ Overlap (τ a) (τ b)) (ha : ¬ IsBot (τ a)) (hb : ¬ IsBot (τ b))
    (hdiv : ∀ e', IsTemporalPart τ e' (a ⊔ b) → P e') :
    StratifiedReference τ (· < ·) P (a ⊔ b) :=
  .sum (.base ⟨hdiv a ⟨le_sup_left, b, le_sup_right, hov⟩, lt_of_le_of_ne (hτ le_sup_left)
      λ h => hov ⟨τ b, hb, h ▸ hτ le_sup_right, le_rfl⟩⟩)
    (.base ⟨hdiv b ⟨le_sup_right, a, le_sup_left, λ o => hov o.symm⟩,
      lt_of_le_of_ne (hτ le_sup_right) λ h => hov ⟨τ a, ha, le_rfl, h ▸ hτ le_sup_left⟩⟩)

/-- The Back and forth scenario of Figure 6.2: four trips of two legs each, a leg at each
instant, the even legs from the lot halfway to the store and the odd legs on to the store. An
event is a set of legs and its runtime the set of their instants. -/
abbrev Leg := Fin 8

/-- *push carts all the way to the store* holds of a nonempty event whose path reaches the
store, that is, one containing a leg on to the store. -/
def PushCartsToStore (e : Finset Leg) : Prop := e.Nonempty ∧ ∃ k ∈ e, k.val % 2 = 1

instance : DecidablePred PushCartsToStore := λ _ => by unfold PushCartsToStore; infer_instance

/-- The fifty-minute event divides along time into its four trips, each of which reaches the
store within a proper part of the runtime: the strata-based account admits the *for*-adverbial
(Figure 6.2a). -/
theorem pushCarts_stratified :
    StratifiedReference id (· < ·) PushCartsToStore (Finset.univ : Finset Leg) :=
  (algClosure_iff_exists_sup' _ _).2
    ⟨{{0, 1}, {2, 3}, {4, 5}, {6, 7}}, by decide, by decide +kernel, by decide +kernel⟩

/-- The halfway legs form a temporal part of the event that does not reach the store, the
offending event of §6.4.1, so the subregion presupposition fails (Figure 6.2b). -/
theorem pushCarts_not_subregion :
    ¬ SubregionPresup id PushCartsToStore (Finset.univ : Finset Leg) := λ ⟨_, hdiv⟩ =>
  absurd (hdiv {0, 2, 4, 6} ⟨by decide, {1, 3, 5, 7}, by decide,
    λ h => overlap_iff_not_disjoint.1 h (by decide)⟩) (by decide)

end Subregion

end Champollion2017
