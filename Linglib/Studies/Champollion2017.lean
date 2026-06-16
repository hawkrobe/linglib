import Linglib.Semantics.Aspect.Stratified
import Linglib.Semantics.Verb.Distributivity
import Linglib.Semantics.Plurality.Cover
import Linglib.Semantics.Plurality.Algebra
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Features.Aktionsart

/-!
# [champollion-2017]: Distributivity as a bridge between aspect and measurement

Paper-anchored study for *Parts of a Whole*, which unifies predicative
distributivity (Ch 4), atelicity (Ch 5–6), and pseudopartitive measurement
(Ch 7) under one property, *stratified reference* (`Stratified.Reference`,
Ch 4 §4.6). This file consumes that substrate against English Fragment
verbs.

## Main definitions

* `materializationOfSumHom` / `LexicallyCumulative` /
  `lexicallyCumulative_imp_cum` — the §2.5 (thematic roles are sum
  homomorphisms) and §2.7.2 (lexical cumulativity ⟹ Krifka `CUM`)
  algebraic substrate.
* `ChampollionPostulates` — Champollion's per-verb distributivity meaning
  postulates (§6.2–6.3), over the Fragment verbs' denotations via
  `Verb.StratifiesOver`.
* `subintervalReference_iff_cover` — atelicity as a Schwarzschild cover
  ([champollion-2017] §5.4, his Theorem 14 at the runtime dimension); the
  genuine consumer of `Semantics/Plurality/Cover.lean`.

## Caveats

* **Vendler classes are not Champollion primitives** (Ch 6 disclaims them
  explicitly). The Vendler↔atelicity theorems are a convenience bridge
  from Fragment Vendler tags to *for*/*in*-adverbial acceptability, not
  Champollion's own diagnostic (the subinterval-reference test).
* **Lexical cumulativity is assumed throughout** (§2.7.2), which is why
  `SubintervalReferenceUniv → CUM` does not hold — see `Aspect/Stratified`.
-/

namespace Champollion2017

open English.Predicates.Verbal
open Features (forXPrediction inXPrediction)
open _root_.Mereology
open Semantics.Plurality.Algebra (Materialization)
open Semantics.Aspect.Stratified
open Semantics.Plurality.Cover (IsFinCover algClosure_iff_exists_finCover)

/-! ### §2.5/§2.7.2 algebraic substrate -/

section ThematicRolesAndCumulativity
variable {E I : Type*} [SemilatticeSup E] [SemilatticeSup I]

/-- Champollion §2.5: any sum-homomorphism `f : Event → α` (thematic role
    or `τ` runtime) packages into a `Materialization` (= `SupHom E I`) via
    `IsSumHom.toSupHom`. -/
def materializationOfSumHom (f : E → I) [hf : IsSumHom f] : Materialization E I :=
  hf.toSupHom

@[simp] theorem materializationOfSumHom_apply (f : E → I) [IsSumHom f] (x : E) :
    materializationOfSumHom f x = f x := rfl

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

/-! ### Distributivity: meaning postulates over `Verb.denote` (§6.2–6.3)

Champollion's per-verb distributivity facts are lexical *meaning
postulates*, stated over the Fragment verbs' denotations via
`Verb.StratifiesOver` — the Verb-API distributivity property (relational
stratified distributive reference of `Verb.denote`), the substrate-grounded
successor to the retired Bool distributivity tags. -/

section Distributivity
variable {Entity State Time : Type*} [LinearOrder Time] [PartialOrder Entity]
  [SemilatticeSup (Event Time)]

/-- [champollion-2017]'s verb-distributivity meaning postulates
    (§6.2–6.3, (19)–(23)), over the Fragment verbs' `CosModel` denotations
    and the model's agent/theme role relations: *see* distributes on both
    roles, *kill* on theme only (collective causation blocks the agent),
    *meet* on neither (inherently collective). Postulates, not theorems —
    Champollion stipulates them lexically. -/
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

/-! ### Vendler ↔ atelicity (convenience bridge, not Champollion's diagnostic)

Champollion Ch 6 disclaims Vendler classes as primitives. These read a
Fragment verb's Vendler tag and the textbook for-adverbial / in-adverbial
prediction — a convenience for the atelic/telic split, distinct from the
subinterval-reference test above. -/

theorem fragment_verb_vendler_classes :
    see.toVerb.vendlerClass = some .state ∧
    kill.toVerb.vendlerClass = some .accomplishment ∧
    meet.toVerb.vendlerClass = some .achievement ∧
    eat.toVerb.vendlerClass = some .accomplishment :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Atelic Vendler classes (states/activities) accept *for X*. -/
theorem atelic_classes_accept_forX :
    forXPrediction .state = .accept ∧ forXPrediction .activity = .accept :=
  ⟨rfl, rfl⟩

/-- Telic Vendler classes (achievements/accomplishments) accept *in X*. -/
theorem telic_classes_accept_inX :
    inXPrediction .achievement = .accept ∧ inXPrediction .accomplishment = .accept :=
  ⟨rfl, rfl⟩

end Champollion2017
