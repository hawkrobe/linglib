import Linglib.Logic.CylindricAlgebra
import Linglib.Semantics.Dynamic.CDRT
import Linglib.Semantics.Dynamic.DRS.Indexed
import Mathlib.Data.Fin.VecNotation

/-!
# Muskens (1996): Combining Montague Semantics and Discourse Representation

This file formalizes the two worked developments of [muskens-1996] over the embedding of
discourse representation theory in classical type theory, in which states are atomic and
discourse referents are functions from states, the substrate at `Semantics/Dynamic/CDRT`.
The compositional fragment gives lexical translations for a fragment of English with
generalized coordination at every category (`cn`, `iv`, `tv`, `detA`, `detEvery`, `detNo`,
`andNP`, `orVP`) and runs the paper's derivations: cross-sentential anaphora, the donkey
sentence, and verb-phrase coordination with anaphora across the conjuncts. The weakest
precondition calculus extracts first-order truth conditions from update meanings; the
paper's `wp` is the relational preimage `SetRel.preimage`, so the compositional rules for
tests, sequencing, and random assignment and the reduction of truth to the weakest
precondition of the trivial condition are the substrate's and mathlib's
(`Update.preimage_test`, `SetRel.preimage_comp`, `Update.preimage_randomAssign`,
`SetRel.preimage_univ_right`), leaving the existential rule (`preimage_dexists`) and the syntactic
characterization of entailment (`drtEntails`).

## Implementation notes

The paper's types translate as follows: static predicates are `E → Prop`, dynamic
propositions are `Update S`, dynamic predicates take a discourse referent to an update
(`DynPred`), and dynamic quantifiers take a dynamic predicate to an update (`DynQuant`).
The composition rules are function application, sequencing, and abstraction and need no
separate formalization.

## References

* [muskens-1996]
-/

namespace Muskens1996

open DynamicSemantics DynamicSemantics.Update SetRel

variable {R S E : Type*}

/-! ### Semantic types -/

/-- Dynamic one-place predicate: type `[π]` in [muskens-1996]. -/
abbrev DynPred (S E : Type*) := Dref S E → Update S

/-- Dynamic generalized quantifier: type `[[π]]` in [muskens-1996]. -/
abbrev DynQuant (S E : Type*) := DynPred S E → Update S

/-! ### T₀ basic translations -/

/-- Common noun: `farmer ↝ λv[|farmer v]`. Type `[π]`. -/
def cn (P : E → Prop) : DynPred S E :=
  λ u => test (Condition.atom1 P u)

/-- Intransitive verb: `stink ↝ λv[|stinks v]`. Type `[π]`. -/
def iv (P : E → Prop) : DynPred S E :=
  λ u => test (Condition.atom1 P u)

/-- Transitive verb: `love ↝ λQλv(Q(λv'[|v loves v']))`.
Type `[[π]] → [π]`: takes an NP (object) and produces a VP. -/
def tv (R : E → E → Prop) : DynQuant S E → DynPred S E :=
  λ Q u => Q (λ v => test (Condition.atom2 R u v))

/-- Indefinite determiner: `aⁿ ↝ λP'λP([uₙ]; P'(uₙ); P(uₙ))`.
Type `[π] → [[π]]`; introduces discourse referent `u`. -/
def detA [RegisterStructure R S E] (u : R) : DynPred S E → DynQuant S E :=
  λ noun vp => randomAssign u ○ (noun (RegisterStructure.val u) ○ vp (RegisterStructure.val u))

/-- Universal determiner: `everyⁿ ↝ λP'λP(([uₙ]; P'(uₙ)) ⇒ P(uₙ))`.
Dynamic implication gives universal force. -/
def detEvery [RegisterStructure R S E] (u : R) : DynPred S E → DynQuant S E :=
  λ noun vp =>
    test (impl (randomAssign u ○ noun (RegisterStructure.val u)) (vp (RegisterStructure.val u)))

/-- Negative determiner: `noⁿ ↝ λP'λP[|not([uₙ]; P'(uₙ); P(uₙ))]`. -/
def detNo [RegisterStructure R S E] (u : R) : DynPred S E → DynQuant S E :=
  λ noun vp =>
    test (neg (randomAssign u ○
      (noun (RegisterStructure.val u) ○ vp (RegisterStructure.val u))))

/-- Proper name NP: `Maryⁿ ↝ λP.P(Mary)`. Type `[[π]]`. -/
def properNP (name : Dref S E) : DynQuant S E :=
  λ P => P name

/-- Pronoun NP: `heₙ ↝ λP.P(uₙ)` — picks up the dref from the antecedent. -/
def pro (u : Dref S E) : DynQuant S E :=
  λ P => P u

/-- Conditional: `if ↝ λpq[|p ⇒ q]`. -/
def cond : Update S → Update S → Update S :=
  λ p q => test (impl p q)

/-- Auxiliary negation: `doesn't ↝ λPλQ[|not Q(P)]` — takes VP (P) then
subject NP (Q), matching [muskens-1996]'s argument order. -/
def auxNeg : DynPred S E → DynQuant S E → Update S :=
  λ P Q => test (neg (Q P))

/-! ### Generalized coordination (§IV)

`and` = sequencing applied pointwise; `or` = `Update` disjunction applied
pointwise. The same schema works at every syntactic category. -/

/-- Sentence-level `and`: `K₁ and K₂ = K₁; K₂`. -/
def andS : Update S → Update S → Update S := comp

/-- Sentence-level `or`: `K₁ or K₂ = [K₁ or K₂]` (disjunction test). -/
def orS : Update S → Update S → Update S :=
  λ D₁ D₂ => test (disj D₁ D₂)

/-- VP-level `and`: `λv(P₁(v); P₂(v))`. -/
def andVP : DynPred S E → DynPred S E → DynPred S E :=
  λ P₁ P₂ u => P₁ u ○ P₂ u

/-- VP-level `or`: `λv[P₁(v) or P₂(v)]`. -/
def orVP : DynPred S E → DynPred S E → DynPred S E :=
  λ P₁ P₂ u => test (disj (P₁ u) (P₂ u))

/-- NP-level `and`: `λP(Q₁(P); Q₂(P))`. -/
def andNP : DynQuant S E → DynQuant S E → DynQuant S E :=
  λ Q₁ Q₂ P => Q₁ P ○ Q₂ P

/-- NP-level `or`: `λP[Q₁(P) or Q₂(P)]`. -/
def orNP : DynQuant S E → DynQuant S E → DynQuant S E :=
  λ Q₁ Q₂ P => test (disj (Q₁ P) (Q₂ P))

/-! ### The paper's derivations -/

section Examples

variable [RegisterStructure R S E]
variable (u₁ u₂ : R)

/-- "A¹ man adores a² woman. She₂ abhors him₁." — cross-sentential anaphora:
`[u₁]; [man u₁]; [u₂]; [woman u₂]; [u₁ adores u₂]; [u₂ abhors u₁]`. The
single-sentence tree is the paper's derivation (39); the man/woman/adores/
abhors box is the worked example Muskens runs the wp calculus on (p. 173),
with truth conditions `∃x₁ x₂ (man x₁ ∧ woman x₂ ∧ adores x₁ x₂ ∧
abhors x₂ x₁)`. -/
def exampleText (man woman : E → Prop) (adores abhors : E → E → Prop) : Update S :=
  detA u₁ (cn man) (tv adores (detA u₂ (cn woman))) ○
    pro (RegisterStructure.val u₂) (tv abhors (pro (RegisterStructure.val u₁)))

/-- "Every¹ farmer who owns a² donkey beats it₂." — universal force from
`detEvery`, anaphoric `it₂` picking up the indefinite's dref:
`([u₁]; [farmer u₁]; [u₂]; [donkey u₂]; [u₁ owns u₂]) ⇒ [u₁ beats u₂]`. -/
def donkeySentence
    (farmer donkey_ : E → Prop) (owns beats : E → E → Prop) : Update S :=
  detEvery u₁
    (λ v => cn farmer v ○ detA u₂ (cn donkey_) (λ w => test (Condition.atom2 owns v w)))
    (tv beats (pro (RegisterStructure.val u₂)))

/-- "A² cat catches a¹ fish and eats it₁." — the paper's (52), decorated as
tree (56): VP coordination with cross-conjunct anaphora. `andVP` sequences
the conjuncts, so the dref introduced by "a¹ fish" is accessible to "it₁"
(contrast (53) with `no¹`, where it is not). -/
def vpCoordExample
    (cat fish : E → Prop) (catches eats : E → E → Prop) : Update S :=
  detA u₂ (cn cat)
    (andVP (tv catches (detA u₁ (cn fish))) (tv eats (pro (RegisterStructure.val u₁))))

end Examples

/-! ### Weakest preconditions (§III.6)

The paper's `wp(K, χ)`, the input states from which `K` can reach a state satisfying `χ`, is
the relational preimage `SetRel.preimage K χ`. Its rules are the substrate's and mathlib's:
WP of a test is `preimage_test`, WP_{;} is `SetRel.preimage_comp`, the existential clause of
WP_{[]} is `preimage_randomAssign`, and Proposition 2, that `wp(K, ⊤)` is the truth condition
`∃j K(i)(j)`, is `SetRel.preimage_univ_right`. Muskens's statement of Proposition 2 carries a
closedness antecedent (proper `K`); in the semantic formulation the identity is unconditional. -/

/-- The weakest precondition of an existential update quantifies that of its scope over the
values of the register. -/
theorem preimage_dexists [RegisterStructure R S E] (u : R) (D : Update S) (χ : Condition S) :
    (dexists u D).preimage χ = {i | ∃ e : E, RegisterStructure.extend i u e ∈ D.preimage χ} := by
  rw [dexists, preimage_comp, preimage_randomAssign]

/-- DRT entailment: all premises true at `i` force the conclusion true at `i`. -/
def drtEntails (premises : List (Update S)) (conclusion : Update S) : Prop :=
  ∀ i, (∀ D ∈ premises, i ∈ D.dom) → i ∈ conclusion.dom

/-- Proposition 3: DRT entailment reduces to entailment of truth conditions
`wp(Kᵢ, ⊤)`. -/
theorem proposition_3 (premises : List (Update S)) (conclusion : Update S) :
    drtEntails premises conclusion ↔
    (∀ i, (∀ D ∈ premises, i ∈ D.preimage Set.univ) → i ∈ conclusion.preimage Set.univ) := by
  simp only [drtEntails, preimage_univ_right]

/-- DPL-style entailment: every output of `D₁` can be extended by `D₂`. -/
def dplEntails (D₁ D₂ : Update S) : Prop :=
  D₁.cod ⊆ D₂.dom

/-- Corollary to Proposition 3: DPL entailment = validity of dynamic
implication. -/
theorem dpl_entailment_eq_dimpl_valid (D₁ D₂ : Update S) :
    dplEntails D₁ D₂ ↔ ∀ i, i ∈ impl D₁ D₂ :=
  ⟨fun h _ _ hj => h ⟨_, hj⟩, fun h _ ⟨i, hj⟩ => h i hj⟩

/-! ### Truth-condition extraction rules -/

/-- TR of negation: `tr(not K) = ¬wp(K, ⊤)`. -/
theorem tr_neg_eq (D : Update S) : neg D = (D.preimage Set.univ)ᶜ := by
  rw [preimage_univ_right, neg_eq_compl_dom]

/-- TR of disjunction: `tr(K₁ or K₂) = wp(K₁, ⊤) ∨ wp(K₂, ⊤)` — the
existential distributes over disjunction. -/
theorem tr_disj_eq (D₁ D₂ : Update S) :
    disj D₁ D₂ = D₁.preimage Set.univ ∪ D₂.preimage Set.univ := by
  rw [preimage_univ_right, preimage_univ_right, disj_eq_dom_union_dom]

/-- TR of implication: `tr(K₁ ⇒ K₂) = ¬wp(K₁, ¬wp(K₂, ⊤))` — no way to
satisfy the antecedent without satisfying the consequent. -/
theorem tr_impl_eq (D₁ D₂ : Update S) :
    impl D₁ D₂ = (D₁.preimage (D₂.preimage Set.univ)ᶜ)ᶜ := by
  rw [preimage_univ_right, ← core_compl, compl_compl, impl_eq_core_dom]

/-! ### Semantic properness -/

/-- Semantic counterpart of [muskens-1996]'s properness (§III.5: a proper
DRS contains no free referents): satisfiability doesn't depend on the input
state. Proposition 1 connects the two — K is proper iff `wp(K, ⊤)` is a
closed formula. The syntactic notion is strictly finer: Muskens notes a
proper box and a non-proper box may have the same semantic value (his
(45) vs (47)), which is why this semantic version is only a counterpart,
not a reformulation. -/
def isProper (D : Update S) : Prop :=
  ∀ i₁ i₂, i₁ ∈ D.dom ↔ i₂ ∈ D.dom

/-- Proper DRSes have state-independent weakest preconditions. -/
theorem proper_wp_uniform (D : Update S) (h : isProper D) :
    ∀ i₁ i₂, i₁ ∈ D.preimage Set.univ ↔ i₂ ∈ D.preimage Set.univ := by
  simp only [preimage_univ_right]; exact h

/-! ### Cylindric algebra

CDRT's dref introduction and dref equality are cylindric-algebra operations
([henkin-monk-tarski-1971]): an existential is true where the cylindrification of its scope's
truth set is, by the substrate's `dom_dexists`, and dref equality is the diagonal. -/

section CylindricAlgebra

open CylindricAlgebra
open CDRT

/-- The equality condition on two discourse referents is the diagonal element. -/
theorem eq_dref_eq_diag {E : Type*} (i j : Nat) :
    Condition.eq (dref i : Dref (State E) E) (dref j) = diag i j := rfl

end CylindricAlgebra

/-! ### fn. 4: the equivalence is a fact about total assignments

[muskens-1996]'s fn. 4 scopes the SEM ≡ verification equivalence
(`DRS.toRel_iff_realize`) to total assignments, contrasting them with
[kamp-reyle-1993]'s partial embeddings, where re-declared referents keep
their values. A DRS that re-declares a referent separates the two: on
`[ | [x | man x] ⇒ [x | mortal x]]` the agree-off-universe semantics may
reassign the re-declared `x`, so it only demands that some mortal exist,
while the persistence rendering (`DRS.toRelAt`, `DRS/Indexed.lean`) forces
every man to be mortal. In a model with a non-mortal man the two truth
values differ (`fn4_diverges`) — the witness is proper (`fn4_isProper`), so
what fails is exactly reuse-freeness (`fn4_not_reuseFreeAt`), the hypothesis
of the reconciliation `DRS.trueRel_iff_toRelAt`. -/

section Fn4

open FirstOrder FirstOrder.Language DRT

/-- Relation symbols of the fn. 4 witness: `man` and `mortal`. -/
inductive Fn4Rel : ℕ → Type
  | man : Fn4Rel 1
  | mortal : Fn4Rel 1

/-- The language of the fn. 4 witness (no function symbols). -/
def fn4Lang : Language := ⟨λ _ => Empty, Fn4Rel⟩

/-- The antecedent `[x | man x]`. -/
def fn4Ante : DRS fn4Lang ℕ := .mk {0} [.rel .man (![0])]

/-- The consequent `[x | mortal x]` — re-declaring `x`. -/
def fn4Cons : DRS fn4Lang ℕ := .mk {0} [.rel .mortal (![0])]

/-- `[ | [x | man x] ⇒ [x | mortal x]]` with the referent `0` re-declared in
the consequent. -/
def fn4 : DRS fn4Lang ℕ := .mk ∅ [.imp fn4Ante fn4Cons]

/-- A man (`0`) who is not mortal, and a mortal (`1`). -/
instance : fn4Lang.Structure (Fin 2) where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .man => λ args => args 0 = 0
    | 1, .mortal => λ args => args 0 = 1

/-- The witness is proper: its referential presuppositions are satisfied. -/
theorem fn4_isProper : fn4.IsProper := by
  simp [DRS.IsProper, fn4, fn4Ante, fn4Cons]

/-- The witness is not reuse-free: the consequent re-declares `0`. -/
theorem fn4_not_reuseFreeAt : ¬ DRS.ReuseFreeAt ∅ fn4 := by
  simp [fn4, fn4Ante, fn4Cons]

/-- Flat truth: every input verifies the witness — the re-declared referent
may be reassigned, so it suffices that some mortal exist. -/
theorem fn4_trueRel (g : ℕ → Fin 2) : DRS.trueRel fn4 g := by
  refine ⟨g, λ x _ => rfl, ?_⟩
  intro c hc
  simp only [fn4, DRS.conditions_mk, List.mem_singleton] at hc
  subst hc
  rw [Embedding.verifies_imp]
  intro g₁ _ _
  refine ⟨Function.update g₁ 0 1,
    λ x hx => by rw [Function.update_apply, ite_eq_right (by simpa [fn4Cons] using hx)], ?_⟩
  intro c hc
  simp only [fn4Cons, DRS.conditions_mk, List.mem_singleton] at hc
  subst hc
  rw [Embedding.verifies_rel]
  show Function.update g₁ 0 1 0 = 1
  simp

/-- Indexed falsity: persistence keeps the re-declared referent's man value, so
no output verifies the witness in a model with a non-mortal man. -/
theorem fn4_not_toRelAt (g : ℕ → Fin 2) : ¬ ∃ g', DRS.toRelAt ∅ fn4 g g' := by
  rintro ⟨g', hg'⟩
  have himp : Condition.holdsAt (∅ ∪ ∅) (.imp fn4Ante fn4Cons) g' := hg'.2.1
  have hman : DRS.toRelAt (∅ ∪ ∅) fn4Ante g' (λ _ => 0) :=
    ⟨λ x hx => absurd hx (by simp), rfl, trivial⟩
  obtain ⟨g₂, heq, hmortal, -⟩ := himp _ hman
  have h0 : g₂ 0 = 0 := heq (by simp [fn4Ante])
  have h1 : g₂ 0 = 1 := hmortal
  exact absurd (h0.symm.trans h1) (by decide)

/-- The reconciliation `DRS.trueRel_iff_toRelAt` fails on the witness:
flat-true, indexed-false. -/
theorem fn4_diverges (g : ℕ → Fin 2) :
    ¬ (DRS.trueRel fn4 g ↔ ∃ g', DRS.toRelAt ∅ fn4 g g') :=
  λ h => fn4_not_toRelAt g (h.mp (fn4_trueRel g))

end Fn4

end Muskens1996
