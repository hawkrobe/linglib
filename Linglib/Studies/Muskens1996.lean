import Linglib.Core.Logic.CylindricAlgebra
import Linglib.Semantics.Dynamic.CDRT
import Linglib.Semantics.Dynamic.DRS.Based
import Mathlib.Data.Fin.VecNotation

/-!
# Muskens (1996): Combining Montague Semantics and Discourse Representation

[muskens-1996] shows that DRT embeds in classical type theory once states are
atomic and discourse referents are functions from states — the Dynamic Ty2
substrate at `DynamicSemantics`. This study covers the paper's two
worked developments over that substrate:

* **The compositional fragment** (§III.4, §IV): lexical translations T₀ for a
  fragment of English, generalized coordination at every category, and the
  paper's derivations (cross-sentential anaphora, the donkey sentence, VP
  coordination with cross-conjunct anaphora).
* **The weakest precondition calculus** (§III.6): compositional extraction of
  first-order truth conditions from `Update` meanings — `wp`, its
  compositional rules, Propositions 2–3, and semantic properness.

## Semantic types (Table 2)

| Muskens type | Lean type | Description |
|--------------|-----------|-------------|
| `et` | `E → Prop` | static predicate |
| `s(st)` | `Update S` | dynamic proposition |
| `[π]` | `Dref S E → Update S` | dynamic predicate (`DynPred`) |
| `[[π]]` | `DynPred S E → Update S` | dynamic quantifier (`DynQuant`) |

Composition rules T₁–T₅ need no special formalization: they are function
application, `dseq`, and λ-abstraction.
-/

namespace Muskens1996

open DynamicSemantics

variable {R S E : Type*}

/-! ### Semantic types -/

/-- Dynamic one-place predicate: type `[π]` in [muskens-1996]. -/
abbrev DynPred (S E : Type*) := Dref S E → Update S

/-- Dynamic generalized quantifier: type `[[π]]` in [muskens-1996]. -/
abbrev DynQuant (S E : Type*) := DynPred S E → Update S

/-! ### T₀ basic translations -/

/-- Common noun: `farmer ↝ λv[|farmer v]`. Type `[π]`. -/
def cn (P : E → Prop) : DynPred S E :=
  λ u => test (atom1 P u)

/-- Intransitive verb: `stink ↝ λv[|stinks v]`. Type `[π]`. -/
def iv (P : E → Prop) : DynPred S E :=
  λ u => test (atom1 P u)

/-- Transitive verb: `love ↝ λQλv(Q(λv'[|v loves v']))`.
Type `[[π]] → [π]`: takes an NP (object) and produces a VP. -/
def tv (R : E → E → Prop) : DynQuant S E → DynPred S E :=
  λ Q u => Q (λ v => test (atom2 R u v))

/-- Indefinite determiner: `aⁿ ↝ λP'λP([uₙ]; P'(uₙ); P(uₙ))`.
Type `[π] → [[π]]`; introduces discourse referent `u`. -/
def detA [RegisterStructure R S E] (u : R) : DynPred S E → DynQuant S E :=
  λ noun vp => dseq (RegisterStructure.randomAssign u)
    (dseq (noun (RegisterStructure.val u)) (vp (RegisterStructure.val u)))

/-- Universal determiner: `everyⁿ ↝ λP'λP(([uₙ]; P'(uₙ)) ⇒ P(uₙ))`.
Dynamic implication gives universal force. -/
def detEvery [RegisterStructure R S E] (u : R) : DynPred S E → DynQuant S E :=
  λ noun vp =>
    test (dimpl (dseq (RegisterStructure.randomAssign u) (noun (RegisterStructure.val u)))
      (vp (RegisterStructure.val u)))

/-- Negative determiner: `noⁿ ↝ λP'λP[|not([uₙ]; P'(uₙ); P(uₙ))]`. -/
def detNo [RegisterStructure R S E] (u : R) : DynPred S E → DynQuant S E :=
  λ noun vp =>
    test (dneg (dseq (RegisterStructure.randomAssign u)
      (dseq (noun (RegisterStructure.val u)) (vp (RegisterStructure.val u)))))

/-- Proper name NP: `Maryⁿ ↝ λP.P(Mary)`. Type `[[π]]`. -/
def properNP (name : Dref S E) : DynQuant S E :=
  λ P => P name

/-- Pronoun NP: `heₙ ↝ λP.P(uₙ)` — picks up the dref from the antecedent. -/
def pro (u : Dref S E) : DynQuant S E :=
  λ P => P u

/-- Conditional: `if ↝ λpq[|p ⇒ q]`. -/
def cond : Update S → Update S → Update S :=
  λ p q => test (dimpl p q)

/-- Auxiliary negation: `doesn't ↝ λPλQ[|not Q(P)]` — takes VP (P) then
subject NP (Q), matching [muskens-1996]'s argument order. -/
def auxNeg : DynPred S E → DynQuant S E → Update S :=
  λ P Q => test (dneg (Q P))

/-! ### Generalized coordination (§IV)

`and` = sequencing applied pointwise; `or` = `Update` disjunction applied
pointwise. The same schema works at every syntactic category. -/

/-- Sentence-level `and`: `K₁ and K₂ = K₁; K₂`. -/
def andS : Update S → Update S → Update S := dseq

/-- Sentence-level `or`: `K₁ or K₂ = [K₁ or K₂]` (disjunction test). -/
def orS : Update S → Update S → Update S :=
  λ D₁ D₂ => test (ddisj D₁ D₂)

/-- VP-level `and`: `λv(P₁(v); P₂(v))`. -/
def andVP : DynPred S E → DynPred S E → DynPred S E :=
  λ P₁ P₂ u => dseq (P₁ u) (P₂ u)

/-- VP-level `or`: `λv[P₁(v) or P₂(v)]`. -/
def orVP : DynPred S E → DynPred S E → DynPred S E :=
  λ P₁ P₂ u => test (ddisj (P₁ u) (P₂ u))

/-- NP-level `and`: `λP(Q₁(P); Q₂(P))`. -/
def andNP : DynQuant S E → DynQuant S E → DynQuant S E :=
  λ Q₁ Q₂ P => dseq (Q₁ P) (Q₂ P)

/-- NP-level `or`: `λP[Q₁(P) or Q₂(P)]`. -/
def orNP : DynQuant S E → DynQuant S E → DynQuant S E :=
  λ Q₁ Q₂ P => test (ddisj (Q₁ P) (Q₂ P))

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
  dseq
    (detA u₁ (cn man) (tv adores (detA u₂ (cn woman))))
    (pro (RegisterStructure.val u₂) (tv abhors (pro (RegisterStructure.val u₁))))

/-- "Every¹ farmer who owns a² donkey beats it₂." — universal force from
`detEvery`, anaphoric `it₂` picking up the indefinite's dref:
`([u₁]; [farmer u₁]; [u₂]; [donkey u₂]; [u₁ owns u₂]) ⇒ [u₁ beats u₂]`. -/
def donkeySentence
    (farmer donkey_ : E → Prop) (owns beats : E → E → Prop) : Update S :=
  detEvery u₁
    (λ v => dseq (cn farmer v) (detA u₂ (cn donkey_) (λ w => test (atom2 owns v w))))
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

Given an `Update` `D` and postcondition `χ`, `wp D χ` characterizes the input
states from which `D` can transition to a state satisfying `χ`. The rules
WP_{[]}, WP_{;} and the TR extraction rules make truth-condition computation
compositional. -/

/-- Weakest precondition: `wp D χ i` iff some output `j` has `D i j ∧ χ j`. -/
def wp (D : Update S) (χ : Condition S) : Condition S :=
  λ i => ∃ j, D i j ∧ χ j

/-- WP of a test: `wp [C] χ = C ∧ χ`. -/
theorem wp_test (C : Condition S) (χ : Condition S) :
    wp (test C) χ = λ i => C i ∧ χ i := by
  ext i
  simp only [wp, test]
  constructor
  · rintro ⟨j, ⟨rfl, hC⟩, hχ⟩; exact ⟨hC, hχ⟩
  · rintro ⟨hC, hχ⟩; exact ⟨i, ⟨rfl, hC⟩, hχ⟩

/-- WP of sequencing (WP_{;}): the postcondition threads through. -/
theorem wp_seq (D₁ D₂ : Update S) (χ : Condition S) :
    wp (dseq D₁ D₂) χ = wp D₁ (wp D₂ χ) := by
  ext i
  simp only [wp, dseq, Relation.Comp]
  constructor
  · rintro ⟨j, ⟨h, hD₁, hD₂⟩, hχ⟩
    exact ⟨h, hD₁, j, hD₂, hχ⟩
  · rintro ⟨h, hD₁, j, hD₂, hχ⟩
    exact ⟨j, ⟨h, hD₁, hD₂⟩, hχ⟩

/-- WP of random assignment (the ∃ clause of WP_{[]}): introducing a dref
existentially quantifies over its values. -/
theorem wp_randomAssign [RegisterStructure R S E] (u : R) (χ : Condition S) :
    wp (RegisterStructure.randomAssign u) χ =
    λ i => ∃ e : E, χ (RegisterStructure.extend i u e) := by
  ext i
  simp only [wp, RegisterStructure.randomAssign]
  constructor
  · rintro ⟨j, ⟨e, rfl⟩, hχ⟩; exact ⟨e, hχ⟩
  · rintro ⟨e, hχ⟩; exact ⟨_, ⟨e, rfl⟩, hχ⟩

/-- WP of existential `Update`: `wp (∃u. D) χ = ∃e, wp D χ (extend i u e)`. -/
theorem wp_dexists [RegisterStructure R S E] (u : R) (D : Update S) (χ : Condition S) :
    wp (RegisterStructure.dexists u D) χ =
    λ i => ∃ e : E, wp D χ (RegisterStructure.extend i u e) := by
  simp only [RegisterStructure.dexists]
  rw [wp_seq, wp_randomAssign]

/-- Proposition 2: `wp(K, ⊤)` is the existential closure `∃j K(i)(j)` —
truth is satisfiability. Muskens's statement carries a closedness
antecedent (proper `K`); in the semantic formulation the identity is
definitional and unconditional. -/
theorem wp_true_eq_closure (D : Update S) :
    wp D (λ _ => True) = closure D := by
  ext i; simp only [wp, closure, and_true]

/-- DRT entailment: all premises true at `i` force the conclusion true at `i`. -/
def drtEntails (premises : List (Update S)) (conclusion : Update S) : Prop :=
  ∀ i, (∀ D ∈ premises, closure D i) → closure conclusion i

/-- Proposition 3: DRT entailment reduces to entailment of truth conditions
`wp(Kᵢ, ⊤)`. -/
theorem proposition_3 (premises : List (Update S)) (conclusion : Update S) :
    drtEntails premises conclusion ↔
    (∀ i, (∀ D ∈ premises, wp D (λ _ => True) i) → wp conclusion (λ _ => True) i) := by
  simp only [drtEntails, wp_true_eq_closure]

/-- DPL-style entailment: every output of `D₁` can be extended by `D₂`. -/
def dplEntails (D₁ D₂ : Update S) : Prop :=
  ∀ i j, D₁ i j → ∃ k, D₂ j k

/-- Corollary to Proposition 3: DPL entailment = validity of dynamic
implication. -/
theorem dpl_entailment_eq_dimpl_valid (D₁ D₂ : Update S) :
    dplEntails D₁ D₂ ↔ ∀ i, dimpl D₁ D₂ i := by
  simp only [dplEntails, dimpl]

/-! ### Truth-condition extraction rules -/

/-- TR of negation: `tr(not K) = ¬wp(K, ⊤)`. -/
theorem tr_neg_eq (D : Update S) :
    dneg D = λ i => ¬ wp D (λ _ => True) i := by
  simp only [wp_true_eq_closure]; rfl

/-- TR of disjunction: `tr(K₁ or K₂) = wp(K₁, ⊤) ∨ wp(K₂, ⊤)` — the
existential distributes over disjunction. -/
theorem tr_disj_eq (D₁ D₂ : Update S) :
    ddisj D₁ D₂ = λ i => wp D₁ (λ _ => True) i ∨ wp D₂ (λ _ => True) i := by
  ext i
  simp only [ddisj, wp, and_true]
  constructor
  · rintro ⟨k, hk⟩
    cases hk with
    | inl h => left; exact ⟨k, h⟩
    | inr h => right; exact ⟨k, h⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨k, Or.inl hk⟩
    · exact ⟨k, Or.inr hk⟩

/-- TR of implication: `tr(K₁ ⇒ K₂) = ¬wp(K₁, ¬wp(K₂, ⊤))` — no way to
satisfy the antecedent without satisfying the consequent. -/
theorem tr_impl_eq (D₁ D₂ : Update S) :
    dimpl D₁ D₂ = λ i => ¬ wp D₁ (λ j => ¬ wp D₂ (λ _ => True) j) i := by
  ext i
  simp only [dimpl, wp, and_true]
  constructor
  · intro h ⟨j, hD₁, hNot⟩
    exact hNot (h j hD₁)
  · intro h j hD₁
    by_contra hNot
    exact h ⟨j, hD₁, hNot⟩

/-! ### Semantic properness -/

/-- Semantic counterpart of [muskens-1996]'s properness (§III.5: a proper
DRS contains no free referents): satisfiability doesn't depend on the input
state. Proposition 1 connects the two — K is proper iff `wp(K, ⊤)` is a
closed formula. The syntactic notion is strictly finer: Muskens notes a
proper box and a non-proper box may have the same semantic value (his
(45) vs (47)), which is why this semantic version is only a counterpart,
not a reformulation. -/
def isProper (D : Update S) : Prop :=
  ∀ i₁ i₂, closure D i₁ ↔ closure D i₂

/-- Proper DRSes have state-independent weakest preconditions. -/
theorem proper_wp_uniform (D : Update S) (h : isProper D) :
    ∀ i₁ i₂, wp D (λ _ => True) i₁ ↔ wp D (λ _ => True) i₂ := by
  simp only [wp_true_eq_closure]; exact h

/-! ### Cylindric-algebra bridges

CDRT's dref introduction and dref equality are cylindric-algebra
operations under `closure` ([henkin-monk-tarski-1971]) — the CDRT face of
the correspondence whose DPL face lives in
`Studies/GroenendijkStokhof1991.lean`. -/

section CylindricAlgebra

open Core.CylindricAlgebra
open CDRT

/-- Discourse referent introduction under closure = cylindrification.

`closure(new n ;; φ) = cₙ(closure(φ))`: introducing dref `n`
then continuing with `φ` equals cylindrifying `φ` at `n`. -/
theorem cdrt_new_seq_eq_cylindrify {E : Type*} (n : Nat) (φ : DProp E) :
    closure (DProp.new n ;; φ) =
    cylindrify n (closure φ) := by
  ext g; simp only [closure, DProp.seq, dseq, Relation.Comp, DProp.new, cylindrify]
  constructor
  · rintro ⟨o, k, ⟨e, rfl⟩, hφ⟩
    exact ⟨e, o, by convert hφ using 2; simp [Function.update_apply]⟩
  · rintro ⟨e, o, hφ⟩
    exact ⟨o, _, ⟨e, rfl⟩, by convert hφ using 2; simp [Function.update_apply]⟩

/-- CDRT equality condition on drefs = diagonal element. -/
theorem cdrt_eq_dref_eq_diagonal {E : Type*} (i j : Nat) :
    eq' (dref i : Dref (State E) E) (dref j) = @diagonal E i j := by
  ext g; simp only [eq', dref, diagonal]

end CylindricAlgebra

/-! ### fn. 4: the equivalence is a fact about total assignments

[muskens-1996]'s fn. 4 scopes the SEM ≡ verification equivalence
(`DRS.toRel_iff_realize`) to total assignments, contrasting them with
[kamp-reyle-1993]'s partial embeddings, where re-declared referents keep
their values. A DRS that re-declares a referent separates the two: on
`[ | [x | man x] ⇒ [x | mortal x]]` the agree-off-universe semantics may
reassign the re-declared `x`, so it only demands that some mortal exist,
while the persistence rendering (`DRS.toRelAt`, `DRS/Based.lean`) forces
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
def fn4Lang : Language := ⟨fun _ => Empty, Fn4Rel⟩

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
    | 1, .man => fun args => args 0 = 0
    | 1, .mortal => fun args => args 0 = 1

/-- The witness is proper: its referential presuppositions are satisfied. -/
theorem fn4_isProper : fn4.IsProper := by
  simp [DRS.IsProper, fn4, fn4Ante, fn4Cons]

/-- The witness is not reuse-free: the consequent re-declares `0`. -/
theorem fn4_not_reuseFreeAt : ¬ DRS.ReuseFreeAt ∅ fn4 := by
  simp [fn4, fn4Ante, fn4Cons]

/-- Flat truth: every input verifies the witness — the re-declared referent
may be reassigned, so it suffices that some mortal exist. -/
theorem fn4_trueRel (g : ℕ → Fin 2) : DRS.trueRel fn4 g := by
  refine ⟨g, fun x _ => rfl, ?_, trivial⟩
  rw [Condition.holds_imp]
  intro g₁ _
  refine ⟨Function.update g₁ 0 1,
    fun x hx => by rw [Function.update_apply, if_neg (by simpa [fn4Cons] using hx)], ?_, trivial⟩
  show Function.update g₁ 0 1 0 = 1
  simp

/-- Based falsity: persistence keeps the re-declared referent's man value, so
no output verifies the witness in a model with a non-mortal man. -/
theorem fn4_not_toRelAt (g : ℕ → Fin 2) : ¬ ∃ g', DRS.toRelAt ∅ fn4 g g' := by
  rintro ⟨g', hg'⟩
  have himp : Condition.holdsAt (∅ ∪ ∅) (.imp fn4Ante fn4Cons) g' := hg'.2.1
  have hman : DRS.toRelAt (∅ ∪ ∅) fn4Ante g' (fun _ => 0) :=
    ⟨fun x hx => absurd hx (by simp), rfl, trivial⟩
  obtain ⟨g₂, heq, hmortal, -⟩ := himp _ hman
  have h0 : g₂ 0 = 0 := heq (by simp [fn4Ante])
  have h1 : g₂ 0 = 1 := hmortal
  exact absurd (h0.symm.trans h1) (by decide)

/-- The reconciliation `DRS.trueRel_iff_toRelAt` fails on the witness:
flat-true, based-false. -/
theorem fn4_diverges (g : ℕ → Fin 2) :
    ¬ (DRS.trueRel fn4 g ↔ ∃ g', DRS.toRelAt ∅ fn4 g g') :=
  fun h => fn4_not_toRelAt g (h.mp (fn4_trueRel g))

end Fn4

end Muskens1996
