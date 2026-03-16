import Linglib.Theories.Semantics.Questions.Denotation.Hamblin

/-!
# Exhaustivity and Answerhood for Questions @cite{dayal-1996} @cite{xiang-2022}

Formalizes two answerhood notions from @cite{dayal-1996} with increasing
strength:

1. **Dayal's Ans(Q) with EP** (@cite{dayal-1996}): the unique strongest true answer
2. **Xiang's Relativized Exhaustivity** (@cite{xiang-2022}): EP relative to
   singleton modal bases

## Key Definitions

- `trueAnswers`: @cite{karttunen-1977}-style answerhood — all true answers
  (no maximality). This is Dayal's first version of Ans(Q) (p. 87, eq. 47;
  restated as eq. 47a on p. 116):
  `Ans(Q) = λp [p ∈ Q ∧ ᵛp]`.
- `dayalAns`: @cite{dayal-1996}'s Ans(Q) — returns the strongest true answer
  (if EP holds), implementing the full revised Ans(Q) (p. 116, eq. 47b):
  `Ans(Q) = ιp[p∈Q ∧ ᵛp ∧ ∀p'∈Q [ᵛp' → p ⊆ p']]`.
- `dayalEP`: @cite{dayal-1996}'s Exhaustivity Presupposition — defined as
  `(dayalAns ...).isSome` so that the equivalence with the existence of a
  strongest answer is true by construction.
  Verified as definition 90 in @cite{xiang-2022}.
- `dayalAnsProposition`: extracts the proposition (W → Bool) from `dayalAns`.
- `relExh`: @cite{xiang-2022}'s Relativized Exhaustivity.
  Verified as definition 91 in @cite{xiang-2022}.
- `toHamblinDen`: converts the explicit question representation to a
  `Hamblin.QuestionDen`, bridging the parametric interface used here with
  the Hamblin denotation type from `Denotation/Hamblin.lean`.

## Key Theorems

- `dayalAns_implies_ep` / `ep_implies_dayalAns`: `dayalAns` returns `some` iff
  `dayalEP` holds. Trivial by construction (`dayalEP := (dayalAns).isSome`).
- `dayalAns_eq_conjunction`: the strongest answer's proposition is pointwise
  equivalent to the conjunction of all true answers — connecting Dayal's Ans(Q)
  to @cite{karttunen-1977}'s complete answer (`Answerhood.karttunenCompleteAnswer`).
- `maximality_strictly_strengthens`: having true answers does NOT imply EP
  (concrete counterexample with incomparable propositions).

## Design

All definitions are polymorphic in `W` (worlds) and `P` (individuals/answers),
taking explicit `List W` universe parameters for decidable computation via
`native_decide`.

Fox 2018 exhaustification machinery (Exh, IE, MC-sets, foxAns, foxPartition)
is in the companion file `FoxExhaustification.lean`.
-/

namespace Theories.Semantics.Questions.Exhaustivity

/-! ### Propositional Entailment -/

/-- Propositional entailment as Bool: `p ⊆ q` over a finite universe.
`propEntails p q worlds = true` iff every world where `p` holds also has `q`. -/
def propEntails {W : Type _} (p q : W → Bool) (worlds : List W) : Bool :=
  worlds.all (λ v => !p v || q v)

/-! ### True Answers (@cite{karttunen-1977}) -/

/-- The answers whose denotation is true at world `w` under modal base `mb`.

This is @cite{karttunen-1977}-style answerhood — the set of all true
answer-propositions with no maximality requirement. Corresponds to Dayal's
first version of Ans(Q) (p. 87, eq. 47 in @cite{dayal-1996}; restated as
eq. 47a on p. 116), before the maximality revision to `dayalAns`
(p. 116, eq. 47b). -/
def trueAnswers {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (w : W) : List P :=
  answers.filter (λ α => qden mb α w)

/-! ### First-Order Question Denotation -/

/-- First-order question denotation: ◇φ_x interpretation.

`foQDen pred mb α w = true` iff there exists an accessible world `v ∈ mb(w)`
where `pred(v, α)` holds. This is the denotation for can-questions where the
wh-trace takes scope below the modal:
  ⟦who can VP⟧(mb)(α)(w) = ∃v ∈ mb(w). VP(v)(α) -/
def foQDen {W P : Type _} (pred : W → P → Bool)
    (mb : W → List W) (α : P) (w : W) : Bool :=
  (mb w).any (λ v => pred v α)

/-! ### Dayal's Ans(Q) -/

/-- Dayal's Ans(Q) operator (@cite{dayal-1996}, p. 116, eq. 47b): returns the
strongest true answer when EP holds.

`Ans(Q) = ιp[p∈Q ∧ ᵛp ∧ ∀p'∈Q [ᵛp' → p ⊆ p']]`

Returns `some α` where α is the strongest true answer (its proposition entails
every other true answer's proposition), or `none` if EP fails. -/
def dayalAns {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W) : Option P :=
  (trueAnswers qden mb answers w).find? (λ α =>
    (trueAnswers qden mb answers w).all (λ β =>
      propEntails (qden mb α) (qden mb β) worlds))

/-! ### Dayal's Exhaustivity Presupposition -/

/-- Dayal's Exhaustivity Presupposition (@cite{dayal-1996}, p. 116, eq. 47b).
Verified as definition 90 in @cite{xiang-2022}.

EP holds at `w` iff `dayalAns` returns a strongest true answer:
  ∃α ∈ True(w). ∀β ∈ True(w). ⟦α⟧ ⊆ ⟦β⟧

Defined as `(dayalAns ...).isSome` so that the equivalence between EP and the
existence of a strongest answer is true by construction, eliminating the need
for separate `dayalAns_implies_ep` / `ep_implies_dayalAns` proofs. -/
def dayalEP {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W) : Bool :=
  (dayalAns qden mb answers worlds w).isSome

/-- Extract the proposition (W → Bool) from `dayalAns`. When EP holds, this
is the strongest true proposition — the one that entails all other true
answer-propositions. This is what left-peripheral semantics refers to as
"Ans(Q)" in contexts like `◇¬know(x, Ans(Q))`. -/
def dayalAnsProposition {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W) :
    Option (W → Bool) :=
  (dayalAns qden mb answers worlds w).map (qden mb)

/-! ### Theorems: dayalAns ↔ dayalEP -/

/-- If `dayalAns` returns an answer, then `dayalEP` holds.
Trivial by construction: `dayalEP := (dayalAns).isSome`. -/
theorem dayalAns_implies_ep {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W)
    (α : P) (h : dayalAns qden mb answers worlds w = some α) :
    dayalEP qden mb answers worlds w = true := by
  simp only [dayalEP, h, Option.isSome_some]

/-- If `dayalEP` holds, then `dayalAns` returns some answer.
Trivial by construction: `dayalEP := (dayalAns).isSome`. -/
theorem ep_implies_dayalAns {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W)
    (h : dayalEP qden mb answers worlds w = true) :
    (dayalAns qden mb answers worlds w).isSome = true :=
  h

/-- The strongest true answer's proposition is pointwise equivalent to the
conjunction of all true answers' propositions.

This connects Dayal's Ans(Q) to @cite{karttunen-1977}'s complete answer
(`Answerhood.karttunenCompleteAnswer` in `Answerhood.lean`): when EP holds,
the strongest true proposition is exactly the conjunction (intersection)
of all true propositions over the finite world set.

Forward: α entails every β ∈ True(w), so if α holds at v, all β hold at v.
Backward: α ∈ True(w), so if all β hold at v, α holds at v. -/
theorem dayalAns_eq_conjunction {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W)
    (α : P) (hα : dayalAns qden mb answers worlds w = some α) :
    ∀ v ∈ worlds,
      qden mb α v =
        (trueAnswers qden mb answers w).all (λ β => qden mb β v) := by
  simp only [dayalAns] at hα
  have hPred := List.find?_some hα
  have hMem := List.mem_of_find?_eq_some hα
  rw [List.all_eq_true] at hPred
  intro v hv
  cases hαv : qden mb α v
  · -- false: .all must be false since α ∈ trueAnswers and qden mb α v = false
    apply Eq.symm; apply eq_false_of_ne_true
    intro hall; rw [List.all_eq_true] at hall
    exact absurd (hall α hMem) (by simp [hαv])
  · -- true: .all must be true since α entails every β
    apply Eq.symm; rw [List.all_eq_true]
    intro β hβ
    have hEnt := hPred β hβ
    simp only [propEntails, List.all_eq_true] at hEnt
    have := hEnt v hv
    simp [hαv] at this
    exact this

/-! ### Maximality Strictly Strengthens Simple Answerhood

Dayal's maximality clause (EP) is strictly stronger than simple
@cite{karttunen-1977}-style answerhood. Having true answers does NOT imply EP:
when two answers have incomparable propositions (neither entails the other),
both can be true but no single answer is strongest.

This is the core motivation for Dayal's revision from simple Ans(Q)
(p. 87, eq. 47 in @cite{dayal-1996}; restated as eq. 47a on p. 116)
to maximal Ans(Q) (p. 116, eq. 47b). -/

/-- Concrete counterexample: two answers with incomparable propositions.
Answer 0 true at worlds {0,1}, answer 1 true at worlds {0,2}.
At world 0 both are true (trueAnswers nonempty), but neither entails the
other ({0,1} ⊄ {0,2} and {0,2} ⊄ {0,1}), so EP fails. -/
theorem maximality_strictly_strengthens :
    let worlds : List (Fin 3) := [0, 1, 2]
    let answers : List (Fin 2) := [0, 1]
    let mb : Fin 3 → List (Fin 3) := λ _ => [0, 1, 2]
    let qden : (Fin 3 → List (Fin 3)) → Fin 2 → Fin 3 → Bool :=
      λ _ ans w => match ans, w with
        | ⟨0, _⟩, ⟨0, _⟩ => true  -- answer 0 true at world 0
        | ⟨0, _⟩, ⟨1, _⟩ => true  -- answer 0 true at world 1
        | ⟨1, _⟩, ⟨0, _⟩ => true  -- answer 1 true at world 0
        | ⟨1, _⟩, ⟨2, _⟩ => true  -- answer 1 true at world 2
        | _, _ => false
    -- Both answers true at world 0 (trueAnswers nonempty)
    (trueAnswers qden mb answers 0).length > 0 ∧
    -- But EP fails (no strongest answer — incomparable propositions)
    dayalEP qden mb answers worlds 0 = false := by
  native_decide

/-! ### Hamblin Denotation Conversion -/

/-- Convert a question given explicitly (answer function + answer list) to a
`Hamblin.QuestionDen` — a set-of-propositions representation.

The resulting Hamblin denotation recognizes a proposition `p` as an answer iff
`p` agrees pointwise (on `worlds`) with some `qden mb α` for α ∈ answers.
This bridges the parametric interface used throughout this file with the
`Hamblin.QuestionDen` type from `Denotation/Hamblin.lean`. -/
def toHamblinDen {W P : Type _} [BEq W]
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) :
    Semantics.Questions.Hamblin.QuestionDen W :=
  Semantics.Questions.Hamblin.fromAlternatives (answers.map (qden mb)) worlds

/-- `dayalEP` is a presupposition on the Hamblin denotation: it holds iff the
set of true propositions in the Hamblin denotation has a unique minimum
(strongest element) under propositional entailment. -/
theorem ep_is_hamblin_presupposition {W P : Type _} [BEq W]
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W) :
    dayalEP qden mb answers worlds w = true →
    ∃ (p : W → Bool),
      Semantics.Questions.Hamblin.isAnswer
        (toHamblinDen qden mb answers worlds) p = true := by
  intro hEP
  -- Extract α from dayalAns being some
  have ⟨α, hα⟩ : ∃ α, dayalAns qden mb answers worlds w = some α := by
    cases h : dayalAns qden mb answers worlds w with
    | none => simp [dayalEP, h] at hEP
    | some a => exact ⟨a, rfl⟩
  -- α ∈ trueAnswers (from find? returning some)
  have hMem : α ∈ trueAnswers qden mb answers w := by
    simp only [dayalAns] at hα
    exact List.mem_of_find?_eq_some hα
  -- trueAnswers filters answers, so α ∈ answers
  have hAns : α ∈ answers := by
    simp only [trueAnswers] at hMem
    exact (List.mem_filter.mp hMem).1
  -- Witness: qden mb α agrees with itself on all worlds
  exact ⟨qden mb α, by
    simp only [Semantics.Questions.Hamblin.isAnswer, toHamblinDen,
      Semantics.Questions.Hamblin.fromAlternatives]
    rw [List.any_eq_true]
    exact ⟨qden mb α, List.mem_map.mpr ⟨α, hAns, rfl⟩, by
      rw [List.all_eq_true]; intro v _; exact beq_self_eq_true _⟩⟩

/-! ### Relativized Exhaustivity -/

/-- Relativized Exhaustivity (@cite{xiang-2022}).
Verified as definition 91 in @cite{xiang-2022}.

RelExh holds at `w` iff for every singleton modal base {v} where v ∈ mb(w),
if {v} makes some answer relevant (both true under {v} and true under the full
mb), then EP holds for {v}:
  ∀v ∈ mb(w). [∃α. qden({v})(α)(w) ∧ qden(mb)(α)(w)] → EP({v})(w)

The key insight: under a singleton modal base {v}, each individual α either
determinately can or determinately cannot VP at v. So for each v, there IS a
strongest true answer (trivially — the answers don't overlap when the modal
base is a singleton). This means RelExh passes for ability-*can* questions
even when the full EP fails due to overlapping answer propositions. -/
def relExh {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W) : Bool :=
  (mb w).all (λ v =>
    let singletonMB : W → List W := λ _ => [v]
    let hasRelevant := answers.any (λ α =>
      qden singletonMB α w && qden mb α w)
    !hasRelevant || dayalEP qden singletonMB answers worlds w)

end Theories.Semantics.Questions.Exhaustivity
