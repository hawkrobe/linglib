/-!
# Exhaustivity Presuppositions for Questions @cite{xiang-2022}

Formalizes Dayal's Exhaustivity Presupposition (EP, definition 90) and Xiang's
Relativized Exhaustivity (RelExh, definition 91) from:

Xiang, Yimei (2022). Relativized Exhaustivity: mention-some and uniqueness.
*Natural Language Semantics* 30:311–362.

## Key Definitions

- `dayalEP`: Dayal (1996)'s Exhaustivity Presupposition — the question
  presupposes that there exists a strongest true answer (one whose proposition
  entails all other true answers' propositions).
- `relExh`: Xiang's Relativized Exhaustivity — EP is evaluated relative to
  *singleton* modal bases. For each accessible world v, restrict the modal base
  to {v} and check EP there. This weakens EP just enough to license
  mention-some for ability-*can* questions while preserving mention-all for
  non-modal and other modal questions.
- `foQDen`: First-order question denotation (◇φ_x interpretation) — the
  building block for can-questions where the wh-trace scopes below the modal.

## Design

All definitions are polymorphic in `W` (worlds) and `P` (individuals/answers),
taking explicit `List W` universe parameters for decidable computation via
`native_decide`. No imports beyond basic Lean — this is pure theory.
-/

namespace Theories.Semantics.Questions.Exhaustivity

/-! ### Propositional Entailment -/

/-- Propositional entailment as Bool: `p ⊆ q` over a finite universe.
`propEntails p q worlds = true` iff every world where `p` holds also has `q`. -/
def propEntails {W : Type _} (p q : W → Bool) (worlds : List W) : Bool :=
  worlds.all (λ v => !p v || q v)

/-! ### True Answers -/

/-- The answers whose denotation is true at world `w` under modal base `mb`. -/
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

/-! ### Dayal's Exhaustivity Presupposition -/

/-- Dayal's Exhaustivity Presupposition (Dayal 1996; Xiang 2022, definition 90).

EP holds at `w` iff there exists a true answer α whose proposition entails the
proposition of every other true answer β:
  ∃α ∈ True(w). ∀β ∈ True(w). ⟦α⟧ ⊆ ⟦β⟧

When EP holds, α is the *strongest true answer* — the exhaustive answer to the
question. When EP fails, no single answer subsumes all others, so the question
has no well-defined exhaustive reading. -/
def dayalEP {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W) : Bool :=
  let trueAt := trueAnswers qden mb answers w
  trueAt.any (λ α =>
    trueAt.all (λ β =>
      propEntails (qden mb α) (qden mb β) worlds))

/-! ### Relativized Exhaustivity -/

/-- Relativized Exhaustivity (Xiang 2022, definition 91).

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
