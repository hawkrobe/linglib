import Linglib.Core.Question.Basic
import Linglib.Core.Question.Hamblin
import Linglib.Theories.Semantics.Questions.Resolution
import Linglib.Theories.Semantics.Questions.Exhaustivity

/-!
# @cite{karttunen-1977}: Syntax and Semantics of Questions

Single-paper formalisation of @cite{karttunen-1977}, "Syntax and
Semantics of Questions", *Linguistics and Philosophy* 1(1):3–44.
The paper introduces the **set-of-true-alternatives** denotation for
questions: a question denotes the set of propositions that are true
and constitute an answer.

## Substrate identification

@cite{karttunen-1977}'s denotation is exactly
`Exhaustivity.trueAlternatives Q w` — the set of `Q`-alternatives
true at `w`. The "complete answer" Karttunen ascribes via the
meaning postulate (§2.4 fn 11) for `know` is exactly
`Exhaustivity.weakAnswer Q w` — the conjunction (intersection) of
all true alternatives.

The substrate joints (`alt_polar_iff`, `Resolves_polar_iff`,
`trueAlternatives_polar_iff_of_nontrivial`, `weakAnswer_polar_of_pos`,
`weakAnswer_polar_of_neg`) live in `Core.Question.Hamblin`,
`Resolution.lean`, and `Exhaustivity.lean`. This file uses them to
prove Karttunen's stated observations directly.

## Outline

* **karttunenDenotation** (§2.1, §2.5): the set of true alternatives.
* **karttunenCompleteAnswer** (§2.4 fn 11): the conjunction of true alts.
* **§2.3 yes/no observation**: `whether p` denotes `{p}` or `{pᶜ}`
  depending on which is true.
* **§2.4 know-meaning postulate**: a state σ supports every true alt
  iff σ ⊆ karttunenCompleteAnswer Q w.
* **§2.5 footnote 13**: the existential presupposition for wh-questions
  is *not* derived in this paper (deferred to @cite{dayal-1996}).

## What this file does NOT replicate

Karttunen's syntactic apparatus (proto-questions, the WH-Quantification
rule, the AQ rule, the YNQ rule) is **encoding machinery**, not
empirical content. We formalise the **denotational consequences** of
those rules. The Hamblin-shaped constructors `Question.polar` and
`Question.which` from `Core.Question.Hamblin` already produce the
right semantic objects.

The §2.10 multiple-wh ambiguity (Baker's observation) and §2.12
quantifier-scope asymmetry require lifted-type machinery and are
deferred to a future Karttunen-1977-extended file once the lifting
substrate is in place.
-/

namespace Phenomena.Questions.Studies.Karttunen1977

open Core Core.Question Semantics.Questions.Resolution
open Semantics.Questions.Exhaustivity

variable {W : Type*}

/-! ### Karttunen's denotation (§2.1, §2.5) -/

/-- @cite{karttunen-1977} §2.1: the **Karttunen denotation** of
    question `Q` at world `w` is the set of true alternatives.
    Definitionally equal to `Exhaustivity.trueAlternatives`. -/
def karttunenDenotation (Q : Question W) (w : W) : Set (Set W) :=
  trueAlternatives Q w

@[simp] theorem karttunenDenotation_eq_trueAlternatives
    (Q : Question W) (w : W) :
    karttunenDenotation Q w = trueAlternatives Q w := rfl

/-! ### The complete-answer view (§2.4 footnote 11) -/

/-- @cite{karttunen-1977} §2.4 fn 11: the **complete answer** to `Q`
    at `w` — the proposition the agent must believe to count as
    knowing `Q`. Equal to `weakAnswer Q w`. -/
def karttunenCompleteAnswer (Q : Question W) (w : W) : Set W :=
  weakAnswer Q w

@[simp] theorem karttunenCompleteAnswer_eq_weakAnswer
    (Q : Question W) (w : W) :
    karttunenCompleteAnswer Q w = weakAnswer Q w := rfl

/-- The complete answer at `w` always contains `w` itself: every true
    alternative contains `w` by definition. -/
theorem mem_karttunenCompleteAnswer_self (Q : Question W) (w : W) :
    w ∈ karttunenCompleteAnswer Q w := by
  intro p _ hwp; exact hwp

/-- The complete answer is the intersection of the Karttunen
    denotation. -/
theorem karttunenCompleteAnswer_eq_sInter (Q : Question W) (w : W) :
    karttunenCompleteAnswer Q w = ⋂₀ (karttunenDenotation Q w) := by
  ext v; constructor
  · intro h p ⟨hp, hwp⟩; exact h p hp hwp
  · intro h p hp hwp; exact h p ⟨hp, hwp⟩

/-! ### §2.3 yes/no observation

`whether Mary cooks` denotes `{[Mary cooks]}` if Mary cooks, else
`{[Mary doesn't cook]}`. Falls out of the substrate
`trueAlternatives_polar_iff_of_nontrivial` joint. -/

/-- @cite{karttunen-1977} §2.3: at a `p`-true world, the polar
    question denotes `{p}`. -/
theorem karttunen_polar_pos (p : Set W) (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    (w : W) (hwp : w ∈ p) :
    karttunenDenotation (Question.polar p) w = {p} := by
  ext q
  rw [karttunenDenotation_eq_trueAlternatives,
      trueAlternatives_polar_iff_of_nontrivial p hne hnu]
  simp [hwp]

/-- @cite{karttunen-1977} §2.3: at a `p`-false world, the polar
    question denotes `{pᶜ}`. -/
theorem karttunen_polar_neg (p : Set W) (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    (w : W) (hwp : w ∉ p) :
    karttunenDenotation (Question.polar p) w = {pᶜ} := by
  ext q
  rw [karttunenDenotation_eq_trueAlternatives,
      trueAlternatives_polar_iff_of_nontrivial p hne hnu]
  simp [hwp]

/-- §2.4 corollary: the complete answer to `whether p` at a `p`-true
    world is just `p`. -/
theorem karttunenCompleteAnswer_polar_pos {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∈ p) :
    karttunenCompleteAnswer (Question.polar p) w = p := by
  rw [karttunenCompleteAnswer_eq_weakAnswer, weakAnswer_polar_of_pos hne hnu hwp]

/-- §2.4 corollary: the complete answer to `whether p` at a `p`-false
    world is `pᶜ`. -/
theorem karttunenCompleteAnswer_polar_neg {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∉ p) :
    karttunenCompleteAnswer (Question.polar p) w = pᶜ := by
  rw [karttunenCompleteAnswer_eq_weakAnswer, weakAnswer_polar_of_neg hne hnu hwp]

/-! ### §2.4 know-meaning postulate

@cite{karttunen-1977} §2.4 footnote 11 provides

    know'_{IV/Q}(x, P) ↔ ∀p [P(p) → know'_t(x, p)]

— knowing a question means knowing each of its true alternatives.
The substrate-level invariant: a state σ supports every true
alternative of `Q` at `w` iff σ ⊆ karttunenCompleteAnswer Q w. -/

theorem subset_karttunenCompleteAnswer_iff (σ : Set W) (Q : Question W) (w : W) :
    σ ⊆ karttunenCompleteAnswer Q w ↔
      ∀ p ∈ alt Q, w ∈ p → σ ⊆ p := by
  constructor
  · intro h p hp hwp v hv
    exact h hv p hp hwp
  · intro h v hv p hp hwp
    exact h p hp hwp hv

/-! ### §2.5 fn 13: empty-denotation observation for wh-questions

When no `e ∈ D` satisfies `P e` at `w`, every Karttunen alternative is
empty (paper p. 20 fn 13). The existential presupposition is *not*
captured at this stage; @cite{dayal-1996} adds it. -/

theorem karttunen_which_no_witness {E : Type*} (D : Set E) (P : E → Set W) (w : W)
    (h : ∀ e ∈ D, w ∉ P e) :
    ∀ q ∈ karttunenDenotation (Question.which D P) w, q = ∅ := by
  intro q hq
  obtain ⟨hq, hwq⟩ := hq
  have hq_mem : q ∈ Question.which D P := alt_subset_props _ hq
  rcases Question.mem_which.mp hq_mem with hempty | ⟨e, heD, hqe⟩
  · exact hempty
  · exact absurd (hqe hwq) (h e heD)

end Phenomena.Questions.Studies.Karttunen1977
