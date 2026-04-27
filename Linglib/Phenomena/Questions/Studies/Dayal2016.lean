import Linglib.Core.Question.Basic
import Linglib.Core.Question.Hamblin
import Linglib.Theories.Semantics.Questions.Exhaustivity
import Linglib.Theories.Semantics.Questions.Resolution

/-!
# @cite{dayal-2016}: Questions
@cite{dayal-1994} @cite{dayal-1996} @cite{karttunen-1977} @cite{groenendijk-stokhof-1984}

Single-paper formalisation of the Dayal answerhood operator
**Ans-D** and the **existential presupposition** (EP) from
@cite{dayal-2016}, *Questions* (Oxford Surveys in Semantics and
Pragmatics 4), Chapter 2 §2.2–§2.3. Builds on Dayal's earlier work
(@cite{dayal-1994}, @cite{dayal-1996}).

## Substrate identification

@cite{dayal-2016} (48a) defines

    Ans-D_W (Q) = λw ιp [p_w ∧ p ∈ Q ∧ ∀p' [[p'_w ∧ p' ∈ Q] → p ⊆ p']]

— the maximally-informative true alternative, with `ι` (iota) the
definite-description operator. The iota's definedness condition is
the **existential presupposition**: a unique strongest true answer
must exist.

This matches `Exhaustivity.IsStrongestTrueAnswer Q w p` exactly:
`p ∈ alt Q ∧ w ∈ p ∧ ∀ q ∈ alt Q, w ∈ q → p ⊆ q`. The substrate's
`dayalAns Q w : Option (Set W)` returns `some` precisely when EP
holds (`IsExhaustivelyResolvable`).

## What this file proves

* **Identification**: `AnsD = dayalAns`, `AnsHS` (strong-exhaustivity
  bridge of (48b)) is the substrate's `IsExhaustivelyResolvable`-based
  per-world equivalence.
* **§2.2.2 architectural move**: Dayal separates the truth requirement
  from question denotation. Captured by the substrate's
  `Question`-vs-`trueAlternatives` split.
* **§2.3.4 EP empirical predictions**:
  - **(57a)**: cancelling EP with *no one* leaves the question itself
    well-formed (the EP fails *post hoc*; the question is felicitous).
    Captured by `IsExhaustivelyResolvable_polar_of_nontrivial`: polar
    questions never have EP failure.
  - **(57b)**: a singular wh-question with multiple incomparable true
    alternatives has no maximally informative answer. EP fails.
* **Polar EP**: a non-trivial polar question always satisfies EP.

## What this file does NOT replicate

* **Number sensitivity** (§2.3.1–§2.3.3) requires plural / atomic
  individuals (`Sharvy 1980`/`Link 1983` join semilattice). Deferred
  to a follow-up that uses `Phenomena.Plurality` substrate.
* **Scope marking** (§2.2.2 ex. 33–37) is a syntax-side phenomenon
  (German *was*-construction, Hindi-Urdu *kyaa*); deferred to the
  Hindi-Urdu fragment + Dayal-2025 study.
* **Beck-Rullmann's `Ans-BR`** (§2.3.3 ex. 52) — alternative proposal
  rejected by Dayal; not formalised.
-/

namespace Phenomena.Questions.Studies.Dayal2016

open Core Core.Question Semantics.Questions.Resolution
open Semantics.Questions.Exhaustivity

variable {W : Type*}

/-! ### Substrate identification -/

/-- @cite{dayal-2016} (48a): the **maximally informative true answer**,
    when defined. Identified with the substrate's `dayalAns`. -/
noncomputable def AnsD (Q : Question W) (w : W) : Option (Set W) :=
  dayalAns Q w

@[simp] theorem ansD_eq_dayalAns (Q : Question W) (w : W) :
    AnsD Q w = dayalAns Q w := rfl

/-- @cite{dayal-2016} (48b): **strong-exhaustivity bridge** — two
    worlds map to the same maximally-informative true answer. -/
def AnsDHStrong (Q : Question W) (w w' : W) : Prop :=
  AnsD Q w = AnsD Q w'

/-- The **existential presupposition** of @cite{dayal-2016} (the iota
    definedness condition of (48a)) — at world `w`, the question `Q`
    has a unique strongest true alternative. -/
def IsEPSatisfied (Q : Question W) (w : W) : Prop :=
  IsExhaustivelyResolvable Q w

@[simp] theorem isEPSatisfied_iff (Q : Question W) (w : W) :
    IsEPSatisfied Q w ↔ IsExhaustivelyResolvable Q w := Iff.rfl

theorem ansD_isSome_iff_EP (Q : Question W) (w : W) :
    (AnsD Q w).isSome ↔ IsEPSatisfied Q w :=
  dayalAns_isSome_iff_EP Q w

/-! ### §2.2.2 architectural move

@cite{dayal-2016} §2.2.2: Dayal (following @cite{dayal-1994}) separates
the truth requirement from the question denotation. Karttunen 1977
hard-wires truth into the question content; G&S 1984 inherits the
truth requirement at the partition level. Dayal's move is to keep
the denotation Hamblin-style (a set of propositions, no truth filter)
and put the truth requirement in the **answerhood operator** (the
λw, ι, ⊆ machinery of Ans-D).

The substrate captures this by keeping `alt Q` truth-independent and
defining `dayalAns` (= Ans-D) as a separate operation that takes the
world `w` as a parameter. The Karttunen denotation (the file
`Karttunen1977.lean`) is then `trueAlternatives Q w` — a *derived*
view, not the question itself. -/

/-- The Karttunen-style "set of true alternatives" is recovered from
    the Dayal-style architecture by applying the truth filter to
    `alt Q`. The substrate exposes this directly via `trueAlternatives`. -/
theorem karttunen_view_eq_trueAlternatives (Q : Question W) (w : W) :
    trueAlternatives Q w = {p ∈ alt Q | w ∈ p} := rfl

/-! ### Polar questions: EP always satisfied -/

/-- A non-trivial polar question never has EP failure: at any world,
    exactly one of `p`, `pᶜ` is true, and that one is trivially the
    maximally-informative true answer. -/
theorem polar_isEPSatisfied {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) (w : W) :
    IsEPSatisfied (Question.polar p) w :=
  isExhaustivelyResolvable_polar_of_nontrivial hne hnu w

/-- For a `p`-true world, `p` itself is a strongest true answer. -/
theorem isStrongestTrueAnswer_polar_pos {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∈ p) :
    IsStrongestTrueAnswer (Question.polar p) w p :=
  isStrongestTrueAnswer_polar_of_pos hne hnu hwp

/-- For a `p`-false world, `pᶜ` is a strongest true answer. -/
theorem isStrongestTrueAnswer_polar_neg {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) {w : W} (hwp : w ∉ p) :
    IsStrongestTrueAnswer (Question.polar p) w pᶜ :=
  isStrongestTrueAnswer_polar_of_neg hne hnu hwp

/-! ### §2.3.4 EP empirical predictions

The empirical content is in the **failure cases** for EP. We capture
two: (a) wh-questions with no true witness; (b) singular-wh questions
with multiple incomparable true atomic witnesses (where uniqueness
fails).

The wh-question-with-no-witness case was already proved as
`Karttunen1977.karttunen_which_no_witness`; here we add the EP-failure
view. -/

/-- @cite{dayal-2016} §2.3.4 (57a) cancellation: when `Q` has no true
    alternative at `w`, the EP fails — the existence presupposition
    is the load-bearing condition that distinguishes Karttunen's
    truth-in-denotation from Dayal's truth-in-answerhood-operator. -/
theorem ep_fails_when_no_true_alt (Q : Question W) (w : W)
    (h : ∀ p ∈ alt Q, w ∉ p) :
    ¬ IsEPSatisfied Q w := by
  rintro ⟨p, hp, hwp, _⟩
  exact h p hp hwp

/-- @cite{dayal-2016} §2.3.3 (45)/(49)/(51): a singular wh-question
    with multiple incomparable true atomic witnesses has no
    maximally-informative answer. EP fails.

    Concrete: alternatives are `like_w(j, m)`, `like_w(j, s)`,
    `like_w(j, b)`. If John likes Mary AND Sue (atomic individuals,
    incomparable propositions), no single proposition entails the
    other; iota is undefined. -/
theorem ep_fails_when_two_incomparable_true_alts (Q : Question W) (w : W)
    (p₁ p₂ : Set W)
    (hp₁ : p₁ ∈ alt Q) (hp₂ : p₂ ∈ alt Q)
    (hwp₁ : w ∈ p₁) (hwp₂ : w ∈ p₂)
    (hp₁_not_sub : ¬ p₁ ⊆ p₂) (hp₂_not_sub : ¬ p₂ ⊆ p₁) :
    ¬ IsEPSatisfied Q w := by
  rintro ⟨q, hq, hwq, hq_min⟩
  -- q ⊆ p₁ and q ⊆ p₂. But this doesn't immediately contradict
  -- incomparability. The contradiction comes from "q is in alt", and
  -- alt elements are MAXIMAL: if q ⊊ p₁ then q is not maximal.
  have hq_sub_p₁ : q ⊆ p₁ := hq_min p₁ hp₁ hwp₁
  have hq_sub_p₂ : q ⊆ p₂ := hq_min p₂ hp₂ hwp₂
  -- Maximality of q: q ∈ alt Q ⇒ ∀r ∈ Q.props, q ⊆ r → q = r
  have hq_max : ∀ r ∈ Q.props, q ⊆ r → q = r := hq.2
  have hp₁_props : p₁ ∈ Q.props := alt_subset_props _ hp₁
  have hp₂_props : p₂ ∈ Q.props := alt_subset_props _ hp₂
  have hqp₁ : q = p₁ := hq_max p₁ hp₁_props hq_sub_p₁
  have hqp₂ : q = p₂ := hq_max p₂ hp₂_props hq_sub_p₂
  -- Now p₁ = q = p₂, contradicting incomparability.
  apply hp₁_not_sub
  rw [← hqp₁, hqp₂]

end Phenomena.Questions.Studies.Dayal2016
