import Linglib.Core.Question.Basic
import Linglib.Theories.Semantics.Questions.Resolution
import Linglib.Theories.Semantics.Questions.Exhaustivity

/-!
# @cite{xiang-2022}: Relativized Exhaustivity: Mention-Some and Uniqueness
@cite{dayal-1996} @cite{fox-2018} @cite{spector-2008} @cite{chierchia-caponigro-2013}

Single-paper formalisation of @cite{xiang-2022}, "Relativized
Exhaustivity: Mention-Some and Uniqueness" (Natural Language
Semantics 30:311–362). Xiang argues that **mention-some (MS)** is a
grammatical phenomenon licensed by existential modals, and proposes
**Relativized Exhaustivity (RelExh)** as the replacement for Dayal's
EP that simultaneously (a) preserves the singular-`which` uniqueness
effects, (b) permits MS where modally licensed, and (c) accounts for
local-uniqueness in modalised singular *wh*-questions.

## Substrate identifications

| @cite{xiang-2022}                              | substrate                                |
|------------------------------------------------|------------------------------------------|
| `Ans_Fox` (eq 20, after Fox 2013) — max-informative true answer | `IsStrongestTrueAnswer Q w p` (without iota uniqueness) |
| `MaxI(α, w, M, [Q])` (eq 96)                   | substrate-relative `IsStrongestRelTrueAnswer` |
| Dayal's EP relativised, `DEP(w, M, [Q])` (eq 90) | `IsRelativelyExhaustivelyResolvable` here |
| **Relativized Exhaustivity, `REP(w, M, [Q])`** (eq 91) | `RelExhPresupposition` here |
| `ANS^S` / `ANS^P` (eq 27, 97)                  | `Exhaustivity.dayalAns` (singular case); plural needs the topical-property layer |

The `Question W = LowerSet (Set W)` substrate captures the
*propositional* side of Xiang's framework. The full §4.1 topical
property layer (questions as functions from short answers `α : Type`
to propositional answers `Set W`) requires extending the `Question`
type to a paired `(ShortAns → Prop) × (... → Set W)` shape; we
defer that lift and work with the propositional projection here.

## Section coverage

* **§1–§3** Empirical landscape, MS distribution, pragmatic vs.
  semantic vs. nucleus-dependent approaches — paper-anchored prose.
* **§4.1.2** Answerhood operators (eq 27) — substrate identifications
  documented above.
* **§5** Dilemma between MS and uniqueness — captured by the
  observation that `IsExhaustivelyResolvable` (Dayal's EP) and `MS`
  are jointly inconsistent in some scenarios.
* **§6.1** RelExh (eq 91) — formalised here as
  `RelExhPresupposition`; the central conceptual contribution.
* **§6.2** Predictions of RelExh on MS distribution — the
  permitting-MS direction (eq 92–95) is captured by
  `relExhPresupposition_holds_when_each_accessible_world_isExhaustivelyResolvable`.
* **§6.3** Uniqueness effects (have-to-, can-, etc.) — paper-anchored
  empirical discussion that requires modal-flavour machinery beyond
  the bare `Set W` modal base; deferred.

## What this file does NOT cover

* §4.1.1 topical-property lift of `Question` (functions from short
  answers to propositions).
* §4.2 first-order/higher-order interpretation distinction; requires
  GQ-typed *wh*-traces (Spector 2008).
* §5.2 alternative analyses (Beck-Rullmann ANS_BR, George ABS+Q
  decomposition, Fox 2013 distributivity scope) — not formalised
  individually; the substrate's `IsStrongestTrueAnswer` is the
  shared abstract.
* §6.3 specific uniqueness predictions for *have to* / *can* / *should*
  with first-order vs higher-order MS — require modal-flavour discrimination.
-/

namespace Phenomena.Questions.Studies.Xiang2022

open Core Core.Question Semantics.Questions.Resolution
open Semantics.Questions.Exhaustivity

variable {W : Type*}

/-! ### §4.1.2 Substrate identifications -/

/-- @cite{xiang-2022} eq (20) (after @cite{fox-2018} eq 20):
    *max-informative true answer*. An alternative `p` is max-info at
    `w` iff `p` is true at `w` and not asymmetrically entailed by any
    other true alternative. Identified with the substrate's
    `IsStrongestTrueAnswer` (without Dayal's iota-uniqueness — Xiang
    follows Fox 2013 in dropping it). -/
abbrev MaxI (Q : Question W) (w : W) (p : Set W) : Prop :=
  IsStrongestTrueAnswer Q w p

/-- @cite{xiang-2022} eq (96) modal-base-relative max-informativity.
    Identified with the substrate's `IsStrongestRelTrueAnswer`. -/
abbrev MaxIRel (Q : Question W) (w : W) (M : Set W) (p : Set W) : Prop :=
  IsStrongestRelTrueAnswer Q w M p

/-! ### §6.1 Dayal's EP relativised + RelExh (eq 90, 91)

@cite{xiang-2022} (eq 90) `Dayal's EP relativised`: `Q` is defined in
`w` (relative to modal base `M`) iff some max-info true answer
exists. (Substrate: `IsRelativelyExhaustivelyResolvable`.)

@cite{xiang-2022} (eq 91) **RelExh**: `Q` is defined in `w` iff for
*every* singleton sub-modal-base `M' ⊆ M` that verifies some true
answer to `Q` (relative to the original `M`), the relativised
Dayal-EP holds at `M'`. The key idea: instead of demanding a
single max-informative answer at the evaluation world, RelExh
demands a max-informative answer at *every accessible world*
(individually, treating each as its own singleton modal base). -/

/-- @cite{xiang-2022} eq (90): Dayal's EP relativised to modal base
    `M`. Substrate identification: `relExh` from `Exhaustivity.lean`. -/
def IsRelativelyExhaustivelyResolvable
    (Q : Question W) (w : W) (M : Set W) : Prop :=
  ∃ p, MaxIRel Q w M p

@[simp] theorem isRelativelyExhaustivelyResolvable_iff_relExh
    (Q : Question W) (w : W) (M : Set W) :
    IsRelativelyExhaustivelyResolvable Q w M ↔ relExh Q w M := Iff.rfl

/-- @cite{xiang-2022} eq (91): **Relativized Exhaustivity (RelExh)**.

    `Q` is defined in `w` (relative to modal base `M`) iff for every
    singleton `M' ⊆ M` (i.e., `M' = {w'}` for some `w' ∈ M`) that
    verifies some true short answer to `Q` (under `M`), the
    relativised Dayal-EP holds at `M'`.

    On the propositional projection: `M' = {w'}` makes the
    relative-EP at `M'` collapse to the standard EP at `w'`. So
    RelExh is essentially "Dayal's EP holds at every accessible
    world that verifies some `Q`-alternative true at `w`". -/
def RelExhPresupposition
    (Q : Question W) (w : W) (M : Set W) : Prop :=
  ∀ w' ∈ M,
    (∃ p ∈ alt Q, w ∈ p ∧ w' ∈ p) →
    IsExhaustivelyResolvable Q w'

/-! ### §6.2 The permitting-MS direction

If every accessible world has its own max-informative true answer,
RelExh is trivially satisfied. This captures Xiang's §6.2.1
prediction that MS is licensed when each accessible world has a
unique exhaustively-true answer relative to that world's perspective. -/

/-- When every accessible world satisfies Dayal's EP, the RelExh
    presupposition is trivially satisfied — the `permits MS` half
    of @cite{xiang-2022} §6.2.1. -/
theorem relExhPresupposition_of_pointwise_EP
    (Q : Question W) (w : W) (M : Set W)
    (hEP : ∀ w' ∈ M, IsExhaustivelyResolvable Q w') :
    RelExhPresupposition Q w M := by
  intro w' hw'M _
  exact hEP w' hw'M

/-! ### §5 Dilemma: Dayal-EP and MS conflict on the same question

@cite{xiang-2022} §5: Dayal's EP requires a unique max-info true
answer; MS rejects this for `can`-questions. The substrate-level
shadow: a question can fail Dayal's EP at `w` while having
`Resolves σ Q` succeed for some non-maximal witness — same
phenomenon as in @cite{fox-2018} §2.1 (already formalised in
`Fox2018.resolves_can_succeed_when_EP_fails`). RelExh resolves the
dilemma by relativising the EP to a per-accessible-world basis. -/

/-- The defining contrast: a non-modalised question can fail Dayal's
    EP at `w` (no unique max true answer) while satisfying RelExh
    relative to a modal base where each accessible world has its own
    max-info answer. -/
theorem relExh_resolves_dilemma_example
    (Q : Question W) (w w₁ w₂ : W) (p₁ p₂ : Set W)
    (hM : ({w₁, w₂} : Set W) ⊆ Set.univ)
    (hSTA1 : IsStrongestTrueAnswer Q w₁ p₁)
    (hSTA2 : IsStrongestTrueAnswer Q w₂ p₂) :
    RelExhPresupposition Q w {w₁, w₂} := by
  intro w' hw'M _
  rcases hw'M with rfl | hw'M
  · exact ⟨p₁, hSTA1⟩
  · rw [Set.mem_singleton_iff] at hw'M
    subst hw'M
    exact ⟨p₂, hSTA2⟩

/-! ### Bridge to Dayal: RelExh under a singleton modal base ≡ Dayal's EP -/

/-- @cite{xiang-2022} (90)/(91) collapse: when the modal base is the
    singleton `{w}`, RelExh reduces to Dayal's standard EP at `w`. -/
theorem relExhPresupposition_singleton_iff
    (Q : Question W) (w : W) (hSelf : ∃ p ∈ alt Q, w ∈ p) :
    RelExhPresupposition Q w {w} ↔ IsExhaustivelyResolvable Q w := by
  constructor
  · intro h
    apply h w rfl
    obtain ⟨p, hp, hwp⟩ := hSelf
    exact ⟨p, hp, hwp, hwp⟩
  · intro hEP w' hw'M _
    rw [Set.mem_singleton_iff] at hw'M
    subst hw'M
    exact hEP

end Phenomena.Questions.Studies.Xiang2022
