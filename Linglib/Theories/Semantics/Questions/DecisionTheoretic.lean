import Linglib.Core.Question.Basic
import Linglib.Core.Question.Relevance
import Linglib.Core.Agent.DecisionTheory
import Linglib.Theories.Semantics.Questions.Resolution

/-!
# Decision-Theoretic Question Semantics
@cite{van-rooy-2003} @cite{van-rooy-safarova-2003} @cite{blackwell-1953} @cite{chierchia-2013}

Topical home for question semantics extended with utility / cost
structure. The "value of a question" is defined relative to a
decision problem; relevance, polar profiles, and Blackwell dominance
are all derived notions over the inquisitive substrate.

## Layout

* **Utility-based relevance** (`@cite{van-rooy-2003}` Op(P)).
  `IsDecisionRelevant Q σ dp` holds when resolving `Q` from state
  `σ` strictly changes the optimal action in `dp`.
* **Polar utility profiles** (`@cite{van-rooy-safarova-2003}`).
  `IsPPQ`, `IsNPQ`, `IsAltQ` classify a polar question's
  utility-asymmetry pattern.
* **Blackwell dominance** (`@cite{blackwell-1953}`). The inquisitive
  setting splits the partition notion of "refinement" into two
  independent directions, both in `Core.Question.Relevance`:
  - `questionEntails P Q` — every P-alt ⊆ some Q-alt (P-alts are
    *contained in* Q-alts).
  - `CoversAltsOf P Q` — every nonempty Q-alt is covered by some
    nonempty P-alt (the dual).
  For partition questions the two coincide. Decision-relevance
  preservation requires the dual; the
  `CoversAltsOf.preserves_decisionRelevant` theorem (proven below)
  is the @cite{van-rooy-2003} bridge.
* **Question entropy / NPI strength** (`@cite{chierchia-2013}`).
  An NPI-licensing context is one whose alternatives carry high
  Shannon entropy. The information-theoretic NPI account is
  @cite{chierchia-2013} (and earlier @cite{israel-1996} for the
  scalar-strengthening variant); @cite{krifka-1995a} *Linguistic
  Analysis* is the foundational lexical-semantic NPI paper but does
  not invoke entropy directly.

## Substrate split

Question denotations are inquisitive (`Core.Question W`) — `Set`-based
alternatives. Decision problems live in `Core.Agent.DecisionTheory`
with `Finset`-based action and cell sets. The bridge requires
`[Fintype W]` plus per-alternative decidability; consumers that don't
need finite computation work directly with the `Set`-shaped
predicates here.
-/

namespace Semantics.Questions.DecisionTheoretic

open Core Core.Question Semantics.Questions.Resolution

variable {W A : Type*}

/-! ### Decision-relevance (@cite{van-rooy-2003} Op(P))

A question is *decision-relevant* if learning its answer can change
which action maximises expected utility. The notion specialises
@cite{van-rooy-2003}'s Op(P) to the inquisitive substrate: rather
than computing `EU(after Q) − EU(before Q)` numerically, we ask
whether *some* alternative of `Q` would shift the optimal action. -/

/-- `Q` is **decision-relevant** to `dp`: there exist two **non-empty**
    alternatives `p, p' ∈ alt Q` and two actions `a, a' ∈ acts` such
    that `a` strictly dominates `a'` on `p` while `a'` strictly
    dominates `a` on `p'`. Then learning *which* alternative obtains
    shifts the optimal choice — the operational content of
    @cite{van-rooy-2003} Op(P) > 0.

    The non-emptiness clauses rule out the degenerate case where
    `Q = ⊥` (only `∅` in `alt`): with empty witness propositions
    the dominance conditions hold vacuously without genuinely
    distinguishing any worlds. Mathlib-shape: a substantive
    decision-relevance claim requires substantive (nonempty) witnesses. -/
def IsDecisionRelevant
    (Q : Question W) (dp : Core.DecisionTheory.DecisionProblem W A)
    (acts : Set A) : Prop :=
  ∃ p ∈ alt Q, p.Nonempty ∧ ∃ p' ∈ alt Q, p'.Nonempty ∧
    ∃ a ∈ acts, ∃ a' ∈ acts,
      (∀ w ∈ p,  dp.utility w a  > dp.utility w a') ∧
      (∀ w ∈ p', dp.utility w a' > dp.utility w a)

/-! ### Bridge to `Core.DecisionTheory.IsResolved` -/

/-- @cite{van-rooy-2003} §3.1 connection: a `IsDecisionRelevant`
    witness `(p, p', a, a')` exhibits two `Q`-alts whose two-action
    restriction is `IsResolved` to *different* witnesses. On `p`,
    action `a` resolves the restricted DP `(dp, {a, a'})`; on `p'`,
    action `a'` does. So `IsDecisionRelevant` is precisely "two
    `Q`-alts resolve to distinct actions" in the substrate's
    `IsResolved` vocabulary. -/
theorem IsDecisionRelevant.alts_resolve_distinct
    {Q : Question W} {dp : Core.DecisionTheory.DecisionProblem W A}
    {acts : Set A} (h : IsDecisionRelevant Q dp acts) :
    ∃ p ∈ alt Q, p.Nonempty ∧ ∃ p' ∈ alt Q, p'.Nonempty ∧
      ∃ a ∈ acts, ∃ a' ∈ acts, a ≠ a' ∧
        Core.DecisionTheory.IsResolved dp {a, a'} p ∧
        Core.DecisionTheory.IsResolved dp {a, a'} p' := by
  obtain ⟨p, hp, hpne, p', hp', hp'ne, a, ha, a', ha', hpa, hpa'⟩ := h
  refine ⟨p, hp, hpne, p', hp', hp'ne, a, ha, a', ha', ?_, ?_, ?_⟩
  · -- a ≠ a': follows from strict-domination on a nonempty p.
    intro heq
    obtain ⟨w, hw⟩ := hpne
    have h1 : dp.utility w a > dp.utility w a' := hpa w hw
    rw [heq] at h1
    exact absurd h1 (lt_irrefl _)
  · -- IsResolved dp {a, a'} p: action a weakly dominates a' on p
    refine ⟨a, by simp, ?_⟩
    intro b hb w hw
    rcases hb with rfl | hb'
    · exact le_refl _
    · rw [Set.mem_singleton_iff] at hb'
      subst hb'
      exact le_of_lt (hpa w hw)
  · -- IsResolved dp {a, a'} p': action a' weakly dominates a on p'
    refine ⟨a', by simp, ?_⟩
    intro b hb w hw
    rcases hb with rfl | hb'
    · exact le_of_lt (hpa' w hw)
    · rw [Set.mem_singleton_iff] at hb'
      subst hb'
      exact le_refl _

/-- The trivial question (single alternative) is not decision-relevant:
    one substantive alternative cannot witness the action-reversal. -/
theorem IsDecisionRelevant.singleton_alt_false
    {Q : Question W} {dp : Core.DecisionTheory.DecisionProblem W A}
    {acts : Set A}
    (hSingle : ∀ p p', p ∈ alt Q → p' ∈ alt Q → p = p') :
    ¬ IsDecisionRelevant Q dp acts := by
  rintro ⟨p, hp, hpne, p', hp', _, a, _, a', _, hpa, hpa'⟩
  rcases hSingle p p' hp hp' with rfl
  obtain ⟨w, hw⟩ := hpne
  exact absurd (hpa w hw) (not_lt_of_gt (hpa' w hw))

/-! ### Polar utility profiles (@cite{van-rooy-safarova-2003})

A polar question `Q? = {p, ¬p}` has a *utility profile* determined by
the asymmetry of action-payoffs between the `p`-cell and the `¬p`-cell.

* **PPQ** (positive polar): the `p`-alternative is utility-preferred.
  Speaker bias toward `p` (e.g., *Did John leave?* in a context where
  John leaving is good news).
* **NPQ** (negative polar): the `¬p`-alternative is preferred.
  Speaker bias toward `¬p` (*Didn't John leave?*).
* **Alt** (alternative question): both alternatives carry comparable
  utility — neither dominates. -/

/-- `Q` is a **PPQ** for action set `acts` and polar split `(p, ¬p)`:
    one specific alternative `p ∈ alt Q` strictly dominates every
    other alternative across every action. The "positive" cell is
    where the speaker's preferred outcome lies. @cite{van-rooy-safarova-2003}. -/
def IsPPQ (Q : Question W) (dp : Core.DecisionTheory.DecisionProblem W A)
    (acts : Set A) (p : Set W) : Prop :=
  p ∈ alt Q ∧
  ∃ a ∈ acts, ∀ p' ∈ alt Q, p' ≠ p →
    ∀ w ∈ p,  ∀ w' ∈ p', dp.utility w a > dp.utility w' a

/-- `Q` is an **NPQ** for action set `acts` and polar split `(p, ¬p)`:
    a strictly *non*-`p` alternative is the utility-preferred one.
    @cite{van-rooy-safarova-2003}. -/
def IsNPQ (Q : Question W) (dp : Core.DecisionTheory.DecisionProblem W A)
    (acts : Set A) (p : Set W) : Prop :=
  p ∈ alt Q ∧
  ∃ p' ∈ alt Q, p' ≠ p ∧ IsPPQ Q dp acts p'

/-- `Q` is an **alternative-utility question** for action set `acts`:
    no single alternative strictly dominates. The utility-balanced
    case. @cite{van-rooy-safarova-2003}. -/
def IsAltQ (Q : Question W) (dp : Core.DecisionTheory.DecisionProblem W A)
    (acts : Set A) : Prop :=
  ∀ p ∈ alt Q, ¬ IsPPQ Q dp acts p

/-- A PPQ rules out the alt-utility classification. -/
theorem IsPPQ.not_isAltQ {Q : Question W}
    {dp : Core.DecisionTheory.DecisionProblem W A} {acts : Set A} {p : Set W}
    (h : IsPPQ Q dp acts p) : ¬ IsAltQ Q dp acts := by
  intro hAlt
  exact hAlt p h.1 h


/-! ### Blackwell informativeness (@cite{blackwell-1953})

The Blackwell informativeness order on questions is
`Core.Question.Relevance.questionEntails P Q`: every alternative of
`P` is contained in some alternative of `Q` (P is finer than Q).
The dual condition — every nonempty Q-alt is covered by a nonempty
P-alt — is `Core.Question.Relevance.CoversAltsOf P Q`. On *partition*
questions the two coincide; on general inquisitive `Question W` they
are distinct. The decision-relevance preservation theorem requires
the dual form. -/

/-! The decision-relevance preservation theorem itself
(`CoversAltsOf.preserves_decisionRelevant`) is declared at the bottom
of this file, *outside* the topic namespace, under
`Core.Question.CoversAltsOf` so dot notation works at consumer
sites. -/

/-! ### Question entropy and NPI strength (@cite{chierchia-2013})

@cite{chierchia-2013} relates NPI distribution to the
*informativeness* of the alternative set raised by a sentence (the
information-theoretic strand earlier traced through @cite{israel-1996}
on lexical-semantic polarity sensitivity). A question whose
alternatives are equiprobable under the prior carries maximal
Shannon entropy; NPIs prefer such high-entropy contexts. The earlier
@cite{krifka-1995a} *Linguistic Analysis* polarity-items paper is the
foundational lexical-semantic NPI account but does not formulate
licensing in entropy terms — the Chierchia/Israel synthesis is the
right citation here.

The numeric API requires real-valued logarithms over the prior;
deferred to a follow-up that lifts `Core.Probability`'s `PMF` API to
expose Shannon entropy. The Prop-level placeholder
`HasMultipleSubstantiveAlternatives` captures the load-bearing
condition that the question is informative — necessary for any
NPI-licensing notion. -/

/-- `Q` has multiple substantive alternatives: some pair of distinct
    alternatives are both nonempty. Necessary for any NPI-licensing
    formulation (a single-alt question carries no informational
    asymmetry). @cite{chierchia-2013} prerequisite. -/
def HasMultipleSubstantiveAlternatives (Q : Question W) : Prop :=
  ∃ p ∈ alt Q, ∃ q ∈ alt Q, p ≠ q ∧ p.Nonempty ∧ q.Nonempty

/-- A decision-relevant question necessarily has multiple substantive
    (nonempty, distinct) alternatives. The substrate-level
    contrapositive of `IsDecisionRelevant.singleton_alt_false`:
    decision-relevance requires informational asymmetry, which is
    @cite{chierchia-2013}'s prerequisite for NPI licensing. So any
    decision-relevant question is a candidate NPI-licensing context. -/
theorem IsDecisionRelevant.imp_HasMultipleSubstantiveAlternatives
    {Q : Question W} {dp : Core.DecisionTheory.DecisionProblem W A}
    {acts : Set A} (h : IsDecisionRelevant Q dp acts) :
    HasMultipleSubstantiveAlternatives Q := by
  obtain ⟨p, hp, hpne, p', hp', hp'ne, a, _, a', _, hpa, hpa'⟩ := h
  refine ⟨p, hp, p', hp', ?_, hpne, hp'ne⟩
  intro heq
  obtain ⟨w, hw⟩ := hpne
  have h1 : dp.utility w a > dp.utility w a' := hpa w hw
  have h2 : dp.utility w a' > dp.utility w a := hpa' w (heq ▸ hw)
  exact absurd h1 (not_lt_of_gt h2)

end Semantics.Questions.DecisionTheoretic

/-! ### `CoversAltsOf` API extensions

Theorem placed under `Core.Question.CoversAltsOf` namespace (not the
file's `Semantics.Questions.DecisionTheoretic` topic namespace) so
dot-notation `hCover.preserves_decisionRelevant` resolves at consumer
sites. Mathlib pattern: declarations follow the type's namespace, not
the file's topic namespace. -/

namespace Core.Question.CoversAltsOf

open Core.Question Semantics.Questions.DecisionTheoretic

variable {W A : Type*}

/-- @cite{blackwell-1953} ↔ @cite{van-rooy-2003}: when every nonempty
    alt of `Q` is covered by a nonempty alt of `P`, decision-relevance
    is preserved from `Q` to `P`. -/
theorem preserves_decisionRelevant
    {P Q : Question W} (hCover : CoversAltsOf P Q)
    {dp : Core.DecisionTheory.DecisionProblem W A} {acts : Set A}
    (hQ : IsDecisionRelevant Q dp acts) :
    IsDecisionRelevant P dp acts := by
  obtain ⟨p, hp, hpne, p', hp', hp'ne, a, ha, a', ha', hpa, hpa'⟩ := hQ
  obtain ⟨pP, hpP, hpP_ne, hpP_sub⟩ := hCover p hp hpne
  obtain ⟨p'P, hp'P, hp'P_ne, hp'P_sub⟩ := hCover p' hp' hp'ne
  exact ⟨pP, hpP, hpP_ne, p'P, hp'P, hp'P_ne, a, ha, a', ha',
         fun w hw => hpa w (hpP_sub hw),
         fun w hw => hpa' w (hp'P_sub hw)⟩

end Core.Question.CoversAltsOf
