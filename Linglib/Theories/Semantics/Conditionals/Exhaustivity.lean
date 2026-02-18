import Linglib.Core.Proposition
import Linglib.Core.QUD
import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Basic
import Linglib.Theories.Semantics.Conditionals.Basic

/-!
# Conditional Perfection via Answer-Level Exhaustification

Formalizes the connection between conditional perfection and speech-act level
exhaustification, following von Fintel (2001) "Conditional strengthening."

## Key Insight

Propositional-level exhaustification of the material conditional does NOT yield
perfection: `EXH(¬A∨C, {¬B∨C}) = (¬A∨C) ∧ B ∧ ¬C` — a specific world, not
`¬A→¬C`. Instead, conditional perfection arises from **answer-level**
exhaustification: the answer "A causes C" is exhaustified against the
alternative "B causes C," yielding "only A causes C." Combined with a coverage
assumption (every C-event has some trigger), this entails `¬A→¬C`.

This is von Fintel's (2001) reconstruction of Cornulier (1983): when the QUD
asks for sufficient conditions for C (antecedent-focus), the conditional answer
triggers exhaustification over alternative antecedents. Evcen, Bale & Barner
(2026) experimentally validate this prediction.

## References

- von Fintel (2001). Conditional strengthening: A case study in implicature.
- Cornulier (1983). "If" and the presumption of exhaustivity.
- Geis & Zwicky (1971). On invited inferences.
- Groenendijk & Stokhof (1984). Studies on the semantics of questions.
- Evcen, Bale & Barner (2026). [Experimental validation]
-/

namespace Semantics.Conditionals.Exhaustivity

open Core.Proposition

-- ============================================================================
-- Section A: Answer-Level Alternatives
-- ============================================================================

/-- An answer space for conditional perfection scenarios.

In a conditional perfection scenario, there is a set of potential triggers
(antecedents) and a causal relation saying which trigger is active at which
world. The key QUD is "which trigger causes C?" and the answer "trigger t
causes C" has alternatives "trigger t' causes C" for each other trigger t'.

This models von Fintel's (2001, §4) analysis: the relevant alternatives are
not propositional alternatives to the conditional, but alternative *answers*
to the question "under which conditions does C hold?" -/
structure AnswerSpace (Trigger W : Type*) where
  /-- Which trigger is active at which world -/
  causes : Trigger → W → Prop
  /-- The set of contextually relevant triggers -/
  triggers : Set Trigger

/-- The proposition "trigger t causes C (at world w)."
This is the answer to the antecedent-focus QUD for trigger t. -/
def answerProp {Trigger W : Type*} (as : AnswerSpace Trigger W)
    (t : Trigger) : Prop' W :=
  λ w => as.causes t w

/-- The set of alternative answers: {"t' causes C" | t' ∈ triggers, t' ≠ t}.
These are the answers that compete with "t causes C" under exhaustification. -/
def answerAlternatives {Trigger W : Type*} (as : AnswerSpace Trigger W)
    (t : Trigger) : Set (Prop' W) :=
  {p | ∃ t' ∈ as.triggers, t' ≠ t ∧ p = answerProp as t'}

-- ============================================================================
-- Section B: QUD Types for Conditionals
-- ============================================================================

/-- Antecedent-focus QUD: partitions worlds by which trigger is active.

Under this QUD, asserting "t causes C" invites exhaustification against
alternative triggers, following Groenendijk & Stokhof's (1984) theory of
exhaustive answers applied to conditionals (von Fintel 2001, pp. 15-17). -/
def antecedentFocusQUD {Trigger W : Type*} [DecidableEq Trigger]
    (activeTrigger : W → Option Trigger) : QUD W :=
  QUD.ofDecEq activeTrigger "antecedent-focus"

/-- Consequent-focus QUD: partitions worlds by what effect obtains.

Under this QUD, the answer lists consequences of a given antecedent.
No exhaustification over alternative antecedents occurs, so no perfection. -/
def consequentFocusQUD {Effect W : Type*} [DecidableEq Effect]
    (activeEffect : W → Option Effect) : QUD W :=
  QUD.ofDecEq activeEffect "consequent-focus"

-- ============================================================================
-- Section C: Connection to exhIE
-- ============================================================================

/-- The exhaustified answer: assert "t causes C" and innocently exclude
all alternative triggers.

This is `exhIE` from Spector (2016) applied at the **answer level** rather
than the propositional level — the key move that makes exhaustification yield
perfection rather than a contradictory specific world.

At the propositional level, `EXH(¬A∨C, {¬B∨C})` gives `A ∧ B ∧ ¬C`.
At the answer level, `EXH("A causes C", {"B causes C"})` gives
"A causes C and B does not cause C" — which with coverage yields perfection. -/
def exhaustifiedAnswer {Trigger W : Type*} (as : AnswerSpace Trigger W)
    (t : Trigger) : Prop' W :=
  NeoGricean.Exhaustivity.exhIE (answerAlternatives as t) (answerProp as t)

-- ============================================================================
-- Section D: General Perfection Theorem
-- ============================================================================

/-- **Conditional perfection from exclusion and coverage.**

If:
- trigger `t` requires precondition `p` (t-worlds are p-worlds),
- all other triggers are excluded (exhaustification),
- every C-event has some trigger (coverage/closure),

then `¬p → ¬C`.

This is the core logical step underlying von Fintel's (2001) analysis:
exhaustification provides exclusion (only t causes C), the QUD-driven
coverage assumption closes the gap to perfection (every C has a cause,
the only cause requires p, so ¬p → ¬C).

The proof is purely structural (no `sorry`, no `native_decide`). -/
theorem perfection_from_exclusion_and_coverage
    {W Trigger : Type*}
    (causes : Trigger → W → Prop) (triggers : Set Trigger)
    (t : Trigger) (_ht : t ∈ triggers)
    (p C : W → Prop)
    (h_t_requires_p : ∀ w, causes t w → p w)
    (h_exclusion : ∀ t' ∈ triggers, t' ≠ t → ∀ w, ¬causes t' w)
    (h_coverage : ∀ w, C w → ∃ t' ∈ triggers, causes t' w)
    (w : W) (hnp : ¬p w) : ¬C w := by
  intro hC
  obtain ⟨t', ht'_mem, ht'_causes⟩ := h_coverage w hC
  have hne : t' ≠ t := by
    intro heq; subst heq
    exact hnp (h_t_requires_p w ht'_causes)
  exact h_exclusion t' ht'_mem hne w ht'_causes

/-- Perfection from an answer space with exclusion and coverage.

Connects the `AnswerSpace` abstraction to the general perfection theorem.
When the exhaustified answer excludes all alternative triggers (exclusion)
and every instance of C has some trigger (coverage), precondition failure
entails consequent failure: `¬p → ¬C`. -/
theorem AnswerSpace.perfection
    {Trigger W : Type*}
    (as : AnswerSpace Trigger W)
    (t : Trigger) (ht : t ∈ as.triggers)
    (p C : W → Prop)
    (h_t_requires_p : ∀ w, as.causes t w → p w)
    (h_exclusion : ∀ t' ∈ as.triggers, t' ≠ t → ∀ w, ¬as.causes t' w)
    (h_coverage : ∀ w, C w → ∃ t' ∈ as.triggers, as.causes t' w)
    (w : W) (hnp : ¬p w) : ¬C w :=
  perfection_from_exclusion_and_coverage as.causes as.triggers t ht p C
    h_t_requires_p h_exclusion h_coverage w hnp

-- ============================================================================
-- Section E: Connecting Exhaustification to Perfection
-- ============================================================================

/-- **Exhaustification excludes innocently excludable alternatives.**

If the exhaustified answer holds at world `w` and alternative trigger `t'`
is innocently excludable (its negation belongs to every MC-set), then
`t'` does not cause C at `w`.

This is the key connecting lemma: it bridges `exhIE` (Spector 2016) to the
exclusion hypothesis in `perfection_from_exclusion_and_coverage`. Without it,
`exhaustifiedAnswer` and the perfection theorem are disconnected definitions. -/
theorem exhaustifiedAnswer_excludes
    {Trigger W : Type*} (as : AnswerSpace Trigger W)
    (t t' : Trigger) (w : W)
    (h_exh : exhaustifiedAnswer as t w)
    (h_ie : NeoGricean.Exhaustivity.isInnocentlyExcludable
              (answerAlternatives as t) (answerProp as t) (answerProp as t'))
    : ¬as.causes t' w := by
  unfold exhaustifiedAnswer NeoGricean.Exhaustivity.exhIE at h_exh
  exact h_exh _ h_ie.2

/-- **Full prediction chain: exhaustification → perfection.**

This is the genuine dependency chain from theory to prediction:

1. `exhaustifiedAnswer as t w` holds (speaker asserts under antecedent-focus QUD)
2. All alternative triggers are innocently excludable (`h_all_ie`)
3. Every C-event has some trigger (`h_coverage`)
4. Trigger `t` requires precondition `p` (`h_t_requires_p`)
5. Therefore: `¬p w → ¬C w`

Steps 1–2 yield local exclusion at `w` (via `exhaustifiedAnswer_excludes`).
Step 3 is the coverage/closure assumption driven by the QUD.
The conclusion follows by `perfection_from_exclusion_and_coverage`.

This theorem closes the gap between the exhaustification mechanism (`exhIE`)
and the perfection result. Without it, the theory has two disconnected pieces:
the definition of exhaustified answers and the perfection theorem, with no
proof that the former provides the exclusion the latter requires. -/
theorem exhaustification_yields_perfection
    {Trigger W : Type*} (as : AnswerSpace Trigger W)
    (t : Trigger) (p C : W → Prop) (w : W)
    (h_t_requires_p : ∀ w, as.causes t w → p w)
    (h_all_ie : ∀ t' ∈ as.triggers, t' ≠ t →
      NeoGricean.Exhaustivity.isInnocentlyExcludable
        (answerAlternatives as t) (answerProp as t) (answerProp as t'))
    (h_coverage : C w → ∃ t' ∈ as.triggers, as.causes t' w)
    (h_exh : exhaustifiedAnswer as t w)
    (hnp : ¬p w) : ¬C w := by
  intro hC
  obtain ⟨t', ht'_mem, ht'_causes⟩ := h_coverage hC
  by_cases hne : t' = t
  · subst hne; exact hnp (h_t_requires_p w ht'_causes)
  · exact absurd ht'_causes
      (exhaustifiedAnswer_excludes as t t' w h_exh (h_all_ie t' ht'_mem hne))

-- ============================================================================
-- Section F: Singleton Alternatives Are Innocently Excludable
-- ============================================================================

/-- **Singleton alternatives are innocently excludable.**

When the alternative set effectively contains a single proposition `a`
(every member equals `a`) and the assertion `φ` is jointly satisfiable with
`¬a`, then `a` is innocently excludable.

**Proof sketch**: Any MC-set E ⊆ {φ, ∼a} (by compatibility, every element
is φ or ∼a' for a' ∈ ALT, and all a' = a). The set {φ, ∼a} is itself
compatible (consistency from `h_consist`). By maximality of E with
E ⊆ {φ, ∼a}: {φ, ∼a} ⊆ E. Hence ∼a ∈ E for every MC-set E.

This closes the gap between the abstract IE machinery (Spector 2016) and
concrete scenarios with a single competing alternative — the typical
case in conditional perfection with two triggers. -/
theorem singleton_alt_innocently_excludable
    {World : Type*}
    (ALT : Set (Core.Proposition.Prop' World))
    (φ a : Core.Proposition.Prop' World)
    (h_mem : a ∈ ALT)
    (h_all_eq : ∀ a' ∈ ALT, a' = a)
    (h_consist : ∃ w, φ w ∧ ¬(a w))
    : NeoGricean.Exhaustivity.isInnocentlyExcludable ALT φ a := by
  open NeoGricean.Exhaustivity in
  constructor
  · exact h_mem
  · -- Goal: ∼a ∈ IE ALT φ, i.e., ∀ E, isMCSet ALT φ E → ∼a ∈ E
    intro E hE_mc
    -- The candidate superset: {φ, ∼a}
    -- Step 1: E ⊆ {φ, ∼a} (by compatibility + singleton condition)
    have h_sub : E ⊆ ({φ, ∼a} : Set (Prop' World)) := by
      intro ψ hψ
      rcases hE_mc.1.2.1 ψ hψ with h | ⟨a', ha'_mem, ha'_eq⟩
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · rw [h_all_eq a' ha'_mem] at ha'_eq
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr ha'_eq))
    -- Step 2: {φ, ∼a} is compatible
    have h_compat : isCompatible ALT φ ({φ, ∼a} : Set (Prop' World)) := by
      refine ⟨Set.mem_insert φ _, ?_, ?_⟩
      · -- Every element is φ or ∼a' for some a' ∈ ALT
        intro ψ hψ
        rcases Set.mem_insert_iff.mp hψ with h | h
        · exact Or.inl h
        · exact Or.inr ⟨a, h_mem, Set.mem_singleton_iff.mp h⟩
      · -- Consistent: ∃ w, φ w ∧ (∼a) w
        obtain ⟨w, hw_phi, hw_not_a⟩ := h_consist
        exact ⟨w, fun ψ hψ => by
          rcases Set.mem_insert_iff.mp hψ with h | h
          · rw [h]; exact hw_phi
          · rw [Set.mem_singleton_iff.mp h]; exact hw_not_a⟩
    -- Step 3: By maximality of E, {φ, ∼a} ⊆ E
    have h_sup : ({φ, ∼a} : Set (Prop' World)) ⊆ E := hE_mc.2 _ h_compat h_sub
    -- Step 4: ∼a ∈ E
    exact h_sup (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))

end Semantics.Conditionals.Exhaustivity
