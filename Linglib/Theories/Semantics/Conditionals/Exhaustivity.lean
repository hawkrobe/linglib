import Mathlib.Data.Set.Basic
import Linglib.Core.Question.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
import Linglib.Theories.Semantics.Conditionals.Basic

/-!
# Conditional Perfection via Answer-Level Exhaustification
@cite{cornulier-1983} @cite{evcen-bale-barner-2026} @cite{groenendijk-stokhof-1984} @cite{von-fintel-2001} @cite{geis-zwicky-1971}

Formalizes the connection between conditional perfection and speech-act level
exhaustification, following @cite{von-fintel-2001} "Conditional strengthening."

## Key Insight

Propositional-level exhaustification of the material conditional does NOT yield
perfection: `EXH(¬A∨C, {¬B∨C}) = (¬A∨C) ∧ B ∧ ¬C` — a specific world, not
`¬A→¬C`. Instead, conditional perfection arises from **answer-level**
exhaustification: the answer "A causes C" is exhaustified against the
alternative "B causes C," yielding "only A causes C." Combined with a coverage
assumption (every C-event has some trigger), this entails `¬A→¬C`.

This is @cite{von-fintel-2001}'s reconstruction of @cite{cornulier-1983}: when the QUD
asks for sufficient conditions for C (antecedent-focus), the conditional answer
triggers exhaustification over alternative antecedents. @cite{evcen-bale-barner-2026} experimentally validate this prediction.

-/

namespace Semantics.Conditionals.Exhaustivity

-- ============================================================================
-- Section A: Answer-Level Alternatives
-- ============================================================================

/-- An answer space for conditional perfection scenarios.

In a conditional perfection scenario, there is a set of potential triggers
(antecedents) and a causal relation saying which trigger is active at which
world. The key QUD is "which trigger causes C?" and the answer "trigger t
causes C" has alternatives "trigger t' causes C" for each other trigger t'.

This models @cite{von-fintel-2001}'s analysis: the relevant alternatives are
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
    (t : Trigger) : Set W :=
  λ w => as.causes t w

/-- The set of alternative answers: {"t' causes C" | t' ∈ triggers, t' ≠ t}.
These are the answers that compete with "t causes C" under exhaustification. -/
def answerAlternatives {Trigger W : Type*} (as : AnswerSpace Trigger W)
    (t : Trigger) : Set (Set W) :=
  {p | ∃ t' ∈ as.triggers, t' ≠ t ∧ p = answerProp as t'}

-- ============================================================================
-- Section B: QUD Types for Conditionals
-- ============================================================================

/-- Antecedent-focus QUD: partitions worlds by which trigger is active.

Under this QUD, asserting "t causes C" invites exhaustification against
alternative triggers, following @cite{groenendijk-stokhof-1984} theory of
exhaustive answers applied to conditionals. -/
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

This is `exhIE` from @cite{spector-2016} applied at the **answer level** rather
than the propositional level — the key move that makes exhaustification yield
perfection rather than a contradictory specific world.

At the propositional level, `EXH(¬A∨C, {¬B∨C})` gives `A ∧ B ∧ ¬C`.
At the answer level, `EXH("A causes C", {"B causes C"})` gives
"A causes C and B does not cause C" — which with coverage yields perfection. -/
def exhaustifiedAnswer {Trigger W : Type*} (as : AnswerSpace Trigger W)
    (t : Trigger) : Set W :=
  Exhaustification.exhIE (answerAlternatives as t) (answerProp as t)

-- ============================================================================
-- Section D: General Perfection Theorem
-- ============================================================================

/-- **Conditional perfection from exclusion and coverage.**

If:
- trigger `t` requires precondition `p` (t-worlds are p-worlds),
- all other triggers are excluded (exhaustification),
- every C-event has some trigger (coverage/closure),

then `¬p → ¬C`.

This is the core logical step underlying @cite{von-fintel-2001}'s analysis:
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

This is the key connecting lemma: it bridges `exhIE` to the
exclusion hypothesis in `perfection_from_exclusion_and_coverage`. Without it,
`exhaustifiedAnswer` and the perfection theorem are disconnected definitions. -/
theorem exhaustifiedAnswer_excludes
    {Trigger W : Type*} (as : AnswerSpace Trigger W)
    (t t' : Trigger) (w : W)
    (h_exh : exhaustifiedAnswer as t w)
    (h_ie : Exhaustification.IsInnocentlyExcludable
              (answerAlternatives as t) (answerProp as t) (answerProp as t'))
    : ¬as.causes t' w := by
  unfold exhaustifiedAnswer Exhaustification.exhIE at h_exh
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
      Exhaustification.IsInnocentlyExcludable
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

**Proof sketch**: Any MC-set E ⊆ {φ, aᶜ} (by compatibility, every element
is φ or a'ᶜ for a' ∈ ALT, and all a' = a). The set {φ, aᶜ} is itself
compatible (consistency from `h_consist`). By maximality of E with
E ⊆ {φ, aᶜ}: {φ, aᶜ} ⊆ E. Hence aᶜ ∈ E for every MC-set E.

This closes the gap between the abstract IE machinery and
concrete scenarios with a single competing alternative — the typical
case in conditional perfection with two triggers. -/
theorem singleton_alt_innocently_excludable
    {World : Type*}
    (ALT : Set (Set World))
    (φ a : Set World)
    (h_mem : a ∈ ALT)
    (h_all_eq : ∀ a' ∈ ALT, a' = a)
    (h_consist : ∃ w, φ w ∧ ¬(a w))
    : Exhaustification.IsInnocentlyExcludable ALT φ a := by
  open Exhaustification in
  constructor
  · exact h_mem
  · -- Goal: aᶜ ∈ IE ALT φ, i.e., ∀ E, IsMCSet ALT φ E → aᶜ ∈ E
    intro E hE_mc
    -- The candidate superset: {φ, aᶜ}
    -- Step 1: E ⊆ {φ, aᶜ} (by compatibility + singleton condition)
    have h_sub : E ⊆ ({φ, aᶜ} : Set (Set World)) := by
      intro ψ hψ
      rcases hE_mc.1.2.1 ψ hψ with h | ⟨a', ha'_mem, ha'_eq⟩
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · rw [h_all_eq a' ha'_mem] at ha'_eq
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr ha'_eq))
    -- Step 2: {φ, aᶜ} is compatible
    have h_compat : IsCompatible ALT φ ({φ, aᶜ} : Set (Set World)) := by
      refine ⟨Set.mem_insert φ _, ?_, ?_⟩
      · -- Every element is φ or a'ᶜ for some a' ∈ ALT
        intro ψ hψ
        rcases Set.mem_insert_iff.mp hψ with h | h
        · exact Or.inl h
        · exact Or.inr ⟨a, h_mem, Set.mem_singleton_iff.mp h⟩
      · -- Consistent: ∃ w, φ w ∧ (aᶜ) w
        obtain ⟨w, hw_phi, hw_not_a⟩ := h_consist
        exact ⟨w, fun ψ hψ => by
          rcases Set.mem_insert_iff.mp hψ with h | h
          · rw [h]; exact hw_phi
          · rw [Set.mem_singleton_iff.mp h]; exact hw_not_a⟩
    -- Step 3: By maximality of E, {φ, aᶜ} ⊆ E
    have h_sup : ({φ, aᶜ} : Set (Set World)) ⊆ E := hE_mc.2 _ h_compat h_sub
    -- Step 4: aᶜ ∈ E
    exact h_sup (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))

-- ============================================================================
-- Section G: General IE for Arbitrary Alternative Sets
-- ============================================================================

/-- **All alternatives are innocently excludable when full exclusion is consistent.**

When there exists a world where φ holds and every alternative in ALT is false,
every alternative is innocently excludable. This generalizes
`singleton_alt_innocently_excludable` from singleton to arbitrary ALT.

**Proof**: The set S = {φ} ∪ {aᶜ | a ∈ ALT} is the unique MC-set: it is
compatible by hypothesis, and every compatible set is a subset of it (by the
compatibility constraint, every element is φ or aᶜ for some a ∈ ALT). By
maximality, every MC-set equals S. Since aᶜ ∈ S for all a ∈ ALT, every
alternative is in IE.

This covers conditional perfection scenarios with any number of alternative
triggers — e.g., 3 buttons in @cite{evcen-bale-barner-2026}'s experimental
paradigm. -/
theorem all_alt_innocently_excludable
    {World : Type*}
    (ALT : Set (Set World))
    (φ : Set World)
    (h_consist : ∃ w, φ w ∧ ∀ a ∈ ALT, ¬(a w))
    : ∀ a ∈ ALT, Exhaustification.IsInnocentlyExcludable ALT φ a := by
  open Exhaustification in
  intro a ha_mem
  constructor
  · exact ha_mem
  · -- Goal: aᶜ ∈ IE ALT φ, i.e., ∀ E, IsMCSet ALT φ E → aᶜ ∈ E
    intro E hE_mc
    -- S_max = {ψ | ψ = φ ∨ ∃ a ∈ ALT, ψ = aᶜ} (= {φ} ∪ {aᶜ | a ∈ ALT})
    -- Defined as a predicate so membership unfolds directly.
    let S_max : Set (Set World) := fun ψ => ψ = φ ∨ ∃ a ∈ ALT, ψ = aᶜ
    -- Step 1: E ⊆ S_max (from compatibility: every element is φ or a'ᶜ)
    have h_sub : E ⊆ S_max := by
      intro ψ hψ
      rcases hE_mc.1.2.1 ψ hψ with h | ⟨a', ha'_mem, ha'_eq⟩
      · exact Or.inl h
      · exact Or.inr ⟨a', ha'_mem, ha'_eq⟩
    -- Step 2: S_max is compatible (φ ∈ S_max, every element is φ or aᶜ, consistent)
    have h_compat : IsCompatible ALT φ S_max := by
      refine ⟨Or.inl rfl, fun ψ hψ => hψ, ?_⟩
      obtain ⟨w, hw_phi, hw_not⟩ := h_consist
      exact ⟨w, fun ψ hψ => by
        rcases hψ with h | ⟨a', ha', heq⟩
        · rw [h]; exact hw_phi
        · rw [heq]; exact hw_not a' ha'⟩
    -- Step 3: By maximality of E, S_max ⊆ E
    have h_sup : S_max ⊆ E := hE_mc.2 _ h_compat h_sub
    -- Step 4: aᶜ ∈ S_max, so aᶜ ∈ E
    exact h_sup (Or.inr ⟨a, ha_mem, rfl⟩)

end Semantics.Conditionals.Exhaustivity
