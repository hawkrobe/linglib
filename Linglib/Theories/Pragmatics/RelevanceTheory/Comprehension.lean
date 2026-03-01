import Mathlib.Data.Rat.Defs

/-!
# The Comprehension Procedure — Sperber & Wilson (1986/95)

The comprehension procedure is the heart of RT's account of utterance
understanding. S&W (2nd ed, Postface):

> "Follow a path of least effort in computing cognitive effects.
>  Test interpretive hypotheses in order of accessibility.
>  Stop when your expectations of relevance are satisfied."

This is an **ordered search** with a **satisficing** criterion:
1. Consider candidate interpretations in order of accessibility
2. For each, assess whether it achieves enough cognitive effects
3. Accept the FIRST interpretation that meets the relevance threshold
4. If none does, communication fails

## The RT Argument Form

The characteristic RT argument shows that interpretation I is selected
by the comprehension procedure in a given scenario. In Lean:

```
theorem my_analysis :
    scenario.comprehensionSelects interpretationI := by ...
```

This requires showing three things:
1. I is a candidate interpretation
2. I's effects reach the relevance threshold (clause a)
3. No more accessible candidate also reaches the threshold (first acceptable)

## Processing Effort Arguments

Processing effort enters at TWO levels:

1. **Accessibility ordering**: more effort → less accessible → tried later.
   This is the `accessibility` field: it determines the ORDER of search.
2. **Relevance trade-off**: more effort → less relevant (other things equal).
   This is the `effort` field: it can RAISE the threshold for an interpretation
   to count as "worth processing."

The `adjustedThreshold` captures this: an interpretation that requires more
effort must produce proportionally more effects to satisfy clause (a).
Set `effortWeight = 0` to ignore effort in the threshold (pure effects-based).

-/

set_option autoImplicit false

namespace Theories.Pragmatics.RelevanceTheory

-- ============================================================================
-- §1. RT Scenarios
-- ============================================================================

/-- An RT scenario: everything the comprehension procedure needs.

    The practitioner sets up a scenario by specifying candidates, their
    accessibility ordering, their effects, and the relevance threshold.
    The comprehension procedure determines which interpretation is selected.

    **Processing effort**: enter `effort` values per interpretation.
    The `adjustedThreshold` adds `effortWeight * effort i` to the base
    threshold, so costlier interpretations must produce more effects. -/
structure RTScenario (I : Type*) where
  /-- Candidate interpretations -/
  candidates : List I
  /-- Accessibility ordering: lower = more accessible = tried first.
      Encodes the "path of least effort" — more accessible interpretations
      require less processing effort to ACCESS (not to SATISFY). -/
  accessibility : I → ℕ
  /-- Cognitive effects of each interpretation -/
  effects : I → ℕ
  /-- Processing effort of each interpretation (cost to derive it) -/
  effort : I → ℕ
  /-- Base relevance threshold: minimum effects to be worth processing
      when effort is zero -/
  threshold : ℕ
  /-- How much each unit of effort raises the threshold.
      Set to 0 for pure effects-based assessment. -/
  effortWeight : ℕ

variable {I : Type*}

/-- The adjusted threshold for interpretation `i`: base threshold plus
    effort-proportional cost. An interpretation must produce at least
    this many effects to be "worth processing." -/
def RTScenario.adjustedThreshold (s : RTScenario I) (i : I) : ℕ :=
  s.threshold + s.effortWeight * s.effort i

-- ============================================================================
-- §2. The Comprehension Procedure
-- ============================================================================

/-- The comprehension procedure selects interpretation `i`.

    An interpretation is selected iff:
    1. It is a candidate
    2. Its effects reach the adjusted threshold (clause a: worth processing)
    3. No more accessible candidate also reaches its own threshold
       (first acceptable: the hearer stops at the first good-enough answer)

    The third condition makes the procedure SATISFICING, not OPTIMIZING —
    the hearer doesn't search for the best interpretation, just the first
    good enough one. -/
def RTScenario.comprehensionSelects (s : RTScenario I) (i : I) : Prop :=
  i ∈ s.candidates ∧
  s.adjustedThreshold i ≤ s.effects i ∧
  ∀ j ∈ s.candidates, s.accessibility j < s.accessibility i →
    s.effects j < s.adjustedThreshold j

/-- Communication failure: no candidate reaches its relevance threshold. -/
def RTScenario.communicationFails (s : RTScenario I) : Prop :=
  ∀ i ∈ s.candidates, s.effects i < s.adjustedThreshold i

-- ============================================================================
-- §3. Structural Properties
-- ============================================================================

/-- If the procedure selects i, communication does not fail. -/
theorem RTScenario.selects_not_fails (s : RTScenario I) (i : I)
    (h : s.comprehensionSelects i) : ¬s.communicationFails := by
  intro hf
  have ⟨hi, heff, _⟩ := h
  exact Nat.not_lt.mpr heff (hf i hi)

/-- If i is selected, every more accessible candidate fails its threshold. -/
theorem RTScenario.selected_blocks (s : RTScenario I) (i j : I)
    (hi : s.comprehensionSelects i) (hj : j ∈ s.candidates)
    (hacc : s.accessibility j < s.accessibility i) :
    s.effects j < s.adjustedThreshold j :=
  hi.2.2 j hj hacc

/-- Two interpretations at different accessibility levels cannot both be
    selected: the more accessible one would block the less accessible one.

    This is a direct consequence of satisficing: once the procedure stops
    at the first good-enough interpretation, less accessible candidates
    are never reached. -/
theorem RTScenario.selects_at_most_one (s : RTScenario I) (i j : I)
    (hi : s.comprehensionSelects i) (hj : s.comprehensionSelects j)
    (hacc : s.accessibility i < s.accessibility j) : False := by
  have h1 := hj.2.2 i hi.1 hacc
  have h2 := hi.2.1
  omega

/-- The selected interpretation passes its threshold. -/
theorem RTScenario.selected_passes_threshold (s : RTScenario I) (i : I)
    (h : s.comprehensionSelects i) :
    s.adjustedThreshold i ≤ s.effects i :=
  h.2.1

/-- If the most accessible candidate passes threshold, it is selected. -/
theorem RTScenario.most_accessible_selected (s : RTScenario I) (i : I)
    (hmem : i ∈ s.candidates)
    (hpass : s.adjustedThreshold i ≤ s.effects i)
    (hmost : ∀ j ∈ s.candidates, ¬(s.accessibility j < s.accessibility i)) :
    s.comprehensionSelects i :=
  ⟨hmem, hpass, fun j hj hacc => absurd hacc (hmost j hj)⟩

-- ============================================================================
-- §4. Processing Effort Arguments
-- ============================================================================

/-- A processing effort argument: interpretation `i` is DISpreferred
    because its effort raises the threshold above its effects, even though
    it would be acceptable at zero effort.

    Example: in a rapid conversational exchange, enriching "some" to
    "some but not all" may cost more effort than the effects justify,
    even though in a slower context the enriched reading would be selected.

    This mechanism is distinctive to RT — NeoGricean theories have no
    counterpart. -/
def RTScenario.blockedByEffort (s : RTScenario I) (i : I) : Prop :=
  s.threshold ≤ s.effects i ∧ s.effects i < s.adjustedThreshold i

/-- An effort-free scenario: effort plays no role in relevance assessment.
    Useful when the argument turns purely on effects, not processing cost. -/
def RTScenario.effortFree (s : RTScenario I) : Prop :=
  s.effortWeight = 0

/-- In an effort-free scenario, the adjusted threshold equals the base. -/
theorem RTScenario.effortFree_threshold (s : RTScenario I) (i : I)
    (h : s.effortFree) : s.adjustedThreshold i = s.threshold := by
  simp only [adjustedThreshold]
  have : s.effortWeight = 0 := h
  rw [this, Nat.zero_mul, Nat.add_zero]

/-- Effort blocking requires nonzero effort weight — in an effort-free
    scenario, no interpretation can be blocked by effort. -/
theorem RTScenario.effortFree_not_blocked (s : RTScenario I) (i : I)
    (h : s.effortFree) : ¬s.blockedByEffort i := by
  intro ⟨hle, hlt⟩
  rw [RTScenario.effortFree_threshold s i h] at hlt
  omega

-- ============================================================================
-- §5. Clause (b): Speaker's Alternatives
-- ============================================================================

/-- Clause (b) of optimal relevance: the communicator's choice was the
    most relevant compatible with their abilities and preferences.

    An alternative stimulus `alt` was AVAILABLE but not used. If `alt`
    would have been more relevant (more effects, less effort), the hearer
    can infer the communicator COULDN'T or DIDN'T WANT TO use it.

    This derives implicatures about the speaker's epistemic state.

    Example: "Some students passed" rather than "All students passed" →
    the speaker wasn't in a position to say "all" → speaker doesn't
    believe all passed. -/
structure ClauseBArgument (I : Type*) where
  /-- The stimulus actually used -/
  actual : I
  /-- An alternative the communicator could have used -/
  alternative : I
  /-- The alternative would have been more relevant -/
  alternativeMoreRelevant : Prop
  /-- The communicator's constraint: inability or preference -/
  communicatorConstraint : Prop

end Theories.Pragmatics.RelevanceTheory
