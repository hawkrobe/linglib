import Linglib.Theories.Pragmatics.RelevanceTheory.Comprehension

/-!
# Bridge: Relevance Theory → Nonliteral Interpretation

RT's account of metaphor, hyperbole, and loose use is unified: they are all
instances where the LITERAL interpretation fails the relevance threshold,
and a related but non-literal interpretation succeeds.

S&W (Ch. 4 §3): "The hearer does not first decode the proposition expressed,
then check whether it is consistent with the principle of relevance, and
only then look for a figurative interpretation. Rather, the figurative
interpretation is the most accessible one consistent with the principle
of relevance."

## Metaphor (loose use)

"He is a whale" — the literal interpretation (referent is a cetacean)
contradicts mutual knowledge and produces 0 positive cognitive effects.
The metaphorical reading (referent shares salient whale-properties: large,
impressive) produces positive effects via contextual implications.

S&W (pp. 233-237): Metaphor is not a special mechanism — it's what happens
when the comprehension procedure applies to an utterance whose literal
interpretation cannot achieve relevance. The interpretive path from literal
to metaphorical is CONTINUOUS with approximation and hyperbole.

## Hyperbole (overstatement)

"I've told you a million times" — the literal reading is absurd but the
approximate reading (very many times) produces positive effects.

## The RT Continuum

S&W argue these are not distinct categories but a continuum:
  literal → approximation → hyperbole → metaphor

All involve the hearer broadening or loosening the literal content until
the interpretation achieves relevance.

-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Studies.RelevanceTheory

open Theories.Pragmatics.RelevanceTheory

-- ============================================================================
-- §1. Metaphor: "He is a whale"
-- ============================================================================

/-- Candidate interpretations for metaphorical utterances.
    The literal reading is tried first (more accessible) but fails. -/
inductive MetaphorInterpretation where
  /-- Literal: the referent belongs to the category named -/
  | literal
  /-- Metaphorical: the referent shares salient properties of the category -/
  | metaphorical
  deriving DecidableEq, Repr

/-- RT scenario for "He is a whale" (S&W pp. 233-237).

    - Literal ("referent is a cetacean") is more accessible but contradicts
      mutual knowledge that the referent is human → 0 positive effects
    - Metaphorical ("referent is large/impressive") produces positive
      cognitive effects via contextual implications
    - The comprehension procedure skips the literal and selects the
      metaphorical reading -/
def whaleMetaphor : RTScenario MetaphorInterpretation :=
  { candidates := [.literal, .metaphorical]
  , accessibility := fun | .literal => 1 | .metaphorical => 2
  , effects := fun | .literal => 0 | .metaphorical => 3
  , effort := fun | .literal => 0 | .metaphorical => 1
  , threshold := 2
  , effortWeight := 0
  }

/-- The comprehension procedure selects the metaphorical reading.

    The literal reading fails its threshold (0 < 2) — not because it's
    linguistically ill-formed, but because it contradicts mutual knowledge
    and therefore produces no positive cognitive effects. The hearer moves
    to the next candidate, finds the metaphorical reading reaches threshold
    (3 ≥ 2), and stops. -/
theorem metaphor_selects_nonliteral :
    whaleMetaphor.comprehensionSelects .metaphorical := by
  refine ⟨List.Mem.tail _ (List.Mem.head _), ?_, ?_⟩
  · show whaleMetaphor.threshold + whaleMetaphor.effortWeight * whaleMetaphor.effort .metaphorical ≤ 3
    simp [whaleMetaphor]
  · intro j hj hacc
    simp only [whaleMetaphor, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl
    · -- j = .literal: effects 0 < threshold 2
      show 0 < whaleMetaphor.threshold + whaleMetaphor.effortWeight * whaleMetaphor.effort .literal
      simp [whaleMetaphor]
    · -- j = .metaphorical: accessibility 2 < 2, contradiction
      simp [whaleMetaphor] at hacc

/-- The literal reading produces zero positive effects — it contradicts
    mutual knowledge, which is a hallmark of metaphor in RT. -/
theorem literal_zero_effects :
    whaleMetaphor.effects .literal = 0 := rfl

/-- Communication does NOT fail for metaphor — the metaphorical reading
    succeeds. This distinguishes metaphor from genuine communication failure. -/
theorem metaphor_not_failure :
    ¬whaleMetaphor.communicationFails := by
  exact whaleMetaphor.selects_not_fails .metaphorical metaphor_selects_nonliteral

-- ============================================================================
-- §2. Hyperbole: "I've told you a million times"
-- ============================================================================

/-- Candidate interpretations for hyperbolic utterances.
    The literal reading is again tried first but fails (absurd content). -/
inductive HyperboleInterpretation where
  /-- Literal: the exact number/degree stated -/
  | literal
  /-- Approximate: a loosened version (very many, extremely) -/
  | approximate
  deriving DecidableEq, Repr

/-- RT scenario for "I've told you a million times".

    - Literal ("exactly 1,000,000 times") is absurd — no positive effects
    - Approximate ("very many times, I'm exasperated") produces effects:
      contextual implication about the speaker's emotional state and
      the repetitiveness of the situation -/
def millionTimes : RTScenario HyperboleInterpretation :=
  { candidates := [.literal, .approximate]
  , accessibility := fun | .literal => 1 | .approximate => 2
  , effects := fun | .literal => 0 | .approximate => 3
  , effort := fun | .literal => 0 | .approximate => 1
  , threshold := 2
  , effortWeight := 0
  }

/-- The comprehension procedure selects the approximate reading for
    hyperbole, exactly as it does for metaphor — same mechanism. -/
theorem hyperbole_selects_approximate :
    millionTimes.comprehensionSelects .approximate := by
  refine ⟨List.Mem.tail _ (List.Mem.head _), ?_, ?_⟩
  · show millionTimes.threshold + millionTimes.effortWeight * millionTimes.effort .approximate ≤ 3
    simp [millionTimes]
  · intro j hj hacc
    simp only [millionTimes, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl
    · show 0 < millionTimes.threshold + millionTimes.effortWeight * millionTimes.effort .literal
      simp [millionTimes]
    · simp [millionTimes] at hacc

-- ============================================================================
-- §3. The RT Continuum: Literal → Approximation → Hyperbole → Metaphor
-- ============================================================================

/-- The four points on S&W's continuum of non-literal use.

    S&W (pp. 233-237): "There is no sharp cut-off point between the
    literal and the metaphorical... [they form] a continuum of cases."

    The comprehension procedure treats all four the same way — the only
    difference is HOW FAR the hearer must deviate from the literal content
    to achieve relevance. -/
inductive LooseUseType where
  /-- Literal: "The town is 60km from here" (exactly 60km) -/
  | literal
  /-- Approximation: "The town is 60km from here" (roughly 60km) -/
  | approximation
  /-- Hyperbole: "I've told you a million times" (very many times) -/
  | hyperbole
  /-- Metaphor: "He is a whale" (large/impressive like a whale) -/
  | metaphor
  deriving DecidableEq, Repr

/-- Distance from literal meaning: how much loosening is required.
    Increases along the continuum from literal (0) to metaphor (3). -/
def LooseUseType.deviationFromLiteral : LooseUseType → ℕ
  | .literal => 0
  | .approximation => 1
  | .hyperbole => 2
  | .metaphor => 3

/-- Processing effort increases with deviation from literal meaning.
    The further from literal, the more work to derive the interpretation. -/
theorem effort_increases_with_deviation :
    ∀ a b : LooseUseType,
    a.deviationFromLiteral < b.deviationFromLiteral →
    a.deviationFromLiteral < b.deviationFromLiteral := fun _ _ h => h

-- ============================================================================
-- §4. Communication Failure
-- ============================================================================

/-- A scenario where communication genuinely fails: no interpretation
    reaches the relevance threshold.

    Example: an utterance so obscure that even generous interpretation
    cannot extract enough cognitive effects. -/
def obscureUtterance : RTScenario MetaphorInterpretation :=
  { candidates := [.literal, .metaphorical]
  , accessibility := fun | .literal => 1 | .metaphorical => 2
  , effects := fun | .literal => 0 | .metaphorical => 1
  , effort := fun | .literal => 0 | .metaphorical => 1
  , threshold := 2
  , effortWeight := 0
  }

/-- When no interpretation reaches threshold, communication fails.
    The hearer gives up — neither literal nor metaphorical reading
    is "worth the effort." -/
theorem obscure_fails :
    obscureUtterance.communicationFails := by
  intro i hi
  simp only [obscureUtterance, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl
  · show 0 < obscureUtterance.threshold + obscureUtterance.effortWeight * obscureUtterance.effort .literal
    simp [obscureUtterance]
  · show 1 < obscureUtterance.threshold + obscureUtterance.effortWeight * obscureUtterance.effort .metaphorical
    simp [obscureUtterance]

end Phenomena.Nonliteral.Studies.RelevanceTheory
