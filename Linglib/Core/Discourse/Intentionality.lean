import Linglib.Core.Discourse.IllocutionaryForce

/-!
# Intentional States: S in S(r)
@cite{searle-1983}

The Intentional-state side of the Searlean parallel: psychological mode,
sincerity conditions linking speech acts to states, causal self-referentiality,
and the `IntentionalState` type.

## The Central Parallel (@cite{searle-1983})

Intentional states (beliefs, desires, intentions) and speech acts share
identical logical structure:

- **Speech acts**: F(p) — illocutionary force F + propositional content p
- **Intentional states**: S(r) — psychological mode S + representative content r

Performing F(p) sincerely *expresses* the corresponding S(r). The conditions
of satisfaction of the speech act are identical to those of the expressed
state. The illocutionary side (F, direction of fit, Searle taxonomy) lives
in `Core/Discourse/IllocutionaryForce.lean`.

## Organization

- **§ 1. Psychological Mode** — the S in S(r)
- **§ 2. Sincerity Conditions** — the F→S bridge
- **§ 3. Causal Self-Referentiality** — the "by way of" requirement
- **§ 4. Intentional State** — S(r) as a type
- **§ 5. Verification**
-/

namespace Core.Discourse

open Core.Mood (IllocutionaryMood)

-- ════════════════════════════════════════════════════════════════
-- § 1. Psychological Mode — S(r)
-- ════════════════════════════════════════════════════════════════

/-- Named psychological modes: the "S" in @cite{searle-1983}'s S(r) notation.

    Parallel to illocutionary force "F" in F(p) for speech acts. Each mode
    has a direction of fit and may or may not be causally self-referential.

    @cite{searle-1983}, Ch. 1: belief, desire, and intention are the
    prototypical modes. Perception (Ch. 2) is a causally self-referential
    mode that plays a key role in the theory's account of how the mind
    relates to the world. -/
inductive PsychMode where
  /-- Bel(p): satisfied iff p obtains. Not self-referential —
      HOW p came to obtain is irrelevant (Ch. 1, p. 8). -/
  | belief
  /-- Des(p): satisfied iff p comes about. Not self-referential —
      HOW p is brought about is irrelevant (Ch. 1, p. 8). -/
  | desire
  /-- Int(p): satisfied iff p is brought about BY WAY OF carrying out
      this intention. Self-referential: state→world (Ch. 3, pp. 85–86). -/
  | intention
  /-- Per(p): satisfied iff the object/state of affairs CAUSES this
      experience. Self-referential: world→state (Ch. 2; Ch. 3, p. 91). -/
  | perception
  /-- Expressive states (pleasure, sorrow, etc.): presuppose the truth
      of their content but impose no fit responsibility (Ch. 1, pp. 7–8). -/
  | expressive
  deriving DecidableEq, Repr, Inhabited

/-- Direction of fit for each psychological mode.

    Beliefs and perceptions: mind-to-world (the state must match reality).
    Desires and intentions: world-to-mind (reality must match the state).
    Expressives: null (presuppose truth, no fit responsibility). -/
def PsychMode.directionOfFit : PsychMode → DirectionOfFit
  | .belief     => .mindToWorld
  | .desire     => .worldToMind
  | .intention  => .worldToMind
  | .perception => .mindToWorld
  | .expressive => .null

-- ════════════════════════════════════════════════════════════════
-- § 2. Sincerity Conditions — the F→S bridge
-- ════════════════════════════════════════════════════════════════

/-- The sincerity condition: performing a speech act with mood F necessarily
    expresses the corresponding Intentional state S, and the conditions of
    satisfaction of the speech act are identical to those of the expressed state.

    @cite{searle-1983}, Ch. 1 §3: you can't say "It's snowing but I don't
    believe it's snowing" — the assertion *eo ipso* expresses the belief.
    Ch. 6, p. 174: "the conditions of satisfaction of the sincerity condition"
    are "identical with the conditions of satisfaction" of the speech act. -/
def sincerityCondition : IllocutionaryMood → PsychMode
  | .declarative   => .belief      -- asserting p expresses Bel(p)
  | .interrogative  => .desire     -- asking expresses Des(addressee answer)
  | .imperative     => .desire     -- ordering expresses Des(hearer do A)
  | .promissive     => .intention  -- promising expresses Int(speaker do A)
  | .exclamative    => .expressive -- exclaiming expresses feeling

-- ════════════════════════════════════════════════════════════════
-- § 3. Causal Self-Referentiality (@cite{searle-1983}, Ch. 3)
-- ════════════════════════════════════════════════════════════════

/-- Causal self-referentiality: whether the Intentional state must itself
    figure in the causal chain producing its conditions of satisfaction.

    Beliefs: no self-referentiality — satisfied iff the state of affairs obtains.
    Intentions: self-referential — "my arm goes up *as a result of* this intention."
    Perceptions: self-referential in reverse — the object must *cause* the experience. -/
inductive CausalSelfRef where
  /-- Not self-referential: satisfaction depends only on the state of affairs
      obtaining. Example: beliefs. -/
  | none
  /-- State-to-world: the state must cause its conditions of satisfaction.
      Example: intentions — "by way of carrying out *this* intention." -/
  | stateToWorld
  /-- World-to-state: the conditions of satisfaction must cause the state.
      Example: perceptions — the object causes the visual experience. -/
  | worldToState
  deriving DecidableEq, Repr

/-- Causal self-referentiality for each psychological mode.

    @cite{searle-1983}, Ch. 3 (table on p. 91): self-referentiality is NOT
    determined by direction of fit alone. Both beliefs and perceptions have
    mind-to-world fit, but only perceptions are self-referential. Both
    desires and intentions have world-to-mind fit, but only intentions are.

    - Perception: the object must *cause* the experience (world→state)
    - Intention: the intention must *cause* its conditions of satisfaction (state→world)
    - Belief/Desire: satisfaction depends only on whether the state of affairs obtains -/
def PsychMode.causalSelfRef : PsychMode → CausalSelfRef
  | .belief     => .none
  | .desire     => .none
  | .intention  => .stateToWorld
  | .perception => .worldToState
  | .expressive => .none

-- ════════════════════════════════════════════════════════════════
-- § 4. Intentional State
-- ════════════════════════════════════════════════════════════════

/-- An Intentional state: psychological mode + representative content.

    @cite{searle-1983}, Ch. 1: "every Intentional state consists of a
    representative content in a psychological mode." Symbolized S(r).

    Conditions of satisfaction are *determined by* the content under the
    direction of fit given by the mode — they are internal to the state. -/
structure IntentionalState (W : Type*) where
  /-- The psychological mode (belief, desire, intention, ...) -/
  mode : PsychMode
  /-- The representative content -/
  content : W → Prop

/-- Conditions of satisfaction: what must obtain for the state to be satisfied.
    These are *identical* to the content — not a separate component. -/
def IntentionalState.conditionsOfSatisfaction {W : Type*}
    (s : IntentionalState W) : W → Prop :=
  s.content

-- ════════════════════════════════════════════════════════════════
-- § 5. Verification
-- ════════════════════════════════════════════════════════════════

-- Sincerity conditions
theorem sincerity_assertion :
    (sincerityCondition .declarative).directionOfFit = .mindToWorld := rfl

theorem sincerity_order :
    (sincerityCondition .imperative).directionOfFit = .worldToMind := rfl

theorem sincerity_promise :
    (sincerityCondition .promissive).directionOfFit = .worldToMind := rfl

theorem sincerity_exclamation :
    (sincerityCondition .exclamative).directionOfFit = .null := rfl

/-- @cite{searle-1983}'s central parallel: the direction of fit of the
    sincerity condition matches the direction of fit of the speech act class.

    Asserting p expresses a mind-to-world state (belief); ordering p expresses
    a world-to-mind state (desire); promising p expresses a world-to-mind
    state (intention). This is constitutive (@cite{searle-1983}, Ch. 1 §3). -/
theorem sincerity_direction_matches_class :
    ∀ m : IllocutionaryMood,
    (sincerityCondition m).directionOfFit = m.directionOfFit := by
  intro m; cases m <;> rfl

-- Causal self-referentiality (on PsychMode, not DirectionOfFit)
theorem beliefs_not_self_referential :
    PsychMode.belief.causalSelfRef = .none := rfl

theorem desires_not_self_referential :
    PsychMode.desire.causalSelfRef = .none := rfl

theorem intentions_self_referential :
    PsychMode.intention.causalSelfRef = .stateToWorld := rfl

theorem perceptions_self_referential :
    PsychMode.perception.causalSelfRef = .worldToState := rfl

/-- @cite{searle-1983}'s key insight (Ch. 3, p. 91): causal self-referentiality
    is NOT determined by direction of fit alone. Beliefs and perceptions
    share mind-to-world fit, but only perceptions are self-referential. -/
theorem self_ref_independent_of_direction :
    PsychMode.belief.directionOfFit = PsychMode.perception.directionOfFit ∧
    PsychMode.belief.causalSelfRef ≠ PsychMode.perception.causalSelfRef :=
  ⟨rfl, nofun⟩

/-- Conditions of satisfaction are internal to the content — not a separate
    component. This `rfl` proof IS the formalization of @cite{searle-1983}'s
    claim (Ch. 1, p. 12): "the Intentional content determines the conditions
    of satisfaction." -/
theorem conditions_are_content {W : Type*} (s : IntentionalState W) :
    s.conditionsOfSatisfaction = s.content := rfl

end Core.Discourse
