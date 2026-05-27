import Linglib.Discourse.IllocutionaryForce

/-!
# Intentional States: S in S(r)
@cite{searle-1983}

The Intentional-state side of the Searlean F(p) / S(r) parallel:
`PsychMode`, `sincerityCondition` (the F → S bridge), `CausalSelfRef`,
and `IntentionalState`. Performing F(p) sincerely expresses the
corresponding S(r); conditions of satisfaction transfer.
-/

namespace Discourse

open Semantics.Mood (IllocutionaryMood)

-- ════════════════════════════════════════════════════════════════
-- § 1. Psychological Mode — S(r)
-- ════════════════════════════════════════════════════════════════

/-- Psychological modes: the "S" in @cite{searle-1983}'s S(r). -/
inductive PsychMode where
  /-- Bel(p): satisfied iff p obtains. -/
  | belief
  /-- Des(p): satisfied iff p comes about. -/
  | desire
  /-- Int(p): satisfied iff p is brought about by carrying out the intention. -/
  | intention
  /-- Per(p): satisfied iff the object causes this experience. -/
  | perception
  /-- Expressive: presupposes truth, no fit responsibility. -/
  | expressive
  deriving DecidableEq, Repr, Inhabited

/-- Direction of fit for each psychological mode. -/
def PsychMode.directionOfFit : PsychMode → DirectionOfFit
  | .belief     => .mindToWorld
  | .desire     => .worldToMind
  | .intention  => .worldToMind
  | .perception => .mindToWorld
  | .expressive => .null

-- ════════════════════════════════════════════════════════════════
-- § 2. Sincerity Conditions — the F→S bridge
-- ════════════════════════════════════════════════════════════════

/-- Sincerity condition: performing a speech act with mood F expresses
    the corresponding Intentional state S. -/
def sincerityCondition : IllocutionaryMood → PsychMode
  | .declarative   => .belief      -- asserting p expresses Bel(p)
  | .interrogative  => .desire     -- asking expresses Des(addressee answer)
  | .imperative     => .desire     -- ordering expresses Des(hearer do A)
  | .promissive     => .intention  -- promising expresses Int(speaker do A)
  | .exclamative    => .expressive -- exclaiming expresses feeling

-- ════════════════════════════════════════════════════════════════
-- § 3. Causal Self-Referentiality (@cite{searle-1983}, Ch. 3)
-- ════════════════════════════════════════════════════════════════

/-- Whether an Intentional state must figure in the causal chain
    producing its conditions of satisfaction (@cite{searle-1983} Ch. 3). -/
inductive CausalSelfRef where
  /-- Not self-referential (beliefs, desires). -/
  | none
  /-- The state must cause its conditions of satisfaction (intentions). -/
  | stateToWorld
  /-- The conditions of satisfaction must cause the state (perceptions). -/
  | worldToState
  deriving DecidableEq, Repr

/-- Causal self-referentiality for each psychological mode.
    Not determined by direction of fit alone: belief and perception
    share mind-to-world fit, but only perception is self-referential. -/
def PsychMode.causalSelfRef : PsychMode → CausalSelfRef
  | .belief     => .none
  | .desire     => .none
  | .intention  => .stateToWorld
  | .perception => .worldToState
  | .expressive => .none

-- ════════════════════════════════════════════════════════════════
-- § 4. Intentional State
-- ════════════════════════════════════════════════════════════════

/-- An Intentional state S(r): psychological mode + representative content. -/
structure IntentionalState (W : Type*) where
  mode : PsychMode
  content : W → Prop

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

/-- The sincerity condition's direction of fit matches the speech act's
    (Searle's central parallel). -/
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

/-- Causal self-referentiality is not determined by direction of fit
    alone: belief and perception share mind-to-world fit but differ in
    self-referentiality. -/
theorem self_ref_independent_of_direction :
    PsychMode.belief.directionOfFit = PsychMode.perception.directionOfFit ∧
    PsychMode.belief.causalSelfRef ≠ PsychMode.perception.causalSelfRef :=
  ⟨rfl, nofun⟩

end Discourse
