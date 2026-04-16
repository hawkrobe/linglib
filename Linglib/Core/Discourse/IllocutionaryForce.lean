import Linglib.Core.Context.Tower

/-!
# Illocutionary Force: F in F(p)
@cite{searle-1969} @cite{searle-1979} @cite{searle-1983} @cite{lakoff-1970}
@cite{francik-clark-1985}

The pragmatic-act side of the Searlean parallel: discourse roles, illocutionary
mood, direction of fit, the five-class taxonomy, and preparatory conditions.
The Intentional-state counterpart S(r) — psychological mode, sincerity
conditions, causal self-referentiality, and IntentionalState — lives in
`Core/Discourse/Intentionality.lean`. Discourse commitments live in
`Core/Discourse/Commitment.lean`.

## Organization

- **§ 1. Discourse Roles**: speaker/addressee (framework-agnostic)
- **§ 2. Illocutionary Mood**: the pragmatic act classification
- **§ 3. Direction of Fit**: Searle's key classification principle
- **§ 4. Illocutionary Taxonomy**: the five classes derived from direction of fit
- **§ 5. Preparatory Conditions**: Searle's felicity conditions on directives
- **§ 6. Verification**
-/

namespace Core.Discourse

open Core.Context

-- ════════════════════════════════════════════════════════════════
-- § 1. Discourse Roles
-- ════════════════════════════════════════════════════════════════

/-- The two fundamental discourse participants. `.addressee` matches
    `KContext.addressee` (not `.listener` as in Semantics.Dynamic). -/
inductive DiscourseRole where
  | speaker
  | addressee
  deriving DecidableEq, Repr, Inhabited

-- ════════════════════════════════════════════════════════════════
-- § 2. Illocutionary Mood
-- ════════════════════════════════════════════════════════════════

/-- Illocutionary mood — the speech-act force of an utterance.

    Distinct from `GramMood` (indicative/subjunctive morphology) and the
    Minimalist `SAPMood` (configurational). This classifies the pragmatic
    act performed — the F in F(p). -/
inductive IllocutionaryMood where
  | declarative
  | interrogative
  | imperative
  | promissive
  | exclamative
  deriving DecidableEq, Repr, Inhabited

/-- Which participant holds epistemic authority for a given illocutionary mood.

    @cite{lakoff-1970}: in declaratives, imperatives, and promissives the speaker is the
    seat of knowledge; in interrogatives the addressee is. -/
def moodAuthority : IllocutionaryMood → DiscourseRole
  | .declarative   => .speaker
  | .interrogative  => .addressee
  | .imperative     => .speaker
  | .promissive     => .speaker
  | .exclamative    => .speaker

/-- Resolve a discourse role to a concrete entity via a ContextTower,
    reading from the origin (speech-act context).
    `.speaker -> tower.origin.agent`, `.addressee -> tower.origin.addressee`. -/
def resolveRole {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    DiscourseRole → E
  | .speaker   => tower.origin.agent
  | .addressee => tower.origin.addressee

-- ════════════════════════════════════════════════════════════════
-- § 3. Direction of Fit (@cite{searle-1983}, Ch. 1 §2)
-- ════════════════════════════════════════════════════════════════

/-- Direction of fit: how responsibility for matching is distributed
    between the Intentional state (or speech act) and the world.

    @cite{searle-1983}'s key classification principle. The metaphor: if a
    shopper's list doesn't match what's in the cart, the *list* is at fault
    (mind-to-world). If a builder's blueprint doesn't match the building,
    the *building* is at fault (world-to-mind). -/
inductive DirectionOfFit where
  /-- Mind-to-world: the state must match independently existing reality.
      Beliefs, perceptions, assertions. If wrong, the *state* is at fault. -/
  | mindToWorld
  /-- World-to-mind: the world must be changed to match the state.
      Desires, intentions, orders, promises.
      If unfulfilled, the *world* is at fault. -/
  | worldToMind
  /-- Null direction: the state presupposes the truth of its content but
      imposes no fit responsibility. Expressives (apologies, congratulations). -/
  | null
  /-- Double direction: both mind-to-world and world-to-mind simultaneously.
      Declarations bring about a state of affairs by representing it as
      obtaining. -/
  | double
  deriving DecidableEq, Repr, Inhabited

-- ════════════════════════════════════════════════════════════════
-- § 4. Illocutionary Taxonomy (@cite{searle-1979})
-- ════════════════════════════════════════════════════════════════

/-- @cite{searle-1979}'s five basic categories of illocutionary acts,
    derived from the mind's representational capacities. These are
    exhaustive and mutually exclusive. Restated in @cite{searle-1983}
    Ch. 6: "the taxonomy is fundamentally a reflection of the various
    ways in which representations can have directions of fit." -/
inductive SearleClass where
  /-- We tell people how things are (assertions, statements, descriptions). -/
  | assertive
  /-- We try to get people to do things (orders, commands, requests). -/
  | directive
  /-- We commit ourselves to doing things (promises, vows, pledges). -/
  | commissive
  /-- We bring about changes by representing them as obtaining (verdicts, appointments). -/
  | declaration
  /-- We express feelings about presupposed states of affairs (apologies, congratulations). -/
  | expressive
  deriving DecidableEq, Repr, Inhabited

/-- Direction of fit for each illocutionary class. The five classes are
    *derived* from the possible directions of fit. -/
def SearleClass.directionOfFit : SearleClass → DirectionOfFit
  | .assertive   => .mindToWorld
  | .directive    => .worldToMind
  | .commissive   => .worldToMind
  | .declaration  => .double
  | .expressive   => .null

/-- Map `IllocutionaryMood` to Searle class. Not injective: both directives
    (imperative) and commissives (promissive) share world-to-mind fit. -/
def IllocutionaryMood.searleClass : IllocutionaryMood → SearleClass
  | .declarative   => .assertive
  | .interrogative  => .directive
  | .imperative     => .directive
  | .promissive     => .commissive
  | .exclamative    => .expressive

/-- Direction of fit for an illocutionary mood, derived via Searle class. -/
def IllocutionaryMood.directionOfFit (m : IllocutionaryMood) : DirectionOfFit :=
  m.searleClass.directionOfFit

-- ════════════════════════════════════════════════════════════════
-- § 5. Preparatory Conditions (@cite{searle-1969} @cite{francik-clark-1985})
-- ════════════════════════════════════════════════════════════════

/-- Preparatory conditions for directive speech acts.

    @cite{searle-1969}: for a request to be felicitous, the hearer must
    satisfy certain preconditions — ability to comply and willingness to
    comply. @cite{francik-clark-1985} show that speakers design indirect
    requests to target the specific preparatory condition most at risk,
    refining "ability" into a subsumption hierarchy:

    ```
    ability
    ├── knowledge
    │   ├── memory       ("Do you remember?")
    │   └── perception   ("Did you see/hear/notice?")
    └── permission       ("Are you allowed?")
    willingness           ("Would you mind?")
    ```

    More specific conditions correspond to more specific (less direct)
    request forms. -/
inductive PreparatoryCondition where
  /-- Hearer is able to perform the requested act (general). -/
  | ability
  /-- Hearer knows the relevant information. Subtype of ability. -/
  | knowledge
  /-- Hearer remembers the information. Subtype of knowledge. -/
  | memory
  /-- Hearer has perceived the relevant source. Subtype of knowledge. -/
  | perception
  /-- Hearer is permitted to perform the act. Subtype of ability. -/
  | permission
  /-- Hearer is willing to perform the act. Independent of ability. -/
  | willingness
  deriving DecidableEq, Repr

/-- Subsumption: `c₁.subsumes c₂` iff satisfying c₂ entails satisfying c₁.

    Memory and perception are subtypes of knowledge; knowledge and
    permission are subtypes of ability. Willingness is independent. -/
def PreparatoryCondition.subsumes : PreparatoryCondition → PreparatoryCondition → Bool
  -- reflexive
  | .ability, .ability | .knowledge, .knowledge | .memory, .memory
  | .perception, .perception | .permission, .permission
  | .willingness, .willingness => true
  -- ability subsumes its subtypes
  | .ability, .knowledge | .ability, .memory
  | .ability, .perception | .ability, .permission => true
  -- knowledge subsumes its subtypes
  | .knowledge, .memory | .knowledge, .perception => true
  | _, _ => false

theorem PreparatoryCondition.subsumes_refl (c : PreparatoryCondition) :
    c.subsumes c = true := by cases c <;> rfl

/-- The specificity chain: memory/perception → knowledge → ability. -/
theorem PreparatoryCondition.specificity_chain :
    PreparatoryCondition.ability.subsumes .knowledge = true ∧
    PreparatoryCondition.knowledge.subsumes .memory = true ∧
    PreparatoryCondition.knowledge.subsumes .perception = true ∧
    PreparatoryCondition.ability.subsumes .permission = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Willingness is independent of ability: neither subsumes the other. -/
theorem PreparatoryCondition.willingness_independent :
    PreparatoryCondition.ability.subsumes .willingness = false ∧
    PreparatoryCondition.willingness.subsumes .ability = false := ⟨rfl, rfl⟩

/-- Directives are the speech act class that has preparatory conditions
    on the hearer's ability and willingness. -/
theorem directive_has_preparatory_conditions :
    SearleClass.directive.directionOfFit = .worldToMind := rfl

-- ════════════════════════════════════════════════════════════════
-- § 6. Verification
-- ════════════════════════════════════════════════════════════════

-- Epistemic authority
theorem epistemic_authority_declarative :
    moodAuthority .declarative = .speaker := rfl

theorem epistemic_authority_interrogative :
    moodAuthority .interrogative = .addressee := rfl

theorem resolve_speaker_is_agent {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    resolveRole tower .speaker = tower.origin.agent := rfl

theorem resolve_addressee_is_addressee {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    resolveRole tower .addressee = tower.origin.addressee := rfl

/-- Discourse role resolution is invariant under tower push: discourse
    roles reflect speech-act participants (from origin), not embedded ones. -/
theorem resolveRole_shift_invariant {W E P T : Type*}
    (tower : ContextTower (KContext W E P T))
    (σ : ContextShift (KContext W E P T)) (r : DiscourseRole) :
    resolveRole (tower.push σ) r = resolveRole tower r := by
  cases r <;> simp only [resolveRole, ContextTower.push_origin]

-- Direction of fit per Searle class
theorem assertive_mind_to_world :
    SearleClass.assertive.directionOfFit = .mindToWorld := rfl

theorem directive_world_to_mind :
    SearleClass.directive.directionOfFit = .worldToMind := rfl

theorem commissive_world_to_mind :
    SearleClass.commissive.directionOfFit = .worldToMind := rfl

theorem declaration_double :
    SearleClass.declaration.directionOfFit = .double := rfl

theorem expressive_null :
    SearleClass.expressive.directionOfFit = .null := rfl

end Core.Discourse
