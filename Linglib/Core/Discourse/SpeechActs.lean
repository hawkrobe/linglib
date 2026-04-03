import Linglib.Core.Context.Tower
import Linglib.Core.Semantics.CommonGround

/-!
# Speech Acts and Intentional States
@cite{searle-1969} @cite{searle-1979} @cite{searle-1983} @cite{kaplan-1989} @cite{lakoff-1970}
@cite{speas-tenny-2003} @cite{brandom-1994} @cite{gunlogson-2001}
@cite{krifka-2015} @cite{bring-gunlogson-2000} @cite{romero-2024}

Unified infrastructure for speech acts, Intentional states, and their
relationship — the parallel that @cite{searle-1983} argues is constitutive
of both language and mind.

## The Central Parallel

@cite{searle-1983}'s core thesis: Intentional states (beliefs, desires,
intentions) and speech acts (assertions, orders, promises) share identical
logical structure:

- **Speech acts**: F(p) — illocutionary force F + propositional content p
- **Intentional states**: S(r) — psychological mode S + representative content r

Four points of similarity:
1. The content/mode distinction applies to both
2. Direction of fit applies to both
3. Sincerity conditions link them: performing F(p) expresses S(r)
4. Conditions of satisfaction are determined by content + direction of fit

## Organization

- **§ 1. Discourse Roles**: speaker/addressee (framework-agnostic)
- **§ 2. Illocutionary Mood**: the pragmatic act classification
- **§ 3. Direction of Fit**: Searle's key classification principle
- **§ 4. Illocutionary Taxonomy**: the five classes derived from direction of fit
- **§ 5. Psychological Mode**: the S in S(r), linked to mood via sincerity conditions
- **§ 6. Causal Self-Referentiality**: the "by way of" requirement on intentions
- **§ 7. Intentional States**: S(r) as a type
- **§ 8. Discourse Commitments**: the public trace of speech acts
- **§ 9. Source-Marked Commitments**: Gunlogson's epistemic source tagging
-/

namespace Core.Discourse

open Core.Context
open Core.Proposition (BProp)

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
-- § 5. Psychological Mode — S(r)
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
-- § 6. Causal Self-Referentiality (@cite{searle-1983}, Ch. 3)
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
-- § 7. Intentional State
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
  content : BProp W

/-- Conditions of satisfaction: what must obtain for the state to be satisfied.
    These are *identical* to the content — not a separate component. -/
def IntentionalState.conditionsOfSatisfaction {W : Type*}
    (s : IntentionalState W) : BProp W :=
  s.content

-- ════════════════════════════════════════════════════════════════
-- § 8. Discourse Commitments (@cite{krifka-2015} @cite{brandom-1994})
-- ════════════════════════════════════════════════════════════════

namespace Commitment

/-- An agent's public discourse commitments: a list of propositions
    the agent has publicly committed to.

    Following @cite{krifka-2015}: the commitment slate tracks what an agent
    is publicly committed to, which may diverge from what they privately
    believe (as in lying, hedging, or performing).

    In @cite{searle-1983}'s terms: commitment is the *public* direction-of-fit
    obligation created by performing a speech act. Asserting p creates a
    mind-to-world commitment (the speaker is responsible if p is false);
    promising p creates a world-to-mind commitment (the speaker is
    responsible if p is unfulfilled). -/
structure CommitmentSlate (W : Type*) where
  /-- The propositions the agent is publicly committed to -/
  commitments : List (BProp W)

namespace CommitmentSlate


variable {W : Type*}

/-- The empty commitment slate: no public commitments. -/
def empty : CommitmentSlate W := ⟨[]⟩

/-- Add a commitment to the slate. -/
def add (s : CommitmentSlate W) (p : BProp W) : CommitmentSlate W :=
  ⟨p :: s.commitments⟩

/-- Retract a commitment (remove first occurrence).

    Not all theories support retraction. Stalnaker's CG model has no
    retraction mechanism; Krifka and Brandom do. -/
def retract (s : CommitmentSlate W) (p : BProp W) [BEq (BProp W)] : CommitmentSlate W :=
  ⟨s.commitments.erase p⟩

/-- Convert commitments to a context set: the worlds compatible with
    all committed propositions. -/
def toContextSet (s : CommitmentSlate W) : BProp W :=
  λ w => s.commitments.all (λ p => p w)

/-- Check if the slate entails a proposition (holds at all compatible worlds). -/
def entails (s : CommitmentSlate W) (p : BProp W) (worlds : List W) : Bool :=
  worlds.all λ w => !s.commitments.all (λ q => q w) || p w

/-- Empty slate is trivial: all worlds are compatible. -/
theorem empty_trivial (w : W) : (empty : CommitmentSlate W).toContextSet w = true := by
  simp only [empty, toContextSet, List.all_nil]

/-- Adding a commitment restricts the context set. -/
theorem add_restricts (s : CommitmentSlate W) (p : BProp W) (w : W) :
    (s.add p).toContextSet w → s.toContextSet w := by
  simp only [add, toContextSet, List.all_cons, Bool.and_eq_true]
  exact And.right

/-- Adding a commitment entails the added proposition. -/
theorem add_entails (s : CommitmentSlate W) (p : BProp W) (w : W) :
    (s.add p).toContextSet w → p w = true := by
  simp only [add, toContextSet, List.all_cons, Bool.and_eq_true]
  exact And.left

end CommitmentSlate

-- ════════════════════════════════════════════════════════════════
-- § 9. Source-Marked Commitments (@cite{gunlogson-2001})
-- ════════════════════════════════════════════════════════════════

/-- The source of a discourse commitment.

    @cite{gunlogson-2001}: commitments are marked by their epistemic source.
    The source determines challengeability: self-generated commitments
    can be challenged by the addressee; other-generated commitments
    can be challenged by the speaker. -/
inductive CommitmentSource where
  /-- Commitment generated from agent's own evidence/beliefs -/
  | selfGenerated
  /-- Commitment attributed to another participant -/
  | otherGenerated
  deriving DecidableEq, Repr, Inhabited

/-- A commitment tagged with its source. -/
structure TaggedCommitment (W : Type*) where
  /-- The propositional content -/
  content : BProp W
  /-- How the commitment was generated -/
  source : CommitmentSource

/-- A source-tagged commitment slate. -/
structure TaggedSlate (W : Type*) where
  /-- The tagged commitments -/
  commitments : List (TaggedCommitment W)

namespace TaggedSlate


variable {W : Type*}

/-- The empty tagged slate. -/
def empty : TaggedSlate W := ⟨[]⟩

/-- Add a tagged commitment. -/
def add (s : TaggedSlate W) (p : BProp W) (src : CommitmentSource) : TaggedSlate W :=
  ⟨⟨p, src⟩ :: s.commitments⟩

/-- Get all self-generated commitments. -/
def selfGenerated (s : TaggedSlate W) : List (BProp W) :=
  s.commitments.filter (·.source == .selfGenerated) |>.map (·.content)

/-- Get all other-generated commitments. -/
def otherGenerated (s : TaggedSlate W) : List (BProp W) :=
  s.commitments.filter (·.source == .otherGenerated) |>.map (·.content)

/-- Convert to a plain (untagged) commitment slate. -/
def toSlate (s : TaggedSlate W) : CommitmentSlate W :=
  ⟨s.commitments.map (·.content)⟩

/-- Convert to context set (ignoring source tags). -/
def toContextSet (s : TaggedSlate W) : BProp W :=
  s.toSlate.toContextSet

end TaggedSlate

/-- Contextual evidence bias.

    Expectation about p induced by evidence available in the current
    discourse situation (@cite{bring-gunlogson-2000}). Used as:
    - A felicity condition on rising declaratives
    - A bias dimension for polar questions -/
inductive ContextualEvidence where
  /-- Current context provides evidence for p. -/
  | forP
  /-- No contextual evidence either way. -/
  | neutral
  /-- Current context provides evidence against p. -/
  | againstP
  deriving DecidableEq, Repr

end Commitment

-- ════════════════════════════════════════════════════════════════
-- § 10. Preparatory Conditions (@cite{searle-1969} @cite{francik-clark-1985})
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
-- § 11. Verification
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

-- ════════════════════════════════════════════════════════════════
-- § 12. HasContextSet Instance
-- ════════════════════════════════════════════════════════════════

open Core.CommonGround in
/-- A commitment slate projects to a context set: the worlds compatible
    with all committed propositions. -/
instance {W : Type*} : HasContextSet (Commitment.CommitmentSlate W) W where
  toContextSet s := λ w => s.toContextSet w

end Core.Discourse
