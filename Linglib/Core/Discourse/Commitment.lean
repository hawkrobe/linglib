import Linglib.Core.Semantics.CommonGround

/-!
# Discourse Commitments
@cite{krifka-2015} @cite{brandom-1994} @cite{gunlogson-2001} @cite{bring-gunlogson-2000}

The public trace of speech acts: commitment slates, source-tagged commitments,
and contextual evidence bias. Pairs with `Core/Discourse/IllocutionaryForce.lean`
(F in F(p)) and `Core/Discourse/Intentionality.lean` (S in S(r)).

Where Intentional states are private, commitments are public — the
publicly-tracked obligations created by performing speech acts. Asserting p
creates a mind-to-world commitment; promising p creates a world-to-mind one.

## Organization

- **§ 1. Commitment Slates** (@cite{krifka-2015}, @cite{brandom-1994})
- **§ 2. Source-Marked Commitments** (@cite{gunlogson-2001})
- **§ 3. Contextual Evidence** (@cite{bring-gunlogson-2000})
- **§ 4. HasContextSet Instance**
-/

namespace Core.Discourse

namespace Commitment

-- ════════════════════════════════════════════════════════════════
-- § 1. Commitment Slates (@cite{krifka-2015} @cite{brandom-1994})
-- ════════════════════════════════════════════════════════════════

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
  commitments : List (W → Prop)

namespace CommitmentSlate

variable {W : Type*}

/-- The empty commitment slate: no public commitments. -/
def empty : CommitmentSlate W := ⟨[]⟩

/-- Add a commitment to the slate. -/
def add (s : CommitmentSlate W) (p : W → Prop) : CommitmentSlate W :=
  ⟨p :: s.commitments⟩

/-- Convert commitments to a context set: the worlds compatible with
    all committed propositions. -/
def toContextSet (s : CommitmentSlate W) : W → Prop :=
  λ w => ∀ p ∈ s.commitments, p w

/-- Check if the slate entails a proposition (holds at all compatible worlds). -/
def entails (s : CommitmentSlate W) (p : W → Prop) : Prop :=
  ∀ w, (∀ q ∈ s.commitments, q w) → p w

/-- Empty slate is trivial: all worlds are compatible. -/
theorem empty_trivial (w : W) : (empty : CommitmentSlate W).toContextSet w := by
  intro p hp
  exact absurd hp (List.not_mem_nil)

/-- Adding a commitment restricts the context set. -/
theorem add_restricts (s : CommitmentSlate W) (p : W → Prop) (w : W) :
    (s.add p).toContextSet w → s.toContextSet w := by
  intro h q hq
  exact h q (List.mem_cons_of_mem p hq)

/-- Adding a commitment entails the added proposition. -/
theorem add_entails (s : CommitmentSlate W) (p : W → Prop) (w : W) :
    (s.add p).toContextSet w → p w := by
  intro h
  exact h p List.mem_cons_self

end CommitmentSlate

-- ════════════════════════════════════════════════════════════════
-- § 2. Source-Marked Commitments (@cite{gunlogson-2001})
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

/-- The **modal force** of a discourse commitment: doxastic (act-as-if-believe)
    vs preferential (act-as-if-effectively-prefer).

    @cite{condoravdi-lauer-2012} @cite{lauer-2013} introduce the preferential
    side; @cite{portner-2018} (commitments to priorities) and @cite{rudin-2018}
    (teleological common ground) develop the doxastic/preferential parallel
    in scoreboard models; @cite{deo-2025-bara} lifts the existing
    `CommitmentSource` source/dependent distinction to apply to *both* forces.

    Default `.doxastic` matches the historical assumption that bare
    `TaggedCommitment` means doxastic — preserves all existing call sites. -/
inductive CommitmentForce where
  /-- Doxastic commitment: speaker publicly commits to acting as though
      they believe the content. The standard assertion case. -/
  | doxastic
  /-- Preferential commitment: speaker publicly commits to acting as
      though the content is among their effective preferences
      (@cite{condoravdi-lauer-2012}). The standard imperative-as-PEP /
      C&L analysis case. -/
  | preferential
  deriving DecidableEq, Repr, Inhabited

/-- A commitment tagged with its epistemic source and modal force.

    Two orthogonal axes:
    * `source` (selfGenerated / otherGenerated): whose evidence supports it
      (@cite{gunlogson-2001}).
    * `commitmentForce` (doxastic / preferential): whether it is a
      belief-like or preference-like commitment (@cite{condoravdi-lauer-2012},
      @cite{lauer-2013}, lifted across `source` by @cite{deo-2025-bara}).

    `commitmentForce` defaults to `.doxastic` so existing two-argument
    anonymous-constructor calls (`⟨content, source⟩`) and existing
    `TaggedSlate.add s p src` invocations continue to type-check. -/
structure TaggedCommitment (W : Type*) where
  /-- The propositional content -/
  content : W → Prop
  /-- How the commitment was generated -/
  source : CommitmentSource
  /-- Whether the commitment is doxastic (default) or preferential. -/
  commitmentForce : CommitmentForce := .doxastic

/-- A source-tagged commitment slate. -/
structure TaggedSlate (W : Type*) where
  /-- The tagged commitments -/
  commitments : List (TaggedCommitment W)

namespace TaggedSlate

variable {W : Type*}

/-- The empty tagged slate. -/
def empty : TaggedSlate W := ⟨[]⟩

/-- Add a tagged commitment. The optional `force` parameter defaults to
    `.doxastic` for backward compatibility with the pre-`CommitmentForce`
    API; pass `.preferential` for C&L-style preferential commitments. -/
def add (s : TaggedSlate W) (p : W → Prop) (src : CommitmentSource)
    (force : CommitmentForce := .doxastic) : TaggedSlate W :=
  ⟨⟨p, src, force⟩ :: s.commitments⟩

/-- Get all self-generated commitments (any force). -/
def selfGenerated (s : TaggedSlate W) : List (W → Prop) :=
  s.commitments.filter (·.source == .selfGenerated) |>.map (·.content)

/-- Get all other-generated commitments (any force). -/
def otherGenerated (s : TaggedSlate W) : List (W → Prop) :=
  s.commitments.filter (·.source == .otherGenerated) |>.map (·.content)

/-- Get all doxastic commitments (any source). The contribution to an
    agent's belief-like commitments — the input to a Stalnakerian
    common ground when intersected across agents. -/
def doxasticContents (s : TaggedSlate W) : List (W → Prop) :=
  s.commitments.filter (·.commitmentForce == .doxastic) |>.map (·.content)

/-- Get all preferential commitments (any source). The contribution to an
    agent's preference-like commitments — the input to a "joint
    preferences" set (@cite{deo-2025-bara} eq. 17c) when intersected
    across agents. -/
def preferentialContents (s : TaggedSlate W) : List (W → Prop) :=
  s.commitments.filter (·.commitmentForce == .preferential) |>.map (·.content)

/-- Dependent commitments (any force) — `DC_x_dep` in
    @cite{deo-2025-bara}'s notation. The `Set`-typed counterpart of
    the legacy `otherGenerated` (List-typed); use this for new code
    and proofs. -/
def dependent (s : TaggedSlate W) : Set (W → Prop) :=
  { p | ∃ c ∈ s.commitments, c.source = .otherGenerated ∧ c.content = p }

/-- Independent (self-sourced) commitments (any force) — `DC_x_ind`. -/
def independent (s : TaggedSlate W) : Set (W → Prop) :=
  { p | ∃ c ∈ s.commitments, c.source = .selfGenerated ∧ c.content = p }

/-- Dependent doxastic commitments — the (`source = .otherGenerated`,
    `commitmentForce = .doxastic`) cell of the 2×2 cross. The agent's
    `DC_x_dep_dox` in @cite{deo-2025-bara}'s notation. -/
def dependentDoxastic (s : TaggedSlate W) : Set (W → Prop) :=
  { p | ∃ c ∈ s.commitments,
        c.source = .otherGenerated ∧ c.commitmentForce = .doxastic ∧ c.content = p }

/-- Dependent preferential commitments — `DC_x_dep_pref`. The 2×2 cell
    targeted by @cite{deo-2025-bara}'s bərə convention (eq. 20). -/
def dependentPreferential (s : TaggedSlate W) : Set (W → Prop) :=
  { p | ∃ c ∈ s.commitments,
        c.source = .otherGenerated ∧ c.commitmentForce = .preferential ∧ c.content = p }

/-- Independent doxastic commitments — `DC_x_ind_dox`. The standard
    Stalnakerian assertion-driven cell. -/
def independentDoxastic (s : TaggedSlate W) : Set (W → Prop) :=
  { p | ∃ c ∈ s.commitments,
        c.source = .selfGenerated ∧ c.commitmentForce = .doxastic ∧ c.content = p }

/-- Independent preferential commitments — `DC_x_ind_pref`. The
    @cite{condoravdi-lauer-2012} imperative-as-PEP cell. -/
def independentPreferential (s : TaggedSlate W) : Set (W → Prop) :=
  { p | ∃ c ∈ s.commitments,
        c.source = .selfGenerated ∧ c.commitmentForce = .preferential ∧ c.content = p }

/-- Convert to a plain (untagged) commitment slate. -/
def toSlate (s : TaggedSlate W) : CommitmentSlate W :=
  ⟨s.commitments.map (·.content)⟩

/-- Convert to context set (ignoring source tags). -/
def toContextSet (s : TaggedSlate W) : W → Prop :=
  s.toSlate.toContextSet

end TaggedSlate

-- ════════════════════════════════════════════════════════════════
-- § 3. Contextual Evidence (@cite{bring-gunlogson-2000})
-- ════════════════════════════════════════════════════════════════

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
-- § 4. HasContextSet Instance
-- ════════════════════════════════════════════════════════════════

open Core.CommonGround in
/-- A commitment slate projects to a context set: the worlds compatible
    with all committed propositions. -/
instance {W : Type*} : HasContextSet (Commitment.CommitmentSlate W) W where
  toContextSet s := λ w => s.toContextSet w

end Core.Discourse
