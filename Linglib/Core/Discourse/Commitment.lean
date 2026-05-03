import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Discourse.Roles

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
- **§ 4. Speaker-Indexed Commitments** (@cite{krifka-2015} `S⊢φ` notation)
- **§ 5. HasContextSet Instance**
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

-- ════════════════════════════════════════════════════════════════
-- § 4. CommitmentGrade typeclass (the commitment-grade algebra)
-- ════════════════════════════════════════════════════════════════

/-- A **commitment grade** is the value type for a graded commitment.
    The typeclass exposes the operations the substrate needs to lift
    binary-only operators (`bipolarQuestion`, `negatedQuestionLow`,
    `toContextSet`) to arbitrary graded weights.

    Instances:
    - `G = Prop`: binary commitment (Krifka, F&B, Brandom, Stalnaker).
      `complement := Not`, `support := id`.
    - `G = Bool`: Bool-valued commitment (Cohen-Krifka 2014 worked
      example with denegation markers). `complement := !`,
      `support := (· = true)`.
    - `G = ℚ` or `G = ℝ`: probabilistic / distributional (deferred
      until a study consumer; would set `complement := (1 - ·)`,
      `support := (· > 0)` or threshold-based).

    The typeclass is small on purpose — only `complement` and `support`
    are required, both per-grade-value (not per-weight-function). The
    per-weight projection follows by composition. -/
class HasSupport (G : Type*) where
  /-- Support predicate: which grades count as "actively committing".
      For `Prop`: identity. For `Bool`: `· = true`. For `ℝ_≥0`:
      `· > 0`. For `ℚ`: `· > 0` (or threshold). Used to project a
      weighted commitment to a binary context-set constraint.

      The minimal axiom-free typeclass for context-set projection.
      `toContextSet` and `toCommitment` consume only this. -/
  support : G → Prop

class CommitmentGrade (G : Type*) extends HasSupport G where
  /-- Negation/complement of a grade. For `Prop`: `Not`; for `Bool`: `!`;
      for `ℚ ∈ [0,1]`: `1 - ·`. Used to construct the "no" branch of
      bipolar questions and the negated content of low-negation questions. -/
  complement : G → G
  /-- Complement is the propositional dual of support: a grade's
      complement is supportable iff the grade itself is not. Holds for
      Prop (LEM-classically) and Bool (definitionally). Does NOT hold
      for ℝ in general (e.g., `0 < 1 - 1/2 = 1/2` AND `0 < 1/2`); the
      law restricts `CommitmentGrade` instances to "Bool-shaped" grades.
      Anderson 2021's ℝ-distributional CG provides only `HasSupport ℝ`,
      not `CommitmentGrade ℝ`. -/
  support_complement_iff_not_support : ∀ g : G, support (complement g) ↔ ¬ support g

instance : HasSupport Prop where
  support := id

instance : CommitmentGrade Prop where
  complement := Not
  support_complement_iff_not_support _ := Iff.rfl

/-! ## No `Bool` instance — by design

A `CommitmentGrade Bool` / `HasSupport Bool` instance was provided in
the original typeclass landing (0.230.658). We removed it because no
consumer needed it post-CohenKrifka2014's migration from
`G = Bool` (decide-style) to `G = Prop` (structural-theorem style).

The Bool instance invited a "decide-and-done" worked-example shape that
the user explicitly steered away from: linglib's thesis is structural
theorems quantifying over content, not concrete-fixture
`decide`-reduces-to-this units. Removing the instance signals that the
typeclass is for *formal grades* (Prop, NNReal, lattice elements with
laws), not for *computational* ones. Consumers that genuinely need Bool
(e.g., for explicit `decide`-based smoke tests) can declare a local
instance with full responsibility for its consequences.

Other potential grades (`ℚ`, `ℝ`, `NNReal`, lattices) provide
instances at the consumer's site (e.g., Anderson 2021's
`HasSupport ℝ` for distributional CG; Anderson does NOT provide
`CommitmentGrade ℝ` because the involution law fails for unrestricted
real-valued weights). -/

-- ════════════════════════════════════════════════════════════════
-- § 5. Speaker-Indexed Commitments (@cite{krifka-2015}, p. 332;
--      @cite{lauer-2013} doxastic/preferential force)
-- ════════════════════════════════════════════════════════════════

/-! ## Polymorphic indexed commitments

`IndexedWeightedCommitment W G` is the substrate's polymorphic
commitment type. Three orthogonal axes:

- `committer : DiscourseRole` — who is committing (Krifka 2015's `S₁`/`S₂`).
- `force : CommitmentForce` — doxastic (belief, declarative) vs preferential
  (Lauer 2013, Condoravdi-Lauer 2011). The doxastic case covers
  Krifka/Farkas-Bruce/Brandom assertion; the preferential case covers
  Lauer's imperative-as-PEP analysis.
- `weight : W → G` (commit) or `content : W → Prop` (refuse) — per-world
  grade in `G`. The `G` parameter selects framework granularity:
  - `G = Prop`: binary commitment (Krifka, Farkas-Bruce, Brandom, Stalnaker).
  - `G = ℝ`:   distributional CG (@cite{anderson-2021}).
  - `G = ℚ`:   credence-bounded (Lauer simplification).

The Krifka 2015 default is the binary doxastic case, exposed via the
`IndexedCommitment W` abbreviation and smart constructors that hide the
`force` and (via `G = Prop`) weight-vs-content asymmetry.
-/

/-- A polymorphic indexed commitment: who commits, with what force, with
    what per-world weight (or, for refusal, what content).

    The `commit` constructor models `S⊢φ` — agent publicly commits to φ
    with weight `weight : W → G` per world.
    The `refuse` constructor models `¬S⊢φ` — agent explicitly does NOT
    commit to content `φ`, distinct from committing to `¬φ`. The
    refuse-content stays at `W → Prop` because refusal is a meta-fact
    about the agent's commitment slate, not about the world.

    The `force` field has no current consumer that explicitly passes
    `.preferential` (every binary call site defaults to `.doxastic` via
    the smart constructors). The next demand for the `.preferential`
    branch is @cite{condoravdi-lauer-2012}'s imperative-as-PEP analysis;
    a study file using `force := .preferential` would be the first
    consumer to exercise this axis. -/
inductive IndexedWeightedCommitment (W : Type*) (G : Type*) where
  /-- `S⊢φ` with per-world grade in G: agent committed to φ at weight `weight`. -/
  | commit (committer : DiscourseRole) (force : CommitmentForce)
           (weight : W → G)
  /-- `¬S⊢φ`: agent explicitly NOT committed to φ. Pragmatically
      weaker than `commit committer .doxastic (fun w => ¬ φ w)`. -/
  | refuse (committer : DiscourseRole) (force : CommitmentForce)
           (content : W → Prop)

namespace IndexedWeightedCommitment

variable {W G : Type*}

/-- The agent who committed (or refused to commit). -/
def committer : IndexedWeightedCommitment W G → DiscourseRole
  | .commit c _ _ => c
  | .refuse c _ _ => c

/-- The commitment force (doxastic / preferential). -/
def force : IndexedWeightedCommitment W G → CommitmentForce
  | .commit _ f _ => f
  | .refuse _ f _ => f

/-- Holds for `commit`, fails for `refuse`. -/
def IsCommit : IndexedWeightedCommitment W G → Prop
  | .commit _ _ _ => True
  | .refuse _ _ _ => False

instance : DecidablePred (@IsCommit W G) := fun ic => by
  cases ic <;> (unfold IsCommit; infer_instance)

/-- Project to the propositional constraint imposed on the context set,
    polymorphic in `G` via `[CommitmentGrade G]`.

    A `commit` excludes worlds where the per-world weight is NOT in
    support (i.e., where `support (weight w)` is false). A `refuse`
    imposes no exclusion (it's a meta-fact about the agent, not about
    the world).

    For `G = Prop`: `support := id`, so `commit committer force φ`
    projects to `φ` itself — recovering the binary `toCommitment`.
    For `G = Bool`: `support := (· = true)`, so `commit ... weight`
    projects to `fun w => weight w = true`. For other `G` (ℚ, ℝ),
    the typeclass's `support` predicate determines the projection. -/
def toCommitment [HasSupport G] :
    IndexedWeightedCommitment W G → (W → Prop)
  | .commit _ _ weight => fun w => HasSupport.support (weight w)
  | .refuse _ _ _ => fun _ => True

/-- `toCommitment` of a `commit` reduces to `support` of the per-world
    weight. The `@[simp]` form makes downstream proofs robust to
    reformulation of `HasSupport.support` (e.g. if the `Prop`
    instance changed from `support := id` to something else, proofs
    that rely on `rfl`-reducing through `support` would break silently;
    proofs that rewrite via this lemma keep working). -/
@[simp]
theorem toCommitment_commit [HasSupport G]
    (c : DiscourseRole) (f : CommitmentForce) (weight : W → G) (w : W) :
    (IndexedWeightedCommitment.commit c f weight).toCommitment w =
      HasSupport.support (weight w) := rfl

/-- `toCommitment` of a `refuse` is trivially true. -/
@[simp]
theorem toCommitment_refuse [HasSupport G]
    (c : DiscourseRole) (f : CommitmentForce) (φ : W → Prop) (w : W) :
    (IndexedWeightedCommitment.refuse (G := G) c f φ).toCommitment w = True := rfl

end IndexedWeightedCommitment

/-- Binary speaker-indexed commitment — the `G = Prop` specialisation.
    This is the Krifka 2015 default, used throughout the binary
    commitment-space substrate. The general type is
    `IndexedWeightedCommitment W G`. -/
abbrev IndexedCommitment (W : Type*) := IndexedWeightedCommitment W Prop

namespace IndexedCommitment

variable {W : Type*}

/-- Smart constructor for the doxastic binary commit case. Equivalent
    to `IndexedWeightedCommitment.commit committer .doxastic content`.
    Existing call sites that don't need preferential force or non-Prop
    grade use this. The `@[match_pattern]` attribute lets pattern-position
    use of `IndexedCommitment.commit c φ` resolve through the abbrev to
    the underlying 3-arg constructor. -/
abbrev commit (committer : DiscourseRole) (content : W → Prop) :
    IndexedCommitment W :=
  IndexedWeightedCommitment.commit committer .doxastic content

/-- Smart constructor for the doxastic binary refuse case. -/
abbrev refuse (committer : DiscourseRole) (content : W → Prop) :
    IndexedCommitment W :=
  IndexedWeightedCommitment.refuse committer .doxastic content

/-- The propositional content of the commitment (binary case).
    For `commit`, the weight `W → Prop` IS the content; for `refuse`,
    it's the refused content. -/
def content : IndexedCommitment W → (W → Prop)
  | IndexedWeightedCommitment.commit _ _ φ => φ
  | IndexedWeightedCommitment.refuse _ _ φ => φ

/-- Project to the propositional constraint imposed on the context set.
    A `commit` excludes worlds incompatible with the weight; a `refuse`
    imposes no exclusion (it's a meta-fact about the agent, not about
    the world). For the CG-as-set view, only `commit`-cases narrow.

    This is what makes `refuse` pragmatically weaker than `commit (¬φ)`:
    `refuse` projects to `True` (no narrowing), while `commit (¬φ)`
    projects to `¬φ` (narrows out φ-worlds). -/
def toCommitment : IndexedCommitment W → (W → Prop)
  | IndexedWeightedCommitment.commit _ _ φ => φ
  | IndexedWeightedCommitment.refuse _ _ _ => fun _ => True

end IndexedCommitment

end Commitment

-- ════════════════════════════════════════════════════════════════
-- § 5. HasContextSet Instance
-- ════════════════════════════════════════════════════════════════

open Core.CommonGround in
/-- A commitment slate projects to a context set: the worlds compatible
    with all committed propositions. -/
instance {W : Type*} : HasContextSet (Commitment.CommitmentSlate W) W where
  toContextSet s := λ w => s.toContextSet w

end Core.Discourse
