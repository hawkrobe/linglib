import Linglib.Discourse.CommonGround
import Linglib.Discourse.SpeechAct.Basic
import Linglib.Discourse.Commitment.Basic

/-!
# Commitment Space Semantics

[krifka-2015] [cohen-krifka-2014]

Krifka's commitment-space framework: the discourse state is a tree — the
root (√C) is the current CommonGround holding speaker-indexed commitments `S⊢φ`,
and continuations are proposed future states from questions.

- Assertion narrows every state with `commit speaker φ`.
- Monopolar questions add a `commit addressee φ` continuation.
- Bipolar questions add two non-contradictory sibling continuations
  (`commit addressee φ` and `commit addressee ¬φ`).
- High-negation questions (`Didn't I win?`) add a `refuse addressee φ`
  continuation, distinct from low-negation (`Did I not win?`) which adds
  `commit addressee ¬φ`.

Per-agent commitment slates track individual public commitments, enabling
the commitment/belief separation (lying, hedging).

## Speaker indexing

The paper's central primitive is the Frege turnstile `S⊢φ` (p. 332):
assertion is responsibility-undertaking, so what enters the CommonGround is
"speaker S is committed to the truth of φ", not bare φ. The substrate uses
`Discourse.Commitment.IndexedCommitment` to model this — the root
holds indexed commitments, projected to a flat context set via
`IndexedCommitment.toCommitment` for the CommonGround-as-set view.

## Sibling files

`Discourse/LayeredAssertion.lean` houses Krifka 2020's
TP/JP/ComP/ActP layered-clause framework. The two files are independent
(neither imports the other); study files target whichever fits.

## Substrate scope

The substrate is **two-role discourse with doxastic/preferential force**.
Out of scope (would need substrate extensions):

- **Brandom-style scorecards** (Brandom 1994): commitment indexed by both a
  *keeper* and a *scorer* (per-keeper-per-scorer scoring). The substrate's
  single `committer : DiscourseRole` is keeper-only.
- **Searle's full 5-force taxonomy** (assertive, directive, commissive,
  expressive, declaration): collapsed here to doxastic/preferential per
  the [lauer-2013] duality. Expressives (wishes, exclamatives) and
  declarations (performatives) are not modelled.
- **Time-indexed commitments** (Lauer 2013 PB/PEP carry a `t` index): the
  substrate has no time index; `rejectFirst` is the closest proxy for
  rescission. True time-indexed commitment dynamics need a separate layer.
- **Anderson 2021 distributional CommonGround**: a probability distribution
  over worlds, hosted as `PMF W` in `Discourse/DistributionalCG.lean`. It is
  *not* routed through the commitment-space substrate: a `CommitmentSpace W ℝ`
  would carry unconstrained per-world reals (no sum-to-one, no normalisation),
  losing exactly the structure Anderson's entropy/KL criteria depend on. The
  two models of the conversational scoreboard are kept distinct.

## Citation discipline

Equation/page citations to [krifka-2015] throughout this file (eqs.
1, 2, 3, 5, 6, 7, 9, 10, 14, 23, 27, 29, 30, 38, 39, 44, 45 with their
respective pages 329-343) were verified against the SALT 25 paper PDF
when added (cf. CHANGELOG entries 0.230.652–0.230.654). Flag drift on
re-audit if substrate operators are renamed or restructured.

-/

namespace Discourse.Krifka

open Discourse.Commitment
  (CommitmentSlate IndexedCommitment IndexedWeightedCommitment CommitmentForce
   HasSupport CommitmentGrade)
open Discourse (DiscourseRole)
open CommonGround (ContextSet)
open Semantics.Mood (IllocutionaryMood)

-- ════════════════════════════════════════════════════
-- § 1. Commitment Space: Tree Structure ([krifka-2015], eq. (2), p. 329)
-- ════════════════════════════════════════════════════

/-- Agent type for two-participant discourse — abbreviation for the
    framework-agnostic `Discourse.DiscourseRole`. The alias name
    `KAgent` mirrors Krifka's `S₁`/`S₂` notation; semantically it IS
    `DiscourseRole` (no separate inductive, no bridge function). -/
abbrev KAgent := DiscourseRole

/-- A commitment space ([krifka-2015], eq. (2), p. 329).

    A set of commitment states organized as root + continuations:

    - **root** (√C): the current commitment state — a list of speaker-indexed
      commitments `S⊢φ` (`IndexedCommitment.commit`) or refusals `¬S⊢φ`
      (`IndexedCommitment.refuse`). All worlds compatible with the
      `commit`-projected propositions are "live".
    - **continuations**: proposed future states, each extending the root
      with additional commitments. Added by questions, resolved by acceptance
      (one becomes the new root) or rejection (one is pruned).

    ## Correspondence to Krifka's set-theoretic model

    Krifka's eq. (2) p. 329: `C is a commitment space if C is a set of
    commitment states, ∩C ≠ ∅ and ∩C ∈ C`. The set of states represented
    by this structure is `root :: continuations` — `root` IS √C (= ∩C,
    always present as a state in C), and `continuations` are the
    additional non-root states. Krifka's `{√C} ∪ X` operands in eqs. (23)
    and (27) correspond to keeping `root` as the always-present floor
    while unioning state-sets into `continuations`. The `rejectFirst`
    operation realises Krifka's ℜ retraction (eq. 10, p. 331): pruning a
    proposed continuation leaves √C as the only remaining floor, which is
    exactly the `{√C}` disjunct.

    ## Krifka's key operations

    - Assert `C + S⊢φ` (eq. (1) and (3), p. 329): adds `commit S φ` to root
      and continuations, narrowing every state.
    - Monopolar question `C + ?φ` (eq. (27), p. 336):
      `{√C} ∪ (C + S₂⊢φ)` — preserve root, propose addressee committing to φ.
    - Bipolar question (eq. (23), p. 335):
      `{√C} ∪ (C + S₂⊢φ) ∪ (C + S₂⊢¬φ)` — two non-contradictory siblings.
    - Accept: take a continuation as the new root.
    - Reject: prune a continuation (= return to `{√C}` disjunct).

    The tree structure captures the assertion/question asymmetry:
    assertions modify the root (the CommonGround changes), while questions only
    add continuations (the CommonGround is preserved until acceptance). -/
structure CommitmentSpace (W : Type*) (G : Type*) where
  /-- Root commitment state √C: indexed commitments currently in the CommonGround.
      The grade type `G` lets the same shape host binary (G = Prop),
      distributional (G = ℝ), or credence-bounded (G = ℚ) commitments. -/
  root : List (IndexedWeightedCommitment W G)
  /-- Proposed future states. Questions add these; acceptance promotes
      one to root. Each continuation is a list of indexed commitments
      that extends (narrows) the root. -/
  continuations : List (List (IndexedWeightedCommitment W G))

namespace CommitmentSpace

variable {W G : Type*}

/-- The empty commitment space: no commitments, no continuations. -/
def empty : CommitmentSpace W G := ⟨[], []⟩

/-- Assert weight `weight` on behalf of `committer`
    ([krifka-2015], eq. (1) and (3), p. 329).

    `C + S⊢φ`: adds `commit committer force weight` to the root and to
    every continuation. Any accepted continuation will also entail the
    weight (with the speaker index recorded). The `force` defaults to
    `.doxastic` (Krifka's standard declarative case); pass `.preferential`
    for the [lauer-2013] imperative-as-PEP case. -/
def assert (cs : CommitmentSpace W G) (committer : DiscourseRole)
           (weight : W → G) (force : CommitmentForce := .doxastic) :
    CommitmentSpace W G :=
  let ic : IndexedWeightedCommitment W G :=
    IndexedWeightedCommitment.commit committer force weight
  { root := ic :: cs.root
    continuations := cs.continuations.map (ic :: ·) }

/-- Monopolar question: propose that the **addressee** commit to weight
    `weight` ([krifka-2015], eq. (27), p. 336).

    `C + ?φ = {√C} ∪ (C + S₂⊢φ)`

    The root stays unchanged (CommonGround preserved). A new continuation is added
    where the addressee has committed to `weight`. Existing continuations
    are also extended by the addressee-commitment. The committer is
    hardcoded to `.addressee` per Krifka's discussion of (30), p. 337:
    "the ? head identifies the committer as S₂". -/
def monopolarQuestion (cs : CommitmentSpace W G) (weight : W → G)
                      (force : CommitmentForce := .doxastic) :
    CommitmentSpace W G :=
  let ic : IndexedWeightedCommitment W G :=
    IndexedWeightedCommitment.commit .addressee force weight
  { root := cs.root
    continuations := (ic :: cs.root) :: cs.continuations.map (ic :: ·) }

/-- High-negation polar question ([krifka-2015], §4 around eq. (39), p. 340).

    `Didn't I win?` = monopolar question with negation at the ComP layer
    (denegation of the addressee's commitment to φ). Proposes that the
    addressee NOT commit to φ — pragmatically weaker than committing to ¬φ.

    Polymorphic in `G`: the `refuse` constructor's content is always
    `W → Prop` (a meta-fact about the agent's slate, not a graded weight),
    so this operator works for any grade type.

    Per [krifka-2015] p. 340: "adding ¬S₂⊢φ to the commitment space
    precludes commitment to φ, but is compatible with commitment to ¬φ.
    Hence ¬S₂⊢φ is pragmatically weaker than S₂⊢¬φ." -/
def negatedQuestionHigh (cs : CommitmentSpace W G) (φ : W → Prop)
                         (force : CommitmentForce := .doxastic) :
    CommitmentSpace W G :=
  let ic : IndexedWeightedCommitment W G :=
    IndexedWeightedCommitment.refuse .addressee force φ
  { root := cs.root
    continuations := (ic :: cs.root) :: cs.continuations.map (ic :: ·) }

/-- The space has no open continuations (no unresolved proposals).

    Renamed from `isSettled` — Krifka has no stability/settledness notion
    in the paper; questions just "restrict legal continuations" (p. 335).
    The right characterization of this state is structural, not pragmatic. -/
def hasNoOpenContinuations : CommitmentSpace W G → Prop
  | ⟨_, []⟩ => True
  | ⟨_, _ :: _⟩ => False

instance : DecidablePred (@hasNoOpenContinuations W G) := fun cs => by
  cases cs with | mk _ conts =>
    cases conts <;> (unfold hasNoOpenContinuations; infer_instance)

/-- Accept the first continuation: it becomes the new root.
    The CommonGround is updated to the accepted proposal's content. -/
def acceptFirst : CommitmentSpace W G → CommitmentSpace W G
  | ⟨_, c :: rest⟩ => ⟨c, rest⟩
  | cs => cs

/-- Reject the first continuation: prune it.
    The CommonGround is unchanged; the proposal is discarded. -/
def rejectFirst : CommitmentSpace W G → CommitmentSpace W G
  | ⟨r, _ :: rest⟩ => ⟨r, rest⟩
  | cs => cs

/-- Denegate a speech act `~A`. Originally introduced by
    [cohen-krifka-2014] §2 (around eq. (26), p. 51, with full
    development through eqs. 31–38, pp. 52–53); inherited by
    [krifka-2015] eq. (5), p. 330.

    `C + ~A = C — [C + A]`: the result keeps √C and prunes the legal
    continuations that would arise from performing the act `A`. The
    caller supplies a Prop-valued predicate `actMarker` identifying the
    commitment that `A` would add to continuations, plus a
    `DecidablePred` instance for the filter. We keep continuations
    that do NOT contain a matching commitment.

    Concrete example: `denegate cs (fun ic => ic matches ASSERT(speaker, doxastic, φ))`
    is `~ASSERT(φ)` — the GRANT(¬φ) of [cohen-krifka-2014] eq. (38).

    Polymorphic in `G`. The predicate-based formulation avoids the
    soundness issue of trying to decide equality on `W → G` (generally
    undecidable for infinite W). -/
def denegate (actMarker : IndexedWeightedCommitment W G → Prop)
              [DecidablePred actMarker] (cs : CommitmentSpace W G) :
    CommitmentSpace W G :=
  { root := cs.root
    continuations := cs.continuations.filter
      (fun cont => decide (¬ ∃ ic ∈ cont, actMarker ic)) }

/-- Denegation preserves the root (CommonGround unchanged) — Krifka 2015 p. 330:
    "denegation does not change the root of the commitment space, but
    prunes its legal developments." -/
@[simp]
theorem denegate_preserves_root (cs : CommitmentSpace W G)
    (actMarker : IndexedWeightedCommitment W G → Prop)
    [DecidablePred actMarker] :
    (cs.denegate actMarker).root = cs.root := rfl

/-- Denegation is idempotent: filtering twice with the same marker is
    the same as filtering once (`List.filter_filter` over the same
    predicate). Worth noting because Krifka's set-difference semantics
    has the same property: `(C - X) - X = C - X`. -/
theorem denegate_idempotent (cs : CommitmentSpace W G)
    (actMarker : IndexedWeightedCommitment W G → Prop)
    [DecidablePred actMarker] :
    (cs.denegate actMarker).denegate actMarker = cs.denegate actMarker := by
  cases cs with | mk r conts =>
    simp only [denegate, List.filter_filter, Bool.and_self]

/-- Denegation never grows the continuation list — `List.filter` is
    length-monotone. -/
theorem denegate_continuation_count_le (cs : CommitmentSpace W G)
    (actMarker : IndexedWeightedCommitment W G → Prop)
    [DecidablePred actMarker] :
    (cs.denegate actMarker).continuations.length ≤ cs.continuations.length := by
  cases cs with | mk r conts =>
    exact List.length_filter_le _ _

/-- If no continuation matches the marker, denegation is the identity.
    The substrate-level form of "you can only denegate what's actually
    in play". -/
theorem denegate_no_match_eq_self (cs : CommitmentSpace W G)
    (actMarker : IndexedWeightedCommitment W G → Prop)
    [DecidablePred actMarker]
    (h : ∀ cont ∈ cs.continuations, ¬ ∃ ic ∈ cont, actMarker ic) :
    cs.denegate actMarker = cs := by
  cases cs with | mk r conts =>
    simp only [denegate]
    congr 1
    apply List.filter_eq_self.mpr
    intro cont hcont
    simp only [decide_eq_true_eq]
    exact h cont hcont

/-- Converse of `denegate_no_match_eq_self`: every continuation that
    SURVIVES denegation does not match the marker. The structural fact
    that justifies calling `denegate` "filtering out matching paths". -/
theorem denegate_surviving_no_match (cs : CommitmentSpace W G)
    (actMarker : IndexedWeightedCommitment W G → Prop)
    [DecidablePred actMarker] :
    ∀ cont ∈ (cs.denegate actMarker).continuations,
      ¬ ∃ ic ∈ cont, actMarker ic := by
  intro cont hcont
  cases cs with | mk r conts =>
    simp only [denegate, List.mem_filter, decide_eq_true_eq] at hcont
    exact hcont.2

/-! ### Polymorphic operators via `[CommitmentGrade G]`

The following operators are polymorphic in `G` via the
`CommitmentGrade` typeclass (`Discourse/Commitment.lean` §4):
`bipolarQuestion` and `negatedQuestionLow` use `complement` to
construct the "no" branch; `toContextSet` and the force-aware variants
use `support` to project per-world weights to `Prop`.

Instances are provided for `G = Prop` (`complement := Not`,
`support := id`) and `G = Bool` (`complement := !`,
`support := (· = true)`). For other `G` (ℚ, ℝ), provide the instance
at the consumer's site.
-/

/-- Bipolar question: propose two sibling continuations, one where the
    addressee commits to φ and one where the addressee commits to
    `complement φ` ([krifka-2015], eq. (23), p. 335).

    `C + ?φ_bi = {√C} ∪ (C + S₂⊢φ) ∪ (C + S₂⊢¬φ)`

    Polymorphic in `G` via `[CommitmentGrade G]`'s `complement`. -/
def bipolarQuestion [CommitmentGrade G] (cs : CommitmentSpace W G)
    (φ : W → G) : CommitmentSpace W G :=
  let yes : IndexedWeightedCommitment W G :=
    .commit .addressee .doxastic φ
  let no  : IndexedWeightedCommitment W G :=
    .commit .addressee .doxastic (fun w => CommitmentGrade.complement (φ w))
  { root := cs.root
    -- Krifka eq. (23) is symmetric in φ and ¬φ: prior continuations
    -- propagate through BOTH the yes-branch and the no-branch.
    continuations := (yes :: cs.root) :: (no :: cs.root) ::
                      (cs.continuations.map (yes :: ·) ++
                       cs.continuations.map (no :: ·)) }

/-- Low-negation polar question ([krifka-2015], §4 around eq. (29), p. 339).

    `Did I not win?` = monopolar question with `complement φ` as TP content.
    Proposes that the addressee commit to ¬φ. Polymorphic in `G` via
    `[CommitmentGrade G]`'s `complement`. -/
def negatedQuestionLow [CommitmentGrade G] (cs : CommitmentSpace W G)
    (φ : W → G) : CommitmentSpace W G :=
  cs.monopolarQuestion (fun w => CommitmentGrade.complement (φ w))

/-- Context set from root: worlds compatible with all root commitments,
    projected via `IndexedWeightedCommitment.toCommitment` (which uses
    the typeclass's `support` predicate per-grade-value).

    Conflates doxastic and preferential commitments — both narrow
    the context set. For force-aware projections that separate the
    two attitudes (per [condoravdi-lauer-2012]), use
    `toDoxasticContextSet` / `toPreferentialContextSet`. -/
def toContextSet [HasSupport G] (cs : CommitmentSpace W G) :
    ContextSet W :=
  fun w => ∀ ic ∈ cs.root, IndexedWeightedCommitment.toCommitment ic w

/-- Doxastic-only context set: worlds compatible with the root's
    `force = .doxastic` commitments only (preferential commitments are
    ignored).

    Models [condoravdi-lauer-2012]'s `PB_w(Sp, p)` projection: "the
    public BELIEFS the speaker is committed to". A declarative assertion
    contributes here; an imperative utterance does not. -/
def toDoxasticContextSet [HasSupport G] (cs : CommitmentSpace W G) :
    ContextSet W :=
  fun w => ∀ ic ∈ cs.root,
    ic.force = .doxastic → IndexedWeightedCommitment.toCommitment ic w

/-- Preferential-only context set: worlds compatible with the root's
    `force = .preferential` commitments only (doxastic commitments are
    ignored).

    Models [condoravdi-lauer-2012]'s `PEP_w(Sp, p)` projection:
    "the public PREFERENCES the speaker is committed to act on". An
    imperative utterance contributes here; a declarative assertion does
    not. The two projections are independent (Lauer 2013 Ch. 5
    closure (5.33b) `pep(p) ∈ PB ⟺ p ∈ PEP` is a HIGHER-ORDER
    interaction not modeled by these flat projections). -/
def toPreferentialContextSet [HasSupport G] (cs : CommitmentSpace W G) :
    ContextSet W :=
  fun w => ∀ ic ∈ cs.root,
    ic.force = .preferential → IndexedWeightedCommitment.toCommitment ic w

/-- Sanity: the conflated `toContextSet` is the conjunction of the
    two force-projections. (`refuse` cases project to True regardless
    of force, so the doxastic and preferential projections agree on them.) -/
theorem toContextSet_eq_doxastic_and_preferential [HasSupport G]
    (cs : CommitmentSpace W G) (w : W) :
    cs.toContextSet w ↔
      cs.toDoxasticContextSet w ∧ cs.toPreferentialContextSet w := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro ic hic _
      exact h ic hic
    · intro ic hic _
      exact h ic hic
  · rintro ⟨hd, hp⟩ ic hic
    cases hf : ic.force
    · exact hd ic hic hf
    · exact hp ic hic hf

/-! ### Theorems -/

/-- Empty space has no open continuations. -/
theorem empty_no_open : (empty : CommitmentSpace W G).hasNoOpenContinuations :=
  True.intro

/-- Assertion preserves the no-open-continuations property
    (no new continuations are added by `assert`). -/
theorem assert_preserves_no_open (cs : CommitmentSpace W G) (_s : DiscourseRole)
    (_weight : W → G) (h : cs.hasNoOpenContinuations) :
    (cs.assert _s _weight).hasNoOpenContinuations := by
  cases cs with | mk r conts =>
    cases conts with
    | nil => exact True.intro
    | cons _ _ => exact h.elim

/-- Monopolar question creates an open continuation
    (negation of the no-open property). -/
theorem monopolar_opens (cs : CommitmentSpace W G) (_weight : W → G)
    (h : cs.hasNoOpenContinuations) :
    ¬ (cs.monopolarQuestion _weight).hasNoOpenContinuations := by
  cases cs with | mk r conts =>
    cases conts with
    | nil => exact id
    | cons _ _ => exact h.elim

/-- Accepting a monopolar question's sole continuation re-closes the space. -/
theorem accept_monopolar_closes (cs : CommitmentSpace W G) (weight : W → G)
    (h : cs.hasNoOpenContinuations) :
    (cs.monopolarQuestion weight).acceptFirst.hasNoOpenContinuations := by
  cases cs with | mk r conts =>
    cases conts with
    | nil => exact True.intro
    | cons _ _ => exact h.elim

/-- Root after assertion (binary case) contains the asserted indexed commitment. -/
theorem assert_in_root (cs : CommitmentSpace W Prop) (s : DiscourseRole)
    (φ : W → Prop) :
    IndexedCommitment.commit s φ ∈ (cs.assert s φ).root := by
  simp only [assert, IndexedCommitment.commit, List.mem_cons, true_or]

/-- Monopolar question preserves the root (CommonGround unchanged). -/
@[simp]
theorem monopolarQuestion_preserves_root (cs : CommitmentSpace W G)
    (weight : W → G) :
    (cs.monopolarQuestion weight).root = cs.root := rfl

/-- Bipolar question preserves the root (CommonGround unchanged). -/
@[simp]
theorem bipolarQuestion_preserves_root [CommitmentGrade G]
    (cs : CommitmentSpace W G) (φ : W → G) :
    (cs.bipolarQuestion φ).root = cs.root := rfl

end CommitmentSpace

/-- Krifka's discourse state: per-agent commitment slates + shared
    commitment space (tree).

    The commitment space tracks the shared discourse structure: what's in
    the CommonGround (root) and what's been proposed (continuations). Per-agent
    slates track individual public commitments, enabling the
    commitment/belief separation central to Krifka's theory. -/
structure KrifkaState (W : Type*) where
  /-- Speaker's individual commitment slate (binary, propositional). -/
  speakerCS : CommitmentSlate W
  /-- Addressee's individual commitment slate. -/
  addresseeCS : CommitmentSlate W
  /-- Shared commitment space (tree): CommonGround + proposed updates.
      Binary specialisation `CommitmentSpace W Prop` of the polymorphic
      `CommitmentSpace W G`. Future graded-state extensions
      (Lauer-credence, Anderson-distributional) belong in a separate
      `WeightedKrifkaState W G` rather than here. -/
  space : CommitmentSpace W Prop

namespace KrifkaState

variable {W : Type*}

/-- Initial state: no commitments, empty space. -/
def empty : KrifkaState W :=
  ⟨CommitmentSlate.empty, CommitmentSlate.empty, CommitmentSpace.empty⟩

/-- Krifka's commitment operator `+_S₁ S₁⊢p` ([krifka-2015], eq. (14), p. 332).

    Speaker (default) commits to p, narrowing the entire space and
    recording on the speaker's slate. Pass `committer := .addressee`
    for the addressee-commits case. The `force` defaults to `.doxastic`
    (declarative assertion); pass `.preferential` for the
    [condoravdi-lauer-2012] imperative-as-PEP analysis. -/
def assert (s : KrifkaState W) (p : W → Prop)
    (committer : DiscourseRole := .speaker)
    (force : CommitmentForce := .doxastic) : KrifkaState W :=
  match committer with
  | .speaker =>
    { s with
      speakerCS := s.speakerCS.add p
      space := s.space.assert .speaker p force }
  | .addressee =>
    { s with
      addresseeCS := s.addresseeCS.add p
      space := s.space.assert .addressee p force }

/-- Monopolar question ([krifka-2015], eq. (27), p. 336):
    speaker proposes that addressee commit to φ. -/
def monopolarQuestion (s : KrifkaState W) (φ : W → Prop) : KrifkaState W :=
  { s with space := s.space.monopolarQuestion φ }

/-- Bipolar question ([krifka-2015], eq. (23), p. 335):
    propose two sibling continuations (φ-commit and ¬φ-commit). -/
def bipolarQuestion (s : KrifkaState W) (φ : W → Prop) : KrifkaState W :=
  { s with space := s.space.bipolarQuestion φ }

/-- Low-negation polar question ([krifka-2015], §4): `Did I not win?`. -/
def negatedQuestionLow (s : KrifkaState W) (φ : W → Prop) : KrifkaState W :=
  { s with space := s.space.negatedQuestionLow φ }

/-- High-negation polar question ([krifka-2015], §4): `Didn't I win?`. -/
def negatedQuestionHigh (s : KrifkaState W) (φ : W → Prop) : KrifkaState W :=
  { s with space := s.space.negatedQuestionHigh φ }

/-- Accept the first continuation: it becomes the new CommonGround root. -/
def acceptContinuation (s : KrifkaState W) : KrifkaState W :=
  { s with space := s.space.acceptFirst }

/-- Reject the first continuation: prune it. -/
def rejectContinuation (s : KrifkaState W) : KrifkaState W :=
  { s with space := s.space.rejectFirst }

/-- Context set: from the commitment space root (= CommonGround), via
    `IndexedCommitment.toCommitment` projection. -/
def contextSet (s : KrifkaState W) : ContextSet W :=
  s.space.toContextSet

/-- The space has no open continuations. -/
def hasNoOpenContinuations (s : KrifkaState W) : Prop :=
  s.space.hasNoOpenContinuations

instance : DecidablePred (@hasNoOpenContinuations W) := fun s =>
  inferInstanceAs (Decidable s.space.hasNoOpenContinuations)

end KrifkaState

-- ════════════════════════════════════════════════════
-- § 2. KrifkaState theorems
-- ════════════════════════════════════════════════════

/-- Commitment Closure: assertion immediately narrows the commitment space.
    The root after asserting φ on behalf of `committer` is the original root
    with the indexed `commit committer φ` prepended.

    In the tree model, this is definitional: `assert` adds the indexed
    commitment to all nodes including the root. -/
theorem commitment_closure {W : Type*} (s : KrifkaState W) (p : W → Prop)
    (committer : DiscourseRole) :
    (s.assert p committer).space.root =
      IndexedCommitment.commit committer p :: s.space.root := by
  cases committer <;> rfl

/-- Questions don't change the CommonGround: the root is preserved. -/
theorem monopolarQuestion_preserves_cg {W : Type*} (s : KrifkaState W) (p : W → Prop) :
    (s.monopolarQuestion p).space.root = s.space.root := rfl

/-- Question then accept ≈ assert (on the root): accepting a monopolar
    question's sole continuation yields the same CommonGround as the addressee
    directly asserting φ.

    This connects the two modes of updating: direct assertion (committer
    imposes) and question-then-accept (speaker proposes, addressee accepts
    by committing themselves). The roots match because both produce
    `commit .addressee φ :: root₀`. -/
theorem monopolarQuestion_accept_eq_assert_addressee_root {W : Type*}
    (s : KrifkaState W) (p : W → Prop) (h : s.space.hasNoOpenContinuations) :
    (s.monopolarQuestion p).acceptContinuation.space.root =
    (s.assert p .addressee).space.root := by
  cases s with | mk sCS aCS space =>
    cases space with | mk r conts =>
      cases conts with
      | nil => rfl
      | cons _ _ => exact h.elim

-- ════════════════════════════════════════════════════
-- § 3. Actor vs Committer ([krifka-2015], p. 337 discussion of (30))
-- ════════════════════════════════════════════════════

/-- The two discourse roles in a speech act.

    Every speech act has an **actor** (who performs the act) and a
    **committer** (who undertakes the commitment). These can diverge:

    - Assertion: actor = speaker, committer = speaker
    - Monopolar question: actor = speaker, committer = addressee
      (the speaker proposes that the addressee commit)

    Per [krifka-2015] p. 337 around eq. (30): the `?` ActP head
    identifies the committer as `S₂`, the addressee; the actor of the
    speech act itself remains `S₁`. -/
structure ActorCommitter where
  actor     : KAgent
  committer : KAgent
  deriving DecidableEq, Repr

/-- In assertions, speaker is both actor and committer. -/
def assertionRoles : ActorCommitter :=
  ⟨.speaker, .speaker⟩

/-- In monopolar questions, speaker acts but addressee commits
    ([krifka-2015], p. 337 discussion of eq. (30)). -/
def questionRoles : ActorCommitter :=
  ⟨.speaker, .addressee⟩

/-- Assertions and questions differ in who commits. -/
theorem actor_committer_diverge :
    assertionRoles.actor = questionRoles.actor ∧
    assertionRoles.committer ≠ questionRoles.committer := by decide

-- ════════════════════════════════════════════════════
-- § 4. Speech Act Composition ([krifka-2015], eqs. (6)–(7), p. 330; §5)
-- ════════════════════════════════════════════════════

/-- A speech act in Krifka's framework: ActP content with its
    discourse function (assertion vs question).

    [krifka-2015] clause structure: ActP > ComP > TP (three layers).
    [krifka-2020] refines this to ActP > ComP > JP > TP. -/
structure SpeechAct (W : Type*) where
  /-- Propositional content (TP layer) -/
  content : W → Prop
  /-- Speech act type: assertion (.) or question (?) -/
  actType : IllocutionaryMood := .declarative
  /-- Actor/committer assignment -/
  roles : ActorCommitter := assertionRoles

/-- Construct a monopolar question speech act
    ([krifka-2015], eq. (27), p. 336):
    proposes a single continuation where the addressee commits to φ. -/
def monopolarQuestionAct {W : Type*} (φ : W → Prop) : SpeechAct W :=
  { content := φ, actType := .interrogative, roles := questionRoles }

/-- Complex speech act: conjunction or disjunction of atomic acts
    ([krifka-2015], eqs. (6)–(7), p. 330).

    [krifka-2015], §5: question tags involve composition of speech acts.
    The difference between matching and reverse tags is conjunction vs
    disjunction:
    - **conj**: both acts performed as one complex move (matching tag,
      eq. (44), p. 342)
    - **disj**: addressee chooses one continuation (reverse tag,
      eq. (45), p. 343) -/
inductive ComplexSpeechAct (W : Type*) where
  /-- A single speech act. -/
  | atom : SpeechAct W → ComplexSpeechAct W
  /-- Conjunction: both acts as one complex move (eq. (6), p. 330).
      "I have won the race, have I?" = ASSERT(rain) & ASK(rain). -/
  | conj : SpeechAct W → SpeechAct W → ComplexSpeechAct W
  /-- Disjunction: offer alternative continuations (eq. (7), p. 330).
      "I have won the race, haven't I?" = ASSERT(φ) ∨ ASK(¬φ). -/
  | disj : SpeechAct W → SpeechAct W → ComplexSpeechAct W

/-- Extract the component speech acts from a complex speech act. -/
def ComplexSpeechAct.components {W : Type*} : ComplexSpeechAct W → List (SpeechAct W)
  | .atom a => [a]
  | .conj a b => [a, b]
  | .disj a b => [a, b]

/-- A matching question tag ([krifka-2015], eq. (44), p. 342):
    conjunction of assertion + monopolar question with same content.

    "I have won the race, have I?" = speaker asserts φ AND asks addressee
    to confirm. Per Krifka p. 342: "this is **not** a move in which the
    speaker first makes an assertion and then asks the addressee to make
    the same assertion. Rather, the two speech acts are first conjoined,
    and then applied as one complex speech act to the commitment space."

    The committers diverge: speaker for the assertion-leg, addressee for
    the question-leg. -/
def matchingTag {W : Type*} (φ : W → Prop) : ComplexSpeechAct W :=
  .conj
    { content := φ, actType := .declarative, roles := assertionRoles }
    (monopolarQuestionAct φ)

/-- A reverse question tag ([krifka-2015], eq. (45), p. 343):
    disjunction of assertion + monopolar question with opposite content.

    "I have won the race, haven't I?" = speaker offers two continuations.
    The addressee picks one. -/
def reverseTag {W : Type*} (φ negφ : W → Prop) : ComplexSpeechAct W :=
  .disj
    { content := φ, actType := .declarative, roles := assertionRoles }
    (monopolarQuestionAct negφ)

/-- In a matching tag, the assertion and question share content. -/
theorem matching_tag_shared_content {W : Type*} (φ : W → Prop) :
    (matchingTag φ).components.map SpeechAct.content = [φ, φ] := rfl

/-- In a matching tag, the speaker is actor in both acts. -/
theorem matching_tag_same_actor {W : Type*} (φ : W → Prop) :
    (matchingTag φ).components.map (·.roles.actor) = [.speaker, .speaker] := rfl

/-- In a matching tag, the committers differ: speaker for assertion,
    addressee for question. -/
theorem matching_tag_committers_diverge {W : Type*} (φ : W → Prop) :
    (matchingTag φ).components.map (·.roles.committer) = [.speaker, .addressee] := rfl

/-- Matching tags are conjunctions, reverse tags are disjunctions. -/
theorem tag_type_distinction {W : Type*} (φ negφ : W → Prop) :
    (∃ a b, matchingTag φ = .conj a b) ∧
    (∃ a b, reverseTag φ negφ = .disj a b) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

namespace KrifkaState

variable {W : Type*}

/-- Apply a single atomic speech act, dispatching on `actType` and
    `roles.committer` to the right operator. -/
def applyAtom (s : KrifkaState W) (a : SpeechAct W) : KrifkaState W :=
  match a.actType with
  | .interrogative => s.monopolarQuestion a.content
  | _ => s.assert a.content a.roles.committer

/-- Apply a complex speech act to a Krifka state.

    For `.conj a b`: per Krifka eq. (6), `[C + 𝔄 & 𝔅] = [C + 𝔄] ∩ [C + 𝔅]
    ≈ C + 𝔄 + 𝔅 ≈ C + 𝔅 + 𝔄` — sequential composition is the paper's own
    approximation when there are no anaphoric ties. We compose sequentially.

    For `.disj a b`: speech-act disjunction (eq. (7), p. 330) is
    `[C + 𝔄] ∪ [C + 𝔅]` on commitment-space sets; the union of two
    list-shaped continuation structures is non-trivial and may produce
    a non-rooted space (per Krifka's prose on Figure 5, p. 330). Left
    as `sorry` to avoid silently returning a wrong answer. Reverse-tag
    worked examples are blocked on this; the structural theorem
    `reverse_tag_is_disjunction` does not depend on `applyComplex`. -/
def applyComplex (s : KrifkaState W) : ComplexSpeechAct W → KrifkaState W
  | .atom a => s.applyAtom a
  | .conj a b => (s.applyAtom a).applyAtom b
  | .disj _ _ => sorry
  -- TODO: speech-act disjunction (Krifka eq. (7), p. 330) requires lifting
  -- list-of-list continuations to a set-union semantics; currently no
  -- consumer needs this. Implement when the first reverse-tag worked
  -- example lands.

end KrifkaState

-- ════════════════════════════════════════════════════
-- § 5. HasContextSet Instances
-- ════════════════════════════════════════════════════

open CommonGround in
/-- A polymorphic commitment space projects to a context set via its root,
    using the `[HasSupport G]` typeclass's `support` projection. Recovers
    the binary case at `G = Prop` definitionally (via `support := id` in
    the `Prop` instance). -/
instance {W G : Type*} [HasSupport G] :
    HasContextSet (CommitmentSpace W G) W where
  toContextSet := CommitmentSpace.toContextSet

open CommonGround in
/-- A Krifka state projects to a context set via the commitment space root. -/
instance {W : Type*} : HasContextSet (KrifkaState W) W where
  toContextSet := KrifkaState.contextSet

open CommonGround in
/-- KrifkaState context set agrees with CommitmentSpace context set. -/
theorem krifkaState_contextSet_eq_space {W : Type*} (s : KrifkaState W) :
    HasContextSet.toContextSet s = HasContextSet.toContextSet s.space := rfl

open Discourse.Commitment (IndexedWeightedCommitment)

/-- Krifka commitment-space instance for `HasAssertion`: assertion prepends
    `commit speaker doxastic φ` to the root, whose projection through
    `HasSupport` narrows the context set by exactly `φ`. -/
instance instHasAssertion {W : Type*} :
    CommonGround.HasAssertion (KrifkaState W) W where
  initial := KrifkaState.empty
  assert s φ := s.assert φ
  toContextSet_initial :=
    Set.eq_univ_of_forall fun _ _ hic => absurd hic List.not_mem_nil
  toContextSet_assert s φ := by
    ext w
    rw [Set.mem_inter_iff]
    constructor
    · intro h
      have head_mem :
          IndexedWeightedCommitment.commit (G := Prop) .speaker .doxastic φ ∈
            (s.assert φ).space.root := by
        simp only [KrifkaState.assert, CommitmentSpace.assert, List.mem_cons, true_or]
      refine ⟨fun ic hic => h ic ?_, h _ head_mem⟩
      simp only [KrifkaState.assert, CommitmentSpace.assert, List.mem_cons]
      exact Or.inr hic
    · rintro ⟨hs, hφ⟩ ic hic
      simp only [KrifkaState.assert, CommitmentSpace.assert, List.mem_cons] at hic
      rcases hic with rfl | hic
      · exact hφ
      · exact hs ic hic

end Discourse.Krifka
