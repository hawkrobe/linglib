import Linglib.Theories.Dialogue.CommitmentSpace
import Linglib.Theories.Dialogue.KOS.Defs
import Linglib.Theories.Dialogue.KOS.Basic
import Linglib.Theories.Dialogue.FarkasBruce
import Linglib.Features.Acceptability

/-!
# Bias in Commitment Space Semantics
@cite{krifka-2015} @cite{cohen-krifka-2014} @cite{ginzburg-2012} @cite{bring-gunlogson-2000}

Worked examples exercising the commitment-space framework of
@cite{krifka-2015} ("Bias in Commitment Space Semantics: Declarative
questions, negated questions, and question tags"). Each worked example
uses a 2-world Weather model and verifies a specific paper claim.

## Coverage

- §1 — 2-world model fixture
- §2 — Assertion (paper §2): speaker-indexed commitment lands in root
- §3 — Monopolar vs bipolar polar questions (paper §3, eqs. 23, 27):
       bipolar produces two non-contradictory siblings, NOT a stacked
       pair of monopolars
- §4 — Negated polar questions (paper §4, eqs. 38–39, Table 1 p. 341):
       low-neg = `commit addressee ¬φ`, high-neg = `refuse addressee φ`,
       pragmatically weaker than low-neg
- §5 — Question tags (paper §5, eqs. 44–45): matching = conjunction,
       reverse = disjunction, NOT sequential composition
- §N — Reciprocal cross-framework contrasts:
       - vs @cite{ginzburg-2012} KOS (per `Phenomena/Dialogue/Studies/Ginzburg2012.lean`
         lines 49–52, which delegates Krifka contrasts here)
       - vs @cite{farkas-bruce-2010} discourse-table model. Krifka §1 (paper
         p. 331) cites F&B as the inspiration for his rejection operator ℜ;
         this section makes the structural relationship Lean-checkable.
- §∞ — Deep structure: the Dialogue Completeness observation —
       framework-agnostic agreement on observable CG at completed traces.

## Out of scope (explicit)

- Speech-act denegation `~𝔄` (paper §1, eq. 5) — substrate gained the
  `denegate` operator at 0.230.656. The first consumer is
  `Phenomena/Assertion/Studies/CohenKrifka2014.lean` (anchored on the
  prior @cite{cohen-krifka-2014} introduction of denegation). This file
  could now exercise denegation but doesn't need to for the §§1–5
  scope; reverse-tag worked examples are blocked on a separate
  `applyComplex .disj` substrate gap.
- JP/ComP layered clause structure — that's @cite{krifka-2020} material;
  see `Phenomena/Assertion/Studies/Krifka2020.lean`.
- Cross-framework contrasts with Stalnaker, Brandom, Lauer, Gunlogson,
  Inquisitive Semantics. Future work; substrates are present.

-/

namespace Phenomena.Assertion.Studies.Krifka2015

open Dialogue.Krifka
open Core.Discourse (DiscourseRole)
open Core.Discourse.Commitment (IndexedCommitment ContextualEvidence)
open Features (Acceptability)

-- ════════════════════════════════════════════════════
-- § 1. Finite World Setup
-- ════════════════════════════════════════════════════

/-- Two-world model: it's raining or it's not. Used by all sections,
    including the cross-framework contrast (no second world type). -/
inductive Weather where | rain | noRain
  deriving DecidableEq, Repr

/-- Proposition: it's raining. -/
def isRaining : Weather → Prop
  | .rain => True
  | .noRain => False

/-- Proposition: it's NOT raining. -/
def isNotRaining : Weather → Prop
  | .rain => False
  | .noRain => True

/-- Initial discourse state: empty commitments, no open continuations. -/
def s₀ : KrifkaState Weather := KrifkaState.empty

-- ════════════════════════════════════════════════════
-- § 2. Assertion (paper §2, eq. 14, p. 332)
-- ════════════════════════════════════════════════════

/-- After asserting "it's raining", the root contains the
    speaker-indexed commitment `S₁⊢φ` — NOT bare `φ`. This is
    the central content of @cite{krifka-2015} eq. (14):
    `⟨..., C*⟩ +^S₁ S₁⊢φ = ⟨..., C*, [C + S₁⊢φ]^S₁⟩`. -/
theorem assert_root_eq :
    (s₀.assert isRaining).space.root =
      [IndexedCommitment.commit .speaker isRaining] := rfl

/-- The speaker's commitment slate records the assertion. -/
theorem assert_speakerCS_records :
    (s₀.assert isRaining).speakerCS.commitments = [isRaining] := rfl

/-- The addressee's slate is unchanged (they haven't accepted yet). -/
theorem assert_addresseeCS_unchanged :
    (s₀.assert isRaining).addresseeCS.commitments = [] := rfl

/-- Assertion adds no continuations to a previously-empty space. -/
theorem assert_no_open_continuations :
    (s₀.assert isRaining).hasNoOpenContinuations := by decide

/-- Assertion-by-addressee (the `Yes`-as-acceptance path) lands the
    indexed commitment with `.addressee` as committer. -/
theorem assert_by_addressee_root_eq :
    (s₀.assert isRaining .addressee).space.root =
      [IndexedCommitment.commit .addressee isRaining] := rfl

-- ════════════════════════════════════════════════════
-- § 3. Monopolar vs Bipolar Questions (paper §3, eqs. 23, 27)
-- ════════════════════════════════════════════════════

/-- Monopolar question preserves the root (CG unchanged) — paper p. 335. -/
theorem monopolar_root_unchanged :
    (s₀.monopolarQuestion isRaining).space.root = [] := rfl

/-- Monopolar question adds exactly one continuation. -/
theorem monopolar_continuations_length_eq_one :
    (s₀.monopolarQuestion isRaining).space.continuations.length = 1 := rfl

/-- The continuation's commitment is by the **addressee**, not the speaker
    (paper p. 337 around eq. 30: "the ? head identifies the committer as S₂"). -/
theorem monopolar_continuation_committer_eq_addressee :
    (s₀.monopolarQuestion isRaining).space.continuations =
      [[IndexedCommitment.commit .addressee isRaining]] := rfl

/-- Bipolar question preserves the root (paper eq. 23). -/
theorem bipolar_root_unchanged :
    (s₀.bipolarQuestion isRaining).space.root = [] := rfl

/-- Bipolar question adds exactly two sibling continuations
    (paper eq. 23, Figure 8 p. 335). -/
theorem bipolar_continuations_length_eq_two :
    (s₀.bipolarQuestion isRaining).space.continuations.length = 2 := rfl

/-- The bipolar continuations are `commit addressee φ` and
    `commit addressee ¬φ` — both indexed to the addressee.

    This is the bug-fix theorem: the deleted Krifka2015.lean modeled
    "bipolar" as two stacked monopolar questions, producing a
    contradictory continuation `[¬φ, φ]`. The faithful Krifka eq. 23
    derivation gives two SEPARATE alternatives, neither of which contains
    both `φ` and `¬φ`. -/
theorem bipolar_continuations_eq :
    ∃ (φ ψ : Weather → Prop),
      (s₀.bipolarQuestion isRaining).space.continuations =
        [[IndexedCommitment.commit .addressee φ],
         [IndexedCommitment.commit .addressee ψ]] ∧
      φ = isRaining ∧
      (∀ w, ψ w ↔ ¬ isRaining w) :=
  ⟨isRaining, fun w => ¬ isRaining w, rfl, rfl, fun _ => Iff.rfl⟩

/-- Neither bipolar continuation is internally contradictory: each is a
    singleton list, so it cannot contain both `φ` and `¬φ`. -/
theorem bipolar_continuations_not_internally_contradictory :
    ∀ cont ∈ (s₀.bipolarQuestion isRaining).space.continuations,
      cont.length = 1 := by
  intro cont hcont
  simp only [KrifkaState.bipolarQuestion, CommitmentSpace.bipolarQuestion, s₀,
             KrifkaState.empty, CommitmentSpace.empty,
             List.map_nil, List.append_nil,
             List.mem_cons, List.not_mem_nil, or_false] at hcont
  rcases hcont with rfl | rfl
  · rfl
  · rfl

/-- Accepting a monopolar question's continuation puts the
    addressee-indexed commitment in the root. The pathway models the
    `Yes` confirmation: addressee commits to φ. -/
theorem accept_monopolar_root_eq :
    (s₀.monopolarQuestion isRaining).acceptContinuation.space.root =
      [IndexedCommitment.commit .addressee isRaining] := rfl

/-- Bridge: `acceptContinuation ∘ monopolarQuestion φ` and
    `assert φ .addressee` produce the same root. The two pathways for
    addressee-commitment converge. -/
theorem monopolarQuestion_accept_eq_assert_addressee :
    (s₀.monopolarQuestion isRaining).acceptContinuation.space.root =
    (s₀.assert isRaining .addressee).space.root := rfl

-- ════════════════════════════════════════════════════
-- § 4. Negated Polar Questions (paper §4, eqs. 38–39, Table 1 p. 341)
-- ════════════════════════════════════════════════════

/-! ## High vs low negation — the paper's titular contribution

@cite{krifka-2015} §4 distinguishes:
- **Low negation**: *Did I not win?* — TP-internal negation, monopolar
  question with `commit addressee ¬φ`. The addressee is asked to commit
  to ¬φ.
- **High negation**: *Didn't I win?* — ComP-level non-commitment, modeled
  as `refuse addressee φ`. The addressee is asked NOT to commit to φ.

Per paper p. 340: "adding ¬S₂⊢φ to the commitment space precludes
commitment to φ, but is compatible with commitment to ¬φ. Hence ¬S₂⊢φ
is pragmatically weaker than S₂⊢¬φ." This pragmatic strength asymmetry
licenses the contextual-evidence pattern in Table 1 (p. 341).
-/

/-- Low negation: `Did I not win?` adds an addressee commitment to ¬φ. -/
theorem low_neg_continuation_eq :
    (s₀.negatedQuestionLow isRaining).space.continuations =
      [[IndexedCommitment.commit .addressee (fun w => ¬ isRaining w)]] := rfl

/-- High negation: `Didn't I win?` adds an addressee REFUSAL to commit to φ.
    Distinct from `commit addressee ¬φ`. -/
theorem high_neg_continuation_eq :
    (s₀.negatedQuestionHigh isRaining).space.continuations =
      [[IndexedCommitment.refuse .addressee isRaining]] := rfl

/-- High-negation polarity is `refuse`, not `commit`. -/
theorem high_neg_uses_refuse :
    ∀ ic ∈ (s₀.negatedQuestionHigh isRaining).space.continuations.flatten,
      ¬ ic.IsCommit := by
  intro ic hic
  -- `(s₀.negatedQuestionHigh isRaining).space.continuations.flatten`
  -- reduces to `[refuse .addressee isRaining]`, so `ic = refuse _ _`.
  have heq : ic = IndexedCommitment.refuse .addressee isRaining :=
    List.mem_singleton.mp hic
  intro h
  rw [heq] at h
  exact h

/-- Pragmatic-strength asymmetry (paper p. 340): the high-negation
    continuation, projected to a context-set constraint, is WEAKER than
    the low-negation continuation — `refuse` projects to the trivial
    `True` constraint, while `commit ¬φ` projects to actual `¬φ`. -/
theorem high_neg_weaker_than_low_neg (w : Weather) :
    -- High-negation continuation imposes no constraint on w
    (∀ ic ∈ ([IndexedCommitment.refuse .addressee isRaining] :
              List (IndexedCommitment Weather)),
        ic.toCommitment w) ∧
    -- Low-negation continuation imposes ¬ isRaining
    (∀ ic ∈ ([IndexedCommitment.commit .addressee
              (fun w => ¬ isRaining w)] :
              List (IndexedCommitment Weather)),
        ic.toCommitment w ↔ ¬ isRaining w) := by
  refine ⟨?_, ?_⟩
  · intro ic hic
    rcases List.mem_singleton.mp hic with rfl
    trivial
  · intro ic hic
    rcases List.mem_singleton.mp hic with rfl
    rfl

/-! ## Table 1 (paper p. 341) — Büring & Gunlogson 2000 licensing

@cite{bring-gunlogson-2000} (cited by @cite{krifka-2015} p. 341)
identifies a 3×3 contextual-evidence × negation-type acceptability
pattern. Contexts (rows): contextual evidence FOR φ / NEUTRAL / AGAINST φ.
Question types (columns): no negation / low negation / high negation.

Krifka's analysis (paper p. 341) explains the pattern in terms of
which READING is licensed when no negation is present:
- (a) FOR-φ: no-neg ok via the **monopolar** reading
- (b) NEUTRAL: no-neg ok via the **bipolar** reading
- (c) AGAINST-φ: no-neg degraded — both readings fail

Cell values use `Features.Acceptability` (`ok` / `marginal` / `anomalous`).
The paper's `(#)` parenthesised hash maps to `marginal`; bare `#` maps to
`anomalous`. The `ContextualEvidence` enum is reused from
`Core.Discourse.Commitment` (originally introduced for
@cite{bring-gunlogson-2000}).
-/

/-- The three negation columns of Krifka's Table 1. -/
inductive NegationType where
  /-- Column (i): no negation — *Is there a vegetarian restaurant?* -/
  | noNeg
  /-- Column (ii): low (TP) negation — *Is there no vegetarian restaurant?* -/
  | lowNeg
  /-- Column (iii): high (ComP) negation — *Isn't there a vegetarian restaurant?* -/
  | highNeg
  deriving DecidableEq, Repr

/-- Which reading licenses the no-negation question in each context
    (per @cite{krifka-2015} p. 341 prose). -/
inductive NoNegReading where
  /-- Setting (a): monopolar reading licenses (speaker has prior evidence). -/
  | monopolarLicensed
  /-- Setting (b): bipolar reading licenses (alternatives equally likely). -/
  | bipolarLicensed
  /-- Setting (c): both readings fail (mono lacks evidence, bi suggests equipoise). -/
  | bothDegraded
  deriving DecidableEq, Repr

/-- Krifka's Table 1 (p. 341): 3×3 contextual-evidence × negation-type
    acceptability matrix. -/
def table1 : ContextualEvidence → NegationType → Acceptability
  | .forP,     .noNeg   => .ok        -- (a, i)  ok (mono)
  | .forP,     .lowNeg  => .anomalous -- (a, ii) #
  | .forP,     .highNeg => .anomalous -- (a, iii) #
  | .neutral,  .noNeg   => .ok        -- (b, i)  ok (bi)
  | .neutral,  .lowNeg  => .anomalous -- (b, ii) #
  | .neutral,  .highNeg => .ok        -- (b, iii) ok
  | .againstP, .noNeg   => .marginal  -- (c, i)  (#) — Krifka's parenthesised
  | .againstP, .lowNeg  => .ok        -- (c, ii) ok
  | .againstP, .highNeg => .ok        -- (c, iii) ok

/-- Per @cite{krifka-2015} p. 341 prose: which reading licenses the
    no-negation question in each contextual-evidence setting. -/
def noNegLicensing : ContextualEvidence → NoNegReading
  | .forP     => .monopolarLicensed
  | .neutral  => .bipolarLicensed
  | .againstP => .bothDegraded

/-- Table 1 as a decide-checked predictive bundle. The pattern is what
    Krifka §4 explains via his monopolar/bipolar/high-vs-low contrast. -/
theorem table1_predictions :
    table1 .forP     .noNeg   = .ok        ∧
    table1 .forP     .lowNeg  = .anomalous ∧
    table1 .forP     .highNeg = .anomalous ∧
    table1 .neutral  .noNeg   = .ok        ∧
    table1 .neutral  .lowNeg  = .anomalous ∧
    table1 .neutral  .highNeg = .ok        ∧
    table1 .againstP .noNeg   = .marginal  ∧
    table1 .againstP .lowNeg  = .ok        ∧
    table1 .againstP .highNeg = .ok := by decide

/-- Per the paper's prose: the no-negation cell licensing diverges across
    contexts — mono in (a), bipolar in (b), both fail in (c). -/
theorem noNeg_licensing_distinguishes_contexts :
    noNegLicensing .forP     = .monopolarLicensed ∧
    noNegLicensing .neutral  = .bipolarLicensed ∧
    noNegLicensing .againstP = .bothDegraded := by decide

-- ════════════════════════════════════════════════════
-- § 5. Question Tags (paper §5, eqs. 44–45)
-- ════════════════════════════════════════════════════

/-! ## Tags as speech-act conjunction / disjunction

Per @cite{krifka-2015} p. 342: matching tags are speech-act CONJUNCTION
applied as ONE complex move — explicitly NOT sequential `assert; question`.
The substrate's `Dialogue.Krifka.matchingTag` and `reverseTag`
(`Theories/Dialogue/CommitmentSpace.lean` §4) capture this directly.
-/

/-- Substrate's `matchingTag φ` is structurally a `conj` of two atomic
    speech acts (paper eq. 44). -/
theorem matching_tag_is_conjunction :
    ∃ a b, (matchingTag isRaining : ComplexSpeechAct Weather) = .conj a b :=
  ⟨_, _, rfl⟩

/-- The matching tag's two speech acts share content — both are about φ. -/
theorem matching_tag_shared_content_eq :
    (matchingTag isRaining : ComplexSpeechAct Weather).components.map
      SpeechAct.content = [isRaining, isRaining] := rfl

/-- The committers diverge: speaker for the assertion-leg, addressee for
    the question-leg (paper p. 342). -/
theorem matching_tag_committers_diverge_eq :
    (matchingTag isRaining : ComplexSpeechAct Weather).components.map
      (·.roles.committer) = [.speaker, .addressee] := rfl

/-- Substrate's `reverseTag φ ¬φ` is structurally a `disj` (paper eq. 45). -/
theorem reverse_tag_is_disjunction :
    ∃ a b, (reverseTag isRaining isNotRaining :
              ComplexSpeechAct Weather) = .disj a b :=
  ⟨_, _, rfl⟩

/-- Worked example: applying a matching tag to the empty state via
    `applyComplex` produces a state where speaker has committed to φ
    (assertion-leg) and a continuation proposes addressee committing
    to φ (question-leg). The substrate sequentialises per paper eq. 6's
    "≈" approximation (no anaphoric ties at this level). -/
theorem matching_tag_apply_root_eq :
    (s₀.applyComplex (matchingTag isRaining)).space.root =
      [IndexedCommitment.commit .speaker isRaining] := rfl

/-- The matching tag's continuation contains the addressee-commit on top
    of the speaker-commit already in the root. Both are present, both
    are non-contradictory (different committers, same content). -/
theorem matching_tag_apply_continuations_eq :
    (s₀.applyComplex (matchingTag isRaining)).space.continuations =
      [[IndexedCommitment.commit .addressee isRaining,
        IndexedCommitment.commit .speaker isRaining]] := rfl

-- ════════════════════════════════════════════════════
-- § N. vs Ginzburg 2012 KOS — architectural contrast
-- ════════════════════════════════════════════════════

/-! ## Krifka commitment-spaces vs KOS per-DGB stance

Per the chronological-dependency rule, this post-2012 study engages the
2012 framework: @cite{krifka-2015} commitment-spaces and
@cite{ginzburg-2012} KOS make **structurally different** but
observationally similar predictions about identical event sequences.

Reciprocal entry to `Phenomena/Dialogue/Studies/Ginzburg2012.lean` lines
49–52, which delegates Krifka contrasts here.

| Question | Krifka 2015 | Ginzburg 2012 (KOS) |
|---|---|---|
| Is CG a single object or per-agent? | Single object, but its entries are speaker-indexed (`IndexedCommitment.commit S₁ φ`) | Per-agent (`DGB.facts`) |
| When does an assertion narrow CG? | Immediately (assert puts `commit S₁ φ` in root) | Only after Accept (one-sided FACTS) |
| Are commitments separable from CG? | Yes — root carries indexed commitments + per-agent slates | Only via separate DGBs |

The architectures cannot be unified by a Galois connection that preserves
both Krifka's eager-narrowing root behaviour and KOS's per-DGB asymmetry.
-/

section vsGinzburg2012

open Dialogue.KOS

/-- The contrast theorem: post-assertion, Krifka's `space.root` narrows
    to a singleton list `[commit speaker isRaining]` (immediate, with
    speaker indexing); KOS's addressee DGB.facts stays `[]` (only the
    speaker side narrows; addressee waits for Accept). -/
theorem krifka_eager_vs_ginzburg_lazy :
    -- Krifka: speaker assert immediately puts indexed commitment in root
    (s₀.assert isRaining).space.root.length = 1 ∧
    -- KOS (addressee perspective): no Accept → no narrowing
    (DGB.initial : DGB Unit (Weather → Prop) Unit Unit).facts = [] := by
  refine ⟨?_, rfl⟩
  rfl

/-- Krifka's root carries indexed commitments (one per committer
    contribution); KOS speaker-side DGB has the fact in their slate while
    addressee-side stays empty. The architectures store the commitment
    in different shapes. -/
theorem krifka_indexed_root_vs_kos_split_dgbs (p : Weather → Prop) :
    -- Krifka: ONE root with a speaker-indexed entry
    (s₀.assert p).space.root = [IndexedCommitment.commit .speaker p] ∧
    -- KOS: speaker-side has p, addressee-side is empty —
    -- they are LITERALLY different DGB values
    let kosSpeaker : DGB Unit (Weather → Prop) Unit Unit :=
      DGB.initial.addFact p
    let kosAddressee : DGB Unit (Weather → Prop) Unit Unit := DGB.initial
    kosSpeaker.facts ≠ kosAddressee.facts := by
  refine ⟨rfl, ?_⟩
  simp only [DGB.addFact, DGB.initial, ne_eq, List.cons_ne_nil, not_false_eq_true]

end vsGinzburg2012

-- ════════════════════════════════════════════════════
-- § N+1. vs Farkas & Bruce 2010 — eager vs lazy CG narrowing
-- ════════════════════════════════════════════════════

/-! ## Krifka commitment-spaces vs Farkas-Bruce discourse-table model

Per @cite{krifka-2015} §1 p. 331: "The last of these commitment stages
would correspond to the notion of a 'Table' in Farkas & Bruce 2010, i.e.,
the conversational stage under negation." Krifka cites @cite{farkas-bruce-2010}
as the explicit inspiration for his rejection operator ℜ. The two
frameworks are observationally similar but structurally distinct on
identical event sequences.

| Question | Krifka 2015 | Farkas-Bruce 2010 |
|---|---|---|
| When does an assertion narrow CG? | Immediately (`commit speaker φ` in root) | Only after addressee accept (one-sided dcS until then) |
| Where does the assertion live pre-acceptance? | Root entry (already in CG, speaker-indexed) | `dcS` slate + `table` issue |
| What does acceptance update? | Adds `commit addressee φ` to root | Pops table issue, adds φ to cg + dcL |
| What's the "stable" predicate? | `hasNoOpenContinuations` (no pending proposals) | `table.isEmpty` (no items on table) |

The eager/lazy distinction is real and non-collapsible at intermediate
states. But at the end of a "completed" assertion+acceptance sequence,
both frameworks agree on the observable CG content modulo Krifka's
speaker indexing — see the Dialogue Completeness observation below.
-/

section vsFarkasBruce2010

open Dialogue.FarkasBruce

/-- Divergence at the assert-only intermediate state: Krifka's CG
    narrows immediately (one indexed entry in `root`); F&B's joint CG
    stays empty because the assertion lives on the table awaiting
    acceptance. The two frameworks DISAGREE on what's "in CG" mid-trace.

    @cite{krifka-2015} p. 332 eq. (14) puts `S₁⊢φ` directly in the
    commitment state; @cite{farkas-bruce-2010}'s `assertDeclarative`
    only updates `dcS` and pushes a table issue. -/
theorem krifka_eager_vs_farkasBruce_lazy_intermediate :
    -- Krifka: speaker assert immediately puts speaker-indexed entry in root
    (s₀.assert isRaining).space.root =
      [IndexedCommitment.commit .speaker isRaining] ∧
    -- F&B: assertDeclarative leaves cg untouched; commitment is on
    -- speaker's slate + table only
    (DiscourseState.empty.assertDeclarative isRaining).cg = [] ∧
    (DiscourseState.empty.assertDeclarative isRaining).dcS = [isRaining] ∧
    (DiscourseState.empty.assertDeclarative isRaining).table.length = 1 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Bridge at the completed-trace state: after the addressee accepts the
    assertion, both frameworks have φ in the joint CG (modulo Krifka's
    speaker indexing on the root entries; F&B's `cg` is bare `Set W`).

    Krifka's "addressee accepts" pathway is `assert φ .addressee`
    (the `Yes` reaction, paper p. 334 eq. 21). F&B's pathway is
    `acceptTop` after `assertDeclarative`. Both end with φ in the
    common ground at the propositional level. -/
theorem krifka_double_assert_eq_farkasBruce_assert_accept :
    let kState  := (s₀.assert isRaining).assert isRaining .addressee
    let fbState := (DiscourseState.empty.assertDeclarative isRaining).acceptTop
    -- Krifka: both speakers' commitments visible in their slates
    kState.speakerCS.commitments   = [isRaining] ∧
    kState.addresseeCS.commitments = [isRaining] ∧
    -- Krifka: both indexed entries in root (most-recent first)
    kState.space.root =
      [IndexedCommitment.commit .addressee isRaining,
       IndexedCommitment.commit .speaker isRaining] ∧
    -- F&B: assertion has migrated from table → cg, with dcS/dcL also updated
    fbState.cg    = [isRaining] ∧
    fbState.dcS   = [isRaining] ∧
    fbState.dcL   = [isRaining] ∧
    fbState.table = [] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The headline observation: at a completed assertion+acceptance trace,
    the two frameworks agree on the **context-set projection** —
    Krifka's projected CG content is exactly `isRaining`.

    The frameworks disagree on what they STORE at intermediate states
    (root vs table, indexed vs flat) but agree on the observable
    they project to (worlds compatible with all committed propositions).
    This is the simplest concrete instance of the
    Dialogue Completeness observation in §∞. -/
theorem krifka_contextSet_at_completed_trace (w : Weather) :
    let kState := (s₀.assert isRaining).assert isRaining .addressee
    kState.contextSet w ↔ isRaining w := by
  constructor
  · intro h
    exact h (IndexedCommitment.commit .speaker isRaining)
            (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro hφ ic hic
    rcases List.mem_cons.mp hic with rfl | hic'
    · exact hφ
    · rcases List.mem_singleton.mp hic' with rfl
      exact hφ

end vsFarkasBruce2010

-- ════════════════════════════════════════════════════
-- § ∞. Deep structure: the Dialogue Completeness observation
-- ════════════════════════════════════════════════════

/-! ## The Dialogue Completeness observation

The cross-framework theorems above (`krifka_contextSet_at_completed_trace`
paired with `krifka_double_assert_eq_farkasBruce_assert_accept`, the
parallel `vsGinzburg2012` block) are concrete instances of a deeper
structural claim. We articulate it here as prose; the typeclass-mediated
universal version is future work.

### Statement

For any two commitment-tracking dialogue frameworks `F₁` and `F₂` over
the same world type `W`, equipped with:

- A shared event signature `DialogueEvent W` (assert, monopolar question,
  bipolar question, low/high negated question, accept, reject, …);
- A step function `step_i : Sᵢ → DialogueEvent W → Sᵢ`;
- A context-set projection `contextSet_i : Sᵢ → Set W` (the observable
  CG content);
- A "completed" predicate `isCompleted_i : Sᵢ → Prop` (no pending
  proposals, no orphan issues),

the conjecture is:

```
∀ events : List (DialogueEvent W),
  isCompleted_F₁ (events.foldl step_F₁ initial_F₁) →
  isCompleted_F₂ (events.foldl step_F₂ initial_F₂) →
  contextSet_F₁ (events.foldl step_F₁ initial_F₁) =
  contextSet_F₂ (events.foldl step_F₂ initial_F₂)
```

Plain English: **dialogue frameworks differ in the journey through
intermediate states; they agree on the observable destination.**
The eager/lazy timing of CG updates, the per-agent commitment slate
shape, the proposal-tracking apparatus — all of these are
framework-internal bookkeeping invisible at completed traces. What's
publicly committed (in the projected context-set sense) at the end of
a completed dialogue is framework-invariant.

### Why it's deep

The conjecture says that `contextSet` is the **maximal observable**
shared across all reasonable models of dialogue. Anything more
fine-grained (commitment indexing, per-agent slates, intermediate
proposal stacks, reaction-pathway distinctions) is a free choice the
modeler makes — and choices on that level don't constrain what counts
as a model of dialogue dynamics per se. Mathematically, this is the
shape of an observational equivalence in a coalgebraic / process-theory
sense: framework states form a coalgebra for the functor
`X ↦ (DialogueEvent → X) × (Set W)`, and the completed-trace agreement
is bisimilarity at the `Set W` observable.

### Status in linglib

This file proves the conjecture's restriction to a 2-element framework
class `{Krifka2015, FarkasBruce2010}` and a 2-event trace
(`assert; accept`). The general statement requires:

1. A `DialogueState` typeclass in `Theories/Dialogue/Common.lean`
   (does not yet exist) parameterising over the four operations above.
2. Per-framework instances for Krifka, Farkas-Bruce, KOS, Stalnaker,
   Brandom, Gunlogson, Lauer.
3. The universal theorem proved either generically (likely needs an
   axiom about how each instance's `step` interprets `DialogueEvent`)
   or per-pair (n² theorems for n frameworks).

The per-pair route is more tractable; the generic route requires
articulating what "interpret an event correctly" means as a coherence
law on instances. Either route lifts cross-framework reconciliation
in linglib from per-file `vsX2010` sections to a structural theorem
about what counts as a dialogue framework at all.

The framework that *refuses the typeclass instance* is the most
informative: @cite{lauer-2013}'s gradient-credence assertion has no
sharp `commit` event in the Krifka/F&B sense, so it would either
reject the `DialogueState` instance or implement it with a non-trivial
projection (mapping credence ≥ θ to commitment for some threshold θ).
The refusal would surface a genuine architectural break between
gradient-pragmatic and categorical-pragmatic models of dialogue.
-/

end Phenomena.Assertion.Studies.Krifka2015
