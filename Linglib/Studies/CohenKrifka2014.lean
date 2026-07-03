import Linglib.Discourse.Commitment.Space

/-!
# Superlative Quantifiers and Meta-Speech Acts
[cohen-krifka-2014] [krifka-2015]

[cohen-krifka-2014] ("Superlative quantifiers and meta-speech
acts", *Linguistics & Philosophy* 37, 41–90) argues that superlative
quantifiers (`at least n`, `at most n`) are quantifiers over META-SPEECH-ACTS.
The apparatus: speech-act denegation `~A` (a meta-speech-act) and
GRANT(φ) := `~ASSERT(¬φ)`. The application: `at most n φ` =
"the maximal n s.t. the speaker GRANTs φ(n)" (paper §3, eqs. 43–51).

This file formalises the SUBSTRATE-LEVEL apparatus (§§2–3 of the paper),
specifically what our list-shape commitment-space substrate can faithfully
express. We focus on STRUCTURAL theorems (∀ commitment space, ∀ content)
rather than concrete-fixture `decide`-units.

## What the substrate captures (✓)

The paper's headline claims that our list-shape substrate can support:

1. **GRANT definition** (paper eq. 38, p. 53): `GRANT(φ) := ~ASSERT(¬φ)`.
   Trivially via the substrate's `denegate` operator.
2. **GRANT structural properties**: preserves CommonGround (substrate's
   `denegate_preserves_root`), doesn't grow continuations
   (`denegate_continuation_count_le`), filters precisely the
   speaker-asserts-¬φ paths (`denegate_surviving_no_match`).
3. **ASSERT entails GRANT** (paper p. 54 prose): ASSERT(φ) and GRANT(φ)
   project to context sets in subset relation — asserted CommonGround is a subset
   of granted CommonGround. This is the paper's "GRANT is weaker than ASSERT" at
   the observable resolution.

## What the substrate cannot capture (✗) — explicit deferrals

4. **Modal duality** (paper eq. 40, p. 54): `ASSERT(φ) ≡ ~GRANT(¬φ)`
   (the analog of `□φ ≡ ¬◇¬φ`). Requires the paper's eq. 28 (`~~A = A`),
   which in turn requires the substrate's denegate to track act
   provenance (which act is being denegated). Our list-shape model
   filters continuations by marker without tracking the marker's
   identity in subsequent operations: `(C - X) - X = C - X` (idempotent),
   not `C - (C - X) = X`. The substrate would need a fundamentally
   different shape (e.g., `ComplexSpeechAct.denegate : SpeechAct →
   ComplexSpeechAct` constructor with denegation as an act, not a
   filter operation) to faithfully capture eq. 40.

5. **Speech-act conjunction = intersection** (paper eq. 31, p. 52):
   `C + [A & B] = (C + A) ∩ (C + B)`. Substrate uses sequential
   composition (`applyComplex .conj`). Paper itself acknowledges (p. 52)
   the equivalence is "≈" — exact only when there are no anaphoric
   ties. Our substrate matches the approximation, not the literal
   set intersection.

6. **De Morgan for speech acts** (paper eqs. 34–35, pp. 52–53):
   `~[A & B] = [~A ∨ ~B]`, `~[A ∨ B] = [~A & ~B]`. Blocked on
   `applyComplex .disj := sorry` in the substrate (Krifka 2015 eq. 7
   set-union semantics on commitment spaces, which can produce
   non-rooted results — paper p. 330 fig 5).

7. **Superlative quantifier semantics** (paper §3, eqs. 43–51):
   `at most n φ` = max-n s.t. speaker GRANTs φ(n). Requires numeric
   content (propositions indexed by ℕ) + iterated speech-act
   conjunction (`&_{n>k}`). Sketched in §∞ below.

## Marker decidability via Classical

The substrate's `denegate` operator requires `[DecidablePred actMarker]`.
For markers that compare propositional content extensionally
(`∀ w, ψ w ↔ φ w`), opaque `ψ : W → Prop` doesn't admit constructive
decidability — `Prop` lacks `DecidableEq`. We supply the instance via
`Classical.decPred`, making `grant` `noncomputable` at this site. This
is fine: the headline theorems are propositional, not computational.
Linglib's prior `decide`-based worked-example style (in earlier drafts
of this file) was unit-test-shaped; structural theorems don't need
computation.

-/

namespace CohenKrifka2014

open Discourse.Krifka
open Discourse (DiscourseRole)
open Discourse.Commitment (IndexedCommitment IndexedWeightedCommitment CommitmentForce)

variable {W : Type*}

-- ════════════════════════════════════════════════════
-- § 1. GRANT definition (paper eq. 38, p. 53)
-- ════════════════════════════════════════════════════

/-- Marker: matches a commit by `committer` with `force` whose content is
    extensionally equivalent to the given target predicate. The
    `commitContentMatches` shape factors out the common
    "(committer, force, content) tuple match" pattern; specific
    markers (like `assertsSpeakerNeg` below) are partial applications. -/
def commitContentMatches (committer : DiscourseRole) (force : CommitmentForce)
    (target : W → Prop) :
    IndexedCommitment W → Prop
  | IndexedWeightedCommitment.commit c f w =>
      c = committer ∧ f = force ∧ ∀ x, w x ↔ target x
  | IndexedWeightedCommitment.refuse _ _ _ => False

/-- Marker for "speaker doxastically asserts content extensionally
    equivalent to ¬φ". Used to define GRANT(φ) via denegation. -/
def assertsSpeakerNeg (φ : W → Prop) : IndexedCommitment W → Prop :=
  commitContentMatches .speaker .doxastic (fun w => ¬ φ w)

/-- DecidablePred via Classical (noncomputable). The marker compares
    propositional content extensionally; decidability would need
    `DecidableEq Prop`, which is not constructively available. -/
noncomputable instance (φ : W → Prop) :
    DecidablePred (assertsSpeakerNeg (W := W) φ) :=
  Classical.decPred _

/-- GRANT(φ) := `~ASSERT(¬φ)` (paper eq. 38, p. 53). Definitionally a
    denegation of the speaker-asserts-¬φ act. The result of `grant cs φ`
    is `cs` with all continuations containing a speaker-doxastic-commits-to-¬φ
    entry filtered out.

    Note: `noncomputable` because the marker's DecidablePred is
    Classical. Theorems below are propositional. -/
noncomputable def grant (cs : CommitmentSpace W Prop) (φ : W → Prop) :
    CommitmentSpace W Prop :=
  cs.denegate (assertsSpeakerNeg φ)

-- ════════════════════════════════════════════════════
-- § 2. GRANT structural properties
-- ════════════════════════════════════════════════════

/-- GRANT preserves the root (CommonGround unchanged). Krifka 2015 p. 330:
    "denegation does not change the root of the commitment space, but
    prunes its legal developments". For any cs and φ. -/
theorem grant_preserves_root (cs : CommitmentSpace W Prop) (φ : W → Prop) :
    (grant cs φ).root = cs.root :=
  CommitmentSpace.denegate_preserves_root cs (assertsSpeakerNeg φ)

/-- GRANT does not grow the continuation list — it can only filter.
    For any cs and φ. -/
theorem grant_continuation_count_le (cs : CommitmentSpace W Prop) (φ : W → Prop) :
    (grant cs φ).continuations.length ≤ cs.continuations.length :=
  CommitmentSpace.denegate_continuation_count_le cs (assertsSpeakerNeg φ)

/-- GRANT is idempotent (`(C - X) - X = C - X`). Note: this is NOT the
    paper's eq. 28 `~~A = A` — see "What the substrate cannot capture"
    in the docstring header. -/
theorem grant_idempotent (cs : CommitmentSpace W Prop) (φ : W → Prop) :
    grant (grant cs φ) φ = grant cs φ :=
  CommitmentSpace.denegate_idempotent cs (assertsSpeakerNeg φ)

/-- The paper's "GRANT prunes the speaker-asserts-¬φ paths" claim,
    structurally. Every continuation surviving GRANT(φ) does NOT contain
    a speaker-doxastic-asserts-¬φ commitment. -/
theorem grant_filters_speaker_neg_assertions
    (cs : CommitmentSpace W Prop) (φ : W → Prop) :
    ∀ cont ∈ (grant cs φ).continuations,
      ¬ ∃ ic ∈ cont, assertsSpeakerNeg φ ic :=
  CommitmentSpace.denegate_surviving_no_match cs (assertsSpeakerNeg φ)

-- ════════════════════════════════════════════════════
-- § 3. ASSERT is stronger than GRANT (paper p. 54)
-- ════════════════════════════════════════════════════

/-! ## ASSERT(φ) entails GRANT(φ) at the context-set observable

Paper p. 54: "GRANTing a proposition Φ ... includes, but does not
enforce, the assertion of Φ." In our substrate, this becomes a
context-set inclusion — every world compatible with the
asserted-φ state is compatible with the granted-φ state.

This is the paper's central pragmatic ordering, captured at our
substrate's resolution. The deeper "modal duality" (eq. 40,
ASSERT(φ) ≡ ~GRANT(¬φ)) is substrate-blocked (see file docstring). -/

/-- `assert .speaker φ` and `grant cs φ` differ in their root: assert
    extends the root with `commit speaker φ`, grant preserves the root.
    Hence the asserted state's context set is a SUBSET of the granted
    state's: every world surviving in the asserted state survives in
    the granted state too. -/
theorem assert_contextSet_subset_grant_contextSet
    (cs : CommitmentSpace W Prop) (φ : W → Prop) :
    ∀ w, (cs.assert .speaker φ).toContextSet w → (grant cs φ).toContextSet w := by
  intro w h ic hic
  -- (grant cs φ).root = cs.root by `grant_preserves_root`
  -- (cs.assert .speaker φ).root = (commit speaker φ) :: cs.root
  -- So `ic ∈ cs.root → ic ∈ (commit speaker φ) :: cs.root`, and the
  -- assertion-side hypothesis covers all such ic.
  rw [grant_preserves_root] at hic
  exact h ic (List.mem_cons_of_mem _ hic)

/-- The strict-stronger direction: there exist `cs`, `φ`, and `w` such
    that `w` is in the granted CommonGround but NOT in the asserted CommonGround. The
    asymmetry that makes ASSERT genuinely stronger than GRANT
    (not just ≤). -/
theorem assert_strictly_stronger_witness :
    ∃ (W : Type) (cs : CommitmentSpace W Prop) (φ : W → Prop) (w : W),
      (grant cs φ).toContextSet w ∧ ¬ (cs.assert .speaker φ).toContextSet w := by
  -- Witness: empty cs, content φ that is False at some world.
  refine ⟨Bool, CommitmentSpace.empty, fun b => b = true, false, ?_, ?_⟩
  · -- Granted CommonGround: empty root, no constraint, every world survives.
    intro ic hic
    rw [grant_preserves_root] at hic
    exact absurd hic (List.not_mem_nil)
  · -- Asserted CommonGround: root contains `commit speaker (· = true)`. The
    -- `toCommitment` projection of this commit at world `false` is
    -- `(fun b => b = true) false = (false = true) = False`.
    intro h
    have hcommit := h (IndexedWeightedCommitment.commit .speaker .doxastic
                        (fun b => b = true))
                       List.mem_cons_self
    -- hcommit : IndexedWeightedCommitment.toCommitment _ false
    -- = CommitmentGrade.support ((fun b => b = true) false)
    -- = CommitmentGrade.support (False)
    -- For Prop: support := id, so this is `False`.
    exact (Bool.false_ne_true hcommit)

-- ════════════════════════════════════════════════════
-- § ∞. Out-of-scope: paper's deeper claims
-- ════════════════════════════════════════════════════

/-! ## What this file does not cover, and why

### Modal duality, paper eq. 40 (ASSERT ≡ ~GRANT(¬))

Substrate-blocked. Our `denegate` filters continuations by marker;
`(C - X) - X = C - X` (idempotent), not `C - (C - X) = X` (paper eq. 28).
A faithful eq. 28 requires the substrate to track WHICH ACT is being
denegated, so that denegating-the-denegation can recover the original.
The architectural shift would be to add `ComplexSpeechAct.denegate :
SpeechAct → ComplexSpeechAct` as a constructor and have `applyComplex`
process it as a meta-act with provenance, not as a free-standing filter.

### Speech-act conjunction = intersection, paper eq. 31

Substrate-approximated. The paper itself acknowledges (p. 52) that
the literal `(C + A) ∩ (C + B)` equality is "≈" approximate — exact
only when there are no anaphoric ties. Our substrate's
`KrifkaState.applyComplex .conj a b = (s.applyAtom a).applyAtom b`
matches the paper's approximation. A literal-set-intersection
substrate would need a different shape (commitment spaces as sets,
not list-of-list).

### De Morgan for speech acts, paper eqs. 34–35

Blocked on substrate `applyComplex .disj := sorry` (Krifka 2015 eq. 7
set-union semantics on commitment spaces; non-rooted results possible).

### Superlative quantifier semantics, paper §3

Blocked on numeric-content fixture (propositions indexed by ℕ) and
generalized speech-act conjunction over a finite range. The
implementable form is paper eq. 46 (conjoined ASSERT(≠n) for n > k),
not eq. 44 (iterated `~GRANT`, blocked on substrate eq. 28). A focused
study `Studies/CohenKrifka2014_Superlatives.lean`
could land later with a finite numeric model.

The empirical anchor for the deferred superlatives study is the paper's
§3.3 cancellability argument (pp. 57–58) distinguishing Cohen-Krifka
from Geurts-Nouwen 2007. -/

end CohenKrifka2014
