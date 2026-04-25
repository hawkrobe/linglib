import Linglib.Theories.Semantics.Gradability.StatesBased

/-!
# Confidence and Certainty as Gradable Attitudes

@cite{cariani-santorio-wellwood-2024}

Gradable attitude adjectives like `confident`, `certain`, `sure`, and
`doubtful` denote properties of confidence states. Unlike accessibility-based
attitudes (`Doxastic.lean`: believe, know) and preference-based attitudes
(`Preferential.lean`: hope, fear), these are **gradable properties of states
with propositional themes** — a third kind of attitude semantics.

## Core Structure

A confidence state has a **holder** (the attitude bearer) and a **theme**
(the proposition the holder is confident about). Confidence states for a
given holder are ordered by a `ConfidenceOrdering`, which extends
`Preorder (ConfidenceState E W)` with a `holder` field.

Key features:
- **Per-holder ordering**: Ann's confidence ordering differs from Bob's
  (CSW §4.1)
- **Not per-theme**: the ordering ranks states across themes, not within
  one theme
- **Not probabilistic**: the ordering need not respect conjunction
  (`conjunction_fallacy_compatible`, CSW (52))
- **Bounded above (for ordinary holders)**: `certain` picks out the
  maximal elements (CSW §5.2). The maximality assumption is supplied
  per-theorem via `h_top`, not baked into the structure — CSW p.19 hedges
  with "for ordinary individuals."

## Logic of Confidence (CSW §4.6)

The ordering validates:
- **Transitivity** of comparative confidence (CSW (54))
- **Antisymmetry** of equative confidence (CSW (55))
- **Upward monotonicity**: confident(p) ∧ more_confident(q, p) → confident(q)
  (CSW (53))

It does NOT validate:
- Probabilistic conjunction: confident(p ∧ q) → confident(p) (CSW (52))
- Connectedness (CSW are agnostic, §4.6 discussion of (58))

-/

namespace Semantics.Attitudes.Confidence

open Semantics.Gradability.StatesBased
open Core.Scale (ComparativeScale Boundedness)

/-! ## §1. Confidence States -/

/-- A confidence state: a state with a holder and a propositional theme.

    CSW §4.1: "there are three states of confidence such that Mary is the
    holder of all three. These states have as themes, respectively, the
    propositions that it's snowing, that Regina is in Saskatchewan, and
    that Brazil will win the World Cup."

    Every ordinary person is the holder of a large number of confidence
    states. The holder field is the Neodavidsonian HOLDER role
    (`ThematicRoles.lean`); the theme is the propositional THEME. -/
structure ConfidenceState (E W : Type*) where
  /-- The attitude bearer -/
  holder : E
  /-- The proposition the holder is confident about -/
  theme : W → Prop

/-! ## §2. Holder-Relativized Confidence Ordering -/

/-- A holder-relativized confidence ordering (CSW §4.1).

    Extends mathlib's `Preorder` with a `holder` field and a consistency
    constraint that all states in the ordering belong to that holder.
    The preorder is at least reflexive and transitive; CSW §4.6 are
    explicitly agnostic about connectedness (totality), which is why
    `Preorder` (not `LinearOrder` or `PartialOrder`) is the right base —
    it permits CSW's discussion of (58) where some propositions are
    incomparable.

    Each holder has their own ordering: orderings vary from holder to
    holder but NOT from theme to theme (CSW p.19). -/
structure ConfidenceOrdering (E W : Type*)
    extends Preorder (ConfidenceState E W) where
  /-- The attitude bearer whose ordering this is -/
  holder : E
  /-- All states in this ordering belong to this holder -/
  holder_consistent : ∀ s₁ s₂ : ConfidenceState E W, le s₁ s₂ →
    s₁.holder = holder ∧ s₂.holder = holder

/-! ## §3. Confident and Certain as StatesBasedEntry

`confident` and `certain` share a `ConfidenceOrdering` but pick out
different positive regions via different `contrastPoint`s. CSW Figures 2
and 3: same background ordering, different cut-offs.

The lexical entries are POS-free (CSW §3.3): the positive form is
`contrastPoint ≤ s` directly on the preorder, with no covert `pos`
morpheme. This is the central architectural commitment of CSW.
-/

/-- Build a `StatesBasedEntry` for a gradable attitude adjective on a
    confidence ordering. The `contrastPt` determines where the positive
    region begins. The boundedness flag classifies the scale shape. -/
def confidenceEntry {E W : Type*} (co : ConfidenceOrdering E W)
    (contrastPt : ConfidenceState E W) (b : Boundedness := .upperBounded) :
    @StatesBasedEntry (ConfidenceState E W) co.toPreorder :=
  letI := co.toPreorder
  { scale := { boundedness := b }
    contrastPoint := contrastPt }

/-- `confident`: positive region begins at a moderate contrast point in
    the upper portion of the confidence ordering (CSW Figure 2). -/
abbrev confidentEntry {E W : Type*} (co : ConfidenceOrdering E W)
    (contrastPt : ConfidenceState E W) :
    @StatesBasedEntry (ConfidenceState E W) co.toPreorder :=
  confidenceEntry co contrastPt

/-- `certain`: positive region IS the set of maximal states (CSW §5.2,
    Figure 3, eq. (69) "fully/100% confident = certain"). The maximality
    of `maxPt` is asserted as a separate hypothesis at use sites
    (`certain_entails_confident`) rather than baked into the constructor,
    matching CSW p.19's "for ordinary individuals" hedge.

    Note: structurally identical to `confidentEntry` — the difference
    between `certain` and `confident` is the *value* of the contrast
    point relative to the ordering, not the entry's shape. -/
abbrev certainEntry {E W : Type*} (co : ConfidenceOrdering E W)
    (maxPt : ConfidenceState E W) :
    @StatesBasedEntry (ConfidenceState E W) co.toPreorder :=
  confidenceEntry co maxPt

/-- `doubts`: a negative-polarity entry on the same confidence ordering
    as `confident`/`certain`. The "positive region" of `doubts` (the
    set of states the predicate holds of) is the *lower* portion of the
    confidence ordering — states the holder has *low* confidence in
    relative to `doubtPt`.

    Structurally identical to `confidentEntry`/`certainEntry` — the
    difference is which region predicate consumers invoke. `confident`
    and `certain` use `inPositiveRegion`; `doubts` uses `inLowerRegion`.

    CSW §5.2 (63c) places "Ann doubts that the dress is blue" in this
    lower region; the inconsistency with (63a)/(63b) is then
    `confident_excludes_doubts` below. -/
abbrev doubtsEntry {E W : Type*} (co : ConfidenceOrdering E W)
    (doubtPt : ConfidenceState E W) :
    @StatesBasedEntry (ConfidenceState E W) co.toPreorder :=
  confidenceEntry co doubtPt

/-- `certain` entails `confident` (CSW (65)/(66)).

    Given that `maxPt` is the top of the ordering (CSW's "ordinary holder"
    assumption), the certainty contrast point dominates any confidence
    contrast point, so by `asymEntails_positive_region` every state in the
    certainty region is also in the confidence region. -/
theorem certain_entails_confident {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt maxPt : ConfidenceState E W)
    (h_top : ∀ s : ConfidenceState E W, co.le s maxPt) :
    letI := co.toPreorder
    asymEntails (certainEntry co maxPt) (confidentEntry co confPt) := by
  show co.le confPt maxPt
  exact h_top confPt

/-- The entailment is asymmetric (CSW (65b)/(66b)): confidence does NOT
    entail certainty whenever the ordering admits a state strictly above
    the confidence contrast point that is not in the certainty region.

    Concretely: if `maxPt` is the certainty contrast point and `confPt`
    is strictly below it (`¬co.le maxPt confPt`), then there is no
    `asymEntails confidentEntry certainEntry` because the contrast points
    don't match in the right direction. -/
theorem confident_not_entails_certain {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt maxPt : ConfidenceState E W)
    (h_strict : ¬co.le maxPt confPt) :
    letI := co.toPreorder
    ¬ asymEntails (confidentEntry co confPt) (certainEntry co maxPt) := by
  show ¬co.le maxPt confPt
  exact h_strict

/-! ## §4. Logic of Confidence Reports (CSW §4.6) -/

/-- Comparative confidence is transitive (CSW (54)/(57)):
    "more confident of p than q" ∧ "more confident of q than r"
    → "more confident of p than r".

    This is `lt_trans` on the linearly-ordered measure type. The
    `ConfidenceOrdering` doesn't enter the proof, but the named lemma
    documents that this is the prediction CSW make for confidence
    comparatives. CSW (57) is contradictory because asserting the
    negation of (54)'s consequent contradicts this generic fact. -/
theorem comparative_transitive {E W D : Type*} [LinearOrder D]
    (μ : ConfidenceState E W → D)
    (s_p s_q s_r : ConfidenceState E W)
    (h_pq : μ s_q < μ s_p) (h_qr : μ s_r < μ s_q) :
    μ s_r < μ s_p :=
  lt_trans h_qr h_pq

/-- Comparative confidence is antisymmetric (CSW (55)):
    "at least as confident of p as q" ∧ "at least as confident of q as p"
    → "equally confident of p and q". -/
theorem comparative_antisymmetric {E W D : Type*} [LinearOrder D]
    (μ : ConfidenceState E W → D)
    (s_p s_q : ConfidenceState E W)
    (h₁ : μ s_q ≤ μ s_p) (h₂ : μ s_p ≤ μ s_q) :
    μ s_p = μ s_q :=
  le_antisymm h₂ h₁

/-- Upward monotonicity of the positive form (CSW (53)):
    "σ is confident that p" ∧ "σ is more confident of q than of p"
    → "σ is confident that q".

    If s_p is in the positive region and s_q is ranked at least as high
    as s_p in the confidence ordering, then s_q is also in the positive
    region — by transitivity through the contrast point. -/
theorem confidence_upward_monotone {E W : Type*}
    (co : ConfidenceOrdering E W)
    (entry : @StatesBasedEntry _ co.toPreorder)
    (s_p s_q : ConfidenceState E W)
    (h_conf : @StatesBasedEntry.inPositiveRegion _ co.toPreorder entry s_p)
    (h_more : co.le s_p s_q) :
    @StatesBasedEntry.inPositiveRegion _ co.toPreorder entry s_q :=
  letI := co.toPreorder
  le_trans h_conf h_more

/-- CSW (63a)/(63c): `confident` and `doubts` are mutually exclusive.

    No confidence state is simultaneously in the confidence region
    (above the confidence contrast point) and the doubt region (below
    the doubt contrast point), provided the doubt contrast point is
    *strictly* below the confidence contrast point. This is the
    substantive content of CSW's claim that "Ann doubts that the dress
    is blue" is inconsistent with "Ann is confident / has confidence
    that the dress is blue".

    Combined with `certain_entails_confident`, this gives CSW's full
    inferential triangle: certain(p) → confident(p), confident(p) ⊥
    doubts(p), so certain(p) ⊥ doubts(p). -/
theorem confident_excludes_doubts {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt doubtPt : ConfidenceState E W)
    (h_strict : ¬ co.le confPt doubtPt)
    (s : ConfidenceState E W) :
    letI := co.toPreorder
    ¬ (StatesBasedEntry.inPositiveRegion (confidentEntry co confPt) s ∧
       StatesBasedEntry.inLowerRegion (doubtsEntry co doubtPt) s) := by
  letI := co.toPreorder
  exact disjoint_regions (confidentEntry co confPt) (doubtsEntry co doubtPt) h_strict s

/-- Confidence orderings need not respect logical conjunction:
    it is consistent to be confident that (p ∧ q) without being
    confident that p (CSW (52), @cite{tversky-kahneman-1983}).

    Witness: ℕ as a toy ordering with contrast point 1 — the state ranked
    2 is in the positive region (1 ≤ 2) while the state ranked 0 is not
    (¬ 1 ≤ 0). Applied to confidence: assign rank 2 to the (p ∧ q)-state
    and rank 0 to the p-state. The ordering is subjective and not
    constrained by logical entailment.

    CSW §4.6 use this to argue against any probability-functional account:
    probability functions force `Pr(p ∧ q) ≤ Pr(p)`. The cross-framework
    refutation is `EpistemicThreshold.confidence_not_probabilistic`,
    which witnesses that no probabilistic credence agrees with this. -/
theorem conjunction_fallacy_compatible :
    ∃ (contrastPt high low : ℕ),
      contrastPt ≤ high ∧ ¬(contrastPt ≤ low) :=
  ⟨1, 2, 0, by omega, by omega⟩

/-! ## §5. Bridge to Neo-Davidsonian Event Semantics

CSW (44) and (47) are the compositional logical forms for positive
and comparative confidence reports respectively. The substrate exposes
both via `confidenceLogicalForm` (presupposition-flattened) and
`comparativeConfidenceLogicalForm` (under unique-state simplification —
CSW fn. 25 explicitly reject this, but it is convenient as a working
form; full (47) requires a `max`-quantified than-clause that
`Wellwood2015.adjectival_max_reduces` already provides at study-file
level).
-/

/-- Truth-conditional content of CSW (44) (presupposition flattened).

    CSW (44) restricts the existential to states in `Dom(⟨D^ho(s)_conf, ≿⟩)`;
    the substrate version drops the domain restriction and lets membership
    in `ConfidenceState E W` stand in for it. For the substrate's
    truth-conditional purposes this is sufficient; for presupposition
    bookkeeping a separate domain-restricted variant would be needed. -/
def confidenceLogicalForm {E W : Type*}
    (co : ConfidenceOrdering E W)
    (entry : @StatesBasedEntry _ co.toPreorder)
    (holder : E) (p : W → Prop) : Prop :=
  ∃ s : ConfidenceState E W,
    s.holder = holder ∧
    @StatesBasedEntry.inPositiveRegion _ co.toPreorder entry s ∧
    s.theme = p

/-- Schematic comparative content under the unique-state simplification.

    The actual CSW (47) abstracts a `max(λd. ...)` over the than-clause;
    this version requires only that *some* `q`-themed state has a strictly
    smaller measure than the `p`-themed state. CSW fn. 25 explicitly
    reject the unique-state assumption ("This is not the picture we
    adopt"), but the simplification is useful for theorem statements that
    don't need the full `max`-quantification. The maximality version lives
    at the study-file level via `Wellwood2015.adjectival_max_reduces`. -/
def comparativeConfidenceLogicalForm {E W : Type*}
    (co : ConfidenceOrdering E W)
    {D : Type*} [LinearOrder D]
    (μ : ConfidenceState E W → D)
    (holder : E) (p q : W → Prop) : Prop :=
  ∃ s_p s_q : ConfidenceState E W,
    s_p.holder = holder ∧ s_p.theme = p ∧
    s_q.holder = holder ∧ s_q.theme = q ∧
    letI := co.toPreorder
    statesComparativeSem μ s_p s_q

end Semantics.Attitudes.Confidence
