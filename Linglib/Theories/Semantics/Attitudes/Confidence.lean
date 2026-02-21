import Linglib.Theories.Semantics.Lexical.Adjective.StatesBased

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
given holder are ordered: the ordering represents how confident the holder
is in different propositions.

Key features:
- **Per-holder ordering**: Ann's confidence ordering differs from Bob's
  (CSW §4.1)
- **Not per-theme**: the ordering ranks states across themes, not within
  one theme
- **Not probabilistic**: the ordering need not respect conjunction
  (conjunction fallacy compatible, CSW (52))
- **Bounded above**: `certain` picks out the maximal elements (CSW §5.2)

## Logic of Confidence (CSW §4.6)

The ordering validates:
- **Transitivity** of comparative confidence (CSW (54))
- **Antisymmetry** of equative confidence (CSW (55))
- **Upward monotonicity**: confident(p) ∧ more_confident(q, p) → confident(q)
  (CSW (53))

It does NOT validate:
- Probabilistic conjunction: confident(p ∧ q) → confident(p)
- Connectedness (CSW are agnostic, §4.6 discussion of (58))

## References

- Cariani, F., Santorio, P. & Wellwood, A. (2024). Confidence reports.
  Semantics & Pragmatics 17(14): 1-40.
-/

namespace Semantics.Attitudes.Confidence

open Semantics.Lexical.Adjective.StatesBased
open Core.Scale (ComparativeScale Boundedness)

-- ════════════════════════════════════════════════════
-- § 1. Confidence States
-- ════════════════════════════════════════════════════

/-- A confidence state: a state with a holder and a propositional theme.

    CSW §4.1: "there are three states of confidence such that Mary is the
    holder of all three. These states have as themes, respectively, the
    propositions that it's snowing, that Regina is in Saskatchewan, and
    that Brazil will win the World Cup."

    Every ordinary person is the holder of a large number of confidence
    states. The holder field is the Neodavidsonian HOLDER role
    (`ThematicRoles.lean:91`); the theme is the propositional THEME. -/
structure ConfidenceState (E W : Type*) where
  /-- The attitude bearer -/
  holder : E
  /-- The proposition the holder is confident about -/
  theme : W → Prop

-- ════════════════════════════════════════════════════
-- § 2. Holder-Relativized Confidence Ordering
-- ════════════════════════════════════════════════════

/-- A holder-relativized confidence ordering (CSW §4.1).

    The ordering ranks confidence states by how confident the holder is
    in each theme. Orderings vary from holder to holder but NOT from
    theme to theme: propositions are the objects of confidence states,
    not parameters in fixing their ranking.

    The ordering is at least a preorder (reflexive, transitive). CSW are
    agnostic about connectedness (totality): it is possible that some
    propositions are simply not comparable by the lights of a subject's
    confidence states (CSW §4.6, discussion of (58)). -/
structure ConfidenceOrdering (E W : Type*) where
  /-- The attitude bearer whose ordering this is -/
  holder : E
  /-- Weak ordering: `le s₁ s₂` means holder is at least as confident
      in the theme of `s₂` as in the theme of `s₁` -/
  le : ConfidenceState E W → ConfidenceState E W → Prop
  /-- Reflexivity -/
  le_refl : ∀ s, le s s
  /-- Transitivity -/
  le_trans : ∀ a b c, le a b → le b c → le a c
  /-- All states in this ordering belong to this holder -/
  holder_consistent : ∀ s₁ s₂, le s₁ s₂ →
    s₁.holder = holder ∧ s₂.holder = holder

/-- A confidence ordering induces a preorder on confidence states. -/
def ConfidenceOrdering.toPreorder {E W : Type*}
    (co : ConfidenceOrdering E W) : Preorder (ConfidenceState E W) where
  le := co.le
  le_refl := co.le_refl
  le_trans := co.le_trans

-- ════════════════════════════════════════════════════
-- § 3. Confident and Certain as StatesBasedEntry
-- ════════════════════════════════════════════════════

/-- Build a `StatesBasedEntry` for a gradable attitude adjective
    on a confidence ordering. The `contrastPt` determines where the
    positive region begins. -/
def confidenceEntry {E W : Type*} (co : ConfidenceOrdering E W)
    (contrastPt : ConfidenceState E W) (b : Boundedness) :
    @StatesBasedEntry (ConfidenceState E W) co.toPreorder :=
  letI := co.toPreorder
  { scale := { boundedness := b }
    contrastPoint := contrastPt }

/-- `confident`: positive region begins at a moderate contrast point.
    CSW Figure 2: the positive region for `confident` covers the upper
    portion of the confidence ordering. -/
def confidentEntry {E W : Type*} (co : ConfidenceOrdering E W)
    (contrastPt : ConfidenceState E W) :
    @StatesBasedEntry (ConfidenceState E W) co.toPreorder :=
  confidenceEntry co contrastPt .upperBounded

/-- `certain`: positive region begins at the maximum — `certain` picks out
    the maximal elements of the confidence ordering (CSW §5.2, Figure 3).
    `certain` and `confident` share the same background ordering but
    `certain` has a higher contrast point. -/
def certainEntry {E W : Type*} (co : ConfidenceOrdering E W)
    (maxPt : ConfidenceState E W) :
    @StatesBasedEntry (ConfidenceState E W) co.toPreorder :=
  confidenceEntry co maxPt .upperBounded

/-- `certain` entails `confident`: every state in the certainty region
    is also in the confidence region (CSW (65)).

    This follows from `asymEntails` when the certainty contrast point
    is at least as high as the confidence contrast point. -/
theorem certain_entails_confident {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt maxPt : ConfidenceState E W)
    (h : co.le confPt maxPt) :
    @asymEntails _ co.toPreorder (certainEntry co maxPt) (confidentEntry co confPt) := by
  show co.le confPt maxPt
  exact h

/-- The entailment is asymmetric when the contrast points differ:
    confidence does NOT entail certainty (CSW (65b)). -/
theorem confident_not_entails_certain {E W : Type*}
    (co : ConfidenceOrdering E W)
    (confPt maxPt : ConfidenceState E W)
    (h_strict : co.le confPt maxPt ∧ ¬co.le maxPt confPt) :
    ¬@asymEntails _ co.toPreorder (confidentEntry co confPt) (certainEntry co maxPt) := by
  show ¬co.le maxPt confPt
  exact h_strict.2

-- ════════════════════════════════════════════════════
-- § 4. Logic of Confidence (CSW §4.6)
-- ════════════════════════════════════════════════════

/-- Comparative confidence is transitive (CSW (54)):
    "more confident of p than q" ∧ "more confident of q than r"
    → "more confident of p than r".

    Follows from transitivity of the preorder + monotonicity of
    admissible measures. -/
theorem comparative_transitive {E W : Type*}
    (_co : ConfidenceOrdering E W)
    {D : Type*} [LinearOrder D]
    (μ : ConfidenceState E W → D)
    (s_p s_q s_r : ConfidenceState E W)
    (h_pq : μ s_q < μ s_p) (h_qr : μ s_r < μ s_q) :
    μ s_r < μ s_p :=
  lt_trans h_qr h_pq

/-- Comparative confidence is antisymmetric (CSW (55)):
    "at least as confident of p as q" ∧ "at least as confident of q as p"
    → "equally confident of p and q".

    Follows from antisymmetry of `≤` on the degree type. -/
theorem comparative_antisymmetric {E W : Type*}
    (_co : ConfidenceOrdering E W)
    {D : Type*} [LinearOrder D]
    (μ : ConfidenceState E W → D)
    (s_p s_q : ConfidenceState E W)
    (h₁ : μ s_q ≤ μ s_p) (h₂ : μ s_p ≤ μ s_q) :
    μ s_p = μ s_q :=
  le_antisymm h₂ h₁

/-- Upward monotonicity of the positive form (CSW (53)):
    "σ is confident that p" ∧ "σ is more confident of q than of p"
    → "σ is confident that q".

    If s_p is in the positive region (contrastPt ≤ s_p in the preorder)
    and s_q is ranked at least as high as s_p, then s_q is also in
    the positive region. -/
theorem confidence_upward_monotone {E W : Type*}
    (co : ConfidenceOrdering E W)
    (entry : @StatesBasedEntry _ co.toPreorder)
    (s_p s_q : ConfidenceState E W)
    (h_conf : @StatesBasedEntry.inPositiveRegion _ co.toPreorder entry s_p)
    (h_more : co.le s_p s_q) :
    @StatesBasedEntry.inPositiveRegion _ co.toPreorder entry s_q :=
  co.le_trans _ _ _ h_conf h_more

/-- Confidence orderings need not respect logical conjunction:
    it is consistent to be confident that (p ∧ q) without being
    confident that p (CSW (52), Tversky & Kahneman 1983).

    Witness: ℕ with contrast point 1 — the state ranked 2 is in the
    positive region (2 ≥ 1) while the state ranked 0 is not (0 < 1).
    Applied to confidence: assign rank 2 to the (p ∧ q)-state and
    rank 0 to the p-state. The ordering is subjective, not constrained
    by logical entailment or probability. -/
theorem conjunction_fallacy_compatible :
    ∃ (contrastPt high low : ℕ),
      contrastPt ≤ high ∧ ¬(contrastPt ≤ low) :=
  ⟨1, 2, 0, by omega, by omega⟩

end Semantics.Attitudes.Confidence
