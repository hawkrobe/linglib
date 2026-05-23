/-!
# Symmetric Alternatives

The **symmetry problem** is the central challenge for any theory of scalar
implicatures based on alternatives. The problem: for any stronger
alternative A of an assertion S, the sentence S ∧ ¬A is also stronger
than S and yields the *opposite* implicature. A theory of alternatives
must explain why A enters the alternative set but S ∧ ¬A does not.

The problem emerged in the early 1970s: @cite{horn-1972} established
the Gricean derivation of scalar implicatures, and @cite{kroch-1972}
discussed the same reasoning for quantifiers, creating the conditions
for recognizing that symmetric alternatives pose a fundamental obstacle.
Every subsequent theory of alternatives is shaped by this problem:

- @cite{katzir-2007} addresses it via **structural complexity**: S ∧ ¬A
  is structurally more complex than S, so it is excluded from F(S)
- @cite{fox-2007}'s **innocent exclusion** correctly handles symmetric
  alternatives (they land in different MCEs, so neither is in I-E)
- @cite{fox-katzir-2011} show that **contextual restriction cannot
  break symmetry** — only the formal alternative set F can
- @cite{breheny-et-al-2018} show that none of these fully solve
  the problem (indirect SIs, gradable adjectives, too many/few
  lexical alternatives remain problematic)
- @cite{fox-spector-2018}'s **economy condition** constrains where
  `exh` can be inserted (not vacuous, not weakening)
- **RSA** (@cite{frank-goodman-2012}, @cite{franke-2011}) **dissolves**
  rather than solves the symmetry problem: the utterance space is
  specified directly, and utterance cost penalizes complex expressions
  like "some but not all"

This file defines the core concepts — `isSymmetric`, complement
equivalence, and contextual relevance closure — as theory-neutral
infrastructure that any approach can import. The definition follows
@cite{fox-katzir-2011} definition 12, but the concept is not specific
to that paper.

The Fox 2007 innocent-exclusion bridge theorems (`symmetric_not_ie`,
`exhB_vacuous_of_ie_empty`, `symmetric_exhB_vacuous`,
`both_excluded_inconsistent`) lived in this file in the legacy
`Bool`/`List` API. They were never called outside their own
docstrings, so the post-`Excluder` reorganization simply drops them
rather than re-deriving Finset versions speculatively. The vacuity
fact for the new API now lives next to its object as
`Exhaustification.innocent_exh_eq_phi_of_innocentlyExcludable_empty`
in `Exhaustification/Innocent.lean`.

## Key Definitions and Theorems

- `isSymmetric`: S₁, S₂ partition S's denotation (def 12)
- `symmetric_complement`: S ∧ ¬S₁ = S₂ when symmetric
- `RelevanceClosure`: closure under ¬ and ∧ (condition 50)
- `context_cannot_break_symmetry`: C preserves symmetry (constraint 28)
-/

namespace Alternatives.Symmetric

-- ============================================================
-- SECTION 1: The Symmetry Predicate
-- ============================================================

/-- Two propositions are **symmetric alternatives** of S if they
    partition S's denotation: their union equals S and they are
    mutually exclusive.

    Formalized from @cite{fox-katzir-2011} definition 12. The
    underlying problem was recognized in the early 1970s
    (@cite{horn-1972}, @cite{kroch-1972}).

    Note: this is stricter than mere non-innocent-excludability.
    Disjuncts p, q of p∨q are often mutually compatible (p ∩ q ≠ ∅)
    and hence NOT symmetric, though they still resist innocent
    exclusion for related reasons (@cite{fox-katzir-2011} fn. 18). -/
def isSymmetric {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) : Bool :=
  -- (a) ⟦S₁⟧ ∪ ⟦S₂⟧ = ⟦S⟧
  domain.all (fun w => (s₁ w || s₂ w) == s w) &&
  -- (b) ⟦S₁⟧ ∩ ⟦S₂⟧ = ∅
  domain.all (fun w => !(s₁ w && s₂ w))


-- ============================================================
-- SECTION 2: Core Properties
-- ============================================================

/-- When S₁, S₂ are symmetric alternatives of S, S ∧ ¬S₁ is
    extensionally equal to S₂. This is the key fact underlying
    the relevance argument: showing S ∧ ¬S₁ is relevant suffices
    to show S₂ is relevant. -/
theorem symmetric_complement {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool)
    (hsym : isSymmetric domain s s₁ s₂ = true) :
    domain.all (fun w => (s w && !s₁ w) == s₂ w) = true := by
  unfold isSymmetric at hsym
  have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hsym
  rw [List.all_eq_true] at ha hb ⊢
  intro w hw
  specialize ha w hw
  specialize hb w hw
  simp [BEq.beq] at ha hb ⊢
  cases h1 : s₁ w <;> cases h2 : s₂ w <;> simp_all


-- ============================================================
-- SECTION 3: Relevance Closure and Constraint 28
-- ============================================================

/-!
## Context Cannot Break Symmetry

The set of contextually relevant sentences C must satisfy closure
conditions (@cite{fox-katzir-2011} condition 50):

(50a) If S is relevant, so is ¬S.
(50b) If S₁, S₂ are relevant, so is S₁ ∧ S₂.

From these conditions, constraint (28) follows: **symmetry cannot be
broken in C**. If S₁ is relevant and S is relevant, then S ∧ ¬S₁ is
relevant (by 50a + 50b). But when S₁, S₂ are symmetric, S ∧ ¬S₁ ≡ S₂
(by `symmetric_complement`). So S₂ is also relevant, and contextual
restriction cannot selectively eliminate one symmetric alternative
while keeping the other.
-/

/-- Closure conditions on relevance (condition 50). -/
structure RelevanceClosure (W : Type) where
  relevant : (W → Bool) → Bool
  negClosed : ∀ (p : W → Bool), relevant p = true →
    relevant (fun w => !p w) = true
  conjClosed : ∀ (p q : W → Bool), relevant p = true →
    relevant q = true → relevant (fun w => p w && q w) = true

/-- **C cannot break symmetry (constraint 28)**: if S₁ is relevant
    and S is relevant, then the symmetric partner S ∧ ¬S₁ (which
    equals S₂ when S₁, S₂ are symmetric by `symmetric_complement`)
    is also relevant.

    Therefore any contextual restriction that keeps S₁ must also
    keep S₂. Symmetry breaking must happen in F, not in C. -/
theorem context_cannot_break_symmetry {W : Type}
    (rc : RelevanceClosure W)
    (s s₁ : W → Bool)
    (hs : rc.relevant s = true)
    (h₁ : rc.relevant s₁ = true) :
    rc.relevant (fun w => s w && !s₁ w) = true :=
  rc.conjClosed s (fun w => !s₁ w) hs (rc.negClosed s₁ h₁)


end Alternatives.Symmetric
