import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Fox2007

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
  alternatives (they land in different MCEs, so neither is in I-E),
  but the problem of which alternatives *enter the set* remains
- @cite{fox-katzir-2011} show that **contextual restriction cannot
  break symmetry** — only the formal alternative set F can
- @cite{breheny-et-al-2018} show that none of these fully solve
  the problem (indirect SIs, gradable adjectives, too many/few
  lexical alternatives remain problematic)

This file defines the core concepts — `isSymmetric`, complement
equivalence, and inconsistency of joint exclusion — as theory-neutral
infrastructure that any approach can import. The definition follows
@cite{fox-katzir-2011} definition 12, but the concept is not specific
to that paper.

## Key Definitions and Theorems

- `isSymmetric`: S₁, S₂ partition S's denotation (def 12)
- `symmetric_complement`: S ∧ ¬S₁ = S₂ when symmetric
- `both_excluded_inconsistent`: excluding both contradicts S
- `symmetric_not_ie`: symmetric alternatives are never in I-E
- `RelevanceClosure`: closure under ¬ and ∧ (condition 50)
- `context_cannot_break_symmetry`: C preserves symmetry (constraint 28)
-/

namespace NeoGricean.Symmetry

open NeoGricean.Exhaustivity.Fox2007 hiding sublists


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
-- SECTION 3: Bridge to Innocent Exclusion (Fox 2007)
-- ============================================================

/-- Excluding both symmetric alternatives is inconsistent with S.
    If S₁, S₂ partition S, then S ∧ ¬S₁ ∧ ¬S₂ is unsatisfiable:
    every S-world is an S₁-world or S₂-world (by the union
    condition) but the exclusion requires it to be neither. -/
theorem both_excluded_inconsistent {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) (alts : List (W → Bool))
    (i₁ i₂ : Nat) (excl : List Nat)
    (hsym : isSymmetric domain s s₁ s₂ = true)
    (hi₁ : alts[i₁]? = some s₁) (hi₂ : alts[i₂]? = some s₂)
    (hm₁ : i₁ ∈ excl) (hm₂ : i₂ ∈ excl) :
    exclusionConsistent domain s alts excl = false := by
  rw [Bool.eq_false_iff]
  intro h
  unfold exclusionConsistent at h
  rw [List.any_eq_true] at h
  obtain ⟨w, hw, hwand⟩ := h
  rw [Bool.and_eq_true_iff] at hwand
  obtain ⟨_, hall⟩ := hwand
  rw [List.all_eq_true] at hall
  have hs1 := hall s₁ (List.mem_filterMap.mpr ⟨i₁, hm₁, hi₁⟩)
  have hs2 := hall s₂ (List.mem_filterMap.mpr ⟨i₂, hm₂, hi₂⟩)
  unfold isSymmetric at hsym
  have ⟨ha, _⟩ := Bool.and_eq_true_iff.mp hsym
  rw [List.all_eq_true] at ha
  specialize ha w hw
  simp [BEq.beq] at ha
  cases s₁ w <;> cases s₂ w <;> simp_all

/-- **General principle**: symmetric alternatives are never innocently
    excludable. If S₁, S₂ partition S's denotation and both appear in
    the alternative set, then neither is in I-E.

    The argument: since ⟦S₁⟧ ∩ ⟦S₂⟧ = ∅ and ⟦S₁⟧ ∪ ⟦S₂⟧ = ⟦S⟧,
    excluding both is unsatisfiable (proved by
    `both_excluded_inconsistent`). So each MCE contains at most
    one of {S₁, S₂}. Since each can be consistently excluded
    individually (witnessed by an S₂-world or S₁-world respectively),
    each appears in some MCE but not all. Hence neither is in
    I-E = ⋂MCEs.

    TODO: the proof requires showing that the list-based
    `maxConsistentExclusions` produces MCEs that witness this
    separation — specifically, that individual excludability
    (`h_sat₁`/`h_sat₂`) extends to maximal exclusion sets. -/
theorem symmetric_not_ie {W : Type} (domain : List W)
    (s s₁ s₂ : W → Bool) (alts : List (W → Bool))
    (i₁ i₂ : Nat) (h_ne : i₁ ≠ i₂)
    (hsym : isSymmetric domain s s₁ s₂ = true)
    (hi₁ : alts[i₁]? = some s₁) (hi₂ : alts[i₂]? = some s₂)
    (h_sat₁ : domain.any s₁ = true)
    (h_sat₂ : domain.any s₂ = true) :
    let ie := ieIndices domain s alts
    ie.contains i₁ = false ∧ ie.contains i₂ = false := by
  sorry


-- ============================================================
-- SECTION 4: Relevance Closure and Constraint 28
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


end NeoGricean.Symmetry
