import Linglib.Theories.Semantics.Tense.TemporalConnectives.Basic

/-!
# @cite{anscombe-1964} / @cite{krifka-2010b}: Under-specification Semantics
@cite{anscombe-1964} @cite{krifka-2010b} @cite{ladusaw-1980} @cite{beaver-condoravdi-2003}

Single lexical entry per connective. Both *before* and *after* are predicates
on time points; multiple readings arise from which point of B is relevant,
determined pragmatically by telicity.

- *before B* = λt. ∀t' ∈ B, t < t' (all of B follows the reference time)
- *after B* = λt. ∃t' ∈ B, t' < t (some of B precedes the reference time)

The quantificational asymmetry (∀ in *before*, ∃ in *after*) is already present
here at Level 1 (point sets), though Anscombe did not highlight it as the source
of the veridicality contrast.

## Level

**Level 1 (point sets)**: operates on `timeTrace` projections of `SentDenotation`.

-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § Anscombe's Truth Conditions
-- ============================================================================

/-- Anscombe's *before B* as a predicate on times (@cite{krifka-2010b}, eq. 13a):
    λt. ∀t' ∈ times(B), t < t'. All times at which B holds follow t.

    "A before B" then holds when some time in A satisfies this predicate. -/
def Anscombe.before (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t < t'

/-- Anscombe's *after B* as a predicate on times (@cite{krifka-2010b}, eq. 13b):
    λt. ∃t' ∈ times(B), t' < t. Some time at which B holds precedes t.

    "A after B" then holds when some time in A satisfies this predicate. -/
def Anscombe.after (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, t' < t

-- ============================================================================
-- § @cite{heinamaki-1974}: Reference Interval Semantics
-- ============================================================================

/-! ### Heinämäki's analysis and equivalence with Anscombe

@cite{heinamaki-1974}'s analysis uses a reference interval I(B) — the temporal
interval associated with B — and defines *before*/*after* by comparison
with that interval's boundary. This is the most standard textbook analysis.

@cite{beaver-condoravdi-2003}: Under two conditions — **left-boundedness** (B has
a leftmost point) and **instantiation** (B is nonempty) — Anscombe and
Heinämäki are truth-conditionally equivalent.

We formalize the reference point as `leftBound` (= inf of timeTrace B)
and prove the equivalence. This completes the Level 4 → Level 1 projection:
B&C's `earliest` unifies both classical Level 1 analyses. -/

/-- Heinämäki's *before*: A happens before the reference point of B.
    The reference point `lb` is the left bound (minimum) of B's time trace.
    "A before B" iff some time in A precedes B's left bound. -/
def Heinamaki.before (A : SentDenotation Time) (lb : Time) : Prop :=
  ∃ t ∈ timeTrace A, t < lb

/-- Heinämäki's *after*: A happens after the reference point of B.
    The reference point `lb` is the left bound (minimum) of B's time trace.
    "A after B" iff some time in A follows B's left bound. -/
def Heinamaki.after (A : SentDenotation Time) (lb : Time) : Prop :=
  ∃ t ∈ timeTrace A, lb < t

/-- Left-boundedness (attained): `lb` is the minimum of `timeTrace B` —
    it belongs to B's time trace and is ≤ every element.

    B&C use the infimum, but for `SentDenotation` (sets of closed intervals)
    the infimum is always attained (intervals include their endpoints via ≤).
    Using the minimum makes the equivalence proof constructive. -/
def isMinTime (B : SentDenotation Time) (lb : Time) : Prop :=
  lb ∈ timeTrace B ∧ ∀ t ∈ timeTrace B, lb ≤ t

/-- **B&C Theorem 1 (before direction)**: Under left-boundedness
    (attained minimum), Anscombe's *before* ↔ Heinämäki's *before*.

    Forward: a < all of B, lb ∈ B, so a < lb.
    Backward: a < lb, lb ≤ all of B, so a < all of B. -/
theorem anscombe_heinamaki_equiv_before
    (A B : SentDenotation Time) (lb : Time)
    (hlb : isMinTime B lb) :
    Anscombe.before A B ↔ Heinamaki.before A lb := by
  constructor
  · rintro ⟨a, ha, hall⟩
    exact ⟨a, ha, hall lb hlb.1⟩
  · rintro ⟨a, ha, halt⟩
    exact ⟨a, ha, fun t' ht' => lt_of_lt_of_le halt (hlb.2 t' ht')⟩

/-- **B&C Theorem 1 (after direction)**: Under left-boundedness
    (attained minimum), Anscombe's *after* ↔ Heinämäki's *after*.

    Forward: t' ∈ B with t' < a, lb ≤ t', so lb < a.
    Backward: lb < a, lb ∈ B, so lb witnesses the existential. -/
theorem anscombe_heinamaki_equiv_after
    (A B : SentDenotation Time) (lb : Time)
    (hlb : isMinTime B lb) :
    Anscombe.after A B ↔ Heinamaki.after A lb := by
  constructor
  · rintro ⟨a, ha, t', ht', hlt⟩
    exact ⟨a, ha, lt_of_le_of_lt (hlb.2 t' ht') hlt⟩
  · rintro ⟨a, ha, hlt⟩
    exact ⟨a, ha, lb, hlb.1, hlt⟩

-- ============================================================================
-- § Logical Properties (@cite{beaver-condoravdi-2003}, §6)
-- ============================================================================

/-! ### *Before* is a strict order (antisymmetric and transitive)

The ∃∀ quantifier pattern of *before* gives it strict-order-like properties.
Antisymmetry: if some point in A precedes all of B, then no point in B can
precede all of A (because A contains such a point).
Transitivity: chaining through the ∀-quantified middle term. -/

/-- *Before* is antisymmetric: if A before B, then not B before A.

    Proof: A before B gives a₀ ∈ A with a₀ < all of B.
    B before A would give b₀ ∈ B with b₀ < all of A.
    But a₀ < b₀ (from first) and b₀ < a₀ (from second). Contradiction. -/
theorem Anscombe.before_antisymmetric (A B : SentDenotation Time) :
    Anscombe.before A B → ¬Anscombe.before B A := by
  rintro ⟨a, ha, h_aB⟩ ⟨b, hb, h_bA⟩
  exact absurd (lt_trans (h_aB b hb) (h_bA a ha)) (lt_irrefl _)

/-- *Before* is transitive: if A before B and B before C, then A before C.

    Proof: A before B gives a₀ ∈ A with a₀ < all of B.
    B before C gives b₀ ∈ B with b₀ < all of C.
    Since a₀ < b₀ (from first, b₀ ∈ B) and b₀ < c for any c ∈ C,
    we have a₀ < c by transitivity of <. -/
theorem Anscombe.before_transitive (A B C : SentDenotation Time) :
    Anscombe.before A B → Anscombe.before B C → Anscombe.before A C := by
  rintro ⟨a, ha, h_aB⟩ ⟨b, hb, h_bC⟩
  exact ⟨a, ha, fun c hc => lt_trans (h_aB b hb) (h_bC c hc)⟩

/-! ### *After* has neither property

The ∃∃ quantifier pattern of *after* is too weak: overlapping intervals
give mutual *after* (breaking antisymmetry), and a gap in the middle
term breaks transitivity. -/

/-- *After* is NOT antisymmetric: overlapping time traces give A after B
    and B after A simultaneously.

    Counterexample: A = {point 0, point 2}, B = {point 1, point 3}.
    A after B: t=2 ∈ A, t'=1 ∈ B, 1 < 2.
    B after A: t=3 ∈ B, t'=0 ∈ A, 0 < 3. -/
theorem Anscombe.after_not_antisymmetric :
    ∃ (A B : SentDenotation ℤ), Anscombe.after A B ∧ Anscombe.after B A := by
  refine ⟨{Interval.point 0, Interval.point 2},
          {Interval.point 1, Interval.point 3}, ?_, ?_⟩
  · exact ⟨2, ⟨Interval.point 2, Or.inr rfl, le_refl _, le_refl _⟩,
           1, ⟨Interval.point 1, Or.inl rfl, le_refl _, le_refl _⟩, by omega⟩
  · exact ⟨3, ⟨Interval.point 3, Or.inr rfl, le_refl _, le_refl _⟩,
           0, ⟨Interval.point 0, Or.inl rfl, le_refl _, le_refl _⟩, by omega⟩

/-- *After* is NOT transitive: A after B and B after C need not give A after C.

    Counterexample: A = {point 2}, B = {point 1, point 4}, C = {point 3}.
    A after B: t=2 ∈ A, t'=1 ∈ B, 1 < 2.
    B after C: t=4 ∈ B, t'=3 ∈ C, 3 < 4.
    Not A after C: only time in A is 2, only time in C is 3, and 3 ≮ 2. -/
theorem Anscombe.after_not_transitive :
    ∃ (A B C : SentDenotation ℤ),
      Anscombe.after A B ∧ Anscombe.after B C ∧ ¬Anscombe.after A C := by
  refine ⟨{Interval.point 2}, {Interval.point 1, Interval.point 4},
          {Interval.point 3}, ?_, ?_, ?_⟩
  · exact ⟨2, ⟨Interval.point 2, rfl, le_refl _, le_refl _⟩,
           1, ⟨Interval.point 1, Or.inl rfl, le_refl _, le_refl _⟩, by omega⟩
  · exact ⟨4, ⟨Interval.point 4, Or.inr rfl, le_refl _, le_refl _⟩,
           3, ⟨Interval.point 3, rfl, le_refl _, le_refl _⟩, by omega⟩
  · rintro ⟨t, ⟨i, hi, hts, htf⟩, t', ⟨j, hj, ht's, ht'f⟩, hlt⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp only [Interval.point] at hts htf ht's ht'f
    omega

-- ============================================================================
-- § Complement Monotonicity and NPI Licensing (@cite{beaver-condoravdi-2003}, §5)
-- ============================================================================

/-! ### *Before* is DE; *after* is UE in the complement position

The complement position of a temporal connective is the B argument in
"A connective B." The quantifier structure of each connective determines
its monotonicity, which in turn determines NPI licensing:
- *before* (∃∀): the ∀ over B reverses subset inclusion → DE → licenses NPIs
- *after* (∃∃): the ∃ over B preserves subset inclusion → UE → blocks NPIs

This is the same insight @cite{beaver-condoravdi-2003} express through `earliest`: the
universal force of `earliest` (selecting the minimum, which R-dominates
all other elements) creates a downward-entailing environment. -/

/-- The complement position of *before* is downward-entailing:
    strengthening B (shrinking its time trace) preserves "A before B."
    This is why *before* licenses NPIs: "before anyone left" ⊨
    "before any *man* left." -/
theorem Anscombe.before_complement_DE (A B B' : SentDenotation Time)
    (h : timeTrace B' ⊆ timeTrace B) :
    Anscombe.before A B → Anscombe.before A B' := by
  rintro ⟨t, ht, hall⟩
  exact ⟨t, ht, fun t' ht' => hall t' (h ht')⟩

/-- The complement position of *after* is upward-entailing:
    weakening B (expanding its time trace) preserves "A after B."
    This is why *after* does NOT license NPIs. -/
theorem Anscombe.after_complement_UE (A B B' : SentDenotation Time)
    (h : timeTrace B ⊆ timeTrace B') :
    Anscombe.after A B → Anscombe.after A B' := by
  rintro ⟨t, ht, t', ht', hlt⟩
  exact ⟨t, ht, t', h ht', hlt⟩

/-- DE + UE are in the right direction: *before* entails downward in the
    complement (licenses NPIs), *after* entails upward (blocks NPIs).
    Stated as a single theorem for the contrast. -/
theorem npi_licensing_from_monotonicity (A B B' : SentDenotation Time) :
    -- DE direction: shrinking B preserves before
    (timeTrace B' ⊆ timeTrace B → Anscombe.before A B → Anscombe.before A B') ∧
    -- UE direction: expanding B preserves after
    (timeTrace B ⊆ timeTrace B' → Anscombe.after A B → Anscombe.after A B') :=
  ⟨Anscombe.before_complement_DE A B B', Anscombe.after_complement_UE A B B'⟩

end Semantics.Tense.TemporalConnectives
