/-!
# Constraint Evaluation

Unified framework for constraint-based candidate evaluation, supporting
two comparison modes:

1. **Lexicographic** (Optimality Theory): constraints are strictly ranked;
   the first constraint where candidates differ determines the winner.
   Used in phonology (Prince & Smolensky 1993/2004) and syntactic
   competition (Erlewine 2016).

2. **Subset inclusion** (Satisfaction ordering): a candidate is at least
   as good as another iff it satisfies every criterion the other satisfies.
   Used in Kratzer's (1991) modal semantics (see `SatisfactionOrdering.lean`).

Both select optimal candidates from a set. They differ in comparison:
`lexLE` yields a total order (OT always picks a winner); `satLE` yields
a partial order (incomparable candidates possible, as in Kratzer's semantics).

## Connection to SatisfactionOrdering

`Core.SatisfactionOrdering.SatisfactionOrdering` is the special case where
violations are binary (0 = satisfied, ≥1 = violated) and comparison uses
subset inclusion (`satLE`). A `SatisfactionOrdering` with criteria
[c₁, ..., cₙ] induces the profile `fun a => [if satisfies a c₁ then 0
else 1, ..., if satisfies a cₙ then 0 else 1]`, and `atLeastAsGood`
coincides with `satLE` on this profile.

## References

- Prince, A. & P. Smolensky (1993/2004). Optimality Theory: Constraint
  Interaction in Generative Grammar.
- Kratzer, A. (1991). Modality. In von Stechow & Wunderlich (eds.),
  Semantics: An International Handbook.
- Erlewine, M. Y. (2016). Anti-locality and optimality in Kaqchikel
  Agent Focus. NALS 24: 923–972.
-/

namespace Core.ConstraintEvaluation

-- ============================================================================
-- § 1: Lexicographic Comparison (Optimality Theory)
-- ============================================================================

/-- Lexicographic ≤ on violation profiles (lists of violation counts).

    Each position is a constraint, ranked highest (head) to lowest (tail).
    At the first position where profiles differ, fewer violations wins.
    Missing entries are implicitly 0 (no violation).

    `lexLE a b = true` means "a is at least as harmonic as b." -/
def lexLE : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => true
  | a :: as, [] => a == 0 && lexLE as []
  | a :: as, b :: bs =>
    if a < b then true
    else if b < a then false
    else lexLE as bs

/-- Strict lexicographic <: a is strictly more harmonic than b. -/
def lexLT (a b : List Nat) : Bool := lexLE a b && !lexLE b a

-- ============================================================================
-- § 2: Subset Comparison (Satisfaction Ordering)
-- ============================================================================

/-- Subset-inclusion ≤ on violation profiles.

    `satLE a b = true` iff every constraint that b satisfies (0 violations),
    a also satisfies. Superset-inclusion on sets of satisfied constraints.

    Unlike `lexLE`, this is a partial order — two candidates may be
    incomparable if each satisfies constraints the other violates.
    This is Kratzer's (1991) ordering on worlds relative to a premise set. -/
def satLE : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => true
  | a :: as, [] => a == 0 && satLE as []
  | a :: as, b :: bs =>
    (b != 0 || a == 0) && satLE as bs

-- ============================================================================
-- § 3: OT Tableau
-- ============================================================================

/-- An OT tableau: candidates evaluated against ranked constraints.

    `profile c` gives the violation list for candidate `c`, with
    position 0 = highest-ranked constraint. -/
structure OTTableau (Candidate : Type) where
  candidates : List Candidate
  profile : Candidate → List Nat
  nonempty : candidates ≠ []

variable {Candidate : Type}

/-- Optimal candidates: those not lexicographically dominated.

    In a well-formed OT tableau this is typically a singleton —
    strict ranking ensures a unique winner when profiles differ. -/
def OTTableau.optimal (t : OTTableau Candidate) : List Candidate :=
  t.candidates.filter fun c =>
    t.candidates.all fun c' => lexLE (t.profile c) (t.profile c')

/-- Satisfaction-optimal: those not dominated under subset inclusion.
    May contain multiple candidates (partial order). -/
def OTTableau.satOptimal (t : OTTableau Candidate) : List Candidate :=
  t.candidates.filter fun c =>
    t.candidates.all fun c' => satLE (t.profile c) (t.profile c')

-- ============================================================================
-- § 4: Properties
-- ============================================================================

/-- Lexicographic ≤ is reflexive. -/
theorem lexLE_refl : (a : List Nat) → lexLE a a = true
  | [] => rfl
  | x :: xs => by
    simp only [lexLE, Nat.lt_irrefl, ite_false]
    exact lexLE_refl xs

/-- `!b || b = true` for any `Bool`. -/
private theorem Bool.not_or_self (b : Bool) : (!b || b) = true := by cases b <;> rfl

/-- Satisfaction ≤ is reflexive. -/
theorem satLE_refl : (a : List Nat) → satLE a a = true
  | [] => rfl
  | x :: xs => by
    unfold satLE
    have h1 : (x != 0 || x == 0) = true := by
      show (!(x == 0) || (x == 0)) = true
      exact Bool.not_or_self (x == 0)
    rw [h1, Bool.true_and]
    exact satLE_refl xs

/-- Lexicographic ≤ is total for equal-length profiles: OT always
    determines a winner (modulo ties). Key difference from `satLE`. -/
theorem lexLE_total (a b : List Nat) (h : a.length = b.length) :
    lexLE a b = true ∨ lexLE b a = true := by
  induction a generalizing b with
  | nil => cases b with
    | nil => exact Or.inl rfl
    | cons _ _ => simp at h
  | cons x xs ih => cases b with
    | nil => simp at h
    | cons y ys =>
      have hlen : xs.length = ys.length := by simpa using h
      unfold lexLE
      by_cases hxy : x < y
      · simp [hxy]
      · by_cases hyx : y < x
        · simp [hxy]; right; simp [hyx]
        · have : x = y := by omega
          subst this; simp [Nat.lt_irrefl]
          exact ih ys hlen

/-- `satLE` is NOT total: candidates can be incomparable when each
    satisfies a constraint the other violates. -/
theorem satLE_not_total : ¬∀ (a b : List Nat), satLE a b = true ∨ satLE b a = true := by
  intro h
  have := h [0, 1] [1, 0]
  cases this with
  | inl h => exact absurd h (by native_decide)
  | inr h => exact absurd h (by native_decide)

/-- Optimal candidates are drawn from the candidate set. -/
theorem optimal_subset (t : OTTableau Candidate) (c : Candidate) :
    c ∈ t.optimal → c ∈ t.candidates :=
  fun hc => (List.mem_filter.mp hc).1

-- ============================================================================
-- § 5: Bidirectional OT — Superoptimality (Blutner 2000)
-- ============================================================================

/-- A pair ⟨f, m⟩ is **blocked** by another pair ⟨f', m'⟩ in set `s` iff:
    1. They share exactly one dimension (same form or same meaning, not both),
    2. The blocker is strictly more harmonic (lexicographic <).

    This is the blocking relation for Blutner's (2000) superoptimality,
    used by de Hoop & Malchukov (2008) for bidirectional case optimization. -/
private def blocked {F M : Type} [BEq F] [BEq M]
    (profile : F × M → List Nat)
    (s : List (F × M)) (p : F × M) : Bool :=
  s.any λ q =>
    ((q.1 == p.1 && !(q.2 == p.2)) || (!(q.1 == p.1) && q.2 == p.2)) &&
    lexLT (profile q) (profile p)

/-- Fixed-point iteration: remove blocked pairs until stable.
    Fuel is bounded by the initial list length (each round removes ≥ 1). -/
private def superoptLoop {F M : Type} [BEq F] [BEq M]
    (profile : F × M → List Nat)
    : List (F × M) → Nat → List (F × M)
  | s, 0 => s
  | s, fuel + 1 =>
    let s' := s.filter λ p => !blocked profile s p
    if s'.length == s.length then s else superoptLoop profile s' fuel

/-- Blutner's (2000) **superoptimal** pairs: the largest set S such that
    no element of S blocks another element of S.

    A pair ⟨f, m⟩ is superoptimal iff:
    - No other superoptimal ⟨f', m⟩ (same meaning) is strictly more harmonic
    - No other superoptimal ⟨f, m'⟩ (same form) is strictly more harmonic

    Computed as a fixed point: start with all pairs, iteratively remove
    blocked pairs until stable. For finite candidate sets this always
    terminates within |pairs| rounds. -/
def superoptimal {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M))
    (profile : F × M → List Nat) : List (F × M) :=
  superoptLoop profile pairs pairs.length

end Core.ConstraintEvaluation
