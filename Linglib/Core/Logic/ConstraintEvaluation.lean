/-!
# Constraint Evaluation
@cite{erlewine-2016} @cite{kratzer-1991}

Unified framework for constraint-based candidate evaluation, supporting
two comparison modes:

1. **Lexicographic** (Optimality Theory): constraints are strictly ranked;
   the first constraint where candidates differ determines the winner.
   Used in phonology (@cite{prince-smolensky-1993}/2004) and syntactic
   competition.

2. **Subset inclusion** (Satisfaction ordering): a candidate is at least
   as good as another iff it satisfies every criterion the other satisfies.
   Used in @cite{kratzer-1991}'s modal semantics (see `SatisfactionOrdering.lean`).

Both select optimal candidates from a set. They differ in comparison:
`lexLE` yields a total order (OT always picks a winner); `satLE` yields
a partial order (incomparable candidates possible, as in Kratzer's semantics).

## Connection to SatisfactionOrdering

`Core.SatisfactionOrdering.SatisfactionOrdering` is the special case where
violations are binary (0 = satisfied, ≥1 = violated) and comparison uses
subset inclusion (`satLE`). A `SatisfactionOrdering` with criteria
[c₁,..., cₙ] induces the profile `fun a => [if satisfies a c₁ then 0
else 1,..., if satisfies a cₙ then 0 else 1]`, and `atLeastAsGood`
coincides with `satLE` on this profile.

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
    This is @cite{kratzer-1991}'s ordering on worlds relative to a premise set. -/
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
-- § 4b: lexLE Transitivity — Total Preorder
-- ============================================================================

/-- `lexLE` with empty left is always true: the empty profile is
    vacuously at least as harmonic as any profile. -/
theorem lexLE_nil (b : List Nat) : lexLE [] b = true := by cases b <;> rfl

/-- Characterization of `lexLE (x :: xs) []`: all entries must be zero. -/
private theorem lexLE_cons_nil_iff (x : Nat) (xs : List Nat) :
    lexLE (x :: xs) [] = true ↔ x = 0 ∧ lexLE xs [] = true := by
  show (x == 0 && lexLE xs []) = true ↔ _
  rw [Bool.and_eq_true, beq_iff_eq]

/-- Characterization of `lexLE (x :: xs) (y :: ys)`: either the head is
    strictly less, or the heads are equal and the tails are ≤. -/
theorem lexLE_cons_cons_iff (x y : Nat) (xs ys : List Nat) :
    lexLE (x :: xs) (y :: ys) = true ↔
    (x < y ∨ (x = y ∧ lexLE xs ys = true)) := by
  show (if x < y then true else if y < x then false else lexLE xs ys) = true ↔ _
  constructor
  · intro h
    by_cases hxy : x < y
    · exact Or.inl hxy
    · rw [if_neg hxy] at h
      by_cases hyx : y < x
      · rw [if_pos hyx] at h; exact absurd h Bool.false_ne_true
      · rw [if_neg hyx] at h
        exact Or.inr ⟨by omega, h⟩
  · intro h
    cases h with
    | inl hlt => rw [if_pos hlt]
    | inr heq =>
      obtain ⟨rfl, htail⟩ := heq
      rw [if_neg (Nat.lt_irrefl x), if_neg (Nat.lt_irrefl x)]
      exact htail

/-- If `lexLE a [] = true` (all entries are zero), then `lexLE a c = true`
    for any `c`. The all-zeros profile is the minimum under `lexLE`. -/
theorem lexLE_of_nil_right : ∀ (a : List Nat),
    lexLE a [] = true → ∀ (c : List Nat), lexLE a c = true
  | [], _, c => lexLE_nil c
  | x :: xs, h, c => by
    rw [lexLE_cons_nil_iff] at h
    obtain ⟨rfl, hxs⟩ := h
    cases c with
    | nil => rw [lexLE_cons_nil_iff]; exact ⟨rfl, hxs⟩
    | cons z zs =>
      rw [lexLE_cons_cons_iff]
      by_cases hz : (0 : Nat) < z
      · exact Or.inl hz
      · have : z = 0 := by omega
        subst this
        exact Or.inr ⟨rfl, lexLE_of_nil_right xs hxs zs⟩

/-- Lexicographic ≤ is transitive. Together with `lexLE_refl` and
    `lexLE_total`, this makes `lexLE` a **total preorder** on
    equal-length profiles — the correct algebraic structure for
    OT harmony ordering. -/
theorem lexLE_trans : ∀ (a b c : List Nat),
    lexLE a b = true → lexLE b c = true → lexLE a c = true
  | [], _, c, _, _ => lexLE_nil c
  | _ :: _, [], c, hab, _ => lexLE_of_nil_right _ hab c
  | x :: xs, y :: ys, [], hab, hbc => by
    rw [lexLE_cons_nil_iff] at hbc
    rw [lexLE_cons_cons_iff] at hab
    rw [lexLE_cons_nil_iff]
    cases hab with
    | inl hxy => exact absurd hxy (by omega)  -- x < 0 impossible
    | inr heq =>
      obtain ⟨rfl, hxsys⟩ := heq
      exact ⟨hbc.1, lexLE_trans xs ys [] hxsys hbc.2⟩
  | x :: xs, y :: ys, z :: zs, hab, hbc => by
    rw [lexLE_cons_cons_iff] at hab hbc ⊢
    cases hab with
    | inl hxy =>
      cases hbc with
      | inl hyz => exact Or.inl (by omega)
      | inr heq => obtain ⟨rfl, _⟩ := heq; exact Or.inl hxy
    | inr heq =>
      obtain ⟨rfl, hxsys⟩ := heq
      cases hbc with
      | inl hyz => exact Or.inl hyz
      | inr heq2 =>
        obtain ⟨rfl, hyszs⟩ := heq2
        exact Or.inr ⟨rfl, lexLE_trans xs ys zs hxsys hyszs⟩

/-- Lexicographic < is irreflexive. -/
theorem lexLT_irrefl (a : List Nat) : lexLT a a = false := by
  simp [lexLT, lexLE_refl]

/-- Lexicographic < is asymmetric: `a < b → ¬(b < a)`. -/
theorem lexLT_asymm (a b : List Nat) (h : lexLT a b = true) :
    lexLT b a = false := by
  unfold lexLT at h ⊢
  rw [Bool.and_eq_true] at h
  simp [h.1]

-- ============================================================================
-- § 4c: Minimum Element Existence
-- ============================================================================

/-- A non-empty list has a minimum element under `lexLE`, provided all
    profiles have equal length. This is the key ingredient for
    `optimal_nonempty`: OT always picks at least one winner. -/
theorem exists_lexLE_minimum {α : Type} (xs : List α) (hne : xs ≠ [])
    (f : α → List Nat)
    (hlen : ∀ a ∈ xs, ∀ b ∈ xs, (f a).length = (f b).length) :
    ∃ x ∈ xs, ∀ y ∈ xs, lexLE (f x) (f y) = true := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    by_cases hrest : rest = []
    · subst hrest
      exact ⟨a, .head _, fun y hy => by
        cases hy with
        | head => exact lexLE_refl (f a)
        | tail _ h => nomatch h⟩
    · have hlen' : ∀ c ∈ rest, ∀ d ∈ rest, (f c).length = (f d).length :=
        fun c hc d hd => hlen c (.tail a hc) d (.tail a hd)
      obtain ⟨m, hm_mem, hm_min⟩ := ih hrest hlen'
      have hlen_am : (f a).length = (f m).length :=
        hlen a (.head _) m (.tail a hm_mem)
      cases lexLE_total (f a) (f m) hlen_am with
      | inl ham =>
        exact ⟨a, .head _, fun y hy => by
          cases hy with
          | head => exact lexLE_refl (f a)
          | tail _ h => exact lexLE_trans (f a) (f m) (f y) ham (hm_min y h)⟩
      | inr hma =>
        exact ⟨m, .tail a hm_mem, fun y hy => by
          cases hy with
          | head => exact hma
          | tail _ h => exact hm_min y h⟩

-- ============================================================================
-- § 5: Bidirectional OT — Superoptimality (@cite{blutner-2000})
-- ============================================================================

/-- A pair ⟨f, m⟩ is **blocked** by another pair ⟨f', m'⟩ in set `s` iff:
    1. They share exactly one dimension (same form or same meaning, not both),
    2. The blocker is strictly more harmonic (lexicographic <).

    This is the blocking relation for @cite{blutner-2000}'s superoptimality,
    used by @cite{de-hoop-malchukov-2008} for bidirectional case optimization. -/
def blocked {F M : Type} [BEq F] [BEq M]
    (profile : F × M → List Nat)
    (s : List (F × M)) (p : F × M) : Bool :=
  s.any λ q =>
    ((q.1 == p.1 && !(q.2 == p.2)) || (!(q.1 == p.1) && q.2 == p.2)) &&
    lexLT (profile q) (profile p)

/-- Iterative removal: remove blocked pairs from current set until stable.
    Fuel is bounded by the initial list length (each round removes ≥ 1). -/
private def iterativeSuperoptLoop {F M : Type} [BEq F] [BEq M]
    (profile : F × M → List Nat)
    : List (F × M) → Nat → List (F × M)
  | s, 0 => s
  | s, fuel + 1 =>
    let s' := s.filter λ p => !blocked profile s p
    if s'.length == s.length then s else iterativeSuperoptLoop profile s' fuel

/-- Iterative-removal superoptimality: start with all pairs, remove those
    blocked by any remaining pair, repeat until stable.

    **Important**: this algorithm is equivalent to strong BiOT (eq. 9 of
    @cite{blutner-2000}) for typical cases — once a pair is removed, it
    can never return, even if its blockers are themselves eliminated.
    For @cite{blutner-2000}'s weak BiOT (eq. 14), use `superoptimal`,
    which correctly re-evaluates against all original pairs each round. -/
def iterativeSuperoptimal {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M))
    (profile : F × M → List Nat) : List (F × M) :=
  iterativeSuperoptLoop profile pairs pairs.length

-- ============================================================================
-- § 6: Superoptimality — Greatest Fixed Point (@cite{blutner-2000})
-- ============================================================================

/-- Greatest-fixed-point iteration for @cite{blutner-2000}'s superoptimality
    (eq. 14). Each round re-evaluates ALL original pairs against the current
    survivor set, so pairs removed in one round can return if their blockers
    were also removed.

    Converges because the operator Φ²(S) is monotone on finite lattices
    (Φ is anti-monotone: fewer survivors → fewer blockers → more survivors).
    Bounded by 2·|pairs| iterations. -/
private def superoptLoop {F M : Type} [BEq F] [BEq M]
    (profile : F × M → List Nat) (pairs : List (F × M))
    : List (F × M) → Nat → List (F × M)
  | s, 0 => s
  | s, fuel + 1 =>
    let s' := pairs.filter λ p => !blocked profile s p
    if s' == s then s' else superoptLoop profile pairs s' fuel

/-- @cite{blutner-2000}'s **superoptimality** (eq. 14): the greatest
    fixed point S = {p ∈ Gen | no q ∈ S blocks p}.

    A pair ⟨A, τ⟩ is super-optimal iff:
    - (Q) No other super-optimal ⟨A', τ⟩ (same meaning) is strictly better
    - (I) No other super-optimal ⟨A, τ'⟩ (same form) is strictly better

    The Q- and I-principles mutually constrain each other: competition under
    Q is restricted to I-surviving pairs, and vice versa. This derives
    @cite{horn-1984}'s division of pragmatic labour: unmarked forms pair with
    unmarked (stereotypical) meanings, marked forms with marked meanings.

    Differs from `iterativeSuperoptimal` (iterative removal) when indirect
    blocking creates cycles — `superoptimal` correctly re-admits pairs whose
    blockers were themselves eliminated. -/
def superoptimal {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M))
    (profile : F × M → List Nat) : List (F × M) :=
  superoptLoop profile pairs pairs (2 * pairs.length)

-- ============================================================================
-- § 7: Strong Bidirectional OT (@cite{blutner-2000} eq. 9)
-- ============================================================================

/-- @cite{blutner-2000}'s **strong bidirectional OT** (eq. 9): Q and I are
    evaluated independently against the full candidate set.

    ⟨A, τ⟩ is optimal iff:
    - (Q) No pair ⟨A', τ⟩ in Gen (same meaning) is strictly better
    - (I) No pair ⟨A, τ'⟩ in Gen (same form) is strictly better

    Unlike superoptimality (eq. 14), the two directions do not constrain
    each other. Strong-optimal ⊆ super-optimal: every strong-optimal pair
    is also super-optimal, but superoptimality can admit additional pairs
    (marked forms for marked meanings). -/
def strongOptimal {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M))
    (profile : F × M → List Nat) : List (F × M) :=
  pairs.filter fun p =>
    -- Q: no better form for same meaning
    !pairs.any (fun q => !(q.1 == p.1) && q.2 == p.2 && lexLT (profile q) (profile p)) &&
    -- I: no better meaning for same form
    !pairs.any (fun q => q.1 == p.1 && !(q.2 == p.2) && lexLT (profile q) (profile p))

-- ============================================================================
-- § 8: Properties of Superoptimality
-- ============================================================================

/-- `blocked` is anti-monotone in the witness set: if no element of a
    larger set blocks `p`, then no element of a subset can block it either. -/
private theorem blocked_anti_mono {F M : Type} [BEq F] [BEq M]
    (profile : F × M → List Nat) (s₁ s₂ : List (F × M)) (p : F × M)
    (hsub : ∀ q, q ∈ s₁ → q ∈ s₂)
    (h : blocked profile s₂ p = false) :
    blocked profile s₁ p = false := by
  unfold blocked at *
  rw [Bool.eq_false_iff] at *
  intro hb
  apply h
  rw [List.any_eq_true] at hb ⊢
  obtain ⟨q, hq_mem, hq_pred⟩ := hb
  exact ⟨q, hsub q hq_mem, hq_pred⟩

/-- Loop invariant: a pair that is in `pairs` and not blocked by `pairs`
    survives every round of `superoptLoop`. -/
private theorem superoptLoop_preserves {F M : Type} [BEq F] [BEq M]
    (profile : F × M → List Nat) (pairs : List (F × M))
    (p : F × M) (hp : p ∈ pairs) (hnb : blocked profile pairs p = false)
    (s : List (F × M)) (fuel : Nat)
    (hps : p ∈ s) (hsub : ∀ q, q ∈ s → q ∈ pairs) :
    p ∈ superoptLoop profile pairs s fuel := by
  induction fuel generalizing s with
  | zero => exact hps
  | succ n ih =>
    unfold superoptLoop
    simp only
    have hp_in_s' : p ∈ pairs.filter (fun q => !blocked profile s q) := by
      rw [List.mem_filter]
      constructor
      · exact hp
      · simp only [Bool.not_eq_true']
        exact blocked_anti_mono profile s pairs p hsub hnb
    split
    · exact hp_in_s'
    · apply ih
      · exact hp_in_s'
      · intro q hq
        exact (List.mem_filter.mp hq).1

/-- A pair that belongs to `pairs` and is not blocked by any element
    of `pairs` is in `superoptimal pairs profile`. -/
theorem superoptimal_of_unblocked {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) (hp : p ∈ pairs)
    (hnb : blocked profile pairs p = false) :
    p ∈ superoptimal pairs profile := by
  unfold superoptimal
  exact superoptLoop_preserves profile pairs p hp hnb
    pairs (2 * pairs.length) hp (fun _ h => h)

end Core.ConstraintEvaluation
