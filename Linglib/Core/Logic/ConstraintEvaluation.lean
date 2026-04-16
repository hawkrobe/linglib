import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.PiLex
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Tropical.Basic

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
`LexLE` yields a total preorder (OT always picks a winner); `SatLE` yields
a preorder (incomparable candidates possible, as in Kratzer's semantics).

## Architecture

Each comparison is a decidable Prop relation (`LexLE`, `SatLE`, `LexLT`).
`Decidable` instances are defined by structural recursion, delegating to
standard combinators (`And.decidable`, `Or.decidable`). Optimality is a
predicate (`IsOptimal`, `IsSatOptimal`); the list-producing `optimal` /
`satOptimal` are derived computations for concrete evaluation
(`native_decide`).

## Algebraic Structure — Violation Semiring

Following @cite{riggle-2009}, violation profiles form a **commutative
semiring** (the "violation semiring") with two operations:

- **⊎ (merge)**: componentwise addition of violation counts — combining
  violations from multiple constraints. This is the `AddCommMonoid`.
- **⊗ (choose winner)**: `min` under harmonic inequality — selecting the
  more harmonic candidate. This is `min` from the `LinearOrder`.

The compatibility axiom (`add_le_add_left`) is Riggle's **distributivity**:
adding violations to both candidates preserves which one wins. This is
the structural property that makes OT optimization decomposable — every
subpath of an optimal path is itself optimal (Dijkstra's principle).

`ViolationProfile n` carries a `LinearOrder` (the ⊗ operation), an
`AddCommMonoid` (the ⊎ operation), and `IsOrderedAddMonoid` (the
compatibility axiom). Together, these encode Riggle's violation semiring
as a standard mathlib ordered monoid.

Different OT variants correspond to different ordered monoids on the
same carrier: classical OT uses lexicographic order; Harmonic Grammar
uses weighted-sum order (the standard tropical semiring).

## Order Instances

**Variable-length** (`LexProfile`, `SatProfile`): wrap `List Nat` with
`Preorder` instances. These are the weakest correct structures — `LexLE`
on variable-length lists is a preorder but not a partial order
(trailing-zero ambiguity).

**Fixed-length** (`ViolationProfile n`, `SatViolationProfile n`): wrap
`Fin n → Nat` with full `LinearOrder` (lexicographic) or `Preorder`
(satisfaction). Fixing the length eliminates the trailing-zero ambiguity,
upgrading `LexLE` to a linear order: reflexive, transitive,
**antisymmetric**, and **total**.

`Tableau C n` is a `Finset`-based OT tableau with `ViolationProfile n`
profiles. Optimality always exists via `Finset.exists_min_image`.

## Connection to SatisfactionOrdering

`Core.SatisfactionOrdering.SatisfactionOrdering` is the special case where
violations are binary (0 = satisfied, ≥1 = violated) and comparison uses
subset inclusion (`SatLE`). A `SatisfactionOrdering` with criteria
[c₁,..., cₙ] induces the profile `fun a => [if satisfies a c₁ then 0
else 1,..., if satisfies a cₙ then 0 else 1]`, and `atLeastAsGood`
coincides with `SatLE` on this profile.

-/

namespace Core.ConstraintEvaluation

-- ============================================================================
-- § 1: Prop Relations
-- ============================================================================

/-- Lexicographic ≤ on violation profiles.

    `LexLE a b` holds iff `a` is at least as harmonic as `b` — at the first
    position where profiles differ, `a` has fewer violations. Missing entries
    are implicitly 0. -/
def LexLE : List Nat → List Nat → Prop
  | [], _ => True
  | a :: as, [] => a = 0 ∧ LexLE as []
  | a :: as, b :: bs => a < b ∨ (a = b ∧ LexLE as bs)

/-- Subset-inclusion ≤ on violation profiles.

    `SatLE a b` holds iff every constraint that `b` satisfies (has 0
    violations), `a` also satisfies. This is a **preorder** (reflexive,
    transitive) but not a partial order on `List Nat` — non-zero values
    are interchangeable (e.g., `SatLE [1] [2]` and `SatLE [2] [1]` both
    hold). On binary {0,1} profiles it becomes a partial order.

    Unlike `LexLE`, `SatLE` is not total — incomparable candidates are
    possible. This is @cite{kratzer-1991}'s ordering on worlds relative
    to a premise set. -/
def SatLE : List Nat → List Nat → Prop
  | [], _ => True
  | a :: as, [] => a = 0 ∧ SatLE as []
  | a :: as, b :: bs => (b ≠ 0 ∨ a = 0) ∧ SatLE as bs

/-- Strict lexicographic <. -/
def LexLT (a b : List Nat) : Prop := LexLE a b ∧ ¬ LexLE b a

-- ============================================================================
-- § 2: Decidability
-- ============================================================================

instance instDecidableLexLE : (a b : List Nat) → Decidable (LexLE a b)
  | [], b => isTrue (by cases b <;> trivial)
  | a :: as, [] =>
    have : Decidable (LexLE as []) := instDecidableLexLE as []
    inferInstanceAs (Decidable (a = 0 ∧ LexLE as []))
  | a :: as, b :: bs =>
    have : Decidable (LexLE as bs) := instDecidableLexLE as bs
    inferInstanceAs (Decidable (a < b ∨ (a = b ∧ LexLE as bs)))

instance instDecidableSatLE : (a b : List Nat) → Decidable (SatLE a b)
  | [], b => isTrue (by cases b <;> trivial)
  | a :: as, [] =>
    have : Decidable (SatLE as []) := instDecidableSatLE as []
    inferInstanceAs (Decidable (a = 0 ∧ SatLE as []))
  | a :: as, b :: bs =>
    have : Decidable (SatLE as bs) := instDecidableSatLE as bs
    inferInstanceAs (Decidable ((b ≠ 0 ∨ a = 0) ∧ SatLE as bs))

instance instDecidableLexLT (a b : List Nat) : Decidable (LexLT a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

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

/-- `c` is optimal in tableau `t`: it is a candidate and lexicographically
    ≤ every other candidate. In a well-formed OT tableau this is typically
    unique — strict ranking ensures a unique winner when profiles differ. -/
def OTTableau.IsOptimal (t : OTTableau Candidate) (c : Candidate) : Prop :=
  c ∈ t.candidates ∧ ∀ c' ∈ t.candidates, LexLE (t.profile c) (t.profile c')

/-- `c` is satisfaction-optimal: it is a candidate and satisfaction ≤ every
    other candidate. May have multiple optimal candidates (partial order). -/
def OTTableau.IsSatOptimal (t : OTTableau Candidate) (c : Candidate) : Prop :=
  c ∈ t.candidates ∧ ∀ c' ∈ t.candidates, SatLE (t.profile c) (t.profile c')

/-- Computable list of optimal candidates (for `native_decide` proofs). -/
def OTTableau.optimal (t : OTTableau Candidate) : List Candidate :=
  t.candidates.filter fun c =>
    t.candidates.all fun c' => decide (LexLE (t.profile c) (t.profile c'))

/-- Computable list of satisfaction-optimal candidates. -/
def OTTableau.satOptimal (t : OTTableau Candidate) : List Candidate :=
  t.candidates.filter fun c =>
    t.candidates.all fun c' => decide (SatLE (t.profile c) (t.profile c'))

/-- `c ∈ t.optimal` iff `t.IsOptimal c`. -/
theorem mem_optimal_iff (t : OTTableau Candidate) (c : Candidate) :
    c ∈ t.optimal ↔ t.IsOptimal c := by
  simp only [OTTableau.optimal, OTTableau.IsOptimal, List.mem_filter,
    List.all_eq_true, decide_eq_true_eq]

/-- `c ∈ t.satOptimal` iff `t.IsSatOptimal c`. -/
theorem mem_satOptimal_iff (t : OTTableau Candidate) (c : Candidate) :
    c ∈ t.satOptimal ↔ t.IsSatOptimal c := by
  simp only [OTTableau.satOptimal, OTTableau.IsSatOptimal, List.mem_filter,
    List.all_eq_true, decide_eq_true_eq]

-- ============================================================================
-- § 4: Properties
-- ============================================================================

/-- Lexicographic ≤ is reflexive. -/
theorem lexLE_refl : (a : List Nat) → LexLE a a
  | [] => trivial
  | _ :: xs => .inr ⟨rfl, lexLE_refl xs⟩

/-- Satisfaction ≤ is reflexive. -/
theorem satLE_refl : (a : List Nat) → SatLE a a
  | [] => trivial
  | x :: xs => ⟨if h : x = 0 then .inr h else .inl h, satLE_refl xs⟩

/-- Lexicographic ≤ is total for equal-length profiles: OT always
    determines a winner (modulo ties). Key difference from `SatLE`. -/
theorem lexLE_total (a b : List Nat) (h : a.length = b.length) :
    LexLE a b ∨ LexLE b a := by
  induction a generalizing b with
  | nil => cases b with
    | nil => exact Or.inl trivial
    | cons _ _ => simp at h
  | cons x xs ih => cases b with
    | nil => simp at h
    | cons y ys =>
      have hlen : xs.length = ys.length := by simpa using h
      by_cases hxy : x < y
      · exact Or.inl (.inl hxy)
      · by_cases hyx : y < x
        · exact Or.inr (.inl hyx)
        · have heq : x = y := by omega
          subst heq
          exact (ih ys hlen).elim
            (fun h => Or.inl (.inr ⟨rfl, h⟩))
            (fun h => Or.inr (.inr ⟨rfl, h⟩))

/-- `SatLE` is NOT total: candidates can be incomparable when each
    satisfies a constraint the other violates. -/
theorem satLE_not_total : ¬∀ (a b : List Nat), SatLE a b ∨ SatLE b a := by
  intro h
  have := h [0, 1] [1, 0]
  cases this with
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)

/-- Optimal candidates are drawn from the candidate set. -/
theorem optimal_subset (t : OTTableau Candidate) (c : Candidate) :
    c ∈ t.optimal → c ∈ t.candidates :=
  fun hc => (List.mem_filter.mp hc).1

-- ============================================================================
-- § 4b: LexLE Structural Lemmas
-- ============================================================================

/-- `LexLE [] b` holds for any `b`: the empty profile is vacuously
    at least as harmonic as any profile. -/
theorem lexLE_nil (b : List Nat) : LexLE [] b := by
  cases b <;> trivial

/-- Characterization of `LexLE (x :: xs) []`: all entries must be zero. -/
theorem lexLE_cons_nil_iff (x : Nat) (xs : List Nat) :
    LexLE (x :: xs) [] ↔ x = 0 ∧ LexLE xs [] :=
  Iff.rfl

/-- Characterization of `LexLE (x :: xs) (y :: ys)`: either the head is
    strictly less, or the heads are equal and the tails are ≤. -/
theorem lexLE_cons_cons_iff (x y : Nat) (xs ys : List Nat) :
    LexLE (x :: xs) (y :: ys) ↔
    (x < y ∨ (x = y ∧ LexLE xs ys)) :=
  Iff.rfl

-- ============================================================================
-- § 4c: LexLE Transitivity — Total Preorder
-- ============================================================================

/-- If `LexLE a [] ` (all entries are zero), then `LexLE a c`
    for any `c`. The all-zeros profile is the minimum under `LexLE`. -/
theorem lexLE_of_nil_right : ∀ (a : List Nat),
    LexLE a [] → ∀ (c : List Nat), LexLE a c
  | [], _, c => lexLE_nil c
  | x :: xs, h, c => by
    obtain ⟨rfl, hxs⟩ := h
    cases c with
    | nil => exact ⟨rfl, hxs⟩
    | cons z zs =>
      by_cases hz : (0 : Nat) < z
      · exact .inl hz
      · have : z = 0 := by omega
        subst this
        exact .inr ⟨rfl, lexLE_of_nil_right xs hxs zs⟩

/-- Lexicographic ≤ is transitive. Together with `lexLE_refl` and
    `lexLE_total`, this makes `LexLE` a **total preorder** on
    equal-length profiles — the correct algebraic structure for
    OT harmony ordering. -/
theorem lexLE_trans : ∀ (a b c : List Nat),
    LexLE a b → LexLE b c → LexLE a c
  | [], _, c, _, _ => lexLE_nil c
  | _ :: _, [], c, hab, _ => lexLE_of_nil_right _ hab c
  | x :: xs, y :: ys, [], hab, hbc => by
    obtain hlt | ⟨rfl, htl⟩ := hab
    · obtain ⟨rfl, _⟩ := hbc; omega
    · exact ⟨hbc.1, lexLE_trans xs ys [] htl hbc.2⟩
  | x :: xs, y :: ys, z :: zs, hab, hbc => by
    obtain hlt₁ | ⟨rfl, htl₁⟩ := hab
    · obtain hlt₂ | ⟨rfl, _⟩ := hbc
      · exact .inl (by omega)
      · exact .inl hlt₁
    · obtain hlt₂ | ⟨rfl, htl₂⟩ := hbc
      · exact .inl hlt₂
      · exact .inr ⟨rfl, lexLE_trans xs ys zs htl₁ htl₂⟩

/-- Lexicographic < is irreflexive. -/
theorem lexLT_irrefl (a : List Nat) : ¬ LexLT a a :=
  fun ⟨h, hn⟩ => hn h

/-- Lexicographic < is asymmetric: `LexLT a b → ¬ LexLT b a`. -/
theorem lexLT_asymm (a b : List Nat) (h : LexLT a b) :
    ¬ LexLT b a :=
  fun ⟨hba, _⟩ => h.2 hba

/-- Lexicographic ≤ is antisymmetric on equal-length profiles: if two
    profiles of the same length are mutually ≤, they are equal.

    This fails on `List Nat` in general (`LexLE [] [0]` and `LexLE [0] []`
    both hold, but `[] ≠ [0]`) — the equal-length precondition eliminates
    the trailing-zero ambiguity that makes `LexLE` merely a preorder. -/
theorem lexLE_antisymm : ∀ (a b : List Nat),
    a.length = b.length → LexLE a b → LexLE b a → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | x :: xs, y :: ys, h, hab, hba => by
    have hlen : xs.length = ys.length := by simpa using h
    rcases hab with hlt | ⟨rfl, htl⟩
    · rcases hba with hlt' | ⟨rfl, _⟩ <;> omega
    · rcases hba with hlt' | ⟨_, htl'⟩
      · omega
      · exact congrArg _ (lexLE_antisymm xs ys hlen htl htl')

-- ============================================================================
-- § 4d: Minimum Element Existence
-- ============================================================================

/-- A non-empty list has a minimum element under `LexLE`, provided all
    profiles have equal length. This is the key ingredient for
    `optimal_nonempty`: OT always picks at least one winner. -/
theorem exists_lexLE_minimum {α : Type} (xs : List α) (hne : xs ≠ [])
    (f : α → List Nat)
    (hlen : ∀ a ∈ xs, ∀ b ∈ xs, (f a).length = (f b).length) :
    ∃ x ∈ xs, ∀ y ∈ xs, LexLE (f x) (f y) := by
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
-- § 4e: SatLE Structural Lemmas
-- ============================================================================

/-- `SatLE [] b` holds for any `b`: the empty profile vacuously
    satisfies the inclusion condition. -/
theorem satLE_nil (b : List Nat) : SatLE [] b := by
  cases b <;> trivial

/-- Characterization of `SatLE (x :: xs) []`: all entries must be zero. -/
theorem satLE_cons_nil_iff (x : Nat) (xs : List Nat) :
    SatLE (x :: xs) [] ↔ x = 0 ∧ SatLE xs [] :=
  Iff.rfl

/-- Characterization of `SatLE (x :: xs) (y :: ys)`: if `y` is satisfied
    (zero) then `x` must also be satisfied, and the tails must be ordered. -/
theorem satLE_cons_cons_iff (x y : Nat) (xs ys : List Nat) :
    SatLE (x :: xs) (y :: ys) ↔ (y ≠ 0 ∨ x = 0) ∧ SatLE xs ys :=
  Iff.rfl

-- ============================================================================
-- § 4f: SatLE Transitivity — Preorder
-- ============================================================================

/-- If `SatLE a []` (all entries are zero), then `SatLE a c`
    for any `c`. The all-zeros profile is the minimum under `SatLE`. -/
theorem satLE_of_nil_right : ∀ (a : List Nat),
    SatLE a [] → ∀ (c : List Nat), SatLE a c
  | [], _, c => satLE_nil c
  | _ :: xs, ⟨rfl, hxs⟩, c => by
    cases c with
    | nil => exact ⟨rfl, hxs⟩
    | cons _ zs => exact ⟨.inr rfl, satLE_of_nil_right xs hxs zs⟩

/-- Satisfaction ≤ is transitive. Together with `satLE_refl`, this
    makes `SatLE` a **preorder** on violation profiles. Unlike `LexLE`,
    `SatLE` is NOT antisymmetric on `List Nat` (see `satLE_not_antisymm`)
    — it IS antisymmetric on binary {0,1} profiles, where it becomes a
    partial order. -/
theorem satLE_trans : ∀ (a b c : List Nat),
    SatLE a b → SatLE b c → SatLE a c
  | [], _, c, _, _ => satLE_nil c
  | _ :: _, [], c, hab, _ => satLE_of_nil_right _ hab c
  | _ :: xs, _ :: ys, [], ⟨hab1, hab2⟩, ⟨rfl, hbc2⟩ => by
    refine ⟨?_, satLE_trans xs ys [] hab2 hbc2⟩
    rcases hab1 with h | h
    · exact absurd rfl h
    · exact h
  | _ :: xs, _ :: ys, _ :: zs, ⟨hab1, hab2⟩, ⟨hbc1, hbc2⟩ => by
    refine ⟨?_, satLE_trans xs ys zs hab2 hbc2⟩
    rcases hbc1 with hz | rfl
    · exact .inl hz
    · rcases hab1 with h | h
      · exact absurd rfl h
      · exact .inr h

/-- `SatLE` is **not antisymmetric** on `List Nat`: non-zero values
    are interchangeable since `SatLE` only distinguishes 0 from ≥1. -/
theorem satLE_not_antisymm :
    ¬∀ (a b : List Nat), SatLE a b → SatLE b a → a = b := by
  intro h
  exact absurd (h [1] [2] (by decide) (by decide)) (by decide)


-- ============================================================================
-- § 5: Bidirectional OT — Blocking (@cite{blutner-2000})
-- ============================================================================

/-- A pair ⟨f, m⟩ is **blocked** by some pair in set `s` iff there exists
    a pair sharing exactly one dimension (same form or same meaning, not
    both) that is strictly more harmonic (lexicographic <).

    This is the blocking relation for @cite{blutner-2000}'s superoptimality,
    used by @cite{de-hoop-malchukov-2008} for bidirectional case optimization. -/
def IsBlocked {F M : Type} [DecidableEq F] [DecidableEq M]
    (profile : F × M → List Nat)
    (s : List (F × M)) (p : F × M) : Prop :=
  ∃ q ∈ s, ((q.1 = p.1 ∧ q.2 ≠ p.2) ∨ (q.1 ≠ p.1 ∧ q.2 = p.2)) ∧
    LexLT (profile q) (profile p)

/-- Computable blocking check (for `native_decide` proofs). -/
def blocked {F M : Type} [DecidableEq F] [DecidableEq M]
    (profile : F × M → List Nat)
    (s : List (F × M)) (p : F × M) : Bool :=
  s.any fun q =>
    decide (((q.1 = p.1 ∧ q.2 ≠ p.2) ∨ (q.1 ≠ p.1 ∧ q.2 = p.2)) ∧
      LexLT (profile q) (profile p))

/-- `blocked` computes `IsBlocked`. -/
theorem isBlocked_iff_blocked {F M : Type} [DecidableEq F] [DecidableEq M]
    (profile : F × M → List Nat) (s : List (F × M)) (p : F × M) :
    IsBlocked profile s p ↔ blocked profile s p = true := by
  simp only [IsBlocked, blocked, List.any_eq_true, decide_eq_true_eq]

-- ============================================================================
-- § 6: Iterative Removal (@cite{blutner-2000})
-- ============================================================================

/-- Iterative removal: remove blocked pairs from current set until stable.
    Fuel is bounded by the initial list length (each round removes ≥ 1). -/
private def iterativeSuperoptLoop {F M : Type} [DecidableEq F] [DecidableEq M]
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
def iterativeSuperoptimal {F M : Type} [DecidableEq F] [DecidableEq M]
    (pairs : List (F × M))
    (profile : F × M → List Nat) : List (F × M) :=
  iterativeSuperoptLoop profile pairs pairs.length

-- ============================================================================
-- § 7: Superoptimality — Greatest Fixed Point (@cite{blutner-2000})
-- ============================================================================

/-- Greatest-fixed-point iteration for @cite{blutner-2000}'s superoptimality
    (eq. 14). Each round re-evaluates ALL original pairs against the current
    survivor set, so pairs removed in one round can return if their blockers
    were also removed.

    Converges because the operator Φ²(S) is monotone on finite lattices
    (Φ is anti-monotone: fewer survivors → fewer blockers → more survivors).
    Bounded by 2·|pairs| iterations. -/
private def superoptLoop {F M : Type} [DecidableEq F] [DecidableEq M]
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
def superoptimal {F M : Type} [DecidableEq F] [DecidableEq M]
    (pairs : List (F × M))
    (profile : F × M → List Nat) : List (F × M) :=
  superoptLoop profile pairs pairs (2 * pairs.length)

-- ============================================================================
-- § 8: Strong Bidirectional OT (@cite{blutner-2000} eq. 9)
-- ============================================================================

/-- @cite{blutner-2000}'s **strong bidirectional OT** (eq. 9): Q and I are
    evaluated independently against the full candidate set.

    ⟨A, τ⟩ is strong-optimal iff:
    - (Q) No pair ⟨A', τ⟩ in Gen (same meaning) is strictly better
    - (I) No pair ⟨A, τ'⟩ in Gen (same form) is strictly better

    Unlike superoptimality (eq. 14), the two directions do not constrain
    each other. Strong-optimal ⊆ super-optimal: every strong-optimal pair
    is also super-optimal, but superoptimality can admit additional pairs
    (marked forms for marked meanings). -/
def IsStrongOptimal {F M : Type} [DecidableEq F] [DecidableEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat) (p : F × M) : Prop :=
  p ∈ pairs ∧
  (∀ q ∈ pairs, q.2 = p.2 → q.1 ≠ p.1 → ¬LexLT (profile q) (profile p)) ∧
  (∀ q ∈ pairs, q.1 = p.1 → q.2 ≠ p.2 → ¬LexLT (profile q) (profile p))

/-- Computable strong-optimal set (for `native_decide` proofs). -/
def strongOptimal {F M : Type} [DecidableEq F] [DecidableEq M]
    (pairs : List (F × M))
    (profile : F × M → List Nat) : List (F × M) :=
  pairs.filter fun p =>
    -- Q: no better form for same meaning
    pairs.all (fun q =>
      decide (q.2 = p.2 → q.1 ≠ p.1 → ¬LexLT (profile q) (profile p))) &&
    -- I: no better meaning for same form
    pairs.all (fun q =>
      decide (q.1 = p.1 → q.2 ≠ p.2 → ¬LexLT (profile q) (profile p)))

/-- `p ∈ strongOptimal` iff `IsStrongOptimal`. -/
theorem mem_strongOptimal_iff {F M : Type} [DecidableEq F] [DecidableEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat) (p : F × M) :
    p ∈ strongOptimal pairs profile ↔ IsStrongOptimal pairs profile p := by
  simp only [strongOptimal, IsStrongOptimal, List.mem_filter,
    Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

-- ============================================================================
-- § 9: Properties of Superoptimality
-- ============================================================================

/-- `blocked` is anti-monotone in the witness set: if no element of a
    larger set blocks `p`, then no element of a subset can block it either. -/
private theorem blocked_anti_mono {F M : Type} [DecidableEq F] [DecidableEq M]
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
private theorem superoptLoop_preserves {F M : Type} [DecidableEq F] [DecidableEq M]
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
theorem superoptimal_of_unblocked {F M : Type} [DecidableEq F] [DecidableEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) (hp : p ∈ pairs)
    (hnb : blocked profile pairs p = false) :
    p ∈ superoptimal pairs profile := by
  unfold superoptimal
  exact superoptLoop_preserves profile pairs p hp hnb
    pairs (2 * pairs.length) hp (fun _ h => h)

-- ============================================================================
-- § 10: LexProfile — Variable-Length Lexicographic Preorder
-- ============================================================================

/-- Violation profile ordered by lexicographic ≤ (OT harmony ordering).

    Wraps `List Nat` so that `≤` means `LexLE` — the standard OT
    comparison where the first differing constraint determines the winner.
    This is a `Preorder` (reflexive, transitive) but not a `PartialOrder`
    on `List Nat`: trailing zeros are invisible (`LexLE [] [0]` and
    `LexLE [0] []` both hold). For a `LinearOrder` on fixed-length profiles,
    use `ViolationProfile n`. -/
structure LexProfile where
  profile : List Nat
  deriving DecidableEq, Repr

instance : LE LexProfile where le a b := LexLE a.profile b.profile
instance : LT LexProfile where lt a b := LexLE a.profile b.profile ∧ ¬ LexLE b.profile a.profile

instance : Preorder LexProfile where
  le_refl a := lexLE_refl a.profile
  le_trans a b c := lexLE_trans a.profile b.profile c.profile

instance (a b : LexProfile) : Decidable (a ≤ b) :=
  instDecidableLexLE a.profile b.profile

instance (a b : LexProfile) : Decidable (a < b) :=
  inferInstanceAs (Decidable (LexLE a.profile b.profile ∧ ¬ LexLE b.profile a.profile))

/-- `LexProfile.≤` is definitionally `LexLE`. -/
theorem LexProfile.le_iff (a b : LexProfile) :
    a ≤ b ↔ LexLE a.profile b.profile := Iff.rfl

/-- `LexProfile.<` is definitionally `LexLT`. -/
theorem LexProfile.lt_iff (a b : LexProfile) :
    a < b ↔ LexLT a.profile b.profile := Iff.rfl

/-- `LexLE` is total on equal-length profiles, expressed via `LexProfile`. -/
theorem LexProfile.le_total (a b : LexProfile)
    (h : a.profile.length = b.profile.length) :
    a ≤ b ∨ b ≤ a :=
  lexLE_total a.profile b.profile h

-- ============================================================================
-- § 11: SatProfile — Variable-Length Satisfaction Preorder
-- ============================================================================

/-- Violation profile ordered by satisfaction ≤ (Kratzer ordering).

    Wraps `List Nat` so that `≤` means `SatLE` — a candidate is at least
    as good as another iff it satisfies every constraint the other satisfies.
    This is a `Preorder` (reflexive, transitive) but neither antisymmetric
    (non-zero values are interchangeable) nor total (incomparable candidates
    are possible). -/
structure SatProfile where
  profile : List Nat
  deriving DecidableEq, Repr

instance : LE SatProfile where le a b := SatLE a.profile b.profile
instance : LT SatProfile where lt a b := SatLE a.profile b.profile ∧ ¬ SatLE b.profile a.profile

instance : Preorder SatProfile where
  le_refl a := satLE_refl a.profile
  le_trans a b c := satLE_trans a.profile b.profile c.profile

instance (a b : SatProfile) : Decidable (a ≤ b) :=
  instDecidableSatLE a.profile b.profile

instance (a b : SatProfile) : Decidable (a < b) :=
  inferInstanceAs (Decidable (SatLE a.profile b.profile ∧ ¬ SatLE b.profile a.profile))

/-- `SatProfile.≤` is definitionally `SatLE`. -/
theorem SatProfile.le_iff (a b : SatProfile) :
    a ≤ b ↔ SatLE a.profile b.profile := Iff.rfl

/-- `SatLE` is NOT total: incomparable candidates are possible. -/
theorem SatProfile.not_le_total :
    ¬∀ (a b : SatProfile), a ≤ b ∨ b ≤ a := by
  intro h
  exact satLE_not_total fun a b => h ⟨a⟩ ⟨b⟩

-- ============================================================================
-- § 12: ViolationProfile n — Fixed-Length Lexicographic Linear Order
-- ============================================================================

/-- Fixed-length violation profile: `n` constraints, each recording a natural
    number of violations.

    Defined as `Lex (Fin n → Nat)` — mathlib's type synonym that equips
    Pi-types with lexicographic ordering. The three layers of structure are:

    - **`LinearOrder`**: from `Pi.Lex` — lexicographic comparison
      (`min` = Riggle's ⊗, choose winner)
    - **`AddCommMonoid`**: componentwise addition of violation counts
      (Riggle's ⊎, merge violations)
    - **`IsOrderedCancelAddMonoid`**: compatibility — adding violations
      preserves the harmony ordering (Riggle's distributivity, Dijkstra's
      principle)

    Unlike `LexProfile` (which wraps `List Nat` and is only a `Preorder`),
    `ViolationProfile n` is a full `LinearOrder`: reflexive, transitive,
    **antisymmetric**, and **total**. The linear order guarantees that every
    non-empty candidate set has a unique minimum (= the OT winner). -/
abbrev ViolationProfile (n : Nat) := Lex (Fin n → Nat)

-- The linear order comes from mathlib's Pi.Lex:
-- Pi.Lex (· < ·) (· < ·) a b ↔ ∃ i, (∀ j < i, a j = b j) ∧ a i < b i
noncomputable example : LinearOrder (ViolationProfile 3) := inferInstance

-- Extensionality for ViolationProfile (Lex has no @[ext] instance)
private theorem vp_ext {n : Nat} {a b : ViolationProfile n}
    (h : ∀ i, a i = b i) : a = b :=
  show toLex (ofLex a) = toLex (ofLex b) from congrArg toLex (funext h)

-- `Add` and `Zero` are inherited from `instAddLex`/`instZeroLex`
-- (which lift `Pi.instAdd` and `Pi.instZero` through the Lex synonym).
-- Pointwise semantics hold definitionally:
example (n : Nat) (a b : ViolationProfile n) (i : Fin n) :
    (a + b) i = a i + b i := rfl
example (n : Nat) (i : Fin n) : (0 : ViolationProfile n) i = 0 := rfl

-- `AddCommMonoid` is NOT lifted automatically (Lex deliberately strips
-- algebraic instances — mathlib's PiLex.lean has `assert_not_exists Monoid`).
-- We prove the axioms manually; Lean picks up `instAddLex`/`instZeroLex`
-- as parent instances, so there is no instance diamond.
instance (n : Nat) : AddCommMonoid (ViolationProfile n) where
  add_assoc a b c := vp_ext fun i => Nat.add_assoc ..
  zero_add a := vp_ext fun i => Nat.zero_add ..
  add_zero a := vp_ext fun i => Nat.add_zero ..
  add_comm a b := vp_ext fun i => Nat.add_comm ..
  nsmul := nsmulRec

/-- `ViolationProfile n` is an ordered additive commutative monoid:
    componentwise addition of violations preserves the lexicographic
    ordering. This is @cite{riggle-2009}'s violation semiring — the
    `AddCommMonoid` is the ⊎ (merge) operation, and `min` from the
    `LinearOrder` is the ⊗ (choose winner) operation. Distributivity
    of ⊗ over ⊎ is exactly `add_le_add_left`.

    The proof works by transferring the lex existential witness: if
    `a < b` at position `i` with all earlier positions equal, then
    `a + c < b + c` at the same position `i` (Nat addition preserves
    strict inequality). -/
instance (n : Nat) : IsOrderedAddMonoid (ViolationProfile n) where
  add_le_add_left a b hab c := by
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · apply le_of_lt
      obtain ⟨i, hpre, hi⟩ := hlt
      exact ⟨i,
        fun j hj => show a j + c j = b j + c j by rw [hpre j hj],
        Nat.add_lt_add_right hi (c i)⟩

/-- Left cancellation for lexicographic ≤: if `a + b ≤ a + c` then `b ≤ c`.
    This strengthens the ordered monoid to an ordered **cancel** monoid,
    which is needed for the tropical semiring derivation. -/
instance (n : Nat) : IsOrderedCancelAddMonoid (ViolationProfile n) where
  le_of_add_le_add_left a b c hab := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · exact le_of_eq (vp_ext fun i => Nat.add_left_cancel (congrFun heq i))
    · apply le_of_lt
      obtain ⟨i, hpre, hi⟩ := hlt
      exact ⟨i,
        fun j hj => Nat.add_left_cancel (hpre j hj),
        Nat.lt_of_add_lt_add_left hi⟩

-- ============================================================================
-- § 12a: Backward Compatibility — vpLE
-- ============================================================================

/-- Lexicographic ≤ on `Fin n → Nat`, defined by recursion on `n`.
    Retained for backward compatibility and computable decidability.
    Equivalent to `¬ Pi.Lex (· < ·) (· < ·) b a`. -/
def vpLE : (n : Nat) → (Fin n → Nat) → (Fin n → Nat) → Prop
  | 0, _, _ => True
  | _ + 1, a, b => a 0 < b 0 ∨ (a 0 = b 0 ∧ vpLE _ (a ∘ Fin.succ) (b ∘ Fin.succ))

instance instDecidableVpLE : (n : Nat) → (a b : Fin n → Nat) → Decidable (vpLE n a b)
  | 0, _, _ => isTrue trivial
  | _ + 1, a, b =>
    have : Decidable (vpLE _ (a ∘ Fin.succ) (b ∘ Fin.succ)) :=
      instDecidableVpLE _ _ _
    inferInstanceAs (Decidable (a 0 < b 0 ∨ (a 0 = b 0 ∧ vpLE _ _ _)))

-- ============================================================================
-- § 12b: Tropical Semiring Derivation (@cite{riggle-2009})
-- ============================================================================

/-- `WithTop (ViolationProfile n)` is a `LinearOrderedAddCommMonoidWithTop`:
    it extends the ordered cancel monoid with a top element (V^∞ in Riggle's
    notation) that absorbs addition. This is the final prerequisite for the
    tropical semiring — mathlib's `Tropical` wrapper then gives us
    `CommSemiring (Tropical (WithTop (ViolationProfile n)))` for free. -/
noncomputable instance (n : Nat) :
    LinearOrderedAddCommMonoidWithTop (WithTop (ViolationProfile n)) where
  top_add' := WithTop.top_add
  isAddLeftRegular_of_ne_top := by
    intro x hx a b hab
    cases x with
    | top => exact absurd rfl hx
    | coe x =>
      cases a with
      | top =>
        cases b with
        | top => rfl
        | coe b =>
          simp only [WithTop.add_top] at hab
          exact absurd hab WithTop.top_ne_coe
      | coe a =>
        cases b with
        | top =>
          simp only [WithTop.add_top] at hab
          exact absurd hab.symm WithTop.top_ne_coe
        | coe b =>
          dsimp at hab
          have h : x + a = x + b := WithTop.coe_injective hab
          exact congrArg _ (le_antisymm
            (le_of_add_le_add_left (le_of_eq h))
            (le_of_add_le_add_left (le_of_eq h.symm)))

/-- **Riggle's violation semiring**: for any number of constraints `n`,
    `Tropical (WithTop (ViolationProfile n))` is automatically a
    `CommSemiring` where:

    - **Tropical addition** (`⊕`) = `min` under harmonic inequality —
      choosing the more harmonic candidate (Riggle's ⊗)
    - **Tropical multiplication** (`⊗`) = componentwise `+` of violation
      counts — merging violations from multiple constraints (Riggle's ⊎)
    - **Additive identity** (`0`) = `⊤` (V^∞) — the infinitely bad candidate
      that loses to everything
    - **Multiplicative identity** (`1`) = the zero profile — the perfect
      candidate with no violations

    This is *derived*, not stipulated: we define `ViolationProfile n` as
    `Lex (Fin n → Nat)` with `LinearOrder` (from Pi.Lex), `AddCommMonoid`
    (componentwise), and `IsOrderedCancelAddMonoid` (compatibility), then
    `WithTop` adds the absorbing top element, and mathlib's `Tropical`
    wrapper provides the semiring structure automatically via `inferInstance`. -/
noncomputable example (n : Nat) :
    CommSemiring (Tropical (WithTop (ViolationProfile n))) :=
  inferInstance

-- ============================================================================
-- § 13: SatViolationProfile n — Fixed-Length Satisfaction Preorder
-- ============================================================================

/-- Pointwise satisfaction ≤ on `Fin n → Nat`: `a ≤ b` iff every constraint
    that `b` satisfies (has 0 violations), `a` also satisfies.

    This is a `Preorder` but not a `PartialOrder`: non-zero values are
    interchangeable (e.g., `[1] ≤ [2]` and `[2] ≤ [1]` both hold). -/
def svpLE {n : Nat} (a b : Fin n → Nat) : Prop :=
  ∀ i : Fin n, b i = 0 → a i = 0

instance {n : Nat} (a b : Fin n → Nat) : Decidable (svpLE a b) :=
  Fintype.decidableForallFintype

/-- Fixed-length violation profile ordered by satisfaction ≤
    (Kratzer ordering). `a ≤ b` iff `a` satisfies every constraint that `b`
    satisfies. -/
@[ext]
structure SatViolationProfile (n : Nat) where
  val : Fin n → Nat
  deriving DecidableEq

instance (n : Nat) : LE (SatViolationProfile n) where le a b := svpLE a.val b.val
instance (n : Nat) : LT (SatViolationProfile n) where lt a b := a ≤ b ∧ ¬ b ≤ a

instance (n : Nat) : Preorder (SatViolationProfile n) where
  le_refl a := fun _ h => h
  le_trans a b c hab hbc := fun i hi => hab i (hbc i hi)

instance {n : Nat} (a b : SatViolationProfile n) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (svpLE a.val b.val))

instance {n : Nat} (a b : SatViolationProfile n) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

-- ============================================================================
-- § 14: Tableau — Finset-Based OT Tableau
-- ============================================================================

/-- An OT tableau with `n` ranked constraints and candidate type `C`.

    Uses `Finset C` for the candidate set (guaranteeing finiteness and
    deduplication) and `ViolationProfile n` for profiles (guaranteeing
    fixed length and providing `LinearOrder`).

    Compare with `OTTableau` above, which uses `List Candidate` and
    `List Nat` for maximal simplicity in downstream evaluations. `Tableau`
    is the mathematically precise version. -/
structure Tableau (C : Type) [DecidableEq C] (n : Nat) where
  candidates : Finset C
  profile : C → ViolationProfile n
  nonempty : candidates.Nonempty

variable {C : Type} [DecidableEq C] {n : Nat}

/-- A candidate is optimal iff it belongs to the candidate set and its
    profile is ≤ every other candidate's profile. -/
def Tableau.IsOptimal (t : Tableau C n) (c : C) : Prop :=
  c ∈ t.candidates ∧ ∀ c' ∈ t.candidates, t.profile c ≤ t.profile c'

/-- **Every tableau has an optimal candidate.** This is the structural
    guarantee of OT: the `LinearOrder` on `ViolationProfile n` ensures
    a minimum always exists in any non-empty finite set.

    Proof delegates to `Finset.exists_min_image` — the general fact that
    a linear-ordered image of a non-empty finset has a minimum. -/
theorem Tableau.exists_optimal (t : Tableau C n) : ∃ c, t.IsOptimal c := by
  obtain ⟨c, hc_mem, hc_min⟩ := Finset.exists_min_image t.candidates t.profile t.nonempty
  exact ⟨c, hc_mem, hc_min⟩

/-- Set of optimal candidates. Noncomputable because the `LinearOrder` on
    `ViolationProfile n` is derived from `Pi.Lex` (classical). For concrete
    OT evaluation, use `OTTableau.optimal` (List-based, fully computable). -/
noncomputable def Tableau.optimal (t : Tableau C n) : Finset C :=
  t.candidates.filter fun c =>
    ∀ c' ∈ t.candidates, t.profile c ≤ t.profile c'

/-- `c ∈ t.optimal` iff `t.IsOptimal c`. -/
theorem Tableau.mem_optimal_iff (t : Tableau C n) (c : C) :
    c ∈ t.optimal ↔ t.IsOptimal c := by
  simp only [Tableau.optimal, Finset.mem_filter, Tableau.IsOptimal]

/-- The optimal set is always non-empty: OT always picks a winner. -/
theorem Tableau.optimal_nonempty (t : Tableau C n) : t.optimal.Nonempty := by
  obtain ⟨c, hc⟩ := t.exists_optimal
  exact ⟨c, (t.mem_optimal_iff c).mpr hc⟩

end Core.ConstraintEvaluation
