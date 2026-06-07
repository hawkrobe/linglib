import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.PiLex
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Tropical.Basic

/-!
# Lexicographic and subset-inclusion orders on `Nat`-valued profiles

Two comparison relations on lists / functions to `ℕ`:

1. **Lexicographic** (`LexLE`): yields a total preorder on `List Nat`
   and a `LinearOrder` on the fixed-length `Lex (Fin n → Nat)`.
2. **Subset inclusion** (`SatLE`): yields a preorder where
   incomparable elements are possible.

## Architecture

`LexLE`, `SatLE`, `LexLT` are decidable `Prop` relations defined by
structural recursion, delegating to standard combinators
(`And.decidable`, `Or.decidable`). `LexMinProblem C n` packages a finite
candidate set with a `Fin n → Nat`-valued score, exposing the
non-empty lex-min set via `Finset.exists_min_image`.

## Algebraic structure — ordered additive monoid

`Lex (Fin n → Nat)` carries:

- **`AddCommMonoid`** — componentwise addition.
- **`LinearOrder`** — the lex order.
- **`IsOrderedAddMonoid`** — additive monotonicity: adding the same
  vector to both sides preserves the lex order.
- **`IsOrderedCancelAddMonoid`** — strict version of the above.

Together these say: `Lex (Fin n → Nat)` is a standard mathlib ordered
commutative monoid. Equivalently, the tropical (min-plus) semiring
view via `Mathlib.Algebra.Tropical.Basic`.

## Variable-length vs fixed-length

**Variable-length** (`LexNatList`): wraps `List Nat` with `Preorder`
instances. Weakest correct structure — `LexLE` on variable-length lists
is a preorder but not a partial order (trailing-zero ambiguity).

**Fixed-length** (`Lex (Fin n → Nat)`, accessed as `LexProfile Nat n`):
full `LinearOrder` (lex). Fixing the length eliminates trailing-zero
ambiguity, upgrading `LexLE` to a linear order. `LexMinProblem C n`
always has a non-empty lex-min set via `Finset.exists_min_image`.

## Connection to `SatisfactionOrdering`

`Core.Order.SatisfactionOrdering` is the binary case
(`0`/`≥ 1` interpreted as "satisfied" / "not") with subset-inclusion
comparison.
-/

namespace Core.Optimization.Evaluation


-- ============================================================================
-- § 1: Prop Relations
-- ============================================================================

/-- Lexicographic ≤ on `List Nat` (interpretable as cost vectors).

    `LexLE a b` holds iff `a` is below `b` at the first position where they differ.
    Trailing entries are implicitly 0. -/
def LexLE : List Nat → List Nat → Prop
  | [], _ => True
  | a :: as, [] => a = 0 ∧ LexLE as []
  | a :: as, b :: bs => a < b ∨ (a = b ∧ LexLE as bs)

/-- Subset-inclusion ≤ on `List Nat`.

    `SatLE a b` holds iff every coordinate at which `b` is `0`, `a` is also `0`. A
    **preorder** (reflexive, transitive) but not a partial order on
    `List Nat` — non-zero values are interchangeable (e.g., `SatLE [1] [2]`
    and `SatLE [2] [1]` both hold). On binary `{0,1}` profiles it becomes
    a partial order. Unlike `LexLE`, `SatLE` is not total. See
    [kratzer-1991] for the linguistic application (ordering of worlds
    relative to a premise set). -/
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
-- § 3: Properties
-- ============================================================================

/-- Lexicographic ≤ is reflexive. -/
theorem lexLE_refl : (a : List Nat) → LexLE a a
  | [] => trivial
  | _ :: xs => .inr ⟨rfl, lexLE_refl xs⟩

/-- Satisfaction ≤ is reflexive. -/
theorem satLE_refl : (a : List Nat) → SatLE a a
  | [] => trivial
  | x :: xs => ⟨if h : x = 0 then .inr h else .inl h, satLE_refl xs⟩

/-- Lexicographic ≤ is total for equal-length profiles. Key difference
    from `SatLE`. -/
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

/-- `SatLE` is NOT total: profiles can be incomparable when each is
    nonzero where the other is zero, and vice versa. -/
theorem satLE_not_total : ¬∀ (a b : List Nat), SatLE a b ∨ SatLE b a := by
  intro h
  have := h [0, 1] [1, 0]
  cases this with
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)

-- ============================================================================
-- § 3b: LexLE Structural Lemmas
-- ============================================================================

/-- `LexLE [] b` holds for any `b`: the empty list is vacuously
    at-most-as-large-as any list. -/
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
    lex order. -/
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

/-- Lexicographic < is transitive: `LexLT a b → LexLT b c → LexLT a c`. -/
theorem lexLT_trans (a b c : List Nat)
    (hab : LexLT a b) (hbc : LexLT b c) : LexLT a c :=
  ⟨lexLE_trans _ _ _ hab.1 hbc.1,
   fun hca => hab.2 (lexLE_trans _ _ _ hbc.1 hca)⟩

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
    `optimal_nonempty`: the lex-min set is non-empty. -/
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
    makes `SatLE` a **preorder**. Unlike `LexLE`,
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
-- § 10: LexNatList — Variable-Length Lexicographic Preorder
-- ============================================================================

/-- `List Nat` wrapped to carry the `LexLE`-`Preorder` instance.

    The bare `List Nat` doesn't carry a `Preorder` from `LexLE` (mathlib
    leaves it ambiguous); this thin wrapper provides one. Only a
    `Preorder` — not a `PartialOrder` — since trailing zeros are invisible
    (`LexLE [] [0]` and `LexLE [0] []` both hold). For a `LinearOrder`,
    use fixed-length `Lex (Fin n → Nat)` (aka `LexProfile Nat n`). -/
structure LexNatList where
  value : List Nat
  deriving DecidableEq, Repr

instance : LE LexNatList where le a b := LexLE a.value b.value
instance : LT LexNatList where lt a b := LexLE a.value b.value ∧ ¬ LexLE b.value a.value

instance : Preorder LexNatList where
  le_refl a := lexLE_refl a.value
  le_trans a b c := lexLE_trans a.value b.value c.value

instance (a b : LexNatList) : Decidable (a ≤ b) :=
  instDecidableLexLE a.value b.value

instance (a b : LexNatList) : Decidable (a < b) :=
  inferInstanceAs (Decidable (LexLE a.value b.value ∧ ¬ LexLE b.value a.value))

/-- `LexNatList.≤` is definitionally `LexLE`. -/
theorem LexNatList.le_iff (a b : LexNatList) :
    a ≤ b ↔ LexLE a.value b.value := Iff.rfl

/-- `LexNatList.<` is definitionally `LexLT`. -/
theorem LexNatList.lt_iff (a b : LexNatList) :
    a < b ↔ LexLT a.value b.value := Iff.rfl

/-- `LexLE` is total on equal-length values, expressed via `LexNatList`. -/
theorem LexNatList.le_total (a b : LexNatList)
    (h : a.value.length = b.value.length) :
    a ≤ b ∨ b ≤ a :=
  lexLE_total a.value b.value h


-- ============================================================================
-- § 12: Instances on `Lex (Fin n → Nat)`
-- ============================================================================

/-- Extensionality helper for `Lex (Fin n → Nat)` (mathlib's `Lex`
    deliberately has no `@[ext]`). -/
private theorem lexFin_ext {n : Nat} {a b : Lex (Fin n → Nat)}
    (h : ∀ i, a i = b i) : a = b :=
  show toLex (ofLex a) = toLex (ofLex b) from congrArg toLex (funext h)

/-- Pointwise addition on `Lex (Fin n → Nat)` reduces componentwise. -/
theorem lexFinNat_add_apply {n : Nat}
    (a b : Lex (Fin n → Nat)) (i : Fin n) :
    (a + b) i = a i + b i := rfl

/-- The zero `Lex (Fin n → Nat)` is pointwise zero. -/
theorem lexFinNat_zero_apply {n : Nat} (i : Fin n) :
    (0 : Lex (Fin n → Nat)) i = 0 := rfl

-- `AddCommMonoid` is NOT lifted automatically (Lex deliberately strips
-- algebraic instances — mathlib's PiLex.lean has `assert_not_exists Monoid`).
-- We prove the axioms manually; Lean picks up `instAddLex`/`instZeroLex`
-- as parent instances, so there is no instance diamond.
instance (n : Nat) : AddCommMonoid (Lex (Fin n → Nat)) where
  add_assoc a b c := lexFin_ext fun i => Nat.add_assoc ..
  zero_add a := lexFin_ext fun i => Nat.zero_add ..
  add_zero a := lexFin_ext fun i => Nat.add_zero ..
  add_comm a b := lexFin_ext fun i => Nat.add_comm ..
  nsmul := nsmulRec

/-- `Lex (Fin n → Nat)` is an ordered additive commutative monoid:
    componentwise addition preserves the lexicographic ordering. The
    proof transfers the lex existential witness: if `a < b` at position
    `i` with all earlier positions equal, then `a + c < b + c` at the
    same position. -/
instance (n : Nat) : IsOrderedAddMonoid (Lex (Fin n → Nat)) where
  add_le_add_left a b hab c := by
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · apply le_of_lt
      obtain ⟨i, hpre, hi⟩ := hlt
      exact ⟨i,
        fun j hj => show a j + c j = b j + c j by rw [hpre j hj],
        Nat.add_lt_add_right hi (c i)⟩

/-- Left cancellation for lexicographic ≤. -/
instance (n : Nat) : IsOrderedCancelAddMonoid (Lex (Fin n → Nat)) where
  le_of_add_le_add_left a b c hab := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · exact le_of_eq (lexFin_ext fun i => Nat.add_left_cancel (congrFun heq i))
    · apply le_of_lt
      obtain ⟨i, hpre, hi⟩ := hlt
      exact ⟨i,
        fun j hj => Nat.add_left_cancel (hpre j hj),
        Nat.lt_of_add_lt_add_left hi⟩

-- ============================================================================
-- § 12a: Decidable Ordering on `Lex (Fin n → Nat)`
-- ============================================================================

/-- Recursive computable lex-≤ on `Fin n → Nat` (decision procedure for the
    noncomputable `Pi.Lex` order). -/
private def lexFinNatLE : (n : Nat) → (Fin n → Nat) → (Fin n → Nat) → Prop
  | 0, _, _ => True
  | _ + 1, a, b => a 0 < b 0 ∨ (a 0 = b 0 ∧ lexFinNatLE _ (a ∘ Fin.succ) (b ∘ Fin.succ))

private instance instDecidableLexFinNatLE :
    (n : Nat) → (a b : Fin n → Nat) → Decidable (lexFinNatLE n a b)
  | 0, _, _ => isTrue trivial
  | _ + 1, a, b =>
    have : Decidable (lexFinNatLE _ (a ∘ Fin.succ) (b ∘ Fin.succ)) :=
      instDecidableLexFinNatLE _ _ _
    inferInstanceAs (Decidable (a 0 < b 0 ∨ (a 0 = b 0 ∧ lexFinNatLE _ _ _)))

/-- `lexFinNatLE` is the negation of `Pi.Lex (· < ·) (· < ·) b a`. Proof
    by induction on `n`: the recursive structure of `lexFinNatLE`
    (head + tail) mirrors the existential structure of `Pi.Lex` (first
    differing position). -/
private theorem lexFinNatLE_iff_not_lt :
    (n : Nat) → (a b : Fin n → Nat) →
    lexFinNatLE n a b ↔
      ¬ (∃ i : Fin n, (∀ j : Fin n, j < i → b j = a j) ∧ b i < a i)
  | 0, _, _ => by
    constructor
    · intro _ ⟨i, _, _⟩; exact i.elim0
    · intro _; exact trivial
  | n + 1, a, b => by
    constructor
    · intro hvp ⟨i, hpre, hlt⟩
      rcases hvp with h_head_lt | ⟨h_head_eq, h_tail⟩
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact absurd hlt (Nat.not_lt.mpr (Nat.le_of_lt h_head_lt))
        · exact absurd (hpre 0 (Fin.succ_pos j)).symm (Nat.ne_of_lt h_head_lt)
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact absurd hlt (Nat.not_lt.mpr (le_of_eq h_head_eq))
        · exact absurd ⟨j,
            fun k hk => hpre k.succ (Fin.succ_lt_succ_iff.mpr hk), hlt⟩
            ((lexFinNatLE_iff_not_lt n (a ∘ Fin.succ) (b ∘ Fin.succ)).mp h_tail)
    · intro hno
      rcases Nat.lt_trichotomy (a 0) (b 0) with hlt | heq | hgt
      · exact Or.inl hlt
      · right; exact ⟨heq,
          (lexFinNatLE_iff_not_lt n (a ∘ Fin.succ) (b ∘ Fin.succ)).mpr fun ⟨j, hp, hl⟩ =>
            hno ⟨j.succ,
              fun k hk => by
                rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
                · exact heq.symm
                · exact hp k' (Fin.succ_lt_succ_iff.mp hk),
              hl⟩⟩
      · exact absurd ⟨(0 : Fin (n + 1)),
          fun j hj => absurd hj (Fin.not_lt_zero j), hgt⟩ hno

/-- Bridge: `lexFinNatLE` agrees with `≤` on `Lex (Fin n → Nat)`. -/
theorem lexFinNatLE_iff_le {n : Nat} (a b : Lex (Fin n → Nat)) :
    lexFinNatLE n a b ↔ a ≤ b := by
  rw [show a ≤ b ↔ ¬ (b < a) from not_lt.symm]
  exact lexFinNatLE_iff_not_lt n a b

/-- Decidable `≤` on `Lex (Fin n → Nat)`. The `LinearOrder` from `Pi.Lex`
    is noncomputable, but this instance provides decidable comparison via
    the recursive `lexFinNatLE`, making downstream `by decide` work. -/
instance instDecidableLexFinNatProfileLE {n : Nat} (a b : Lex (Fin n → Nat)) :
    Decidable (a ≤ b) :=
  decidable_of_iff (lexFinNatLE n a b) (lexFinNatLE_iff_le a b)

/-- Decidable `<` on `Lex (Fin n → Nat)`. -/
instance instDecidableLexFinNatProfileLT {n : Nat} (a b : Lex (Fin n → Nat)) :
    Decidable (a < b) :=
  decidable_of_iff (¬ b ≤ a) (@not_le _ _ b a)

-- ============================================================================
-- § 12b: Smart constructor for `Lex (Fin n → Nat)` from atom-wise functions
-- ============================================================================

/-- Build a `Lex (Fin n → Nat)` from `n` atom-wise evaluation functions.
    Given atoms as `Fin n → C → Nat`, produce the lex-comparable
    fixed-length vector for `c : C`. -/
def lexFinNatOf {C : Type*} {n : Nat}
    (atoms : Fin n → C → Nat) (c : C) : Lex (Fin n → Nat) :=
  toLex fun i => atoms i c

-- ============================================================================
-- § 12c: Tropical Semiring Derivation
-- ============================================================================

/-- `WithTop (Lex (Fin n → Nat))` is a `LinearOrderedAddCommMonoidWithTop`:
    it extends the ordered cancel monoid with an absorbing top element.
    Prerequisite for the tropical semiring: mathlib's `Tropical` wrapper
    then provides `CommSemiring` automatically. -/
noncomputable instance (n : Nat) :
    LinearOrderedAddCommMonoidWithTop (WithTop (Lex (Fin n → Nat))) where
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

/-- The tropical semiring on `Lex (Fin n → Nat)`:
    `Tropical (WithTop (Lex (Fin n → Nat)))` is a `CommSemiring` where
    addition is `min` (under the lex order) and multiplication is
    componentwise `+`. Derived, not stipulated. Linguistic packaging:
    `Phonology/Constraint/Dequantization/ViolationSemiring.lean` after
    [riggle-2009]. -/
noncomputable example (n : Nat) :
    CommSemiring (Tropical (WithTop (Lex (Fin n → Nat)))) :=
  inferInstance


-- ============================================================================
-- § 14: LexMinProblem — finite candidate set with a lex-comparable score
-- ============================================================================

/-- A finite candidate set `C` with a `Fin n → Nat`-valued score and a
    nonemptiness witness. The lex-min set is nonempty
    (`exists_lexMin`), computable (`lexMins`), and accessible via the
    `IsLexMin` predicate. -/
structure LexMinProblem (C : Type*) [DecidableEq C] (n : Nat) where
  candidates : Finset C
  profile : C → Lex (Fin n → Nat)
  nonempty : candidates.Nonempty

variable {C : Type*} [DecidableEq C] {n : Nat}

/-- A candidate is a lex-minimizer iff it's in the candidate set and its
    score is ≤ every other candidate's score. -/
def LexMinProblem.IsLexMin (t : LexMinProblem C n) (c : C) : Prop :=
  c ∈ t.candidates ∧ ∀ c' ∈ t.candidates, t.profile c ≤ t.profile c'

/-- **Every problem has a lex-minimizer.** Delegates to
    `Finset.exists_min_image` — the linear-ordered image of a nonempty
    finset has a minimum. -/
theorem LexMinProblem.exists_lexMin (t : LexMinProblem C n) :
    ∃ c, t.IsLexMin c := by
  obtain ⟨c, hc_mem, hc_min⟩ := Finset.exists_min_image t.candidates t.profile t.nonempty
  exact ⟨c, hc_mem, hc_min⟩

/-- The set of lex-minimizers. Computable via `instDecidableLexFinNatProfileLE`;
    consumers can use `by decide` to verify lex-mins on concrete problems. -/
def LexMinProblem.lexMins (t : LexMinProblem C n) : Finset C :=
  t.candidates.filter fun c =>
    ∀ c' ∈ t.candidates, t.profile c ≤ t.profile c'

/-- `c ∈ t.lexMins` iff `t.IsLexMin c`. -/
theorem LexMinProblem.mem_lexMins_iff (t : LexMinProblem C n) (c : C) :
    c ∈ t.lexMins ↔ t.IsLexMin c := by
  simp only [LexMinProblem.lexMins, Finset.mem_filter, LexMinProblem.IsLexMin]

/-- The lex-min set is always nonempty. -/
theorem LexMinProblem.lexMins_nonempty (t : LexMinProblem C n) : t.lexMins.Nonempty := by
  obtain ⟨c, hc⟩ := t.exists_lexMin
  exact ⟨c, (t.mem_lexMins_iff c).mpr hc⟩

/-- Lex-minimizers belong to the candidate set. -/
theorem LexMinProblem.lexMins_subset (t : LexMinProblem C n) (c : C) :
    c ∈ t.lexMins → c ∈ t.candidates :=
  fun hc => ((t.mem_lexMins_iff c).mp hc).1

-- ============================================================================
-- § 14a: Computable Finset Predicates
-- ============================================================================

/-- Check a Bool predicate for all elements of a Finset. Computable via
    `Finset.decidableBAll` — avoids noncomputable `Finset.toList`. -/
def Finset.checkAll {α : Type} [DecidableEq α]
    (s : Finset α) (p : α → Bool) : Bool :=
  decide (∀ c ∈ s, p c = true)

/-- Check a Bool predicate for some element of a Finset. -/
def Finset.checkAny {α : Type} [DecidableEq α]
    (s : Finset α) (p : α → Bool) : Bool :=
  decide (∃ c ∈ s, p c = true)

-- ============================================================================
-- § 15: Component lemma on `Lex (Fin n → Nat)`
-- ============================================================================

/-- If `a ≤ b` lex-wise, then their first components satisfy
    `a 0 ≤ b 0`. -/
theorem lexFinNat_le_apply_zero {n : Nat}
    {a b : Lex (Fin (n + 1) → Nat)} (h : a ≤ b) : a 0 ≤ b 0 := by
  by_contra hgt
  push Not at hgt
  exact absurd (show b < a from
    ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), hgt⟩)
    (not_lt.mpr h)

end Core.Optimization.Evaluation
