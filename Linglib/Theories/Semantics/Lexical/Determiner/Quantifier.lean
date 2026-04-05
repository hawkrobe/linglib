import Linglib.Theories.Semantics.Montague.Types
import Linglib.Theories.Semantics.Composition.TypeShifting
import Linglib.Core.Logic.Quantification
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

/-!
# Generalized Quantifiers
@cite{barwise-cooper-1981} @cite{keenan-stavi-1986} @cite{peters-westerstahl-2006} @cite{van-de-pol-etal-2023} @cite{mostowski-1957}

Determiners have type `(e→t) → ((e→t) → t)`:
- `⟦every⟧ = λR.λS. ∀x. R(x) → S(x)`
- `⟦some⟧ = λR.λS. ∃x. R(x) ∧ S(x)`
- `⟦no⟧ = λR.λS. ¬∃x. R(x) ∧ S(x)`

## Semantic Universals

Three properties conjectured to hold of all simple (lexicalized) determiners:
- **Conservativity**: `Q(A, B) ↔ Q(A, A ∩ B)` — only the restrictor matters
- **Quantity** (isomorphism closure): meaning depends only on cardinalities
  `|A ∩ B|`, `|A \ B|`, `|B \ A|`, `|M \ (A ∪ B)|`
- **Monotonicity**: Q is either upward or downward monotone in scope

@cite{van-de-pol-etal-2023} show quantifiers satisfying these universals have
shorter minimal description length, suggesting a simplicity bias explains
the universals.

## Organization

- **Generic GQ properties**: `Core.Quantification` — `Conservative`, `ScopeUpwardMono`,
  `ScopeDownwardMono`, `outerNeg`, `innerNeg`, `dualQ`, etc. (model-agnostic)
- **Concrete denotations**: `every_sem`, `some_sem`, etc. — require `[Fintype m.Entity]`
  for decidable computation via `decide (∀/∃ x, ...)`
- **Counting quantifiers**: `most_sem`, `few_sem`, etc. — use `Finset.univ.filter`
  for cardinality comparisons

`ScopeUpwardMono`/`ScopeDownwardMono` are equivalent to Mathlib's
`Monotone`/`Antitone` (see `Core.Quantification.scopeUpMono_iff_monotone`),
connecting to `Semantics.Entailment.Polarity.IsUpwardEntailing = Monotone`.

-/

namespace Semantics.Lexical.Determiner.Quantifier

open Semantics.Montague
open Core.Quantification

def Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

/-- Decidability of implication (not in Lean 4 core). -/
instance decImpl {p q : Prop} [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then
    if hq : q then .isTrue (fun _ => hq)
    else .isFalse (fun h => hq (h hp))
  else .isTrue (fun h => absurd h hp)


/-- Count of elements satisfying a predicate, via `Finset.univ.filter`. -/
def count {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] : Nat :=
  (Finset.univ.filter P).card

def every_sem (m : Model) [Fintype m.Entity] : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (∀ x : m.Entity, R x = true → S x = true)

def some_sem (m : Model) [Fintype m.Entity] : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (∃ x : m.Entity, R x = true ∧ S x = true)

/-- Partee's `A` (existential closure) = Barwise & Cooper's `⟦some⟧`.
    Both compute `λR.λS. ∃x. R(x) ∧ S(x)` over a finite domain.
    `A` takes the domain explicitly; `some_sem` uses `decide` over `Fintype`. -/
theorem A_eq_some_sem (m : Model) [Fintype m.Entity] (domain : List m.Entity)
    (hComplete : ∀ x : m.Entity, x ∈ domain) :
    Semantics.Composition.TypeShifting.A domain = some_sem m := by
  funext R S
  simp only [Semantics.Composition.TypeShifting.A, some_sem, Model.interpTy]
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, _, h⟩
    exact ⟨x, by simp only [Bool.and_eq_true] at h; exact h⟩
  · rintro ⟨x, hR, hS⟩
    exact ⟨x, hComplete x, by simp [hR, hS]⟩

def no_sem (m : Model) [Fintype m.Entity] : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (∀ x : m.Entity, R x = true → S x = false)

/-- `⟦most⟧(R)(S) = |R ∩ S| > |R \ S|` -/
def most_sem (m : Model) [Fintype m.Entity] : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (count (fun x : m.Entity => R x = true ∧ S x = true) >
            count (fun x : m.Entity => R x = true ∧ S x = false))

/-- `⟦few⟧(R)(S) = |R ∩ S| < |R \ S|` — a minority of Rs are Ss.
    Dual of `most_sem`: few(R,S) ↔ ¬most(R,S) ∧ ¬half(R,S). -/
def few_sem (m : Model) [Fintype m.Entity] : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (count (fun x : m.Entity => R x = true ∧ S x = true) <
            count (fun x : m.Entity => R x = true ∧ S x = false))

/-- `⟦half⟧(R)(S) = 2 * |R ∩ S| = |R|` — exactly half of Rs are Ss. -/
def half_sem (m : Model) [Fintype m.Entity] : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (2 * count (fun x : m.Entity => R x = true ∧ S x = true) =
            count (fun x : m.Entity => R x = true))

/-- `⟦at least n⟧(R)(S) = |R ∩ S| ≥ n` -/
def at_least_n_sem (m : Model) [Fintype m.Entity] (n : Nat) : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (count (fun x : m.Entity => R x = true ∧ S x = true) ≥ n)

/-- `⟦at most n⟧(R)(S) = |R ∩ S| ≤ n` -/
def at_most_n_sem (m : Model) [Fintype m.Entity] (n : Nat) : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (count (fun x : m.Entity => R x = true ∧ S x = true) ≤ n)

/-- `⟦exactly n⟧(R)(S) = |R ∩ S| = n` -/
def exactly_n_sem (m : Model) [Fintype m.Entity] (n : Nat) : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (count (fun x : m.Entity => R x = true ∧ S x = true) = n)

/-- `⟦all but n⟧(R)(S) = |R \ S| = n` — exactly n R-elements are non-S.
    Generalizes "every" (= all but 0). The exceptive counterpart of
    `exactly_n_sem` (which counts |R ∩ S| = n). -/
def all_but_n_sem (m : Model) [Fintype m.Entity] (n : Nat) : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (count (fun x : m.Entity => R x = true ∧ S x = false) = n)

/-- `⟦between n and k⟧(R)(S) = n ≤ |R ∩ S| ≤ k` -/
def between_n_m_sem (m : Model) [Fintype m.Entity] (n k : Nat) : m.interpTy Ty.det :=
  gqMeet (at_least_n_sem m n) (at_most_n_sem m k)

instance : Fintype ToyEntity where
  elems := {.john, .mary, .pizza, .book}
  complete := fun x => by cases x <;> simp

/-- Bridge: `toyModel.Entity = ToyEntity` is definitional but opaque to instance search. -/
instance : Fintype toyModel.Entity :=
  show Fintype ToyEntity by infer_instance

section ToyLexicon

def student_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .john => true
    | .mary => true
    | _ => false

def person_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .john => true
    | .mary => true
    | _ => false

def thing_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ _ => true

end ToyLexicon

section Examples

open ToyLexicon

def everyStudentSleeps : toyModel.interpTy .t :=
  every_sem toyModel student_sem sleeps_sem

#guard !everyStudentSleeps

def someStudentSleeps : toyModel.interpTy .t :=
  some_sem toyModel student_sem sleeps_sem

#guard someStudentSleeps

def noStudentSleeps : toyModel.interpTy .t :=
  no_sem toyModel student_sem sleeps_sem

#guard !noStudentSleeps

def everyStudentLaughs : toyModel.interpTy .t :=
  every_sem toyModel student_sem laughs_sem

#guard everyStudentLaughs
#guard some_sem toyModel student_sem laughs_sem

def everyPersonSleeps : toyModel.interpTy .t :=
  every_sem toyModel person_sem sleeps_sem

def somePersonSleeps : toyModel.interpTy .t :=
  some_sem toyModel person_sem sleeps_sem

#guard !everyPersonSleeps
#guard somePersonSleeps

end Examples

-- ============================================================================
-- Fintype Model Proofs (require Fintype for decidable quantification)
-- ============================================================================

section FintypeProofs

variable {m : Model} [Fintype m.Entity]

-- === Bijection invariance (for QuantityInvariant) ===

/-- `∀ x, P x` is invariant under bijective substitution. -/
theorem forall_bij_inv (f : m.Entity → m.Entity) (hBij : Function.Bijective f)
    (P : m.Entity → Prop) :
    (∀ x, P x) ↔ (∀ x, P (f x)) := by
  constructor
  · intro h x; exact h (f x)
  · intro h x; obtain ⟨y, rfl⟩ := hBij.surjective x; exact h y

/-- `∃ x, P x` is invariant under bijective substitution. -/
theorem exists_bij_inv (f : m.Entity → m.Entity) (hBij : Function.Bijective f)
    (P : m.Entity → Prop) :
    (∃ x, P x) ↔ (∃ x, P (f x)) := by
  constructor
  · intro ⟨x, hx⟩; obtain ⟨y, rfl⟩ := hBij.surjective x; exact ⟨y, hx⟩
  · intro ⟨y, hy⟩; exact ⟨f y, hy⟩

/-- `count P = count (P ∘ f)` when f is a bijection. -/
theorem count_bij_inv (f : m.Entity → m.Entity) (hBij : Function.Bijective f)
    {P : m.Entity → Prop} [DecidablePred P] :
    count P = @count _ _ (P ∘ f) (fun x => ‹DecidablePred P› (f x)) := by
  simp only [count, Function.comp]
  symm; apply Finset.card_bij (fun x _ => f x)
  · intro x hx; simp [Finset.mem_filter] at hx ⊢; exact hx
  · intro x₁ _ x₂ _ h; exact hBij.injective h
  · intro y hy
    simp [Finset.mem_filter] at hy
    obtain ⟨x, rfl⟩ := hBij.surjective y
    exact ⟨x, by simp [Finset.mem_filter, hy], rfl⟩

-- === Conservativity proofs ===

/-- `⟦every⟧` is conservative: `∀x. R(x) → S(x)` iff `∀x. R(x) → (R(x) ∧ S(x))`. -/
theorem every_conservative : Conservative (every_sem m) := by
  intro R S; dsimp only [every_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact forall_congr' fun x => by cases R x <;> simp

/-- `⟦some⟧` is conservative: `∃x. R(x) ∧ S(x)` iff `∃x. R(x) ∧ (R(x) ∧ S(x))`. -/
theorem some_conservative : Conservative (some_sem m) := by
  intro R S; dsimp only [some_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact exists_congr fun x => by cases R x <;> simp

/-- `⟦no⟧` is conservative: `∀x. R(x) → ¬S(x)` iff `∀x. R(x) → ¬(R(x) ∧ S(x))`. -/
theorem no_conservative : Conservative (no_sem m) := by
  intro R S; dsimp only [no_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact forall_congr' fun x => by cases R x <;> simp

@[simp] private theorem count_and_idem (R S : m.Entity → Bool) :
    count (fun x : m.Entity => R x = true ∧ (R x && S x) = true) =
    count (fun x : m.Entity => R x = true ∧ S x = true) := by
  congr 1; ext x; cases R x <;> simp

@[simp] private theorem count_and_neg_idem (R S : m.Entity → Bool) :
    count (fun x : m.Entity => R x = true ∧ (R x && S x) = false) =
    count (fun x : m.Entity => R x = true ∧ S x = false) := by
  congr 1; ext x; cases R x <;> simp

/-- `⟦most⟧` is conservative: the R-elements in S are the R-elements in R∩S. -/
theorem most_conservative : Conservative (most_sem m) := by
  intro R S; simp only [most_sem, count_and_idem, count_and_neg_idem]

/-- `⟦few⟧` is conservative: the R-elements in S are the R-elements in R∩S. -/
theorem few_conservative : Conservative (few_sem m) := by
  intro R S; simp only [few_sem, count_and_idem, count_and_neg_idem]

/-- `⟦half⟧` is conservative: depends only on R ∩ S within R. -/
theorem half_conservative : Conservative (half_sem m) := by
  intro R S; simp only [half_sem, count_and_idem]

/-- `⟦at least n⟧` is conservative: |R ∩ S| = |R ∩ (R ∩ S)|. -/
theorem at_least_n_conservative (n : Nat) : Conservative (at_least_n_sem m n) := by
  intro R S; simp only [at_least_n_sem, count_and_idem]

/-- `⟦at most n⟧` is conservative. -/
theorem at_most_n_conservative (n : Nat) : Conservative (at_most_n_sem m n) := by
  intro R S; simp only [at_most_n_sem, count_and_idem]

/-- `⟦exactly n⟧` is conservative. -/
theorem exactly_n_conservative (n : Nat) : Conservative (exactly_n_sem m n) := by
  intro R S; simp only [exactly_n_sem, count_and_idem]

-- === Scope monotonicity proofs ===

/-- `⟦every⟧` is upward monotone in scope. -/
theorem every_scope_up : ScopeUpwardMono (every_sem m) := by
  intro R S S' hSS' h
  dsimp only [every_sem] at *; rw [decide_eq_true_eq] at *
  intro x hR; exact hSS' x (h x hR)

/-- `⟦some⟧` is upward monotone in scope. -/
theorem some_scope_up : ScopeUpwardMono (some_sem m) := by
  intro R S S' hSS' h
  dsimp only [some_sem] at *; rw [decide_eq_true_eq] at *
  obtain ⟨x, hR, hS⟩ := h
  exact ⟨x, hR, hSS' x hS⟩

/-- `⟦no⟧` is downward monotone in scope. -/
theorem no_scope_down : ScopeDownwardMono (no_sem m) := by
  intro R S S' hSS' h
  dsimp only [no_sem] at *; rw [decide_eq_true_eq] at *
  intro x hR
  cases hS : S x
  · rfl
  · exact absurd (hSS' x hS) (by simp [h x hR])

/-- If `p x = true → q x = true` for all x, then filter by p is a sublist
    of filter by q, so its length is ≤. -/
private theorem filter_length_le_of_imp {β : Type*} (l : List β) (p q : β → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.filter_cons]
    split <;> split
    · exact Nat.succ_le_succ ih
    · rename_i hp hq; exact absurd (h a hp) (by simp [hq])
    · exact Nat.le_succ_of_le ih
    · exact ih

/-- Finset.filter monotonicity: if P implies Q pointwise, then |filter P| ≤ |filter Q|. -/
private theorem count_le_of_imp {P Q : m.Entity → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x → Q x) :
    count P ≤ count Q := by
  apply Finset.card_le_card
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

/-- `⟦few⟧` is downward monotone in scope: if S ⊆ S' and few(R,S'),
    then few(R,S). Fewer Ss among Rs means even fewer S-subsets. -/
theorem few_scope_down : ScopeDownwardMono (few_sem m) := by
  intro R S S' hSS' h
  dsimp only [few_sem] at *; rw [decide_eq_true_eq] at *
  have h1 : count (fun x : m.Entity => R x = true ∧ S x = true) ≤
      count (fun x : m.Entity => R x = true ∧ S' x = true) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩
  have h2 : count (fun x : m.Entity => R x = true ∧ S' x = false) ≤
      count (fun x : m.Entity => R x = true ∧ S x = false) :=
    count_le_of_imp fun x ⟨hR, hS'⟩ => by
      refine ⟨hR, ?_⟩; cases hS : S x
      · exact rfl
      · exact absurd (hSS' x hS) (by simp [hS'])
  omega

/-- `⟦most⟧` is upward monotone in scope: if S ⊆ S' and most(R,S),
    then most(R,S'). |R∩S'| ≥ |R∩S| > |R\S| ≥ |R\S'|. -/
theorem most_scope_up : ScopeUpwardMono (most_sem m) := by
  intro R S S' hSS' h
  dsimp only [most_sem] at *; rw [decide_eq_true_eq] at *
  have h1 : count (fun x : m.Entity => R x = true ∧ S x = true) ≤
      count (fun x : m.Entity => R x = true ∧ S' x = true) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩
  have h2 : count (fun x : m.Entity => R x = true ∧ S' x = false) ≤
      count (fun x : m.Entity => R x = true ∧ S x = false) :=
    count_le_of_imp fun x ⟨hR, hS'⟩ => by
      refine ⟨hR, ?_⟩; cases hS : S x
      · exact rfl
      · exact absurd (hSS' x hS) (by simp [hS'])
  omega

-- === Counting quantifier identities (@cite{peters-westerstahl-2006} §4.3) ===

/-- `⟦some⟧ = ⟦at least 1⟧`: existential quantification is "at least one". -/
theorem some_eq_at_least_1 : some_sem m = at_least_n_sem m 1 := by
  funext (R : m.Entity → Bool) (S : m.Entity → Bool)
  dsimp only [some_sem, at_least_n_sem, Model.interpTy]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro ⟨x, hR, hS⟩
    simp only [count]
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hR, hS⟩⟩).ne'
  · intro h
    simp only [count] at h
    have hpos : 0 < (Finset.univ.filter (fun x : m.Entity => R x = true ∧ S x = true)).card :=
      by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, hx.1, hx.2⟩

/-- `outerNeg ⟦some⟧ = ⟦no⟧`: negating existence gives universal negation. -/
theorem outerNeg_some_eq_no : outerNeg (some_sem m) = no_sem m := by
  funext R S; dsimp only [outerNeg, some_sem, no_sem]
  rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, not_exists]
  exact forall_congr' fun x => by cases R x <;> cases S x <;> simp

/-- `⟦at most n⟧ = outerNeg ⟦at least n+1⟧`: duality of lower and upper bounds.
    This is the counting quantifier instance of the Square of Opposition. -/
theorem at_most_eq_outerNeg_at_least_succ (n : Nat) :
    at_most_n_sem m n = outerNeg (at_least_n_sem m (n + 1)) := by
  funext R S; dsimp only [at_most_n_sem, at_least_n_sem, outerNeg, Model.interpTy]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

/-- `⟦no⟧ = ⟦at most 0⟧`. Derived algebraically:
    no = outerNeg(some) = outerNeg(at_least 1) = at_most 0. -/
theorem no_eq_at_most_0 : no_sem m = at_most_n_sem m 0 := by
  rw [← outerNeg_some_eq_no, some_eq_at_least_1, at_most_eq_outerNeg_at_least_succ]

/-- `⟦exactly n⟧ = ⟦at least n⟧ ⊓ ⟦at most n⟧` in the GQ lattice.
    "Exactly n" is the meet of a lower bound and an upper bound. -/
theorem exactly_eq_meet_at_least_at_most (n : Nat) :
    exactly_n_sem m n = gqMeet (at_least_n_sem m n) (at_most_n_sem m n) := by
  funext R S; dsimp only [exactly_n_sem, at_least_n_sem, at_most_n_sem, gqMeet, Model.interpTy]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  omega

/-- `⟦at least n⟧` is Mon↑ in scope: enlarging B cannot decrease |A ∩ B|. -/
theorem at_least_n_scope_up (n : Nat) : ScopeUpwardMono (at_least_n_sem m n) := by
  intro R S S' hSS' h
  dsimp only [at_least_n_sem] at *; rw [decide_eq_true_eq] at *
  exact le_trans h (count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩)

/-- `⟦at most n⟧` is Mon↓ in scope. Derived from duality:
    outerNeg flips Mon↑ to Mon↓ (Prop 8), and `at_most = outerNeg(at_least)`. -/
theorem at_most_n_scope_down (n : Nat) : ScopeDownwardMono (at_most_n_sem m n) := by
  rw [at_most_eq_outerNeg_at_least_succ]
  exact outerNeg_up_to_down _ (at_least_n_scope_up _)

-- === Quantity / Isomorphism Closure (@cite{mostowski-1957}) ===

/--
Quantity / Isomorphism closure:
Q(A, B) depends only on the four cardinalities
`|A ∩ B|`, `|A \ B|`, `|B \ A|`, `|M \ (A ∪ B)|`.

Equivalently: permuting the domain does not change the quantifier's
truth value. This is the type ⟨1,1⟩ (binary) generalization of
@cite{mostowski-1957}'s permutation invariance for type ⟨1⟩ (unary)
quantifiers; the extension to binary determiners is due to
@cite{van-benthem-1984} (building on Lindström 1966).
-/
def Quantity (q : m.interpTy Ty.det) : Prop :=
  ∀ (R₁ S₁ R₂ S₂ : m.Entity → Bool),
    count (fun x => R₁ x = true ∧ S₁ x = true) =
    count (fun x => R₂ x = true ∧ S₂ x = true) →
    count (fun x => R₁ x = true ∧ S₁ x = false) =
    count (fun x => R₂ x = true ∧ S₂ x = false) →
    count (fun x => R₁ x = false ∧ S₁ x = true) =
    count (fun x => R₂ x = false ∧ S₂ x = true) →
    count (fun x => R₁ x = false ∧ S₁ x = false) =
    count (fun x => R₂ x = false ∧ S₂ x = false) →
    q R₁ S₁ = q R₂ S₂

/--
A quantifier satisfies all three Barwise & Cooper universals.
@cite{van-de-pol-etal-2023} show these quantifiers have shorter MDL.
-/
def SatisfiesUniversals (q : m.interpTy Ty.det) : Prop :=
  Conservative q ∧ Quantity q ∧ (ScopeUpwardMono q ∨ ScopeDownwardMono q)

/-- Proportional (@cite{peters-westerstahl-2006} §4.3): Q's truth value depends
    only on the ratio |A ∩ B| / |A| (the proportion of A-elements in B).

    Under CONS + QUANT, cardinal quantifiers ("at least 3") depend on
    absolute cardinalities, while proportional quantifiers ("most", "half")
    depend only on the proportion of A-elements that are B-elements.

    Formally: if the cross-ratio |A₁∩B₁|·|A₂\B₂| = |A₂∩B₂|·|A₁\B₁|
    (same ratio of successes to failures) and both restrictors are
    non-empty, the truth values agree.

    Proportional ⊂ Quantity: Quantity requires all four cells to match;
    Proportional requires only the ratio of two cells (hTT, hTF). -/
def Proportional (q : m.interpTy Ty.det) : Prop :=
  ∀ (R₁ S₁ R₂ S₂ : m.Entity → Bool),
    let tt₁ := count (fun x : m.Entity => R₁ x = true ∧ S₁ x = true)
    let tf₁ := count (fun x : m.Entity => R₁ x = true ∧ S₁ x = false)
    let tt₂ := count (fun x : m.Entity => R₂ x = true ∧ S₂ x = true)
    let tf₂ := count (fun x : m.Entity => R₂ x = true ∧ S₂ x = false)
    0 < tt₁ + tf₁ → 0 < tt₂ + tf₂ →
    tt₁ * tf₂ = tt₂ * tf₁ →
    q R₁ S₁ = q R₂ S₂

-- === Quantity ↔ QuantityInvariant (@cite{mostowski-1957}) ===

/-- `Quantity → QuantityInvariant`: cardinality-dependence implies bijection-invariance.
    Proof: a bijection preserves `count` (via `count_bij_inv`),
    so all four cell cardinalities match, and `Quantity` gives the result. -/
theorem quantityInvariant_of_quantity (q : m.interpTy Ty.det) (hQ : Quantity q) :
    Core.Quantification.QuantityInvariant q := by
  intro A B A' B' f hBij hA hB
  have cell : ∀ (g : Bool → Bool → Prop) [DecidablePred (fun (x : m.Entity) => g (A x) (B x))]
      [DecidablePred (fun (x : m.Entity) => g (A' x) (B' x))],
      count (fun (x : m.Entity) => g (A x) (B x)) =
      count (fun (x : m.Entity) => g (A' x) (B' x)) := by
    intro g _ _
    show ((Finset.univ : Finset m.Entity).filter (fun x => g (A x) (B x))).card =
         ((Finset.univ : Finset m.Entity).filter (fun x => g (A' x) (B' x))).card
    symm
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ (α := m.Entity) _, by rw [hA x, hB x]; exact hx.2⟩
    · intro _ _ _ _ h; exact hBij.injective h
    · intro y hy
      obtain ⟨x, rfl⟩ := hBij.surjective y
      exact ⟨x, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ (α := m.Entity) _, by
          rw [← hA x, ← hB x]; exact (Finset.mem_filter.mp hy).2⟩, rfl⟩
  exact hQ A B A' B'
    (cell (fun a b => a = true ∧ b = true))
    (cell (fun a b => a = true ∧ b = false))
    (cell (fun a b => a = false ∧ b = true))
    (cell (fun a b => a = false ∧ b = false))

local instance decEqEntity : DecidableEq m.Entity := m.decEq

private lemma card_cell (R S : m.Entity → Bool) (b₁ b₂ : Bool) :
    Fintype.card {x : m.Entity // R x == b₁ && S x == b₂} =
    count (fun x : m.Entity => (R x == b₁) = true ∧ (S x == b₂) = true) := by
  simp only [count]
  rw [← Fintype.card_subtype]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) (fun x => by
    simp only [Equiv.refl_apply, Bool.and_eq_true])

private def entityEquivCells (R S : m.Entity → Bool) :
    m.Entity ≃ Σ (b₁ : Bool) (b₂ : Bool), {x : m.Entity // R x == b₁ && S x == b₂} where
  toFun x := ⟨R x, S x, ⟨x, by simp⟩⟩
  invFun := λ ⟨_, _, ⟨x, _⟩⟩ => x
  left_inv x := rfl
  right_inv := λ ⟨b₁, b₂, ⟨x, h⟩⟩ => by
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h₁, h₂⟩
    subst h₁ h₂
    rfl

private lemma build_bijection (R₁ S₁ R₂ S₂ : m.Entity → Bool)
    (h_len : ∀ b₁ b₂, count (fun x : m.Entity => (R₁ x == b₁) = true ∧ (S₁ x == b₂) = true) =
                       count (fun x : m.Entity => (R₂ x == b₁) = true ∧ (S₂ x == b₂) = true)) :
    ∃ (f : m.Entity ≃ m.Entity), (∀ x, R₁ (f x) = R₂ x) ∧ (∀ x, S₁ (f x) = S₂ x) := by
  have h_card : ∀ b₁ b₂, Fintype.card {x : m.Entity // R₂ x == b₁ && S₂ x == b₂} =
                         Fintype.card {x : m.Entity // R₁ x == b₁ && S₁ x == b₂} := by
    intro b₁ b₂
    rw [card_cell, card_cell, ←h_len b₁ b₂]
  let innerEquiv (b₁ b₂ : Bool) : {x : m.Entity // R₂ x == b₁ && S₂ x == b₂} ≃
                                  {x : m.Entity // R₁ x == b₁ && S₁ x == b₂} :=
    Fintype.equivOfCardEq (h_card b₁ b₂)
  let e3 : (Σ b₁ b₂, {x : m.Entity // R₂ x == b₁ && S₂ x == b₂}) ≃
           (Σ b₁ b₂, {x : m.Entity // R₁ x == b₁ && S₁ x == b₂}) :=
    Equiv.sigmaCongrRight (λ b₁ => Equiv.sigmaCongrRight (λ b₂ => innerEquiv b₁ b₂))
  let e1 := entityEquivCells R₁ S₁
  let e2 := entityEquivCells R₂ S₂
  let f := e2.trans (e3.trans e1.symm)
  use f
  have h_prop : ∀ x, R₁ (f x) = R₂ x ∧ S₁ (f x) = S₂ x := by
    intro x
    have h_eval : f x = (innerEquiv (R₂ x) (S₂ x) ⟨x, by simp⟩).val := rfl
    have h_inner := (innerEquiv (R₂ x) (S₂ x) ⟨x, by simp⟩).property
    rw [←h_eval] at h_inner
    simp only [Bool.and_eq_true, beq_iff_eq] at h_inner
    exact h_inner
  exact ⟨λ x => (h_prop x).1, λ x => (h_prop x).2⟩

private lemma hypotheses_to_all (R₁ S₁ R₂ S₂ : m.Entity → Bool)
    (hTT : count (fun x : m.Entity => R₁ x = true ∧ S₁ x = true) =
           count (fun x : m.Entity => R₂ x = true ∧ S₂ x = true))
    (hTF : count (fun x : m.Entity => R₁ x = true ∧ S₁ x = false) =
           count (fun x : m.Entity => R₂ x = true ∧ S₂ x = false))
    (hFT : count (fun x : m.Entity => R₁ x = false ∧ S₁ x = true) =
           count (fun x : m.Entity => R₂ x = false ∧ S₂ x = true))
    (hFF : count (fun x : m.Entity => R₁ x = false ∧ S₁ x = false) =
           count (fun x : m.Entity => R₂ x = false ∧ S₂ x = false)) :
    ∀ (b₁ b₂ : Bool), count (fun x : m.Entity => (R₁ x == b₁) = true ∧ (S₁ x == b₂) = true) =
             count (fun x : m.Entity => (R₂ x == b₁) = true ∧ (S₂ x == b₂) = true) := by
  intro b₁ b₂
  simp only [beq_iff_eq]
  cases b₁ <;> cases b₂ <;> assumption

/-- `QuantityInvariant → Quantity`: bijection-invariance implies cardinality-dependence.
    On a finite domain, matching cell cardinalities guarantees a cell-preserving
    bijection exists (permute elements within each of the four (R,S) cells). -/
theorem quantity_of_quantityInvariant (q : m.interpTy Ty.det)
    (hQ : Core.Quantification.QuantityInvariant q) :
    Quantity q := by
  intro R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  have h_len := hypotheses_to_all R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  obtain ⟨f, hR, hS⟩ := build_bijection R₁ S₁ R₂ S₂ h_len
  exact hQ R₁ S₁ R₂ S₂ f f.bijective hR hS

-- === Non-conservative counterexample ===

/-- A non-conservative quantifier for contrast: `⟦M⟧(A,B) = |A| > |B|`
(van de Pol et al.'s hypothetical counterpart to "most"). -/
def m_sem (m : Model) [Fintype m.Entity] : m.interpTy Ty.det :=
  fun (R : m.Entity → Bool) (S : m.Entity → Bool) =>
    decide (count (fun x : m.Entity => R x = true) > count (fun x : m.Entity => S x = true))

/-- M is not conservative: it inspects B outside A.
Witness: R = {john, mary}, S = {john, pizza}.
m_sem R S = (2 > 2) = false, but m_sem R (R∩S) = (2 > 1) = true. -/
theorem m_not_conservative : ¬Conservative (m_sem (m := toyModel)) := by
  intro h
  exact absurd
    (h student_sem (λ x => match x with | .john => true | .pizza => true | _ => false))
    (by native_decide)

-- === Symmetry proofs (P&W Ch.6) ===

/-- `⟦some⟧` is symmetric: ∃x.R(x)∧S(x) = ∃x.S(x)∧R(x). -/
theorem some_symmetric : QSymmetric (some_sem m) := by
  intro R S; dsimp only [some_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact exists_congr fun x => by cases R x <;> cases S x <;> simp [And.comm]

/-- `⟦no⟧` is symmetric: ¬∃x.R(x)∧S(x) = ¬∃x.S(x)∧R(x). -/
theorem no_symmetric : QSymmetric (no_sem m) := by
  intro R S; dsimp only [no_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact forall_congr' fun x => by cases R x <;> cases S x <;> simp

/-- `⟦every⟧` is NOT symmetric. Witness: R=students, S=things (everything).
    every(students)(things)=true but every(things)(students)=false. -/
theorem every_not_symmetric : ¬QSymmetric (every_sem (m := toyModel)) := by
  intro h; exact absurd (h student_sem thing_sem) (by native_decide)

-- === Intersectivity via CONSERV+SYMM bridge ===

/-- `⟦some⟧` is intersective (follows from CONSERV + SYMM). -/
theorem some_intersective : IntersectionCondition (some_sem m) :=
  (conserv_symm_iff_int _ some_conservative).mp some_symmetric

/-- `⟦no⟧` is intersective. -/
theorem no_intersective : IntersectionCondition (no_sem m) :=
  (conserv_symm_iff_int _ no_conservative).mp no_symmetric

-- === Left anti-additivity (P&W §5.8) ===

private theorem list_all_and {β : Type*} {l : List β} {p q : β → Bool} :
    l.all (λ x => p x && q x) = (l.all p && l.all q) := by
  induction l with
  | nil => simp [List.all_nil]
  | cons a t ih =>
    simp only [List.all_cons]
    rw [ih]
    cases p a <;> cases q a <;> simp

/-- `⟦every⟧` is left anti-additive: every(A∪B, C) = every(A,C) ∧ every(B,C). -/
theorem every_laa : LeftAntiAdditive (every_sem m) := by
  intro R R' S; dsimp only [every_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro h; exact ⟨fun x hR => h x (by simp [hR]),
                     fun x hR' => h x (by simp [hR'])⟩
  · intro ⟨h1, h2⟩ x hRR'
    simp only [Bool.or_eq_true] at hRR'
    rcases hRR' with hR | hR'
    · exact h1 x hR
    · exact h2 x hR'

/-- `⟦no⟧` is left anti-additive: no(A∪B, C) = no(A,C) ∧ no(B,C). -/
theorem no_laa : LeftAntiAdditive (no_sem m) := by
  intro R R' S; dsimp only [no_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro h; exact ⟨fun x hR => h x (by simp [hR]),
                     fun x hR' => h x (by simp [hR'])⟩
  · intro ⟨h1, h2⟩ x hRR'
    simp only [Bool.or_eq_true] at hRR'
    rcases hRR' with hR | hR'
    · exact h1 x hR
    · exact h2 x hR'

-- === Right anti-additivity (scope position, P&W §5.9) ===

/-- `⟦no⟧` is right anti-additive: no(A, B∪C) = no(A,B) ∧ no(A,C).
    "Nobody saw A-or-B" ↔ "Nobody saw A and nobody saw B".
    This licenses strong NPIs in scope: "Nobody lifted a finger." -/
theorem no_raa : RightAntiAdditive (no_sem m) := by
  intro R S S'; dsimp only [no_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun x hR => ?_, fun x hR => ?_⟩
    · have hSS' := h x hR
      cases hS : S x
      · rfl
      · simp [hS] at hSS'
    · have hSS' := h x hR
      cases hS' : S' x
      · rfl
      · simp [hS'] at hSS'
  · intro ⟨h1, h2⟩ x hR
    have hS := h1 x hR; have hS' := h2 x hR
    simp [hS, hS']

/-- @cite{peters-westerstahl-2006} Prop 13: the only non-trivial CONSERV, EXT,
    and ISOM quantifiers satisfying LAA are `every` and `no` (and `A = ∅`).
    TODO: Full proof requires showing that under ISOM, LAA + CONSERV + non-triviality
    forces the quantifier to be one of these three, by number triangle analysis. -/
theorem laa_characterization :
    LeftAntiAdditive (every_sem m) ∧
    LeftAntiAdditive (no_sem m) ∧
    ¬LeftAntiAdditive (most_sem (m := toyModel)) := by
  exact ⟨every_laa, no_laa, by
    intro h
    -- A = {john, pizza}, B = {mary}, C = {john, mary}
    -- most(A∪B, C) = most({j,p,m}, {j,m}) = 2>1 = true
    -- most(A, C) = most({j,p}, {j,m}) = 1>1 = false  → conjunction false
    exact absurd (h (λ x => match x with | .john | .pizza => true | _ => false)
                    (λ x => match x with | .mary => true | _ => false)
                    (λ x => match x with | .john | .mary => true | _ => false))
                 (by native_decide)⟩

-- === Duality square (P&W §1.1.1) ===

/-- Inner negation maps `every` to `no`: every...not = no.
    `∀x. R(x) → ¬S(x)` = `¬∃x. R(x) ∧ S(x)`. -/
theorem innerNeg_every_eq_no : innerNeg (every_sem m) = no_sem m := by
  funext R S; dsimp only [innerNeg, every_sem, no_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact forall_congr' fun x => by cases S x <;> simp

/-- The dual of `every` is `some`: Q̌(every) = some.
    `¬(∀x. R(x) → ¬S(x))` = `∃x. R(x) ∧ S(x)`. -/
theorem dualQ_every_eq_some : dualQ (every_sem m) = some_sem m := by
  funext R S; dsimp only [dualQ, outerNeg, innerNeg, every_sem, some_sem]
  rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  push Not
  exact exists_congr fun x => by cases R x <;> cases S x <;> simp

-- === Extension (P&W Ch.4): spectator irrelevance ===

/-- `every_sem` satisfies Extension: spectator elements
    (outside the restrictor) don't affect truth values.
    Proof: `!R(e) || S(e) = true` when `R(e) = false`, so `all` is unchanged. -/
theorem every_ext_spectator {m : Model} (es : List m.Entity) (e : m.Entity)
    (R S : m.Entity → Bool) (hR : R e = false) :
    (e :: es).all (λ x => !R x || S x) =
    es.all (λ x => !R x || S x) := by
  simp [List.all_cons, hR]

/-- `some_sem` satisfies Extension. -/
theorem some_ext_spectator {m : Model} (es : List m.Entity) (e : m.Entity)
    (R S : m.Entity → Bool) (hR : R e = false) :
    (e :: es).any (λ x => R x && S x) =
    es.any (λ x => R x && S x) := by
  simp [List.any_cons, hR]

/-- `no_sem` satisfies Extension. -/
theorem no_ext_spectator {m : Model} (es : List m.Entity) (e : m.Entity)
    (R S : m.Entity → Bool) (hR : R e = false) :
    (e :: es).all (λ x => !R x || !S x) =
    es.all (λ x => !R x || !S x) := by
  simp [List.all_cons, hR]

/-- `most_sem` satisfies Extension: spectators don't enter
    either R∩S or R\S, so the cardinality comparison is unchanged. -/
theorem most_ext_spectator {m : Model} (es : List m.Entity) (e : m.Entity)
    (R S : m.Entity → Bool) (hR : R e = false) :
    (e :: es).filter (λ x => R x && S x) = es.filter (λ x => R x && S x) ∧
    (e :: es).filter (λ x => R x && !S x) = es.filter (λ x => R x && !S x) := by
  constructor <;> (simp [hR])

-- === Extension: composed with denotations (P&W Ch.4) ===

private theorem all_filter_eq {α : Type*} (es : List α) (R S : α → Bool) :
    es.all (λ x => !R x || S x) = (es.filter R).all S := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, List.filter_cons]
    cases hR : R a
    · simp only [Bool.not_false, ↓reduceIte]; exact ih
    · simp only [Bool.not_true, Bool.false_or, ↓reduceIte, List.all_cons]; exact congrArg _ ih

private theorem any_filter_eq {α : Type*} (es : List α) (R S : α → Bool) :
    es.any (λ x => R x && S x) = (es.filter R).any S := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons, List.filter_cons]
    cases hR : R a
    · simp only [Bool.false_and, ↓reduceIte]; exact ih
    · simp only [Bool.true_and, ↓reduceIte, List.any_cons]; exact congrArg _ ih

private theorem all_neg_filter_eq {α : Type*} (es : List α) (R S : α → Bool) :
    es.all (λ x => !R x || !S x) = (es.filter R).all (λ x => !S x) := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, List.filter_cons]
    cases hR : R a
    · simp only [Bool.not_false, ↓reduceIte]; exact ih
    · simp only [Bool.not_true, Bool.false_or, ↓reduceIte, List.all_cons]; exact congrArg _ ih

private theorem filter_and_eq {α : Type*} (es : List α) (R S : α → Bool) :
    es.filter (λ x => R x && S x) = (es.filter R).filter S := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    simp only [List.filter_cons]
    cases hR : R a <;> cases hS : S a
    all_goals simp only [hR, hS, Bool.false_and, Bool.true_and,
                          Bool.false_eq_true, ↓reduceIte, List.filter_cons, ih]

/-- `every_sem` Extension at the denotation level: truth depends only on
    R-elements of the domain. Spectators are irrelevant.
    `every(R,S) = ∀x∈R. S(x)`. -/
theorem every_sem_extension (es : List m.Entity) (hComplete : ∀ x, x ∈ es) (R S : m.Entity → Bool) :
    every_sem m R S = (es.filter R).all S := by
  dsimp only [every_sem, Model.interpTy]; rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro h x hx; simp only [List.mem_filter] at hx; exact h x hx.2
  · intro h x hR; exact h x (List.mem_filter.mpr ⟨hComplete x, hR⟩)

/-- `some_sem` Extension at the denotation level.
    `some(R,S) = ∃x∈R. S(x)`. -/
theorem some_sem_extension (es : List m.Entity) (hComplete : ∀ x, x ∈ es) (R S : m.Entity → Bool) :
    some_sem m R S = (es.filter R).any S := by
  dsimp only [some_sem, Model.interpTy]; rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true]
  constructor
  · intro ⟨x, hR, hS⟩; exact ⟨x, List.mem_filter.mpr ⟨hComplete x, hR⟩, hS⟩
  · intro ⟨x, hx, hS⟩; exact ⟨x, (List.mem_filter.mp hx).2, hS⟩

/-- `no_sem` Extension at the denotation level.
    `no(R,S) = ∀x∈R. ¬S(x)`. -/
theorem no_sem_extension (es : List m.Entity) (hComplete : ∀ x, x ∈ es) (R S : m.Entity → Bool) :
    no_sem m R S = (es.filter R).all (λ x => !S x) := by
  dsimp only [no_sem, Model.interpTy]; rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro h x hx
    have hm := List.mem_filter.mp hx
    have hSF := h x hm.2
    cases hS : S x <;> simp_all
  · intro h x hR
    have hNS := h x (List.mem_filter.mpr ⟨hComplete x, hR⟩)
    simp only [Bool.not_eq_true'] at hNS; exact hNS

-- === Positive/Negative Strong (P&W Ch.6) ===

/-- `every_sem` is positive strong: every(A,A) = true for all A.
    Proof: `R(x) = true → R(x) = true` for all x. -/
theorem every_positive_strong : PositiveStrong (every_sem m) := by
  intro R; dsimp only [every_sem]; rw [decide_eq_true_eq]
  intro x hR; exact hR

/-- `no_sem` is negative strong (@cite{peters-westerstahl-2006} §5.3 fn.9):
    no(A,A) = false for all non-empty A.
    For the empty restrictor, no(∅,∅) = true (vacuously), so `NegativeStrong`
    (which requires Q(R,R) = false for ALL R) fails when empty R exists.
    We prove the non-empty case. -/
theorem no_negative_strong_nonempty (R : m.Entity → Bool)
    (hR : ∃ x : m.Entity, R x = true) :
    no_sem m R R = false := by
  dsimp only [no_sem, Model.interpTy]
  rw [Bool.eq_false_iff]
  intro h; rw [decide_eq_true_eq] at h
  obtain ⟨x, hRx⟩ := hR
  exact absurd (h x hRx) (by simp [hRx])

/-- `no_sem` is NOT positive strong: no(A,A) = false when A is non-empty.
    Counterexample: R = {john}. -/
theorem no_not_positive_strong : ¬PositiveStrong (no_sem (m := toyModel)) := by
  intro h; exact absurd (h student_sem) (by native_decide)

-- === K&S Existential det classification (§3.3, G3) ===

/-- `⟦some⟧` is existential (K&S G3): some(A,B) = some(A∩B, everything).
    some is natural in there-sentences: "There are some cats." -/
theorem some_existential : Existential (some_sem m) := by
  intro R S; dsimp only [some_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact exists_congr fun x => by cases R x <;> simp

/-- `⟦no⟧` is existential (K&S G3): no(A,B) = no(A∩B, everything).
    no is natural in there-sentences: "There are no cats." -/
theorem no_existential : Existential (no_sem m) := by
  intro R S; dsimp only [no_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact forall_congr' fun x => by cases R x <;> simp

/-- `⟦every⟧` is NOT existential (K&S §3.3).
    "every" is not natural in there-sentences: *"There is every cat."
    Witness: R=students, S=things. every(R,S)=true but every(R∩S, 1)=true trivially,
    yet every(thing, student)≠every(thing∩student, 1). -/
theorem every_not_existential : ¬Existential (every_sem (m := toyModel)) := by
  intro h; exact absurd (h thing_sem student_sem) (by native_decide)

/-- `⟦most⟧` is NOT existential (K&S §3.3).
    "most" is not natural in there-sentences: *"There are most cats."
    Witness: R={john,mary}, S={john,pizza}. |R∩S|=1 vs |R\S|=1, so most(R,S)=false.
    But most(R∩S, 1_P): |{john}∩1_P|=1 vs |{john}\1_P|=0, so most(R∩S, 1_P)=true. -/
theorem most_not_existential : ¬Existential (most_sem (m := toyModel)) := by
  intro h
  exact absurd (h student_sem (λ x => match x with | .john => true | .pizza => true | _ => false))
    (by native_decide)

-- ============================================================================
-- @cite{van-benthem-1984}: Relational Properties of Concrete Quantifiers
-- ============================================================================

/-- `⟦every⟧` is transitive: A ⊆ B and B ⊆ C implies A ⊆ C. -/
theorem every_transitive : QTransitive (every_sem m) := by
  intro A B C hAB hBC
  dsimp only [every_sem] at *; rw [decide_eq_true_eq] at *
  intro x hA; exact hBC x (hAB x hA)

/-- `⟦every⟧` is antisymmetric: A ⊆ B and B ⊆ A implies A = B. -/
theorem every_antisymmetric : QAntisymmetric (every_sem m) := by
  intro A B hAB hBA
  dsimp only [every_sem] at *; rw [decide_eq_true_eq] at *
  funext x; cases hA : A x <;> cases hB : B x <;> simp_all

/-- `⟦some⟧` is quasi-reflexive: A∩B ≠ ∅ implies A∩A ≠ ∅ (i.e., A ≠ ∅). -/
theorem some_quasi_reflexive : QuasiReflexive (some_sem m) := by
  intro A B hQAB
  dsimp only [some_sem] at *; rw [decide_eq_true_eq] at *
  obtain ⟨x, hA, _⟩ := hQAB
  exact ⟨x, hA, hA⟩

/-- `⟦no⟧` is quasi-universal: A∩A = ∅ (i.e., A = ∅) implies A∩B = ∅ for all B. -/
theorem no_quasi_universal : QuasiUniversal (no_sem m) := by
  intro A B hQAA
  dsimp only [no_sem] at *; rw [decide_eq_true_eq] at *
  intro x hA; exact absurd hA (by simp [hQAA x hA])

-- ============================================================================
-- @cite{van-benthem-1984}: Double Monotonicity Classification
-- ============================================================================

/-- `⟦every⟧` is restrictor-↓ (anti-persistent).
    Follows from Zwarts bridge: reflexive + transitive + CONSERV → ↓MON. -/
theorem every_restrictor_down : RestrictorDownwardMono (every_sem m) :=
  zwarts_refl_trans_restrictorDown _ every_conservative every_positive_strong every_transitive

/-- `⟦some⟧` is restrictor-↑ (persistent): A ⊆ A' and some(A,B) → some(A',B). -/
theorem some_restrictor_up : RestrictorUpwardMono (some_sem m) := by
  intro R R' S hRR' hQ
  dsimp only [some_sem] at *; rw [decide_eq_true_eq] at *
  obtain ⟨x, hR, hS⟩ := hQ
  exact ⟨x, hRR' x hR, hS⟩

/-- `⟦no⟧` is restrictor-↓ (anti-persistent): A ⊆ A' and no(A',B) → no(A,B). -/
theorem no_restrictor_down : RestrictorDownwardMono (no_sem m) := by
  intro R R' S hRR' hQ
  dsimp only [no_sem] at *; rw [decide_eq_true_eq] at *
  intro x hR; exact hQ x (hRR' x hR)

/-- `⟦every⟧` has double monotonicity ↓MON↑ (@cite{van-benthem-1984} §4.2). -/
theorem every_doubleMono :
    RestrictorDownwardMono (every_sem m) ∧ ScopeUpwardMono (every_sem m) :=
  ⟨every_restrictor_down, every_scope_up⟩

/-- `⟦some⟧` has double monotonicity ↑MON↑. -/
theorem some_doubleMono :
    RestrictorUpwardMono (some_sem m) ∧ ScopeUpwardMono (some_sem m) :=
  ⟨some_restrictor_up, some_scope_up⟩

/-- `⟦no⟧` has double monotonicity ↓MON↓. -/
theorem no_doubleMono :
    RestrictorDownwardMono (no_sem m) ∧ ScopeDownwardMono (no_sem m) :=
  ⟨no_restrictor_down, no_scope_down⟩

/-- `outerNeg ⟦every⟧` (= "not all") has double monotonicity ↑MON↓. -/
theorem notAll_doubleMono :
    RestrictorUpwardMono (outerNeg (every_sem m)) ∧
    ScopeDownwardMono (outerNeg (every_sem m)) :=
  ⟨outerNeg_restrictorDown_to_up _ every_restrictor_down,
   outerNeg_up_to_down _ every_scope_up⟩

/-- `⟦every⟧` is filtrating: every(A,B) ∧ every(A,C) → every(A, B∩C). -/
theorem every_filtrating : Filtrating (every_sem m) := by
  intro A B C hAB hAC
  dsimp only [every_sem] at *; rw [decide_eq_true_eq] at *
  intro x hA; simp [hAB x hA, hAC x hA]

-- ============================================================================
-- Aristotelian Square of Opposition
-- @cite{belnap-1970} @cite{strawson-1952}
--
-- The four traditional forms (A/E/I/O) and their logical relations,
-- derived from generalized quantifier denotations:
--   A: every(R,S) = ∀x. R(x) → S(x)     (universal affirmative)
--   E: no(R,S)    = ∀x. R(x) → ¬S(x)    (universal negative)
--   I: some(R,S)  = ∃x. R(x) ∧ S(x)     (particular affirmative)
--   O: ¬every(R,S)                        (particular negative)
-- ============================================================================

/-- **Contradiction (A vs O)**: the A-form and O-form are contradictories. -/
theorem every_contradicts_notEvery (R S : m.Entity → Bool) :
    every_sem m R S = !(outerNeg (every_sem m) R S) := by
  simp [outerNeg, Bool.not_not]

/-- **Contradiction (E vs I)**: the E-form and I-form are contradictories.

    Follows from `outerNeg_some_eq_no`: negating "some" gives "no". -/
theorem no_contradicts_some (R S : m.Entity → Bool) :
    no_sem m R S = !(some_sem m R S) :=
  (congr_fun (congr_fun outerNeg_some_eq_no R) S).symm

/-- **Contrariety (A ∧ E)**: the A-form and E-form can't both hold
    unless the restrictor is empty. If every R is S and no R is S,
    then nothing satisfies R. -/
theorem a_e_contrary (R S : m.Entity → Bool) :
    every_sem m R S = true → no_sem m R S = true →
    ∀ x : m.Entity, R x = false := by
  dsimp only [every_sem, no_sem, Model.interpTy]
  rw [decide_eq_true_eq, decide_eq_true_eq]
  intro hA hE x
  cases hR : R x
  · rfl
  · have h1 := hA x hR; have h2 := hE x hR; simp_all

/-- **Subalternation (A → I)**: the A-form entails the I-form when the
    restrictor is non-empty. This is @cite{belnap-1970}'s assertiveness
    condition: ∀x(Cx/Bx) presupposes ∃xCx. @cite{strawson-1952} argued
    "All S are P" presupposes there are Ss — Belnap *derives* this. -/
theorem subalternation_a_i (R S : m.Entity → Bool)
    (hR : ∃ x : m.Entity, R x = true) :
    every_sem m R S = true → some_sem m R S = true := by
  dsimp only [every_sem, some_sem, Model.interpTy]
  rw [decide_eq_true_eq, decide_eq_true_eq]
  intro hA
  obtain ⟨x, hRx⟩ := hR
  exact ⟨x, hRx, hA x hRx⟩

/-- **Subalternation (E → O)**: the E-form entails the O-form when the
    restrictor is non-empty. -/
theorem subalternation_e_o (R S : m.Entity → Bool)
    (hR : ∃ x : m.Entity, R x = true) :
    no_sem m R S = true → outerNeg (every_sem m) R S = true := by
  intro hE
  simp only [outerNeg]
  cases hA : every_sem m R S
  · rfl
  · obtain ⟨x, hRx⟩ := hR
    have := a_e_contrary R S hA hE x
    simp_all

/-- **Subcontrariety (I ∨ O)**: the I-form and O-form can't both fail
    when the restrictor is non-empty. Either some R is S, or not every
    R is S (or both). -/
theorem subcontrariety_i_o (R S : m.Entity → Bool)
    (hR : ∃ x : m.Entity, R x = true) :
    some_sem m R S = true ∨ outerNeg (every_sem m) R S = true := by
  cases hS : some_sem m R S
  · right
    simp only [outerNeg]
    cases hA : every_sem m R S
    · rfl
    · have hE : no_sem m R S = true := by rw [no_contradicts_some, hS]; rfl
      obtain ⟨x, hRx⟩ := hR
      exact absurd (a_e_contrary R S hA hE x) (by simp [hRx])
  · exact Or.inl rfl

-- ============================================================================
-- Basic Left Monotonicities (@cite{peters-westerstahl-2006} §5.5)
-- ============================================================================

/-- `⟦some⟧` is ↑_SE Mon: adding elements of B to A preserves some(A,B). -/
theorem some_upSE : UpSEMon (some_sem m) := by
  exact restrictorUpMono_to_upSE _ some_restrictor_up

/-- `⟦some⟧` is ↑_SW Mon: adding elements outside B to A preserves some(A,B). -/
theorem some_upSW : UpSWMon (some_sem m) := by
  exact restrictorUpMono_to_upSW _ some_restrictor_up

/-- `⟦every⟧` is ↓_NW Mon: removing elements of B from A preserves every(A,B). -/
theorem every_downNW : DownNWMon (every_sem m) := by
  exact restrictorDownMono_to_downNW _ every_restrictor_down

/-- `⟦every⟧` is ↓_NE Mon: removing elements outside B from A preserves every(A,B). -/
theorem every_downNE : DownNEMon (every_sem m) := by
  exact restrictorDownMono_to_downNE _ every_restrictor_down

/-- `⟦no⟧` is ↓_NW Mon. -/
theorem no_downNW : DownNWMon (no_sem m) := by
  exact restrictorDownMono_to_downNW _ no_restrictor_down

/-- `⟦no⟧` is ↓_NE Mon. -/
theorem no_downNE : DownNEMon (no_sem m) := by
  exact restrictorDownMono_to_downNE _ no_restrictor_down

-- ============================================================================
-- Smooth Quantifiers (@cite{peters-westerstahl-2006} §5.6)
-- ============================================================================

/-- `⟦some⟧` is ↓_NE Mon (direct proof).
    Removing non-S elements from A preserves ∃x.R(x)∧S(x) since the witness is in S. -/
theorem some_downNE : DownNEMon (some_sem m) := by
  intro R S R' hSub hKeep hQ
  dsimp only [some_sem] at *; rw [decide_eq_true_eq] at *
  obtain ⟨x, hR, hS⟩ := hQ
  exact ⟨x, hKeep x hR hS, hS⟩

/-- `⟦some⟧` is smooth (↓_NE + ↑_SE).
    @cite{peters-westerstahl-2006} §5.6: persistence gives ↑_SE;
    the witness argument gives ↓_NE directly. -/
theorem some_smooth : Smooth (some_sem m) :=
  ⟨some_downNE, restrictorUpMono_to_upSE _ some_restrictor_up⟩

/-- `⟦every⟧` is ↑_SE Mon (direct proof).
    Adding B-elements to A preserves ∀x.R(x)→S(x) since the new elements satisfy S. -/
theorem every_upSE_direct : UpSEMon (every_sem m) := by
  intro R S R' hSub hDiff hQ
  dsimp only [every_sem] at *; rw [decide_eq_true_eq] at *
  intro x hR'
  cases hS : S x
  · exact absurd hS (by simp [hQ x (hDiff x hR' hS)])
  · rfl

/-- `⟦every⟧` is smooth (↓_NE + ↑_SE). Anti-persistence gives ↓_NE;
    adding S-elements to A preserves ∀x.R(x)→S(x) (direct ↑_SE proof). -/
theorem every_smooth : Smooth (every_sem m) :=
  ⟨every_downNE, every_upSE_direct⟩

/-- `⟦no⟧` is co-smooth (↓_NW + ↑_SW). Follows from anti-persistence. -/
theorem no_coSmooth_partial : DownNWMon (no_sem m) ∧ DownNEMon (no_sem m) :=
  (anti_persistent_iff_downNW_and_downNE _).mp no_restrictor_down

private lemma filter_sublist_of_imp {α : Type*} {l : List α}
    {p q : α → Bool} (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.filter_cons]
    by_cases hpa : p a = true
    · rw [if_pos hpa, if_pos (h a List.mem_cons_self hpa)]
      exact ih'.cons₂ a
    · rw [if_neg hpa]
      by_cases hqa : q a = true
      · rw [if_pos hqa]; exact ih'.cons a
      · rw [if_neg hqa]; exact ih'

/-- `⟦most⟧` is ↓_NE Mon (direct proof).
    Removing non-S elements from A preserves |A∩S| > |A\S| since |A∩S| stays
    the same while |A\S| decreases. -/
theorem most_downNE : DownNEMon (most_sem m) := by
  intro R S R' hSub hKeep hQ
  dsimp only [most_sem] at *; rw [decide_eq_true_eq] at *
  have hEq : count (fun x : m.Entity => R' x = true ∧ S x = true) =
      count (fun x : m.Entity => R x = true ∧ S x = true) := by
    simp only [count]; congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hR', hS⟩; exact ⟨hSub x hR', hS⟩
    · intro ⟨hR, hS⟩; exact ⟨hKeep x hR hS, hS⟩
  have hLe : count (fun x : m.Entity => R' x = true ∧ S x = false) ≤
      count (fun x : m.Entity => R x = true ∧ S x = false) :=
    count_le_of_imp fun x ⟨hR', hS⟩ => ⟨hSub x hR', hS⟩
  omega

/-- `⟦most⟧` is ↑_SE Mon (direct proof).
    Adding S-elements to A preserves |A∩S| > |A\S| since |A∩S| grows
    while |A\S| stays the same. -/
theorem most_upSE : UpSEMon (most_sem m) := by
  intro R S R' hSub hDiff hQ
  dsimp only [most_sem] at *; rw [decide_eq_true_eq] at *
  have hEq : count (fun x : m.Entity => R' x = true ∧ S x = false) =
      count (fun x : m.Entity => R x = true ∧ S x = false) := by
    simp only [count]; congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hR', hS⟩; exact ⟨hDiff x hR' hS, hS⟩
    · intro ⟨hR, hS⟩; exact ⟨hSub x hR, hS⟩
  have hLe : count (fun x : m.Entity => R x = true ∧ S x = true) ≤
      count (fun x : m.Entity => R' x = true ∧ S x = true) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hSub x hR, hS⟩
  omega

/-- `⟦most⟧` is smooth. This is a key empirical fact: most natural language
    Mon↑ determiners are smooth (@cite{peters-westerstahl-2006} §5.6, (5.28)). -/
theorem most_smooth : Smooth (most_sem m) :=
  ⟨most_downNE, most_upSE⟩

-- === Counting quantifier smoothness ===

/-- `⟦at least n⟧` is persistent (Mon↑ in restrictor), hence ↑_SE and ↑_SW. -/
theorem at_least_n_restrictor_up (n : Nat) : RestrictorUpwardMono (at_least_n_sem m n) := by
  intro R R' S hRR' h
  dsimp only [at_least_n_sem] at *; rw [decide_eq_true_eq] at *
  exact le_trans h (count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hRR' x hR, hS⟩)

/-- `⟦at least n⟧` is ↓_NE Mon: removing non-S elements from A preserves
    |A ∩ S| ≥ n since the S-witnesses are retained. -/
theorem at_least_n_downNE (n : Nat) : DownNEMon (at_least_n_sem m n) := by
  intro R S R' hSub hKeep hQ
  dsimp only [at_least_n_sem] at *; rw [decide_eq_true_eq] at *
  have hEq : count (fun x : m.Entity => R' x = true ∧ S x = true) =
      count (fun x : m.Entity => R x = true ∧ S x = true) := by
    simp only [count]; congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hR', hS⟩; exact ⟨hSub x hR', hS⟩
    · intro ⟨hR, hS⟩; exact ⟨hKeep x hR hS, hS⟩
  omega

/-- `⟦at least n⟧` is smooth (↓_NE + ↑_SE).
    Persistence gives ↑_SE; the witness-preservation argument gives ↓_NE. -/
theorem at_least_n_smooth (n : Nat) : Smooth (at_least_n_sem m n) :=
  ⟨at_least_n_downNE n, restrictorUpMono_to_upSE _ (at_least_n_restrictor_up n)⟩

/-- `⟦at most n⟧` is anti-persistent (Mon↓ in restrictor). Derived from duality:
    outerNeg flips Mon↑_restrictor to Mon↓_restrictor. -/
theorem at_most_n_restrictor_down (n : Nat) : RestrictorDownwardMono (at_most_n_sem m n) := by
  rw [at_most_eq_outerNeg_at_least_succ]
  exact outerNeg_restrictorUp_to_down _ (at_least_n_restrictor_up _)

/-- `⟦at most n⟧` is co-smooth (↓_NW + ↑_SW). Derived from duality:
    Smooth(at_least) ↔ CoSmooth(outerNeg(at_least)) = CoSmooth(at_most). -/
theorem at_most_n_coSmooth (n : Nat) : CoSmooth (at_most_n_sem m n) := by
  rw [at_most_eq_outerNeg_at_least_succ]
  exact (smooth_iff_outerNeg_coSmooth _).mp (at_least_n_smooth _)

-- ============================================================================
-- Quantity / Isomorphism Closure Proofs (@cite{mostowski-1957})
-- ============================================================================

/-- `Quantity` is closed under outerNeg: if Q depends only on cell cardinalities,
    so does ~Q. -/
theorem quantity_outerNeg (q : m.interpTy Ty.det) (h : Quantity q) :
    Quantity (outerNeg q) := by
  intro R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  simp only [outerNeg]; rw [h R₁ S₁ R₂ S₂ hTT hTF hFT hFF]

/-- `Quantity` is closed under meet: if Q₁ and Q₂ depend only on cell
    cardinalities, so does Q₁ ⊓ Q₂. -/
theorem quantity_gqMeet (q₁ q₂ : m.interpTy Ty.det)
    (h₁ : Quantity q₁) (h₂ : Quantity q₂) :
    Quantity (gqMeet q₁ q₂) := by
  intro R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  simp only [gqMeet]
  rw [h₁ R₁ S₁ R₂ S₂ hTT hTF hFT hFF, h₂ R₁ S₁ R₂ S₂ hTT hTF hFT hFF]

/-- `⟦at least n⟧` satisfies Quantity: truth depends only on |A ∩ B|. -/
theorem at_least_n_quantity (n : Nat) : Quantity (at_least_n_sem m n) := by
  intro R₁ S₁ R₂ S₂ hTT _ _ _
  dsimp only [at_least_n_sem]
  exact congrArg (fun k => decide (k ≥ n)) hTT

/-- `⟦at most n⟧` satisfies Quantity: truth depends only on |A ∩ B|. -/
theorem at_most_n_quantity (n : Nat) : Quantity (at_most_n_sem m n) := by
  intro R₁ S₁ R₂ S₂ hTT _ _ _
  dsimp only [at_most_n_sem]
  exact congrArg (fun k => decide (k ≤ n)) hTT

/-- `⟦exactly n⟧` satisfies Quantity. Derived from meet closure:
    exactly n = (at least n) ⊓ (at most n). -/
theorem exactly_n_quantity (n : Nat) : Quantity (exactly_n_sem m n) := by
  rw [exactly_eq_meet_at_least_at_most]
  exact quantity_gqMeet _ _ (at_least_n_quantity n) (at_most_n_quantity n)

/-- `⟦some⟧` satisfies Quantity. Derived: some = at least 1. -/
theorem some_quantity : Quantity (some_sem m) := by
  rw [some_eq_at_least_1]; exact at_least_n_quantity 1

/-- `⟦no⟧` satisfies Quantity. Derived: no = at most 0. -/
theorem no_quantity : Quantity (no_sem m) := by
  rw [no_eq_at_most_0]; exact at_most_n_quantity 0

/-- `⟦every⟧` satisfies Quantity: truth depends only on |A \ B|.
    every(A,B) ↔ |A \ B| = 0. Proof via QuantityInvariant bridge:
    `forall_bij_inv` gives bijection-invariance, `quantity_of_quantityInvariant`
    converts to cell-cardinality form. -/
private theorem every_quantityInvariant :
    Core.Quantification.QuantityInvariant (every_sem m) := by
  intro A B A' B' f hBij hA hB
  dsimp only [every_sem]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  rw [forall_bij_inv f hBij]
  exact forall_congr' fun x => by rw [hA, hB]

theorem every_quantity : Quantity (every_sem m) :=
  quantity_of_quantityInvariant _ every_quantityInvariant

/-- `⟦most⟧` satisfies Quantity: truth depends on |A ∩ B| and |A \ B|.
    most(A,B) ↔ |A ∩ B| > |A \ B|. -/
theorem most_quantity : Quantity (most_sem m) := by
  intro R₁ S₁ R₂ S₂ hTT hTF _ _
  dsimp only [most_sem]
  exact congrArg₂ (fun a b => decide (a > b)) hTT hTF

/-- `⟦few⟧` satisfies Quantity: truth depends on |A ∩ B| and |A \ B|.
    few(A,B) ↔ |A ∩ B| < |A \ B|. -/
theorem few_quantity : Quantity (few_sem m) := by
  intro R₁ S₁ R₂ S₂ hTT hTF _ _
  dsimp only [few_sem]
  exact congrArg₂ (fun a b => decide (a < b)) hTT hTF

/-- Count decomposition: |R| = |R∩S| + |R\S|. Every R-element is either in S or not. -/
private theorem count_decompose (R S : m.Entity → Bool) :
    count (fun x : m.Entity => R x = true) =
    count (fun x : m.Entity => R x = true ∧ S x = true) +
    count (fun x : m.Entity => R x = true ∧ S x = false) := by
  simp only [count]
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hR; cases hS : S x <;> simp [hR]
    · intro h; rcases h with ⟨hR, _⟩ | ⟨hR, _⟩ <;> exact hR
  · simp only [Finset.disjoint_filter]
    intro x _ ⟨_, h1⟩ ⟨_, h2⟩; simp [h1] at h2

/-- `⟦half⟧` satisfies Quantity: truth depends on |A ∩ B| and |A \ B|.
    half(A,B) ↔ 2 * |A ∩ B| = |A|, and |A| = |A ∩ B| + |A \ B|. -/
theorem half_quantity : Quantity (half_sem m) := by
  intro R₁ S₁ R₂ S₂ hTT hTF _ _
  dsimp only [half_sem]
  exact congrArg₂ (fun a b => decide (2 * a = b)) hTT
    (show count (fun x : m.Entity => R₁ x = true) =
          count (fun x : m.Entity => R₂ x = true) by
      have h₁ := count_decompose R₁ S₁
      have h₂ := count_decompose R₂ S₂
      omega)

-- ============================================================================
-- SatisfiesUniversals (@cite{van-de-pol-etal-2023})
-- ============================================================================

/-- `⟦some⟧` satisfies all three universals: CONSERV ∧ QUANTITY ∧ Mon↑. -/
theorem some_satisfiesUniversals : SatisfiesUniversals (some_sem m) :=
  ⟨some_conservative, some_quantity, Or.inl some_scope_up⟩

/-- `⟦every⟧` satisfies all three universals: CONSERV ∧ QUANTITY ∧ Mon↑. -/
theorem every_satisfiesUniversals : SatisfiesUniversals (every_sem m) :=
  ⟨every_conservative, every_quantity, Or.inl every_scope_up⟩

/-- `⟦no⟧` satisfies all three universals: CONSERV ∧ QUANTITY ∧ Mon↓. -/
theorem no_satisfiesUniversals : SatisfiesUniversals (no_sem m) :=
  ⟨no_conservative, no_quantity, Or.inr no_scope_down⟩

/-- `⟦most⟧` satisfies all three universals: CONSERV ∧ QUANTITY ∧ Mon↑. -/
theorem most_satisfiesUniversals : SatisfiesUniversals (most_sem m) :=
  ⟨most_conservative, most_quantity, Or.inl most_scope_up⟩

/-- `⟦few⟧` satisfies all three universals: CONSERV ∧ QUANTITY ∧ Mon↓. -/
theorem few_satisfiesUniversals : SatisfiesUniversals (few_sem m) :=
  ⟨few_conservative, few_quantity, Or.inr few_scope_down⟩

/-- `⟦at least n⟧` satisfies all three universals: CONSERV ∧ QUANTITY ∧ Mon↑. -/
theorem at_least_n_satisfiesUniversals (n : Nat) :
    SatisfiesUniversals (at_least_n_sem m n) :=
  ⟨at_least_n_conservative n, at_least_n_quantity n, Or.inl (at_least_n_scope_up n)⟩

/-- `⟦at most n⟧` satisfies all three universals: CONSERV ∧ QUANTITY ∧ Mon↓. -/
theorem at_most_n_satisfiesUniversals (n : Nat) :
    SatisfiesUniversals (at_most_n_sem m n) :=
  ⟨at_most_n_conservative n, at_most_n_quantity n, Or.inr (at_most_n_scope_down n)⟩

/-- `⟦exactly n⟧` satisfies CONSERV ∧ QUANTITY but is neither Mon↑ nor Mon↓
    for n ≥ 1. This is expected: "exactly n" is a non-monotone quantifier.
    We prove the first two universals. -/
theorem exactly_n_conservative_quantity (n : Nat) :
    Conservative (exactly_n_sem m n) ∧ Quantity (exactly_n_sem m n) :=
  ⟨exactly_n_conservative n, exactly_n_quantity n⟩

-- ============================================================================
-- Exceptive Quantifiers: "all but n" (@cite{peters-westerstahl-2006})
-- ============================================================================

/-- `⟦all but 0⟧ = ⟦every⟧`: zero exceptions means universal. -/
theorem all_but_0_eq_every : all_but_n_sem m 0 = every_sem m := by
  funext (R : m.Entity → Bool) (S : m.Entity → Bool)
  dsimp only [all_but_n_sem, every_sem, Model.interpTy]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro h x hR
    by_contra hS
    have : 0 < count (fun x : m.Entity => R x = true ∧ S x = false) :=
      Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hR, by cases hSx : S x <;> simp_all⟩⟩
    omega
  · intro h
    simp only [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ ⟨hR, hS⟩
    have := h x hR; cases hSx : S x <;> simp_all

/-- `⟦all but n⟧` is conservative: depends only on R ∩ S within R. -/
theorem all_but_n_conservative (n : Nat) : Conservative (all_but_n_sem m n) := by
  intro R S; simp only [all_but_n_sem, count_and_neg_idem]

/-- `⟦all but n⟧` satisfies Quantity: truth depends only on |A \ B|. -/
theorem all_but_n_quantity (n : Nat) : Quantity (all_but_n_sem m n) := by
  intro R₁ S₁ R₂ S₂ _ hTF _ _
  dsimp only [all_but_n_sem]
  exact congrArg (fun k => decide (k = n)) hTF

/-- `⟦all but n⟧` satisfies CONSERV ∧ QUANTITY (but not MON for n ≥ 1). -/
theorem all_but_n_conservative_quantity (n : Nat) :
    Conservative (all_but_n_sem m n) ∧ Quantity (all_but_n_sem m n) :=
  ⟨all_but_n_conservative n, all_but_n_quantity n⟩

/-- `⟦between n and k⟧` is conservative (from meet closure). -/
theorem between_n_m_conservative (n k : Nat) :
    Conservative (between_n_m_sem m n k) := by
  intro R S; simp only [between_n_m_sem, gqMeet]
  rw [(at_least_n_conservative n R S), (at_most_n_conservative k R S)]

/-- `⟦between n and k⟧` satisfies Quantity (from meet closure). -/
theorem between_n_m_quantity (n k : Nat) : Quantity (between_n_m_sem m n k) :=
  quantity_gqMeet _ _ (at_least_n_quantity n) (at_most_n_quantity k)

/-- `⟦between n and k⟧` satisfies CONSERV ∧ QUANTITY. -/
theorem between_n_m_conservative_quantity (n k : Nat) :
    Conservative (between_n_m_sem m n k) ∧ Quantity (between_n_m_sem m n k) :=
  ⟨between_n_m_conservative n k, between_n_m_quantity n k⟩

-- ============================================================================
-- Proportional Quantifiers (@cite{peters-westerstahl-2006} §4.3)
-- ============================================================================

/-- Cross-ratio preserves strict inequality (one direction):
    if a₁ * b₂ = a₂ * b₁ and a₂ + b₂ > 0, then a₁ > b₁ → a₂ > b₂. -/
private theorem cross_ratio_preserves_gt (a₁ b₁ a₂ b₂ : Nat)
    (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁)
    (hgt : a₁ > b₁) :
    a₂ > b₂ := by
  by_contra hle
  push Not at hle
  rcases Nat.eq_zero_or_pos b₂ with rfl | hb₂pos
  · omega
  · have h1 : (b₁ + 1) * b₂ ≤ a₁ * b₂ :=
      Nat.mul_le_mul_right b₂ hgt
    have h3 : a₂ * b₁ ≤ b₂ * b₁ :=
      Nat.mul_le_mul_right b₁ hle
    rw [Nat.add_mul] at h1
    rw [Nat.mul_comm b₂ b₁] at h3
    omega

/-- Cross-ratio preserves strict inequality (biconditional). -/
private theorem cross_ratio_gt_iff (a₁ b₁ a₂ b₂ : Nat)
    (hne₁ : 0 < a₁ + b₁) (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) :
    a₁ > b₁ ↔ a₂ > b₂ :=
  ⟨cross_ratio_preserves_gt a₁ b₁ a₂ b₂ hne₂ hcross,
   cross_ratio_preserves_gt a₂ b₂ a₁ b₁ hne₁ hcross.symm⟩

/-- Cross-ratio preserves strict `<` inequality. -/
private theorem cross_ratio_lt_iff (a₁ b₁ a₂ b₂ : Nat)
    (hne₁ : 0 < a₁ + b₁) (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) :
    a₁ < b₁ ↔ a₂ < b₂ := by
  have hcross' : b₁ * a₂ = b₂ * a₁ := by
    rw [Nat.mul_comm b₁ a₂, Nat.mul_comm b₂ a₁]; exact hcross.symm
  exact cross_ratio_gt_iff b₁ a₁ b₂ a₂ (by omega) (by omega) hcross'

/-- Cross-ratio preserves equality. -/
private theorem cross_ratio_eq_iff (a₁ b₁ a₂ b₂ : Nat)
    (hne₁ : 0 < a₁ + b₁) (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁) :
    a₁ = b₁ ↔ a₂ = b₂ := by
  constructor
  · intro heq
    rw [heq] at hcross hne₁
    rw [Nat.mul_comm a₂ b₁] at hcross
    exact (Nat.mul_left_cancel (by omega) hcross).symm
  · intro heq
    rw [heq] at hcross hne₂
    rw [Nat.mul_comm a₁ b₂] at hcross
    exact Nat.mul_left_cancel (by omega) hcross

/-- `⟦most⟧` is proportional: most(A,B) ↔ |A∩B| > |A\B| depends only on
    the ratio |A∩B|/|A\B|. Cross-ratio equality preserves the > comparison. -/
theorem most_proportional : Proportional (most_sem m) := by
  intro R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross
  simp only [most_sem, Model.interpTy]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact cross_ratio_gt_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross

/-- `⟦few⟧` is proportional: few(A,B) ↔ |A∩B| < |A\B|. -/
theorem few_proportional : Proportional (few_sem m) := by
  intro R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross
  simp only [few_sem, Model.interpTy]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact cross_ratio_lt_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross

/-- Core arithmetic: 2a = a+b ↔ a = b, and cross-ratio preserves this. -/
private theorem half_prop_core (a₁ b₁ a₂ b₂ : Nat)
    (hNE₁ : 0 < a₁ + b₁) (hNE₂ : 0 < a₂ + b₂)
    (hCross : a₁ * b₂ = a₂ * b₁) :
    (2 * a₁ = a₁ + b₁) ↔ (2 * a₂ = a₂ + b₂) := by
  constructor
  · intro h
    have := (cross_ratio_eq_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross).mp (by omega)
    omega
  · intro h
    have := (cross_ratio_eq_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross).mpr (by omega)
    omega

theorem half_proportional : Proportional (half_sem m) := by
  intro R₁ S₁ R₂ S₂
  dsimp only []
  intro hNE₁ hNE₂ hCross
  simp only [half_sem]
  rw [count_decompose R₁ S₁, count_decompose R₂ S₂]
  simp only [Model.interpTy]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact half_prop_core _ _ _ _ hNE₁ hNE₂ hCross

/-- `⟦at least n⟧` is NOT proportional for n ≥ 2: it depends on absolute count,
    not ratio. Counterexample on toyModel: |{john}∩{john}| = 1, |{john}\{john}| = 0
    vs |{john,mary}∩{john,mary}| = 2, |{john,mary}\{john,mary}| = 0.
    Same ratio (1/0 = 2/0 in cross-ratio: 1*0 = 0 = 2*0) but at_least_2
    gives false for the first and true for the second. -/
theorem at_least_2_not_proportional : ¬Proportional (at_least_n_sem toyModel 2) := by
  intro h
  -- R₁ = {john}, S₁ = {john}: tt₁ = 1, tf₁ = 0
  -- R₂ = {john,mary}, S₂ = {john,mary}: tt₂ = 2, tf₂ = 0
  -- cross-ratio: 1 * 0 = 2 * 0 ✓, non-emptiness: 1 > 0 ✓, 2 > 0 ✓
  -- But at_least_2({john},{john}) = false, at_least_2({john,mary},{john,mary}) = true
  let R₁ : toyModel.Entity → Bool := fun x => match x with | .john => true | _ => false
  let S₁ := R₁
  let R₂ : toyModel.Entity → Bool := fun x => match x with | .john | .mary => true | _ => false
  let S₂ := R₂
  have := h R₁ S₁ R₂ S₂ (by native_decide) (by native_decide) (by native_decide)
  have h1 : at_least_n_sem toyModel 2 R₁ S₁ = false := rfl
  have h2 : at_least_n_sem toyModel 2 R₂ S₂ = true := rfl
  rw [h1, h2] at this
  exact Bool.noConfusion this

end FintypeProofs

end Semantics.Lexical.Determiner.Quantifier
