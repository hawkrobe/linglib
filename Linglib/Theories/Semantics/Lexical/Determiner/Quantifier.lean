import Linglib.Theories.Semantics.Montague.Types
import Linglib.Theories.Semantics.Composition.TypeShifting
import Linglib.Core.Logic.Quantification
import Mathlib.Data.List.Perm.Basic

/-!
# Generalized Quantifiers
@cite{barwise-cooper-1981} @cite{keenan-stavi-1986} @cite{van-de-pol-2023} @cite{van-de-pol-etal-2023} @cite{mostowski-1957}

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
- `FiniteModelProofs`: Concrete proofs for specific denotations (requires FiniteModel)

`ScopeUpwardMono`/`ScopeDownwardMono` are equivalent to Mathlib's
`Monotone`/`Antitone` (see `Core.Quantification.scopeUpMono_iff_monotone`),
connecting to `Semantics.Entailment.Polarity.IsUpwardEntailing = Monotone`.

-/

namespace Semantics.Lexical.Determiner.Quantifier

open Semantics.Montague
open Core.Quantification

def Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

/-- A model with a computable finite domain.
    `nodup` ensures each entity appears exactly once, which is needed for
    `QuantityInvariant` (bijection-invariance of filter-length–based quantifiers). -/
class FiniteModel (m : Model) where
  elements : List m.Entity
  complete : ∀ x : m.Entity, x ∈ elements
  nodup : elements.Nodup

def every_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    FiniteModel.elements.all (λ x => !restrictor x || scope x)

def some_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    FiniteModel.elements.any (λ x => restrictor x && scope x)

/-- Partee's `A` (existential closure) = Barwise & Cooper's `⟦some⟧`.
    Both compute `λR.λS. ∃x. R(x) ∧ S(x)` over a finite domain.
    `A` takes the domain explicitly; `some_sem` uses `FiniteModel.elements`. -/
theorem A_eq_some_sem (m : Model) [fm : FiniteModel m] :
    Semantics.Composition.TypeShifting.A fm.elements = some_sem m := by
  funext R S; rfl

def no_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    FiniteModel.elements.all (λ x => !restrictor x || !scope x)

/-- `⟦most⟧(R)(S) = |R ∩ S| > |R \ S|` -/
def most_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    let inBoth := FiniteModel.elements.filter (λ x => restrictor x && scope x)
    let inROnly := FiniteModel.elements.filter (λ x => restrictor x && !scope x)
    decide (inBoth.length > inROnly.length)

/-- `⟦few⟧(R)(S) = |R ∩ S| < |R \ S|` — a minority of Rs are Ss.
    Dual of `most_sem`: few(R,S) ↔ ¬most(R,S) ∧ ¬half(R,S). -/
def few_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    let inBoth := FiniteModel.elements.filter (λ x => restrictor x && scope x)
    let inROnly := FiniteModel.elements.filter (λ x => restrictor x && !scope x)
    decide (inBoth.length < inROnly.length)

/-- `⟦half⟧(R)(S) = 2 * |R ∩ S| = |R|` — exactly half of Rs are Ss. -/
def half_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    let inR := FiniteModel.elements.filter restrictor |>.length
    let inBoth := FiniteModel.elements.filter (λ x => restrictor x && scope x) |>.length
    decide (2 * inBoth = inR)

/-- `⟦at least n⟧(R)(S) = |R ∩ S| ≥ n` -/
def at_least_n_sem (m : Model) [FiniteModel m] (n : Nat) : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    let count := FiniteModel.elements.filter (λ x => restrictor x && scope x) |>.length
    decide (count ≥ n)

/-- `⟦at most n⟧(R)(S) = |R ∩ S| ≤ n` -/
def at_most_n_sem (m : Model) [FiniteModel m] (n : Nat) : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    let count := FiniteModel.elements.filter (λ x => restrictor x && scope x) |>.length
    decide (count ≤ n)

/-- `⟦exactly n⟧(R)(S) = |R ∩ S| = n` -/
def exactly_n_sem (m : Model) [FiniteModel m] (n : Nat) : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    let count := FiniteModel.elements.filter (λ x => restrictor x && scope x) |>.length
    decide (count = n)

instance : FiniteModel toyModel where
  elements := [.john, .mary, .pizza, .book]
  complete := λ x => by cases x <;> simp
  nodup := by simp [List.nodup_cons, List.mem_cons, List.mem_singleton]

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
-- Finite Model Proofs (require FiniteModel for FiniteModel.elements)
-- ============================================================================

section FiniteModelProofs

variable {m : Model} [FiniteModel m]

-- === Bijection invariance of filter length (for QuantityInvariant) ===

/-- Bijection on a Nodup+complete list is a permutation of that list.
    Key step for proving `QuantityInvariant` of cardinality-based quantifiers. -/
private theorem map_bij_perm (f : m.Entity → m.Entity) (hBij : Function.Bijective f) :
    (FiniteModel.elements.map f).Perm FiniteModel.elements := by
  rw [List.perm_ext_iff_of_nodup
    (FiniteModel.nodup.map hBij.injective) FiniteModel.nodup]
  intro a; constructor
  · intro h; exact FiniteModel.complete a
  · intro _; rw [List.mem_map]; exact ⟨hBij.surjective a |>.choose, FiniteModel.complete _,
      hBij.surjective a |>.choose_spec⟩

/-- Filter length is invariant under bijective predicate substitution.
    `|filter P elements| = |filter (P ∘ f) elements|` when f is a bijection. -/
theorem filter_length_bij_inv (f : m.Entity → m.Entity) (hBij : Function.Bijective f)
    (P : m.Entity → Bool) :
    (FiniteModel.elements.filter P).length =
    (FiniteModel.elements.filter (P ∘ f)).length := by
  have hPerm := map_bij_perm f hBij
  have h1 : (FiniteModel.elements.filter P).length =
      ((FiniteModel.elements.map f).filter P).length :=
    (hPerm.filter P).length_eq.symm
  rw [List.filter_map] at h1
  rw [h1, List.length_map]

/-- `all P elements = all (P ∘ f) elements` when f is a bijection on a
    Nodup+complete domain. Both reduce to `∀ x, P x = true`. -/
theorem all_bij_inv (f : m.Entity → m.Entity) (hBij : Function.Bijective f)
    (P : m.Entity → Bool) :
    FiniteModel.elements.all P = FiniteModel.elements.all (P ∘ f) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h x hx; exact h (f x) (FiniteModel.complete _)
  · intro h x hx
    obtain ⟨y, rfl⟩ := hBij.surjective x
    exact h y (FiniteModel.complete _)

/-- `any P elements = any (P ∘ f) elements` when f is a bijection. -/
theorem any_bij_inv (f : m.Entity → m.Entity) (hBij : Function.Bijective f)
    (P : m.Entity → Bool) :
    FiniteModel.elements.any P = FiniteModel.elements.any (P ∘ f) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · intro ⟨x, _, hP⟩
    obtain ⟨y, rfl⟩ := hBij.surjective x
    exact ⟨y, FiniteModel.complete _, hP⟩
  · intro ⟨y, _, hP⟩; exact ⟨f y, FiniteModel.complete _, hP⟩

-- === Conservativity proofs ===

/-- `⟦every⟧` is conservative: `∀x. R(x) → S(x)` iff `∀x. R(x) → (R(x) ∧ S(x))`. -/
theorem every_conservative : Conservative (every_sem m) := by
  intro R S
  simp only [every_sem]
  congr 1; ext x
  cases R x <;> simp

/-- `⟦some⟧` is conservative: `∃x. R(x) ∧ S(x)` iff `∃x. R(x) ∧ (R(x) ∧ S(x))`. -/
theorem some_conservative : Conservative (some_sem m) := by
  intro R S
  simp only [some_sem]
  congr 1; ext x
  cases R x <;> simp

/-- `⟦no⟧` is conservative: `∀x. R(x) → ¬S(x)` iff `∀x. R(x) → ¬(R(x) ∧ S(x))`. -/
theorem no_conservative : Conservative (no_sem m) := by
  intro R S
  simp only [no_sem]
  congr 1; ext x
  cases R x <;> simp

@[simp] private theorem bool_and_idem (a b : Bool) :
    (a && (a && b)) = (a && b) := by
  cases a <;> cases b <;> rfl

@[simp] private theorem bool_and_neg_idem (a b : Bool) :
    (a && Bool.not (a && b)) = (a && Bool.not b) := by
  cases a <;> cases b <;> rfl

/-- `⟦most⟧` is conservative: the R-elements in S are the R-elements in R∩S. -/
theorem most_conservative : Conservative (most_sem m) := by
  intro R S
  simp only [most_sem]
  simp_rw [bool_and_idem, bool_and_neg_idem]

/-- `⟦few⟧` is conservative: the R-elements in S are the R-elements in R∩S. -/
theorem few_conservative : Conservative (few_sem m) := by
  intro R S
  simp only [few_sem]
  simp_rw [bool_and_idem, bool_and_neg_idem]

/-- `⟦half⟧` is conservative: depends only on R ∩ S within R. -/
theorem half_conservative : Conservative (half_sem m) := by
  intro R S
  simp only [half_sem]
  simp_rw [bool_and_idem]

/-- `⟦at least n⟧` is conservative: |R ∩ S| = |R ∩ (R ∩ S)|. -/
theorem at_least_n_conservative (n : Nat) : Conservative (at_least_n_sem m n) := by
  intro R S
  simp only [at_least_n_sem]
  simp_rw [bool_and_idem]

/-- `⟦at most n⟧` is conservative. -/
theorem at_most_n_conservative (n : Nat) : Conservative (at_most_n_sem m n) := by
  intro R S
  simp only [at_most_n_sem]
  simp_rw [bool_and_idem]

/-- `⟦exactly n⟧` is conservative. -/
theorem exactly_n_conservative (n : Nat) : Conservative (exactly_n_sem m n) := by
  intro R S
  simp only [exactly_n_sem]
  simp_rw [bool_and_idem]

-- === Scope monotonicity proofs ===

/-- `⟦every⟧` is upward monotone in scope. -/
theorem every_scope_up : ScopeUpwardMono (every_sem m) := by
  intro R S S' hSS' h
  simp only [every_sem] at *
  rw [List.all_eq_true] at *
  intro x hx
  specialize h x hx
  cases hR : R x
  · simp
  · simp [hR] at h ⊢; exact hSS' x h

/-- `⟦some⟧` is upward monotone in scope. -/
theorem some_scope_up : ScopeUpwardMono (some_sem m) := by
  intro R S S' hSS' h
  simp only [some_sem] at *
  rw [List.any_eq_true] at *
  obtain ⟨x, hx, hpred⟩ := h
  refine ⟨x, hx, ?_⟩
  cases hR : R x <;> simp_all

/-- `⟦no⟧` is downward monotone in scope. -/
theorem no_scope_down : ScopeDownwardMono (no_sem m) := by
  intro R S S' hSS' h
  simp only [no_sem] at *
  rw [List.all_eq_true] at *
  intro x hx
  specialize h x hx
  cases hR : R x
  · simp
  · simp [hR] at h ⊢
    cases hS : S x
    · rfl
    · exact absurd (hSS' x hS) (by simp [h])

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

/-- `⟦few⟧` is downward monotone in scope: if S ⊆ S' and few(R,S'),
    then few(R,S). Fewer Ss among Rs means even fewer S-subsets. -/
theorem few_scope_down : ScopeDownwardMono (few_sem m) := by
  intro R S S' hSS' h
  simp only [few_sem] at *
  rw [decide_eq_true_eq] at *
  have hFilter_sub : (FiniteModel.elements.filter (λ x => R x && S x)).length ≤
      (FiniteModel.elements.filter (λ x => R x && S' x)).length :=
    filter_length_le_of_imp _ _ _ (fun x hx => by
      simp only [Bool.and_eq_true] at *; exact ⟨hx.1, hSS' x hx.2⟩)
  have hFilter_sup : (FiniteModel.elements.filter (λ x => R x && !S' x)).length ≤
      (FiniteModel.elements.filter (λ x => R x && !S x)).length :=
    filter_length_le_of_imp _ _ _ (fun x hx => by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at *
      refine ⟨hx.1, ?_⟩
      cases hS : S x
      · rfl
      · exact absurd (hSS' x hS) (by simp [hx.2]))
  omega

/-- `⟦most⟧` is upward monotone in scope: if S ⊆ S' and most(R,S),
    then most(R,S'). |R∩S'| ≥ |R∩S| > |R\S| ≥ |R\S'|. -/
theorem most_scope_up : ScopeUpwardMono (most_sem m) := by
  intro R S S' hSS' h
  simp only [most_sem] at *
  rw [decide_eq_true_eq] at *
  have hFilter_sub : (FiniteModel.elements.filter (λ x => R x && S x)).length ≤
      (FiniteModel.elements.filter (λ x => R x && S' x)).length :=
    filter_length_le_of_imp _ _ _ (fun x hx => by
      simp only [Bool.and_eq_true] at *; exact ⟨hx.1, hSS' x hx.2⟩)
  have hFilter_sup : (FiniteModel.elements.filter (λ x => R x && !S' x)).length ≤
      (FiniteModel.elements.filter (λ x => R x && !S x)).length :=
    filter_length_le_of_imp _ _ _ (fun x hx => by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at *
      refine ⟨hx.1, ?_⟩
      cases hS : S x
      · rfl
      · exact absurd (hSS' x hS) (by simp [hx.2]))
  omega

-- === Counting quantifier identities (@cite{peters-westerstahl-2006} §5) ===

/-- Bridge between `List.any` and `List.filter.length`: existential check ↔ non-empty filter. -/
private lemma any_eq_decide_filter_ge_one {β : Type*} (l : List β) (p : β → Bool) :
    l.any p = decide ((l.filter p).length ≥ 1) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.any_cons, List.filter_cons]
    cases p a <;> simp [ih]

/-- `⟦some⟧ = ⟦at least 1⟧`: existential quantification is "at least one". -/
theorem some_eq_at_least_1 : some_sem m = at_least_n_sem m 1 := by
  funext R S; simp only [some_sem, at_least_n_sem]
  exact any_eq_decide_filter_ge_one _ _

/-- `outerNeg ⟦some⟧ = ⟦no⟧`: negating existence gives universal negation. -/
theorem outerNeg_some_eq_no : outerNeg (some_sem m) = no_sem m := by
  funext R S; simp only [outerNeg, some_sem, no_sem]
  rw [List.not_any_eq_all_not]; simp_rw [Bool.not_and]

/-- `⟦at most n⟧ = outerNeg ⟦at least n+1⟧`: duality of lower and upper bounds.
    This is the counting quantifier instance of the Square of Opposition. -/
theorem at_most_eq_outerNeg_at_least_succ (n : Nat) :
    at_most_n_sem m n = outerNeg (at_least_n_sem m (n + 1)) := by
  funext R S
  simp only [at_most_n_sem, at_least_n_sem, outerNeg]
  generalize (FiniteModel.elements.filter (fun x => R x && S x)).length = k
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
  funext R S
  simp only [exactly_n_sem, at_least_n_sem, at_most_n_sem, gqMeet]
  generalize (FiniteModel.elements.filter (fun x => R x && S x)).length = k
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  omega

/-- `⟦at least n⟧` is Mon↑ in scope: enlarging B cannot decrease |A ∩ B|. -/
theorem at_least_n_scope_up (n : Nat) : ScopeUpwardMono (at_least_n_sem m n) := by
  intro R S S' hSS' h
  simp only [at_least_n_sem, decide_eq_true_eq] at *
  exact le_trans h (filter_length_le_of_imp _ _ _ (fun x hx => by
    simp only [Bool.and_eq_true] at hx ⊢; exact ⟨hx.1, hSS' x hx.2⟩))

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
    (FiniteModel.elements.filter (λ x => R₁ x && S₁ x)).length =
    (FiniteModel.elements.filter (λ x => R₂ x && S₂ x)).length →
    (FiniteModel.elements.filter (λ x => R₁ x && !S₁ x)).length =
    (FiniteModel.elements.filter (λ x => R₂ x && !S₂ x)).length →
    (FiniteModel.elements.filter (λ x => !R₁ x && S₁ x)).length =
    (FiniteModel.elements.filter (λ x => !R₂ x && S₂ x)).length →
    (FiniteModel.elements.filter (λ x => !R₁ x && !S₁ x)).length =
    (FiniteModel.elements.filter (λ x => !R₂ x && !S₂ x)).length →
    q R₁ S₁ = q R₂ S₂

/--
A quantifier satisfies all three Barwise & Cooper universals.
@cite{van-de-pol-etal-2023} show these quantifiers have shorter MDL.
-/
def SatisfiesUniversals (q : m.interpTy Ty.det) : Prop :=
  Conservative q ∧ Quantity q ∧ (ScopeUpwardMono q ∨ ScopeDownwardMono q)

-- === Quantity ↔ QuantityInvariant (@cite{mostowski-1957}) ===

/-- `Quantity → QuantityInvariant`: cardinality-dependence implies bijection-invariance.
    Proof: a bijection preserves filter lengths (via `filter_length_bij_inv`),
    so all four cell cardinalities match, and `Quantity` gives the result. -/
theorem quantityInvariant_of_quantity (q : m.interpTy Ty.det) (hQ : Quantity q) :
    Core.Quantification.QuantityInvariant q := by
  intro A B A' B' f hBij hA hB
  have cell : ∀ (g : Bool → Bool → Bool),
      (FiniteModel.elements.filter (λ x => g (A x) (B x))).length =
      (FiniteModel.elements.filter (λ x => g (A' x) (B' x))).length := by
    intro g
    have hEq : (λ x => g (A' x) (B' x)) = (λ x => g (A x) (B x)) ∘ f :=
      funext λ x => show g (A' x) (B' x) = g (A (f x)) (B (f x)) by
        rw [(hA x).symm, (hB x).symm]
    rw [hEq]; exact filter_length_bij_inv f hBij _
  exact hQ A B A' B' (cell (· && ·))
    (cell (λ a b => a && !b)) (cell (λ a b => !a && b)) (cell (λ a b => !a && !b))

local instance decEqEntity : DecidableEq m.Entity := m.decEq

def finsetElems : Finset m.Entity := FiniteModel.elements.toFinset

local instance fintypeEntity : Fintype m.Entity where
  elems := finsetElems
  complete := by intro x; simp [finsetElems, FiniteModel.complete x]

private lemma card_cell (R S : m.Entity → Bool) (b₁ b₂ : Bool) :
    Fintype.card {x : m.Entity // R x == b₁ && S x == b₂} =
    (FiniteModel.elements.filter (λ x => R x == b₁ && S x == b₂)).length := by
  have : Fintype.card {x : m.Entity // R x == b₁ && S x == b₂} =
         (FiniteModel.elements.filter (λ x => R x == b₁ && S x == b₂)).toFinset.card := by
    apply Fintype.card_of_subtype
    intro x
    simp [FiniteModel.complete x]
  rw [this]
  apply List.toFinset_card_of_nodup
  apply List.Nodup.filter
  exact FiniteModel.nodup

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
    (h_len : ∀ b₁ b₂, (FiniteModel.elements.filter (λ x => R₁ x == b₁ && S₁ x == b₂)).length =
                      (FiniteModel.elements.filter (λ x => R₂ x == b₁ && S₂ x == b₂)).length) :
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
    (hTT : (FiniteModel.elements.filter (λ x => R₁ x && S₁ x)).length =
           (FiniteModel.elements.filter (λ x => R₂ x && S₂ x)).length)
    (hTF : (FiniteModel.elements.filter (λ x => R₁ x && !S₁ x)).length =
           (FiniteModel.elements.filter (λ x => R₂ x && !S₂ x)).length)
    (hFT : (FiniteModel.elements.filter (λ x => !R₁ x && S₁ x)).length =
           (FiniteModel.elements.filter (λ x => !R₂ x && S₂ x)).length)
    (hFF : (FiniteModel.elements.filter (λ x => !R₁ x && !S₁ x)).length =
           (FiniteModel.elements.filter (λ x => !R₂ x && !S₂ x)).length) :
    ∀ (b₁ b₂ : Bool), (FiniteModel.elements.filter (λ x => R₁ x == b₁ && S₁ x == b₂)).length =
             (FiniteModel.elements.filter (λ x => R₂ x == b₁ && S₂ x == b₂)).length := by
  intro b₁ b₂
  cases b₁ <;> cases b₂
  · have H1 : (λ x => R₁ x == false && S₁ x == false) = (λ x => !R₁ x && !S₁ x) := by funext x; cases R₁ x <;> cases S₁ x <;> rfl
    have H2 : (λ x => R₂ x == false && S₂ x == false) = (λ x => !R₂ x && !S₂ x) := by funext x; cases R₂ x <;> cases S₂ x <;> rfl
    rw [H1, H2]; exact hFF
  · have H1 : (λ x => R₁ x == false && S₁ x == true) = (λ x => !R₁ x && S₁ x) := by funext x; cases R₁ x <;> cases S₁ x <;> rfl
    have H2 : (λ x => R₂ x == false && S₂ x == true) = (λ x => !R₂ x && S₂ x) := by funext x; cases R₂ x <;> cases S₂ x <;> rfl
    rw [H1, H2]; exact hFT
  · have H1 : (λ x => R₁ x == true && S₁ x == false) = (λ x => R₁ x && !S₁ x) := by funext x; cases R₁ x <;> cases S₁ x <;> rfl
    have H2 : (λ x => R₂ x == true && S₂ x == false) = (λ x => R₂ x && !S₂ x) := by funext x; cases R₂ x <;> cases S₂ x <;> rfl
    rw [H1, H2]; exact hTF
  · have H1 : (λ x => R₁ x == true && S₁ x == true) = (λ x => R₁ x && S₁ x) := by funext x; cases R₁ x <;> cases S₁ x <;> rfl
    have H2 : (λ x => R₂ x == true && S₂ x == true) = (λ x => R₂ x && S₂ x) := by funext x; cases R₂ x <;> cases S₂ x <;> rfl
    rw [H1, H2]; exact hTT

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
def m_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    let inA := FiniteModel.elements.filter restrictor |>.length
    let inB := FiniteModel.elements.filter scope |>.length
    decide (inA > inB)

/-- M is not conservative: it inspects B outside A.
Witness: R = {john, mary}, S = {john, pizza}.
m_sem R S = (2 > 2) = false, but m_sem R (R∩S) = (2 > 1) = true. -/
theorem m_not_conservative : ¬Conservative (m_sem (m := toyModel)) := by
  intro h
  have := h student_sem (λ x => match x with | .john => true | .pizza => true | _ => false)
  simp only [m_sem, student_sem, FiniteModel.elements] at this
  exact absurd this Bool.noConfusion

-- === Symmetry proofs (P&W Ch.6) ===

/-- `⟦some⟧` is symmetric: ∃x.R(x)∧S(x) = ∃x.S(x)∧R(x). -/
theorem some_symmetric : QSymmetric (some_sem m) := by
  intro R S
  simp only [some_sem]
  congr 1; ext x
  cases R x <;> cases S x <;> rfl

/-- `⟦no⟧` is symmetric: ¬∃x.R(x)∧S(x) = ¬∃x.S(x)∧R(x). -/
theorem no_symmetric : QSymmetric (no_sem m) := by
  intro R S
  simp only [no_sem]
  congr 1; ext x
  cases R x <;> cases S x <;> rfl

/-- `⟦every⟧` is NOT symmetric. Witness: R=students, S=things (everything).
    every(students)(things)=true but every(things)(students)=false. -/
theorem every_not_symmetric : ¬QSymmetric (every_sem (m := toyModel)) := by
  intro h
  have := h student_sem thing_sem
  simp only [every_sem, student_sem, thing_sem, FiniteModel.elements] at this
  exact absurd this Bool.noConfusion

-- === Intersectivity via CONSERV+SYMM bridge ===

/-- `⟦some⟧` is intersective (follows from CONSERV + SYMM). -/
theorem some_intersective : IntersectionCondition (some_sem m) :=
  (conserv_symm_iff_int _ some_conservative).mp some_symmetric

/-- `⟦no⟧` is intersective. -/
theorem no_intersective : IntersectionCondition (no_sem m) :=
  (conserv_symm_iff_int _ no_conservative).mp no_symmetric

-- === Left anti-additivity (P&W §5.9) ===

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
  intro R R' S
  simp only [every_sem]
  have : FiniteModel.elements.all (λ x => !(R x || R' x) || S x) =
         FiniteModel.elements.all (λ x => (!R x || S x) && (!R' x || S x)) := by
    congr 1; funext x; cases R x <;> cases R' x <;> cases S x <;> rfl
  rw [this, list_all_and]

/-- `⟦no⟧` is left anti-additive: no(A∪B, C) = no(A,C) ∧ no(B,C). -/
theorem no_laa : LeftAntiAdditive (no_sem m) := by
  intro R R' S
  simp only [no_sem]
  have : FiniteModel.elements.all (λ x => !(R x || R' x) || !S x) =
         FiniteModel.elements.all (λ x => (!R x || !S x) && (!R' x || !S x)) := by
    congr 1; funext x; cases R x <;> cases R' x <;> cases S x <;> rfl
  rw [this, list_all_and]

-- === Right anti-additivity (scope position, P&W §5.9) ===

/-- `⟦no⟧` is right anti-additive: no(A, B∪C) = no(A,B) ∧ no(A,C).
    "Nobody saw A-or-B" ↔ "Nobody saw A and nobody saw B".
    This licenses strong NPIs in scope: "Nobody lifted a finger." -/
theorem no_raa : RightAntiAdditive (no_sem m) := by
  intro R S S'
  simp only [no_sem]
  have : FiniteModel.elements.all (λ x => !R x || !(S x || S' x)) =
         FiniteModel.elements.all (λ x => (!R x || !S x) && (!R x || !S' x)) := by
    congr 1; funext x; cases R x <;> cases S x <;> cases S' x <;> rfl
  rw [this, list_all_and]

-- === Duality square (P&W §1.1.1) ===

/-- Inner negation maps `every` to `no`: every...not = no.
    `∀x. R(x) → ¬S(x)` = `¬∃x. R(x) ∧ S(x)`. -/
theorem innerNeg_every_eq_no : innerNeg (every_sem m) = no_sem m := by
  funext R S; simp [innerNeg, every_sem, no_sem]

/-- The dual of `every` is `some`: Q̌(every) = some.
    `¬(∀x. R(x) → ¬S(x))` = `∃x. R(x) ∧ S(x)`. -/
theorem dualQ_every_eq_some : dualQ (every_sem m) = some_sem m := by
  funext R S; simp only [dualQ, outerNeg, innerNeg, every_sem, some_sem]
  simp [List.all_eq_not_any_not, Bool.not_not]

-- === Extension (P&W Ch.4): spectator irrelevance ===

/-- `every_sem` satisfies FiniteModel Extension: spectator elements
    (outside the restrictor) don't affect truth values.
    Proof: `!R(e) || S(e) = true` when `R(e) = false`, so `all` is unchanged. -/
theorem every_ext_spectator {m : Model} (es : List m.Entity) (e : m.Entity)
    (R S : m.Entity → Bool) (hR : R e = false) :
    (e :: es).all (λ x => !R x || S x) =
    es.all (λ x => !R x || S x) := by
  simp [List.all_cons, hR]

/-- `some_sem` satisfies FiniteModel Extension. -/
theorem some_ext_spectator {m : Model} (es : List m.Entity) (e : m.Entity)
    (R S : m.Entity → Bool) (hR : R e = false) :
    (e :: es).any (λ x => R x && S x) =
    es.any (λ x => R x && S x) := by
  simp [List.any_cons, hR]

/-- `no_sem` satisfies FiniteModel Extension. -/
theorem no_ext_spectator {m : Model} (es : List m.Entity) (e : m.Entity)
    (R S : m.Entity → Bool) (hR : R e = false) :
    (e :: es).all (λ x => !R x || !S x) =
    es.all (λ x => !R x || !S x) := by
  simp [List.all_cons, hR]

/-- `most_sem` satisfies FiniteModel Extension: spectators don't enter
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
    `every(R,S) = ∀x∈filter(R). S(x)`. -/
theorem every_sem_extension (R S : m.Entity → Bool) :
    every_sem m R S =
    (FiniteModel.elements.filter R).all S := by
  simp only [every_sem]; exact all_filter_eq _ R S

/-- `some_sem` Extension at the denotation level.
    `some(R,S) = ∃x∈filter(R). S(x)`. -/
theorem some_sem_extension (R S : m.Entity → Bool) :
    some_sem m R S =
    (FiniteModel.elements.filter R).any S := by
  simp only [some_sem]; exact any_filter_eq _ R S

/-- `no_sem` Extension at the denotation level.
    `no(R,S) = ∀x∈filter(R). ¬S(x)`. -/
theorem no_sem_extension (R S : m.Entity → Bool) :
    no_sem m R S =
    (FiniteModel.elements.filter R).all (λ x => !S x) := by
  simp only [no_sem]; exact all_neg_filter_eq _ R S

/-- `most_sem` Extension at the denotation level.
    `most(R,S) = |filter(R) ∩ S| > |filter(R) \ S|`. -/
theorem most_sem_extension (R S : m.Entity → Bool) :
    most_sem m R S =
    decide (((FiniteModel.elements.filter R).filter S).length >
            ((FiniteModel.elements.filter R).filter (λ x => !S x)).length) := by
  show most_sem m R S = _
  simp only [most_sem, filter_and_eq]
  rfl

-- === Positive/Negative Strong (P&W Ch.6) ===

/-- `every_sem` is positive strong: every(A,A) = true for all A.
    Proof: `!R(x) || R(x) = true` for all x. -/
theorem every_positive_strong : PositiveStrong (every_sem m) := by
  intro R
  simp only [every_sem]
  rw [List.all_eq_true]
  intro x _
  cases R x <;> rfl

-- === K&S Existential det classification (§3.3, G3) ===

/-- `⟦some⟧` is existential (K&S G3): some(A,B) = some(A∩B, everything).
    some is natural in there-sentences: "There are some cats." -/
theorem some_existential : Existential (some_sem m) := by
  intro R S
  simp only [some_sem]
  congr 1; ext x
  cases R x <;> simp

/-- `⟦no⟧` is existential (K&S G3): no(A,B) = no(A∩B, everything).
    no is natural in there-sentences: "There are no cats." -/
theorem no_existential : Existential (no_sem m) := by
  intro R S
  simp only [no_sem]
  congr 1; ext x
  cases R x <;> simp

/-- `⟦every⟧` is NOT existential (K&S §3.3).
    "every" is not natural in there-sentences: *"There is every cat."
    Witness: R=students, S=things. every(R,S)=true but every(R∩S, 1)=true trivially,
    yet every(thing, student)≠every(thing∩student, 1). -/
theorem every_not_existential : ¬Existential (every_sem (m := toyModel)) := by
  intro h
  have := h thing_sem student_sem
  simp only [every_sem, thing_sem, student_sem, FiniteModel.elements] at this
  exact absurd this Bool.noConfusion

/-- `⟦most⟧` is NOT existential (K&S §3.3).
    "most" is not natural in there-sentences: *"There are most cats."
    Witness: R={john,mary}, S={john,pizza}. |R∩S|=1 vs |R\S|=1, so most(R,S)=false.
    But most(R∩S, 1_P): |{john}∩1_P|=1 vs |{john}\1_P|=0, so most(R∩S, 1_P)=true. -/
theorem most_not_existential : ¬Existential (most_sem (m := toyModel)) := by
  intro h
  have := h student_sem (λ x => match x with | .john => true | .pizza => true | _ => false)
  simp only [most_sem, student_sem, FiniteModel.elements] at this
  exact absurd this Bool.noConfusion

/-- Existential ↔ weak (strength metadata): the existential dets are exactly those
    that can appear in there-sentences. Third independent path to weak/strong. -/
theorem some_existential_weak_bridge :
    Existential (some_sem m) ∧
    ¬Existential (every_sem (m := toyModel)) :=
  ⟨some_existential, every_not_existential⟩

-- ============================================================================
-- @cite{van-benthem-1984}: Relational Properties of Concrete Quantifiers
-- ============================================================================

/-- `⟦every⟧` is transitive: A ⊆ B and B ⊆ C implies A ⊆ C. -/
theorem every_transitive : QTransitive (every_sem m) := by
  intro A B C hAB hBC
  simp only [every_sem] at *
  rw [List.all_eq_true] at *
  intro x hx
  specialize hAB x hx; specialize hBC x hx
  cases hA : A x
  · simp
  · simp [hA] at hAB; simp [hAB] at hBC; simp [hBC]

/-- `⟦every⟧` is antisymmetric: A ⊆ B and B ⊆ A implies A = B. -/
theorem every_antisymmetric : QAntisymmetric (every_sem m) := by
  intro A B hAB hBA
  simp only [every_sem] at hAB hBA
  rw [List.all_eq_true] at hAB hBA
  funext x
  specialize hAB x (FiniteModel.complete x)
  specialize hBA x (FiniteModel.complete x)
  cases hA : A x <;> cases hB : B x <;> simp [hA, hB] at hAB hBA ⊢

/-- `⟦some⟧` is quasi-reflexive: A∩B ≠ ∅ implies A∩A ≠ ∅ (i.e., A ≠ ∅). -/
theorem some_quasi_reflexive : QuasiReflexive (some_sem m) := by
  intro A B hQAB
  simp only [some_sem] at *
  rw [List.any_eq_true] at *
  obtain ⟨x, hx, hpred⟩ := hQAB
  exact ⟨x, hx, by cases hA : A x <;> simp_all⟩

/-- `⟦no⟧` is quasi-universal: A∩A = ∅ (i.e., A = ∅) implies A∩B = ∅ for all B. -/
theorem no_quasi_universal : QuasiUniversal (no_sem m) := by
  intro A B hQAA
  simp only [no_sem] at *
  rw [List.all_eq_true] at *
  intro x hx
  have := hQAA x hx
  cases hA : A x <;> simp_all

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
  simp only [some_sem] at *
  rw [List.any_eq_true] at *
  obtain ⟨x, hx, hpred⟩ := hQ
  exact ⟨x, hx, by cases hR : R x <;> simp_all [hRR' x]⟩

/-- `⟦no⟧` is restrictor-↓ (anti-persistent): A ⊆ A' and no(A',B) → no(A,B). -/
theorem no_restrictor_down : RestrictorDownwardMono (no_sem m) := by
  intro R R' S hRR' hQ
  simp only [no_sem] at *
  rw [List.all_eq_true] at *
  intro x hx
  have h := hQ x hx
  cases hR : R x <;> simp_all [hRR' x]

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

/-- `⟦most⟧` has double monotonicity ↑MON↑ (scope-upward, restrictor-upward).
    Note: most is NOT restrictor-downward-monotone (A'⊆A and most(A,B) ↛ most(A',B)).
    Restrictor-upward follows from quasi-reflexivity + scope-upward (Zwarts). -/
theorem most_doubleMono :
    ScopeUpwardMono (most_sem m) :=
  most_scope_up

/-- `⟦every⟧` is filtrating: every(A,B) ∧ every(A,C) → every(A, B∩C). -/
theorem every_filtrating : Filtrating (every_sem m) := by
  intro A B C hAB hAC
  simp only [every_sem] at *
  rw [List.all_eq_true] at *
  intro x hx
  have h1 := hAB x hx
  have h2 := hAC x hx
  cases hA : A x
  · simp
  · simp [hA] at h1 h2; simp [h1, h2]

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
    FiniteModel.elements.any R = false := by
  simp only [every_sem, no_sem]
  intro hA hE
  rw [List.all_eq_true] at hA hE
  rw [Bool.eq_false_iff]
  intro hAny
  rw [List.any_eq_true] at hAny
  obtain ⟨x, hx, hRx⟩ := hAny
  have h1 := hA x hx
  have h2 := hE x hx
  simp [hRx] at h1 h2
  exact absurd h1 (by rw [h2]; exact Bool.noConfusion)

/-- **Subalternation (A → I)**: the A-form entails the I-form when the
    restrictor is non-empty. This is @cite{belnap-1970}'s assertiveness
    condition: ∀x(Cx/Bx) presupposes ∃xCx. @cite{strawson-1952} argued
    "All S are P" presupposes there are Ss — Belnap *derives* this. -/
theorem subalternation_a_i (R S : m.Entity → Bool)
    (hR : FiniteModel.elements.any R = true) :
    every_sem m R S = true → some_sem m R S = true := by
  simp only [every_sem, some_sem]
  intro hA
  rw [List.all_eq_true] at hA
  rw [List.any_eq_true] at hR ⊢
  obtain ⟨x, hx, hRx⟩ := hR
  exact ⟨x, hx, by have := hA x hx; simp [hRx] at this; simp [hRx, this]⟩

/-- **Subalternation (E → O)**: the E-form entails the O-form when the
    restrictor is non-empty. -/
theorem subalternation_e_o (R S : m.Entity → Bool)
    (hR : FiniteModel.elements.any R = true) :
    no_sem m R S = true → outerNeg (every_sem m) R S = true := by
  intro hE
  simp only [outerNeg]
  cases hA : every_sem m R S
  · rfl
  · exact absurd hR (by simp [a_e_contrary R S hA hE])

/-- **Subcontrariety (I ∨ O)**: the I-form and O-form can't both fail
    when the restrictor is non-empty. Either some R is S, or not every
    R is S (or both). -/
theorem subcontrariety_i_o (R S : m.Entity → Bool)
    (hR : FiniteModel.elements.any R = true) :
    some_sem m R S = true ∨ outerNeg (every_sem m) R S = true := by
  cases hS : some_sem m R S
  · right
    simp only [outerNeg]
    cases hA : every_sem m R S
    · rfl
    · have hE : no_sem m R S = true := by rw [no_contradicts_some, hS]; rfl
      exact absurd hR (by simp [a_e_contrary R S hA hE])
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
  simp only [some_sem] at *
  rw [List.any_eq_true] at *
  obtain ⟨x, hx, hpred⟩ := hQ
  refine ⟨x, hx, ?_⟩
  rw [Bool.and_eq_true] at hpred
  have hR'x := hKeep x hpred.1 hpred.2
  simp [hR'x, hpred.2]

/-- `⟦some⟧` is smooth (↓_NE + ↑_SE).
    @cite{peters-westerstahl-2006} §5.6: persistence gives ↑_SE;
    the witness argument gives ↓_NE directly. -/
theorem some_smooth : Smooth (some_sem m) :=
  ⟨some_downNE, restrictorUpMono_to_upSE _ some_restrictor_up⟩

/-- `⟦every⟧` is ↑_SE Mon (direct proof).
    Adding B-elements to A preserves ∀x.R(x)→S(x) since the new elements satisfy S. -/
theorem every_upSE_direct : UpSEMon (every_sem m) := by
  intro R S R' hSub hDiff hQ
  simp only [every_sem] at *
  rw [List.all_eq_true] at *
  intro x hx
  cases hR'x : R' x
  · simp
  · cases hSx : S x
    · have hRx : R x = true := hDiff x hR'x hSx
      have := hQ x hx; simp [hRx] at this
      exact absurd hSx (by simp [this])
    · simp

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
  simp only [most_sem, decide_eq_true_eq] at *
  have hEq : FiniteModel.elements.filter (fun x => R' x && S x) =
      FiniteModel.elements.filter (fun x => R x && S x) :=
    List.filter_congr (fun x _ => by
      cases hS : S x <;> simp only [hS, Bool.and_false, Bool.and_true]
      cases hR'x : R' x
      · cases hRx : R x
        · rfl
        · exact absurd (hKeep x hRx hS) (by simp [hR'x])
      · exact (hSub x hR'x).symm)
  have hLe : (FiniteModel.elements.filter (fun x => R' x && !S x)).length ≤
      (FiniteModel.elements.filter (fun x => R x && !S x)).length :=
    (filter_sublist_of_imp (fun x _ h => by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h ⊢; exact ⟨hSub x h.1, h.2⟩)).length_le
  rw [hEq]; omega

/-- `⟦most⟧` is ↑_SE Mon (direct proof).
    Adding S-elements to A preserves |A∩S| > |A\S| since |A∩S| grows
    while |A\S| stays the same. -/
theorem most_upSE : UpSEMon (most_sem m) := by
  intro R S R' hSub hDiff hQ
  simp only [most_sem, decide_eq_true_eq] at *
  have hEq : FiniteModel.elements.filter (fun x => R' x && !S x) =
      FiniteModel.elements.filter (fun x => R x && !S x) :=
    List.filter_congr (fun x _ => by
      cases hS : S x <;> simp only [hS, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true]
      cases hR'x : R' x
      · cases hRx : R x
        · rfl
        · exact absurd (hSub x hRx) (by simp [hR'x])
      · exact (hDiff x hR'x hS).symm)
  have hLe : (FiniteModel.elements.filter (fun x => R x && S x)).length ≤
      (FiniteModel.elements.filter (fun x => R' x && S x)).length :=
    (filter_sublist_of_imp (fun x _ h => by
      simp only [Bool.and_eq_true] at h ⊢; exact ⟨hSub x h.1, h.2⟩)).length_le
  rw [hEq]; omega

/-- `⟦most⟧` is smooth. This is a key empirical fact: most natural language
    Mon↑ determiners are smooth (@cite{peters-westerstahl-2006} §5.6, (5.28)). -/
theorem most_smooth : Smooth (most_sem m) :=
  ⟨most_downNE, most_upSE⟩

-- === Counting quantifier smoothness ===

/-- `⟦at least n⟧` is persistent (Mon↑ in restrictor), hence ↑_SE and ↑_SW. -/
theorem at_least_n_restrictor_up (n : Nat) : RestrictorUpwardMono (at_least_n_sem m n) := by
  intro R R' S hRR' h
  simp only [at_least_n_sem, decide_eq_true_eq] at *
  exact le_trans h ((filter_sublist_of_imp (fun x _ hx => by
    simp only [Bool.and_eq_true] at hx ⊢; exact ⟨hRR' x hx.1, hx.2⟩)).length_le)

/-- `⟦at least n⟧` is ↓_NE Mon: removing non-S elements from A preserves
    |A ∩ S| ≥ n since the S-witnesses are retained. -/
theorem at_least_n_downNE (n : Nat) : DownNEMon (at_least_n_sem m n) := by
  intro R S R' hSub hKeep hQ
  simp only [at_least_n_sem, decide_eq_true_eq] at hQ
  simp only [at_least_n_sem, decide_eq_true_eq]
  have hEq : FiniteModel.elements.filter (fun x => R' x && S x) =
      FiniteModel.elements.filter (fun x => R x && S x) :=
    List.filter_congr (fun x _ => by
      cases hS : S x <;> simp only [Bool.and_false, Bool.and_true]
      cases hR'x : R' x
      · cases hRx : R x
        · rfl
        · exact absurd (hKeep x hRx hS) (by simp [hR'x])
      · exact (hSub x hR'x).symm)
  exact hEq ▸ hQ

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

-- === Smoothness implies scope monotonicity (Prop 9 verification) ===

/-- Smooth + CONSERV → Mon↑ applied to `⟦some⟧`: an alternative derivation
    of scope-upward-monotonicity from smoothness. -/
theorem some_scope_up_from_smooth : ScopeUpwardMono (some_sem m) :=
  smooth_conservative_scopeUpMono _ some_conservative some_smooth

/-- Smooth + CONSERV → Mon↑ applied to `⟦every⟧`. -/
theorem every_scope_up_from_smooth : ScopeUpwardMono (every_sem m) :=
  smooth_conservative_scopeUpMono _ every_conservative every_smooth

/-- Smooth + CONSERV → Mon↑ applied to `⟦at least n⟧`. -/
theorem at_least_n_scope_up_from_smooth (n : Nat) : ScopeUpwardMono (at_least_n_sem m n) :=
  smooth_conservative_scopeUpMono _ (at_least_n_conservative n) (at_least_n_smooth n)

end FiniteModelProofs

end Semantics.Lexical.Determiner.Quantifier
