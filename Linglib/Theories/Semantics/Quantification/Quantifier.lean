import Linglib.Core.IntensionalLogic.Frame
import Linglib.Fragments.ToyDomain
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
  `ScopeDownwardMono`, `outerNeg`, `innerNeg`, `dualQ`, etc. (model-agnostic, Bool-valued)
- **Prop-valued GQ properties**: Defined locally in this file for Prop-valued denotations
  (`PConservative`, `PScopeUpwardMono`, etc.)
- **Concrete denotations**: `every_sem`, `some_sem`, etc. — Prop-valued, matching
  `Denot .t = Prop`
- **Counting quantifiers**: `most_sem`, `few_sem`, etc. — use `Finset.univ.filter`
  for cardinality comparisons

-/

namespace Semantics.Quantification.Quantifier

open Core.IntensionalLogic
open Semantics.Montague (toyModel ToyEntity)
open Core.Quantification

def Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

-- ============================================================================
-- Prop-valued GQ property definitions
-- ============================================================================

/-- Prop-valued generalized quantifier denotation. -/
abbrev PropGQ (α : Type*) := (α → Prop) → (α → Prop) → Prop

/-- Prop-valued conservativity: `Q(A, B) ↔ Q(A, A ∩ B)`. -/
def PConservative {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S : α → Prop), q R S ↔ q R (fun x => R x ∧ S x)

/-- Prop-valued scope-upward-monotone. -/
def PScopeUpwardMono {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S S' : α → Prop),
    (∀ x, S x → S' x) → q R S → q R S'

/-- Prop-valued scope-downward-monotone. -/
def PScopeDownwardMono {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S S' : α → Prop),
    (∀ x, S x → S' x) → q R S' → q R S

/-- Prop-valued symmetric. -/
def PQSymmetric {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S : α → Prop), q R S ↔ q S R

/-- Prop-valued intersection condition. -/
def PIntersectionCondition {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S R' S' : α → Prop),
    (∀ x, (R x ∧ S x) ↔ (R' x ∧ S' x)) →
    (q R S ↔ q R' S')

/-- Prop-valued restrictor-upward-monotone (persistent). -/
def PRestrictorUpwardMono {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R R' S : α → Prop),
    (∀ x, R x → R' x) → q R S → q R' S

/-- Prop-valued restrictor-downward-monotone (anti-persistent). -/
def PRestrictorDownwardMono {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R R' S : α → Prop),
    (∀ x, R x → R' x) → q R' S → q R S

/-- Prop-valued positive strong: Q(A,A) for all A. -/
def PPositiveStrong {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R : α → Prop), q R R

/-- Prop-valued existential. -/
def PExistential {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S : α → Prop), q R S ↔ q (fun x => R x ∧ S x) (fun _ => True)

/-- Prop-valued left anti-additive. -/
def PLeftAntiAdditive {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R R' S : α → Prop),
    q (fun x => R x ∨ R' x) S ↔ (q R S ∧ q R' S)

/-- Prop-valued right anti-additive. -/
def PRightAntiAdditive {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S S' : α → Prop),
    q R (fun x => S x ∨ S' x) ↔ (q R S ∧ q R S')

/-- Prop-valued transitive. -/
def PQTransitive {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (A B C : α → Prop), q A B → q B C → q A C

/-- Prop-valued antisymmetric. -/
def PQAntisymmetric {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (A B : α → Prop), q A B → q B A → A = B

/-- Prop-valued quasi-reflexive. -/
def PQuasiReflexive {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (A B : α → Prop), q A B → q A A

/-- Prop-valued quasi-universal. -/
def PQuasiUniversal {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (A B : α → Prop), q A A → q A B

/-- Prop-valued filtrating. -/
def PFiltrating {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (A B C : α → Prop),
    q A B → q A C → q A (fun x => B x ∧ C x)

/-- Prop-valued outer negation. -/
def pouterNeg {α : Type*} (q : PropGQ α) : PropGQ α :=
  fun R S => ¬q R S

/-- Prop-valued inner negation. -/
def pinnerNeg {α : Type*} (q : PropGQ α) : PropGQ α :=
  fun R S => q R (fun x => ¬S x)

/-- Prop-valued dual. -/
def pdualQ {α : Type*} (q : PropGQ α) : PropGQ α :=
  pouterNeg (pinnerNeg q)

/-- Prop-valued meet. -/
def pgqMeet {α : Type*} (f g : PropGQ α) : PropGQ α :=
  fun R S => f R S ∧ g R S

/-- Prop-valued ↑_SE Mon. -/
def PUpSEMon {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R x → R' x) →
    (∀ x, R' x → ¬S x → R x) →
    q R S → q R' S

/-- Prop-valued ↑_SW Mon. -/
def PUpSWMon {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R x → R' x) →
    (∀ x, R' x → S x → R x) →
    q R S → q R' S

/-- Prop-valued ↓_NW Mon. -/
def PDownNWMon {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R' x → R x) →
    (∀ x, R x → ¬S x → R' x) →
    q R S → q R' S

/-- Prop-valued ↓_NE Mon. -/
def PDownNEMon {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R' x → R x) →
    (∀ x, R x → S x → R' x) →
    q R S → q R' S

/-- Prop-valued smooth. -/
def PSmooth {α : Type*} (q : PropGQ α) : Prop := PDownNEMon q ∧ PUpSEMon q

/-- Prop-valued co-smooth. -/
def PCoSmooth {α : Type*} (q : PropGQ α) : Prop := PDownNWMon q ∧ PUpSWMon q

/-- Prop-valued quantity invariant. -/
def PQuantityInvariant {α : Type*} (q : PropGQ α) : Prop :=
  ∀ (A B A' B' : α → Prop) (f : α → α),
    Function.Bijective f →
    (∀ x, A (f x) ↔ A' x) → (∀ x, B (f x) ↔ B' x) →
    (q A B ↔ q A' B')

/-- Prop-valued satisfies-universals. -/
def PSatisfiesUniversals {α : Type*} (q : PropGQ α) : Prop :=
  PConservative q ∧ (PScopeUpwardMono q ∨ PScopeDownwardMono q)

-- ============================================================================
-- Bridge lemmas: pouterNeg monotonicity flips
-- ============================================================================

theorem pouterNeg_up_to_down {α : Type*} (q : PropGQ α)
    (h : PScopeUpwardMono q) : PScopeDownwardMono (pouterNeg q) := by
  intro R S S' hSS' hNot hQ
  exact hNot (h R S S' hSS' hQ)

theorem pouterNeg_restrictorDown_to_up {α : Type*} (q : PropGQ α)
    (h : PRestrictorDownwardMono q) : PRestrictorUpwardMono (pouterNeg q) := by
  intro R R' S hRR' hNot hQ
  exact hNot (h R R' S hRR' hQ)

theorem pouterNeg_restrictorUp_to_down {α : Type*} (q : PropGQ α)
    (h : PRestrictorUpwardMono q) : PRestrictorDownwardMono (pouterNeg q) := by
  intro R R' S hRR' hNot hQ
  exact hNot (h R R' S hRR' hQ)

-- ============================================================================
-- Bridge: Zwarts-style for Prop-valued GQs
-- ============================================================================

/-- Reflexive + transitive + conservative → restrictor-↓. -/
theorem pzwarts_refl_trans_restrictorDown {α : Type*} (q : PropGQ α)
    (hCons : PConservative q) (hRefl : PPositiveStrong q) (hTrans : PQTransitive q) :
    PRestrictorDownwardMono q := by
  intro R R' S hRR' hQ
  have hRR'Q : q R R' := by
    rw [hCons R R']
    have : (fun x => R x ∧ R' x) = R := by
      funext x; exact propext ⟨And.left, fun h => ⟨h, hRR' x h⟩⟩
    rw [this]; exact hRefl R
  exact hTrans R R' S hRR'Q hQ

-- ============================================================================
-- Smooth/co-smooth bridge lemmas
-- ============================================================================

theorem pRestrictorUpMono_to_upSE {α : Type*} (q : PropGQ α)
    (h : PRestrictorUpwardMono q) : PUpSEMon q := by
  intro R S R' hSub _ hQ; exact h R R' S hSub hQ

theorem pRestrictorUpMono_to_upSW {α : Type*} (q : PropGQ α)
    (h : PRestrictorUpwardMono q) : PUpSWMon q := by
  intro R S R' hSub _ hQ; exact h R R' S hSub hQ

theorem pRestrictorDownMono_to_downNW {α : Type*} (q : PropGQ α)
    (h : PRestrictorDownwardMono q) : PDownNWMon q := by
  intro R S R' hSub _ hQ; exact h R' R S hSub hQ

theorem pRestrictorDownMono_to_downNE {α : Type*} (q : PropGQ α)
    (h : PRestrictorDownwardMono q) : PDownNEMon q := by
  intro R S R' hSub _ hQ; exact h R' R S hSub hQ

theorem pSmooth_iff_outerNeg_coSmooth {α : Type*} (q : PropGQ α)
    (hSmooth : PSmooth q) : PCoSmooth (pouterNeg q) := by
  constructor
  · -- PDownNWMon (pouterNeg q): R'⊆R, R\S⊆R', ¬qRS → ¬qR'S
    -- Contrapositive uses PUpSEMon: R'⊆R, R\S⊆R' → qR'S → qRS
    intro R S R' hSub hKeep hNQ hQ
    exact hNQ (hSmooth.2 R' S R hSub hKeep hQ)
  · -- PUpSWMon (pouterNeg q): R⊆R', R'∩S⊆R, ¬qRS → ¬qR'S
    -- Contrapositive uses PDownNEMon: R⊆R', R'∩S⊆R → qR'S → qRS
    intro R S R' hSub hKeep hNQ hQ
    exact hNQ (hSmooth.1 R' S R hSub hKeep hQ)

/-- Decidability of implication (not in Lean 4 core). -/
instance decImpl {p q : Prop} [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then
    if hq : q then .isTrue (fun _ => hq)
    else .isFalse (fun h => hq (h hp))
  else .isTrue (fun h => absurd h hp)


/-- Count of elements satisfying a predicate, via `Finset.univ.filter`. -/
def count {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] : Nat :=
  (Finset.univ.filter P).card

-- ============================================================================
-- Denotations
-- ============================================================================

def every_sem (F : Frame) [Fintype F.Entity] : F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    ∀ x : F.Entity, R x → S x

def some_sem (F : Frame) [Fintype F.Entity] : F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    ∃ x : F.Entity, R x ∧ S x

/-- Partee's `A` (existential closure) = Barwise & Cooper's `⟦some⟧`.
    Both compute `λR.λS. ∃x. R(x) ∧ S(x)` over a finite domain.
    `A` takes the domain explicitly; `some_sem` uses `∃` over the entity type. -/
theorem A_eq_some_sem (F : Frame) [Fintype F.Entity] (domain : List F.Entity)
    (hComplete : ∀ x : F.Entity, x ∈ domain) :
    Semantics.Composition.TypeShifting.A domain = some_sem F := by
  funext R S
  simp only [Semantics.Composition.TypeShifting.A, some_sem]
  exact propext ⟨fun ⟨x, _, hR, hS⟩ => ⟨x, hR, hS⟩,
                 fun ⟨x, hR, hS⟩ => ⟨x, hComplete x, hR, hS⟩⟩

def no_sem (F : Frame) [Fintype F.Entity] : F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    ∀ x : F.Entity, R x → ¬S x

open Classical in
/-- `⟦most⟧(R)(S) = |R ∩ S| > |R \ S|` -/
noncomputable def most_sem (F : Frame) [Fintype F.Entity] : F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    count (fun x : F.Entity => R x ∧ S x) >
    count (fun x : F.Entity => R x ∧ ¬S x)

open Classical in
/-- `⟦few⟧(R)(S) = |R ∩ S| < |R \ S|` — a minority of Rs are Ss.
    Dual of `most_sem`: few(R,S) ↔ ¬most(R,S) ∧ ¬half(R,S). -/
noncomputable def few_sem (F : Frame) [Fintype F.Entity] : F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    count (fun x : F.Entity => R x ∧ S x) <
    count (fun x : F.Entity => R x ∧ ¬S x)

open Classical in
/-- `⟦half⟧(R)(S) = 2 * |R ∩ S| = |R|` — exactly half of Rs are Ss. -/
noncomputable def half_sem (F : Frame) [Fintype F.Entity] : F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    2 * count (fun x : F.Entity => R x ∧ S x) =
    count (fun x : F.Entity => R x)

open Classical in
/-- `⟦at least n⟧(R)(S) = |R ∩ S| ≥ n` -/
noncomputable def at_least_n_sem (F : Frame) [Fintype F.Entity] (n : Nat) :
    F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    count (fun x : F.Entity => R x ∧ S x) ≥ n

open Classical in
/-- `⟦at most n⟧(R)(S) = |R ∩ S| ≤ n` -/
noncomputable def at_most_n_sem (F : Frame) [Fintype F.Entity] (n : Nat) :
    F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    count (fun x : F.Entity => R x ∧ S x) ≤ n

open Classical in
/-- `⟦exactly n⟧(R)(S) = |R ∩ S| = n` -/
noncomputable def exactly_n_sem (F : Frame) [Fintype F.Entity] (n : Nat) :
    F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    count (fun x : F.Entity => R x ∧ S x) = n

open Classical in
/-- `⟦all but n⟧(R)(S) = |R \ S| = n` — exactly n R-elements are non-S.
    Generalizes "every" (= all but 0). The exceptive counterpart of
    `exactly_n_sem` (which counts |R ∩ S| = n). -/
noncomputable def all_but_n_sem (F : Frame) [Fintype F.Entity] (n : Nat) :
    F.Denot Ty.det :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    count (fun x : F.Entity => R x ∧ ¬S x) = n

/-- `⟦between n and k⟧(R)(S) = n ≤ |R ∩ S| ≤ k` -/
noncomputable def between_n_m_sem (F : Frame) [Fintype F.Entity] (n k : Nat) :
    F.Denot Ty.det :=
  pgqMeet (at_least_n_sem F n) (at_most_n_sem F k)

instance : Fintype ToyEntity where
  elems := {.john, .mary, .pizza, .book}
  complete := fun x => by cases x <;> simp

/-- Bridge: `toyModel.Entity = ToyEntity` is definitional but opaque to instance search. -/
instance : Fintype toyModel.Entity :=
  show Fintype ToyEntity by infer_instance

section ToyLexicon

def student_sem : toyModel.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def person_sem : toyModel.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def thing_sem : toyModel.Denot (.e ⇒ .t) :=
  λ _ => True

instance : DecidablePred student_sem :=
  fun x => match x with | .john | .mary => .isTrue (by simp [student_sem])
                        | .pizza | .book => .isFalse (by simp [student_sem])

instance : DecidablePred person_sem :=
  fun x => match x with | .john | .mary => .isTrue (by simp [person_sem])
                        | .pizza | .book => .isFalse (by simp [person_sem])

instance : DecidablePred thing_sem := fun _ => .isTrue trivial

end ToyLexicon

section Examples

open Semantics.Montague.ToyLexicon

/-- Not every student sleeps (john sleeps but mary doesn't). -/
theorem not_everyStudentSleeps : ¬every_sem toyModel student_sem sleeps_sem := by
  intro h
  have := h ToyEntity.mary (by simp [student_sem])
  simp [sleeps_sem] at this

/-- Some student sleeps (john does). -/
theorem someStudentSleeps : some_sem toyModel student_sem sleeps_sem :=
  ⟨ToyEntity.john, by simp [student_sem], by simp [sleeps_sem]⟩

/-- Not no student sleeps (john does). -/
theorem not_noStudentSleeps : ¬no_sem toyModel student_sem sleeps_sem := by
  intro h
  have := h ToyEntity.john (by simp [student_sem])
  simp [sleeps_sem] at this

/-- Every student laughs (john and mary both laugh). -/
theorem everyStudentLaughs : every_sem toyModel student_sem laughs_sem := by
  intro x hR
  match x with
  | .john => simp [laughs_sem]
  | .mary => simp [laughs_sem]
  | .pizza => simp [student_sem] at hR
  | .book => simp [student_sem] at hR

/-- Some student laughs. -/
theorem someStudentLaughs : some_sem toyModel student_sem laughs_sem :=
  ⟨ToyEntity.john, by simp [student_sem], by simp [laughs_sem]⟩

/-- Not every person sleeps. -/
theorem not_everyPersonSleeps : ¬every_sem toyModel person_sem sleeps_sem := by
  intro h; have := h ToyEntity.mary (by simp [person_sem]); simp [sleeps_sem] at this

/-- Some person sleeps. -/
theorem somePersonSleeps : some_sem toyModel person_sem sleeps_sem :=
  ⟨ToyEntity.john, by simp [person_sem], by simp [sleeps_sem]⟩

end Examples

-- ============================================================================
-- Fintype Model Proofs (require Fintype for decidable quantification)
-- ============================================================================

section FintypeProofs

open Classical Semantics.Montague.ToyLexicon

variable {F : Frame} [Fintype F.Entity]

-- === Bijection invariance (for QuantityInvariant) ===

/-- `∀ x, P x` is invariant under bijective substitution. -/
theorem forall_bij_inv (f : F.Entity → F.Entity) (hBij : Function.Bijective f)
    (P : F.Entity → Prop) :
    (∀ x, P x) ↔ (∀ x, P (f x)) := by
  constructor
  · intro h x; exact h (f x)
  · intro h x; obtain ⟨y, rfl⟩ := hBij.surjective x; exact h y

/-- `∃ x, P x` is invariant under bijective substitution. -/
theorem exists_bij_inv (f : F.Entity → F.Entity) (hBij : Function.Bijective f)
    (P : F.Entity → Prop) :
    (∃ x, P x) ↔ (∃ x, P (f x)) := by
  constructor
  · intro ⟨x, hx⟩; obtain ⟨y, rfl⟩ := hBij.surjective x; exact ⟨y, hx⟩
  · intro ⟨y, hy⟩; exact ⟨f y, hy⟩

/-- `count P = count (P ∘ f)` when f is a bijection. -/
theorem count_bij_inv (f : F.Entity → F.Entity) (hBij : Function.Bijective f)
    {P : F.Entity → Prop} [DecidablePred P] :
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
theorem every_conservative : PConservative (every_sem F) := by
  intro R S; simp only [every_sem]
  exact ⟨fun h x hR => ⟨hR, h x hR⟩, fun h x hR => (h x hR).2⟩

/-- `⟦some⟧` is conservative: `∃x. R(x) ∧ S(x)` iff `∃x. R(x) ∧ (R(x) ∧ S(x))`. -/
theorem some_conservative : PConservative (some_sem F) := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, hR, hR, hS⟩, fun ⟨x, hR, _, hS⟩ => ⟨x, hR, hS⟩⟩

/-- `⟦no⟧` is conservative: `∀x. R(x) → ¬S(x)` iff `∀x. R(x) → ¬(R(x) ∧ S(x))`. -/
theorem no_conservative : PConservative (no_sem F) := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x hR ⟨_, hS⟩ => h x hR hS, fun h x hR hS => h x hR ⟨hR, hS⟩⟩

private theorem count_congr_iff {P Q : F.Entity → Prop}
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x ↔ Q x) : count P = count Q := by
  unfold count; congr 1; ext x
  constructor
  · intro hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, (h x).mp hx.2⟩
  · intro hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, (h x).mpr hx.2⟩

/-- Instance-polymorphic: `count(R∧S) = count(R∧(R∧S))` for any `DecidablePred` instances.
    Universally quantifying over instances avoids the decidability diamond that arises
    when counting quantifier definitions and proofs elaborate in different scopes. -/
private theorem count_and_idem_any (R S : F.Entity → Prop)
    (inst1 : DecidablePred (fun x : F.Entity => R x ∧ S x))
    (inst2 : DecidablePred (fun x : F.Entity => R x ∧ (R x ∧ S x))) :
    @count _ _ _ inst1 = @count _ _ _ inst2 := by
  unfold count; congr 1; ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨hR, hS⟩ => ⟨hR, hR, hS⟩, fun ⟨hR, _, hS⟩ => ⟨hR, hS⟩⟩

/-- Instance-polymorphic: `count(R∧¬S) = count(R∧¬(R∧S))` for any `DecidablePred` instances. -/
private theorem count_neg_idem_any (R S : F.Entity → Prop)
    (inst1 : DecidablePred (fun x : F.Entity => R x ∧ ¬S x))
    (inst2 : DecidablePred (fun x : F.Entity => R x ∧ ¬(R x ∧ S x))) :
    @count _ _ _ inst1 = @count _ _ _ inst2 := by
  unfold count; congr 1; ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨hR, hNS⟩ => ⟨hR, fun ⟨_, hS⟩ => hNS hS⟩,
         fun ⟨hR, hN⟩ => ⟨hR, fun hS => hN ⟨hR, hS⟩⟩⟩

/-- `⟦most⟧` is conservative: the R-elements in S are the R-elements in R∩S. -/
theorem most_conservative : PConservative (most_sem F) := by
  intro R S; simp only [most_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _, ← count_neg_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _, count_neg_idem_any R S _ _]; exact h

/-- `⟦few⟧` is conservative: the R-elements in S are the R-elements in R∩S. -/
theorem few_conservative : PConservative (few_sem F) := by
  intro R S; simp only [few_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _, ← count_neg_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _, count_neg_idem_any R S _ _]; exact h

/-- `⟦half⟧` is conservative: depends only on R ∩ S within R. -/
theorem half_conservative : PConservative (half_sem F) := by
  intro R S; simp only [half_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _]; exact h

/-- `⟦at least n⟧` is conservative: |R ∩ S| = |R ∩ (R ∩ S)|. -/
theorem at_least_n_conservative (n : Nat) : PConservative (at_least_n_sem F n) := by
  intro R S; simp only [at_least_n_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _]; exact h

/-- `⟦at most n⟧` is conservative. -/
theorem at_most_n_conservative (n : Nat) : PConservative (at_most_n_sem F n) := by
  intro R S; simp only [at_most_n_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _]; exact h

/-- `⟦exactly n⟧` is conservative. -/
theorem exactly_n_conservative (n : Nat) : PConservative (exactly_n_sem F n) := by
  intro R S; simp only [exactly_n_sem]
  constructor <;> intro h
  · rw [← count_and_idem_any R S _ _]; exact h
  · rw [count_and_idem_any R S _ _]; exact h

-- === Scope monotonicity proofs ===

/-- `⟦every⟧` is upward monotone in scope. -/
theorem every_scope_up : PScopeUpwardMono (every_sem F) := by
  intro R S S' hSS' h x hR; exact hSS' x (h x hR)

/-- `⟦some⟧` is upward monotone in scope. -/
theorem some_scope_up : PScopeUpwardMono (some_sem F) := by
  intro R S S' hSS' ⟨x, hR, hS⟩; exact ⟨x, hR, hSS' x hS⟩

/-- `⟦no⟧` is downward monotone in scope. -/
theorem no_scope_down : PScopeDownwardMono (no_sem F) := by
  intro R S S' hSS' h x hR hS; exact h x hR (hSS' x hS)

/-- Finset.filter monotonicity: if P implies Q pointwise, then |filter P| ≤ |filter Q|. -/
private theorem count_le_of_imp {P Q : F.Entity → Prop}
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x → Q x) :
    count P ≤ count Q := by
  apply Finset.card_le_card
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

/-- `⟦few⟧` is downward monotone in scope: if S ⊆ S' and few(R,S'),
    then few(R,S). Fewer Ss among Rs means even fewer S-subsets. -/
theorem few_scope_down : PScopeDownwardMono (few_sem F) := by
  intro R S S' hSS' h
  simp only [few_sem] at *
  have h1 : count (fun x : F.Entity => R x ∧ S x) ≤
      count (fun x : F.Entity => R x ∧ S' x) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩
  have h2 : count (fun x : F.Entity => R x ∧ ¬S' x) ≤
      count (fun x : F.Entity => R x ∧ ¬S x) :=
    count_le_of_imp fun x ⟨hR, hNS'⟩ => ⟨hR, fun hS => hNS' (hSS' x hS)⟩
  omega

/-- `⟦most⟧` is upward monotone in scope: if S ⊆ S' and most(R,S),
    then most(R,S'). |R∩S'| ≥ |R∩S| > |R\S| ≥ |R\S'|. -/
theorem most_scope_up : PScopeUpwardMono (most_sem F) := by
  intro R S S' hSS' h
  simp only [most_sem] at *
  have h1 : count (fun x : F.Entity => R x ∧ S x) ≤
      count (fun x : F.Entity => R x ∧ S' x) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩
  have h2 : count (fun x : F.Entity => R x ∧ ¬S' x) ≤
      count (fun x : F.Entity => R x ∧ ¬S x) :=
    count_le_of_imp fun x ⟨hR, hNS'⟩ => ⟨hR, fun hS => hNS' (hSS' x hS)⟩
  omega

-- === Counting quantifier identities (@cite{peters-westerstahl-2006} §4.3) ===

/-- `⟦some⟧ = ⟦at least 1⟧`: existential quantification is "at least one". -/
theorem some_eq_at_least_1 :
    (some_sem F : PropGQ F.Entity) = (at_least_n_sem F 1 : PropGQ F.Entity) := by
  funext R S
  simp only [some_sem, at_least_n_sem]
  exact propext ⟨
    fun ⟨x, hR, hS⟩ => by
      simp only [count]
      exact Nat.one_le_iff_ne_zero.mpr (Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hR, hS⟩⟩).ne',
    fun h => by
      simp only [count] at h
      have hpos : 0 < (Finset.univ.filter (fun x : F.Entity => R x ∧ S x)).card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨x, hx.1, hx.2⟩⟩

/-- `outerNeg ⟦some⟧ = ⟦no⟧`: negating existence gives universal negation. -/
theorem pouterNeg_some_eq_no :
    (pouterNeg (some_sem F) : PropGQ F.Entity) = (no_sem F : PropGQ F.Entity) := by
  funext R S; simp only [pouterNeg, some_sem, no_sem]
  exact propext ⟨
    fun h x hR hS => h ⟨x, hR, hS⟩,
    fun h ⟨x, hR, hS⟩ => h x hR hS⟩

/-- `⟦at most n⟧ = outerNeg ⟦at least n+1⟧`: duality of lower and upper bounds.
    This is the counting quantifier instance of the Square of Opposition. -/
theorem at_most_eq_pouterNeg_at_least_succ (n : Nat) :
    (at_most_n_sem F n : PropGQ F.Entity) =
    (pouterNeg (at_least_n_sem F (n + 1)) : PropGQ F.Entity) := by
  funext R S; simp only [at_most_n_sem, at_least_n_sem, pouterNeg]
  exact propext ⟨fun h hGe => by omega, fun h => by omega⟩

/-- `⟦no⟧ = ⟦at most 0⟧`. Derived algebraically:
    no = outerNeg(some) = outerNeg(at_least 1) = at_most 0. -/
theorem no_eq_at_most_0 :
    (no_sem F : PropGQ F.Entity) = (at_most_n_sem F 0 : PropGQ F.Entity) := by
  rw [← pouterNeg_some_eq_no, some_eq_at_least_1, at_most_eq_pouterNeg_at_least_succ]

/-- `⟦exactly n⟧ = ⟦at least n⟧ ⊓ ⟦at most n⟧` in the GQ lattice.
    "Exactly n" is the meet of a lower bound and an upper bound. -/
theorem exactly_eq_meet_at_least_at_most (n : Nat) :
    (exactly_n_sem F n : PropGQ F.Entity) =
    (pgqMeet (at_least_n_sem F n) (at_most_n_sem F n) : PropGQ F.Entity) := by
  funext R S; simp only [exactly_n_sem, at_least_n_sem, at_most_n_sem, pgqMeet]
  exact propext ⟨fun h => ⟨by omega, by omega⟩, fun ⟨h1, h2⟩ => by omega⟩

/-- `⟦at least n⟧` is Mon↑ in scope: enlarging B cannot decrease |A ∩ B|. -/
theorem at_least_n_scope_up (n : Nat) : PScopeUpwardMono (at_least_n_sem F n) := by
  intro R S S' hSS' h
  simp only [at_least_n_sem] at *
  exact le_trans h (count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hR, hSS' x hS⟩)

/-- `⟦at most n⟧` is Mon↓ in scope. Derived from duality:
    outerNeg flips Mon↑ to Mon↓, and `at_most = outerNeg(at_least)`. -/
theorem at_most_n_scope_down (n : Nat) : PScopeDownwardMono (at_most_n_sem F n) := by
  rw [at_most_eq_pouterNeg_at_least_succ]
  exact pouterNeg_up_to_down _ (at_least_n_scope_up _)

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
def Quantity (q : PropGQ F.Entity) : Prop :=
  ∀ (R₁ S₁ R₂ S₂ : F.Entity → Prop),
    count (fun x => R₁ x ∧ S₁ x) =
    count (fun x => R₂ x ∧ S₂ x) →
    count (fun x => R₁ x ∧ ¬S₁ x) =
    count (fun x => R₂ x ∧ ¬S₂ x) →
    count (fun x => ¬R₁ x ∧ S₁ x) =
    count (fun x => ¬R₂ x ∧ S₂ x) →
    count (fun x => ¬R₁ x ∧ ¬S₁ x) =
    count (fun x => ¬R₂ x ∧ ¬S₂ x) →
    (q R₁ S₁ ↔ q R₂ S₂)

/-- `Quantity → QuantityInvariant`: cardinality-dependence implies bijection-invariance.
    TODO: proof requires adapting cell-bijection machinery to Prop predicates. -/
theorem quantityInvariant_of_quantity (q : PropGQ F.Entity) (hQ : Quantity q) :
    PQuantityInvariant q := by
  sorry

variable [DecidableEq F.Entity]

/-- `QuantityInvariant → Quantity`: bijection-invariance implies cardinality-dependence.
    TODO: proof requires adapting cell-bijection machinery to Prop predicates. -/
theorem quantity_of_quantityInvariant (q : PropGQ F.Entity)
    (hQ : PQuantityInvariant q) :
    Quantity q := by
  sorry

-- === Non-conservative counterexample ===

/-- A non-conservative quantifier for contrast: `⟦M⟧(A,B) = |A| > |B|`
(van de Pol et al.'s hypothetical counterpart to "most"). -/
noncomputable def m_sem (F : Frame) [Fintype F.Entity] : PropGQ F.Entity :=
  fun (R : F.Entity → Prop) (S : F.Entity → Prop) =>
    count (fun x : F.Entity => R x) > count (fun x : F.Entity => S x)

/-- M is not conservative: it inspects B outside A. -/
theorem m_not_conservative : ¬PConservative (m_sem (F := toyModel)) := by
  intro h
  have := (h student_sem (fun x => match x with | .john => True | .pizza => True | _ => False)).mp
  simp only [m_sem, student_sem, count] at this
  -- student_sem has 2 elements, the scope predicate also has 2, so ¬(2 > 2)
  -- but student_sem ∧ scope has 1 element, so 2 > 1
  sorry

-- === Symmetry proofs (P&W Ch.6) ===

/-- `⟦some⟧` is symmetric: ∃x.R(x)∧S(x) = ∃x.S(x)∧R(x). -/
theorem some_symmetric : PQSymmetric (some_sem F) := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, hS, hR⟩, fun ⟨x, hS, hR⟩ => ⟨x, hR, hS⟩⟩

/-- `⟦no⟧` is symmetric: ¬∃x.R(x)∧S(x) = ¬∃x.S(x)∧R(x). -/
theorem no_symmetric : PQSymmetric (no_sem F) := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x hS hR => h x hR hS, fun h x hR hS => h x hS hR⟩

/-- `⟦every⟧` is NOT symmetric. Witness: R=students, S=things (everything).
    every(students)(things)=true but every(things)(students)=false. -/
theorem every_not_symmetric : ¬PQSymmetric (every_sem (F := toyModel)) := by
  intro h
  have := (h student_sem thing_sem).mp (fun x _ => trivial)
  exact absurd (this ToyEntity.pizza trivial) (by simp [student_sem])

-- === Intersectivity via CONSERV+SYMM bridge ===

/-- `⟦some⟧` is intersective (follows from CONSERV + SYMM). -/
theorem some_intersective : PIntersectionCondition (some_sem F) := by
  intro R S R' S' hInt
  simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => let ⟨hR', hS'⟩ := (hInt x).mp ⟨hR, hS⟩; ⟨x, hR', hS'⟩,
         fun ⟨x, hR', hS'⟩ => let ⟨hR, hS⟩ := (hInt x).mpr ⟨hR', hS'⟩; ⟨x, hR, hS⟩⟩

/-- `⟦no⟧` is intersective. -/
theorem no_intersective : PIntersectionCondition (no_sem F) := by
  intro R S R' S' hInt
  simp only [no_sem]
  constructor
  · intro h x hR' hS'
    have ⟨hR, hS⟩ := (hInt x).mpr ⟨hR', hS'⟩
    exact h x hR hS
  · intro h x hR hS
    have ⟨hR', hS'⟩ := (hInt x).mp ⟨hR, hS⟩
    exact h x hR' hS'

-- === Left anti-additivity (P&W §5.8) ===

/-- `⟦every⟧` is left anti-additive: every(A∪B, C) = every(A,C) ∧ every(B,C). -/
theorem every_laa : PLeftAntiAdditive (every_sem F) := by
  intro R R' S; simp only [every_sem]
  constructor
  · intro h; exact ⟨fun x hR => h x (Or.inl hR), fun x hR' => h x (Or.inr hR')⟩
  · intro ⟨h1, h2⟩ x hRR'
    rcases hRR' with hR | hR'
    · exact h1 x hR
    · exact h2 x hR'

/-- `⟦no⟧` is left anti-additive: no(A∪B, C) = no(A,C) ∧ no(B,C). -/
theorem no_laa : PLeftAntiAdditive (no_sem F) := by
  intro R R' S; simp only [no_sem]
  constructor
  · intro h; exact ⟨fun x hR => h x (Or.inl hR), fun x hR' => h x (Or.inr hR')⟩
  · intro ⟨h1, h2⟩ x hRR'
    rcases hRR' with hR | hR'
    · exact h1 x hR
    · exact h2 x hR'

/-- `⟦no⟧` is right anti-additive: no(A, B∪C) = no(A,B) ∧ no(A,C).
    "Nobody saw A-or-B" ↔ "Nobody saw A and nobody saw B".
    This licenses strong NPIs in scope: "Nobody lifted a finger." -/
theorem no_raa : PRightAntiAdditive (no_sem F) := by
  intro R S S'; simp only [no_sem]
  constructor
  · intro h
    exact ⟨fun x hR hS => h x hR (Or.inl hS),
           fun x hR hS' => h x hR (Or.inr hS')⟩
  · intro ⟨h1, h2⟩ x hR hSS'
    rcases hSS' with hS | hS'
    · exact h1 x hR hS
    · exact h2 x hR hS'

/-- @cite{peters-westerstahl-2006} Prop 13: the only non-trivial CONSERV, EXT,
    and ISOM quantifiers satisfying LAA are `every` and `no` (and `A = ∅`). -/
theorem laa_characterization :
    PLeftAntiAdditive (every_sem F) ∧
    PLeftAntiAdditive (no_sem F) := ⟨every_laa, no_laa⟩

-- === Duality square (P&W §1.1.1) ===

/-- Inner negation maps `every` to `no`: every...not = no.
    `∀x. R(x) → ¬S(x)` = `¬∃x. R(x) ∧ S(x)`. -/
theorem pinnerNeg_every_eq_no :
    (pinnerNeg (every_sem F) : PropGQ F.Entity) = (no_sem F : PropGQ F.Entity) := by
  funext R S; simp only [pinnerNeg, every_sem, no_sem]

/-- The dual of `every` is `some`: Q̌(every) = some.
    `¬(∀x. R(x) → ¬S(x))` = `∃x. R(x) ∧ S(x)`. -/
theorem pdualQ_every_eq_some :
    (pdualQ (every_sem F) : PropGQ F.Entity) = (some_sem F : PropGQ F.Entity) := by
  funext R S; simp only [pdualQ, pouterNeg, pinnerNeg, every_sem, some_sem]
  exact propext ⟨
    fun h => by push_neg at h; exact h,
    fun ⟨x, hR, hS⟩ h => h x hR hS⟩

-- === Extension: spectator irrelevance (List-based proofs preserved for compatibility) ===

/-- `every_sem` satisfies Extension: spectator elements
    (outside the restrictor) don't affect truth values. -/
theorem every_ext_spectator {F : Frame} (es : List F.Entity) (e : F.Entity)
    (R S : F.Entity → Bool) (hR : R e = false) :
    (e :: es).all (λ x => !R x || S x) =
    es.all (λ x => !R x || S x) := by
  simp [List.all_cons, hR]

/-- `some_sem` satisfies Extension. -/
theorem some_ext_spectator {F : Frame} (es : List F.Entity) (e : F.Entity)
    (R S : F.Entity → Bool) (hR : R e = false) :
    (e :: es).any (λ x => R x && S x) =
    es.any (λ x => R x && S x) := by
  simp [List.any_cons, hR]

/-- `no_sem` satisfies Extension. -/
theorem no_ext_spectator {F : Frame} (es : List F.Entity) (e : F.Entity)
    (R S : F.Entity → Bool) (hR : R e = false) :
    (e :: es).all (λ x => !R x || !S x) =
    es.all (λ x => !R x || !S x) := by
  simp [List.all_cons, hR]

/-- `most_sem` satisfies Extension: spectators don't enter
    either R∩S or R\S, so the cardinality comparison is unchanged. -/
theorem most_ext_spectator {F : Frame} (es : List F.Entity) (e : F.Entity)
    (R S : F.Entity → Bool) (hR : R e = false) :
    (e :: es).filter (λ x => R x && S x) = es.filter (λ x => R x && S x) ∧
    (e :: es).filter (λ x => R x && !S x) = es.filter (λ x => R x && !S x) := by
  constructor <;> (simp [hR])

-- === Positive/Negative Strong (P&W Ch.6) ===

/-- `every_sem` is positive strong: every(A,A) = true for all A.
    Proof: `R(x) → R(x)` for all x. -/
theorem every_positive_strong : PPositiveStrong (every_sem F) := by
  intro R x hR; exact hR

/-- `no_sem` is negative strong on non-empty restrictors:
    no(A,A) = false for all non-empty A. -/
theorem no_negative_strong_nonempty (R : F.Entity → Prop)
    (hR : ∃ x : F.Entity, R x) :
    ¬no_sem F R R := by
  intro h
  obtain ⟨x, hRx⟩ := hR
  exact h x hRx hRx

/-- `no_sem` is NOT positive strong: no(A,A) = false when A is non-empty.
    Counterexample: R = {john}. -/
theorem no_not_positive_strong : ¬PPositiveStrong (no_sem (F := toyModel)) := by
  intro h
  have := h student_sem
  exact this ToyEntity.john (by simp [student_sem]) (by simp [student_sem])

-- === K&S Existential det classification (§3.3, G3) ===

/-- `⟦some⟧` is existential (K&S G3): some(A,B) = some(A∩B, everything).
    some is natural in there-sentences: "There are some cats." -/
theorem some_existential : PExistential (some_sem F) := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, ⟨hR, hS⟩, trivial⟩,
         fun ⟨x, ⟨hR, hS⟩, _⟩ => ⟨x, hR, hS⟩⟩

/-- `⟦no⟧` is existential (K&S G3): no(A,B) = no(A∩B, everything). -/
theorem no_existential : PExistential (no_sem F) := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x ⟨hR, hS⟩ _ => h x hR hS,
         fun h x hR hS => h x ⟨hR, hS⟩ trivial⟩

/-- `⟦every⟧` is NOT existential (K&S §3.3). -/
theorem every_not_existential : ¬PExistential (every_sem (F := toyModel)) := by
  intro h
  -- every(thing, student) should be false (pizza is a thing but not a student)
  -- but every(thing ∩ student, True) = every(student, True) = true
  have hFwd := (h thing_sem student_sem).mpr
  have : every_sem toyModel (fun x => thing_sem x ∧ student_sem x) (fun _ => True) := by
    intro x _; trivial
  have := hFwd this
  exact absurd (this ToyEntity.pizza trivial) (by simp [student_sem])

/-- `⟦most⟧` is NOT existential (K&S §3.3). -/
theorem most_not_existential : ¬PExistential (most_sem (F := toyModel)) := by
  intro h
  -- most(student, sleeps): |{john}∩{john}|=1 vs |{mary}\{john}|=1, so 1 > 1 = false
  -- most(student∩sleeps, True) = most({john}, True): |{john}|=1 vs |∅|=0, so 1 > 0 = true
  have hFwd := (h student_sem sleeps_sem).mpr
  have hInner : most_sem toyModel (fun x => student_sem x ∧ sleeps_sem x) (fun _ => True) := by
    simp only [most_sem, count]
    -- The intersection {student ∧ sleeps} = {john}, and its negation in the restrictor is ∅
    sorry
  sorry

-- ============================================================================
-- @cite{van-benthem-1984}: Relational Properties of Concrete Quantifiers
-- ============================================================================

/-- `⟦every⟧` is transitive: A ⊆ B and B ⊆ C implies A ⊆ C. -/
theorem every_transitive : PQTransitive (every_sem F) := by
  intro A B C hAB hBC x hA; exact hBC x (hAB x hA)

/-- `⟦every⟧` is antisymmetric: A ⊆ B and B ⊆ A implies A = B. -/
theorem every_antisymmetric : PQAntisymmetric (every_sem F) := by
  intro A B hAB hBA
  funext x; exact propext ⟨fun hA => hAB x hA, fun hB => hBA x hB⟩

/-- `⟦some⟧` is quasi-reflexive: A∩B ≠ ∅ implies A∩A ≠ ∅ (i.e., A ≠ ∅). -/
theorem some_quasi_reflexive : PQuasiReflexive (some_sem F) := by
  intro A B ⟨x, hA, _⟩; exact ⟨x, hA, hA⟩

/-- `⟦no⟧` is quasi-universal: A∩A = ∅ (i.e., A = ∅) implies A∩B = ∅ for all B. -/
theorem no_quasi_universal : PQuasiUniversal (no_sem F) := by
  intro A B hAA x hA; exact absurd hA (hAA x hA)

-- ============================================================================
-- @cite{van-benthem-1984}: Double Monotonicity Classification
-- ============================================================================

/-- `⟦every⟧` is restrictor-↓ (anti-persistent).
    Follows from Zwarts bridge: reflexive + transitive + CONSERV → ↓MON. -/
theorem every_restrictor_down : PRestrictorDownwardMono (every_sem F) :=
  pzwarts_refl_trans_restrictorDown _ every_conservative every_positive_strong every_transitive

/-- `⟦some⟧` is restrictor-↑ (persistent): A ⊆ A' and some(A,B) → some(A',B). -/
theorem some_restrictor_up : PRestrictorUpwardMono (some_sem F) := by
  intro R R' S hRR' ⟨x, hR, hS⟩; exact ⟨x, hRR' x hR, hS⟩

/-- `⟦no⟧` is restrictor-↓ (anti-persistent): A ⊆ A' and no(A',B) → no(A,B). -/
theorem no_restrictor_down : PRestrictorDownwardMono (no_sem F) := by
  intro R R' S hRR' hQ x hR; exact hQ x (hRR' x hR)

/-- `⟦every⟧` has double monotonicity ↓MON↑ (@cite{van-benthem-1984} §4.2). -/
theorem every_doubleMono :
    PRestrictorDownwardMono (every_sem F) ∧ PScopeUpwardMono (every_sem F) :=
  ⟨every_restrictor_down, every_scope_up⟩

/-- `⟦some⟧` has double monotonicity ↑MON↑. -/
theorem some_doubleMono :
    PRestrictorUpwardMono (some_sem F) ∧ PScopeUpwardMono (some_sem F) :=
  ⟨some_restrictor_up, some_scope_up⟩

/-- `⟦no⟧` has double monotonicity ↓MON↓. -/
theorem no_doubleMono :
    PRestrictorDownwardMono (no_sem F) ∧ PScopeDownwardMono (no_sem F) :=
  ⟨no_restrictor_down, no_scope_down⟩

/-- `outerNeg ⟦every⟧` (= "not all") has double monotonicity ↑MON↓. -/
theorem notAll_doubleMono :
    PRestrictorUpwardMono (pouterNeg (every_sem F)) ∧
    PScopeDownwardMono (pouterNeg (every_sem F)) :=
  ⟨pouterNeg_restrictorDown_to_up _ every_restrictor_down,
   pouterNeg_up_to_down _ every_scope_up⟩

/-- `⟦every⟧` is filtrating: every(A,B) ∧ every(A,C) → every(A, B∩C). -/
theorem every_filtrating : PFiltrating (every_sem F) := by
  intro A B C hAB hAC x hA; exact ⟨hAB x hA, hAC x hA⟩

-- ============================================================================
-- Aristotelian Square of Opposition
-- @cite{belnap-1970} @cite{strawson-1952}
-- ============================================================================

/-- **Contradiction (A vs O)**: the A-form and O-form are contradictories. -/
theorem every_contradicts_notEvery (R S : F.Entity → Prop) :
    every_sem F R S ↔ ¬(pouterNeg (every_sem F) R S) := by
  simp [pouterNeg, Classical.not_not]

/-- **Contradiction (E vs I)**: the E-form and I-form are contradictories. -/
theorem no_contradicts_some (R S : F.Entity → Prop) :
    no_sem F R S ↔ ¬(some_sem F R S) := by
  simp only [no_sem, some_sem]; push_neg; rfl

/-- **Contrariety (A ∧ E)**: the A-form and E-form can't both hold
    unless the restrictor is empty. -/
theorem a_e_contrary (R S : F.Entity → Prop) :
    every_sem F R S → no_sem F R S →
    ∀ x : F.Entity, ¬R x := by
  intro hA hE x hR
  exact hE x hR (hA x hR)

/-- **Subalternation (A → I)**: the A-form entails the I-form when the
    restrictor is non-empty. -/
theorem subalternation_a_i (R S : F.Entity → Prop)
    (hR : ∃ x : F.Entity, R x) :
    every_sem F R S → some_sem F R S := by
  intro hA; obtain ⟨x, hRx⟩ := hR; exact ⟨x, hRx, hA x hRx⟩

/-- **Subalternation (E → O)**: the E-form entails the O-form when the
    restrictor is non-empty. -/
theorem subalternation_e_o (R S : F.Entity → Prop)
    (hR : ∃ x : F.Entity, R x) :
    no_sem F R S → pouterNeg (every_sem F) R S := by
  intro hE hA
  obtain ⟨x, hRx⟩ := hR
  exact hE x hRx (hA x hRx)

/-- **Subcontrariety (I ∨ O)**: the I-form and O-form can't both fail
    when the restrictor is non-empty. -/
theorem subcontrariety_i_o (R S : F.Entity → Prop)
    (hR : ∃ x : F.Entity, R x) :
    some_sem F R S ∨ pouterNeg (every_sem F) R S := by
  by_cases h : some_sem F R S
  · exact Or.inl h
  · right; intro hA
    apply h; obtain ⟨x, hRx⟩ := hR; exact ⟨x, hRx, hA x hRx⟩

-- ============================================================================
-- Basic Left Monotonicities (@cite{peters-westerstahl-2006} §5.5)
-- ============================================================================

/-- `⟦some⟧` is ↑_SE Mon: adding elements of B to A preserves some(A,B). -/
theorem some_upSE : PUpSEMon (some_sem F) :=
  pRestrictorUpMono_to_upSE _ some_restrictor_up

/-- `⟦some⟧` is ↑_SW Mon: adding elements outside B to A preserves some(A,B). -/
theorem some_upSW : PUpSWMon (some_sem F) :=
  pRestrictorUpMono_to_upSW _ some_restrictor_up

/-- `⟦every⟧` is ↓_NW Mon: removing elements of B from A preserves every(A,B). -/
theorem every_downNW : PDownNWMon (every_sem F) :=
  pRestrictorDownMono_to_downNW _ every_restrictor_down

/-- `⟦every⟧` is ↓_NE Mon: removing elements outside B from A preserves every(A,B). -/
theorem every_downNE : PDownNEMon (every_sem F) :=
  pRestrictorDownMono_to_downNE _ every_restrictor_down

/-- `⟦no⟧` is ↓_NW Mon. -/
theorem no_downNW : PDownNWMon (no_sem F) :=
  pRestrictorDownMono_to_downNW _ no_restrictor_down

/-- `⟦no⟧` is ↓_NE Mon. -/
theorem no_downNE : PDownNEMon (no_sem F) :=
  pRestrictorDownMono_to_downNE _ no_restrictor_down

-- ============================================================================
-- Smooth Quantifiers (@cite{peters-westerstahl-2006} §5.6)
-- ============================================================================

/-- `⟦some⟧` is ↓_NE Mon (direct proof).
    Removing non-S elements from A preserves ∃x.R(x)∧S(x) since the witness is in S. -/
theorem some_downNE : PDownNEMon (some_sem F) := by
  intro R S R' hSub hKeep ⟨x, hR, hS⟩
  exact ⟨x, hKeep x hR hS, hS⟩

/-- `⟦some⟧` is smooth (↓_NE + ↑_SE). -/
theorem some_smooth : PSmooth (some_sem F) :=
  ⟨some_downNE, pRestrictorUpMono_to_upSE _ some_restrictor_up⟩

/-- `⟦every⟧` is ↑_SE Mon (direct proof).
    Adding B-elements to A preserves ∀x.R(x)→S(x) since the new elements satisfy S. -/
theorem every_upSE_direct : PUpSEMon (every_sem F) := by
  intro R S R' hSub hDiff hQ x hR'
  by_cases hS : S x
  · exact hS
  · exact hQ x (hDiff x hR' hS)

/-- `⟦every⟧` is smooth (↓_NE + ↑_SE). -/
theorem every_smooth : PSmooth (every_sem F) :=
  ⟨every_downNE, every_upSE_direct⟩

/-- `⟦no⟧` is co-smooth (↓_NW + ↑_SW). Follows from anti-persistence. -/
theorem no_coSmooth_partial : PDownNWMon (no_sem F) ∧ PDownNEMon (no_sem F) :=
  ⟨pRestrictorDownMono_to_downNW _ no_restrictor_down,
   pRestrictorDownMono_to_downNE _ no_restrictor_down⟩

/-- `⟦most⟧` is ↓_NE Mon (direct proof). -/
theorem most_downNE : PDownNEMon (most_sem F) := by
  intro R S R' hSub hKeep hQ
  simp only [most_sem] at *
  have hEq : count (fun x : F.Entity => R' x ∧ S x) =
      count (fun x : F.Entity => R x ∧ S x) := by
    simp only [count]; congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hR', hS⟩ => ⟨hSub x hR', hS⟩, fun ⟨hR, hS⟩ => ⟨hKeep x hR hS, hS⟩⟩
  have hLe : count (fun x : F.Entity => R' x ∧ ¬S x) ≤
      count (fun x : F.Entity => R x ∧ ¬S x) :=
    count_le_of_imp fun x ⟨hR', hS⟩ => ⟨hSub x hR', hS⟩
  omega

/-- `⟦most⟧` is ↑_SE Mon (direct proof). -/
theorem most_upSE : PUpSEMon (most_sem F) := by
  intro R S R' hSub hDiff hQ
  simp only [most_sem] at *
  have hEq : count (fun x : F.Entity => R' x ∧ ¬S x) =
      count (fun x : F.Entity => R x ∧ ¬S x) := by
    simp only [count]; congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hR', hS⟩ => ⟨hDiff x hR' hS, hS⟩, fun ⟨hR, hS⟩ => ⟨hSub x hR, hS⟩⟩
  have hLe : count (fun x : F.Entity => R x ∧ S x) ≤
      count (fun x : F.Entity => R' x ∧ S x) :=
    count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hSub x hR, hS⟩
  omega

/-- `⟦most⟧` is smooth. -/
theorem most_smooth : PSmooth (most_sem F) :=
  ⟨most_downNE, most_upSE⟩

-- === Counting quantifier smoothness ===

/-- `⟦at least n⟧` is persistent (Mon↑ in restrictor). -/
theorem at_least_n_restrictor_up (n : Nat) : PRestrictorUpwardMono (at_least_n_sem F n) := by
  intro R R' S hRR' h
  simp only [at_least_n_sem] at *
  exact le_trans h (count_le_of_imp fun x ⟨hR, hS⟩ => ⟨hRR' x hR, hS⟩)

/-- `⟦at least n⟧` is ↓_NE Mon. -/
theorem at_least_n_downNE (n : Nat) : PDownNEMon (at_least_n_sem F n) := by
  intro R S R' hSub hKeep hQ
  simp only [at_least_n_sem] at *
  have hEq : count (fun x : F.Entity => R' x ∧ S x) =
      count (fun x : F.Entity => R x ∧ S x) := by
    simp only [count]; congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hR', hS⟩ => ⟨hSub x hR', hS⟩, fun ⟨hR, hS⟩ => ⟨hKeep x hR hS, hS⟩⟩
  omega

/-- `⟦at least n⟧` is smooth (↓_NE + ↑_SE). -/
theorem at_least_n_smooth (n : Nat) : PSmooth (at_least_n_sem F n) :=
  ⟨at_least_n_downNE n, pRestrictorUpMono_to_upSE _ (at_least_n_restrictor_up n)⟩

/-- `⟦at most n⟧` is anti-persistent (Mon↓ in restrictor). -/
theorem at_most_n_restrictor_down (n : Nat) : PRestrictorDownwardMono (at_most_n_sem F n) := by
  rw [at_most_eq_pouterNeg_at_least_succ]
  exact pouterNeg_restrictorUp_to_down _ (at_least_n_restrictor_up _)

/-- `⟦at most n⟧` is co-smooth (↓_NW + ↑_SW). -/
theorem at_most_n_coSmooth (n : Nat) : PCoSmooth (at_most_n_sem F n) := by
  rw [at_most_eq_pouterNeg_at_least_succ]
  exact pSmooth_iff_outerNeg_coSmooth _ (at_least_n_smooth _)

-- ============================================================================
-- Quantity / Isomorphism Closure Proofs (@cite{mostowski-1957})
-- ============================================================================

/-- `Quantity` is closed under pouterNeg. -/
theorem quantity_pouterNeg (q : PropGQ F.Entity) (h : Quantity q) :
    Quantity (pouterNeg q) := by
  intro R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  simp only [pouterNeg]; exact Iff.not (h R₁ S₁ R₂ S₂ hTT hTF hFT hFF)

/-- `Quantity` is closed under pgqMeet. -/
theorem quantity_pgqMeet (q₁ q₂ : PropGQ F.Entity)
    (h₁ : Quantity q₁) (h₂ : Quantity q₂) :
    Quantity (pgqMeet q₁ q₂) := by
  intro R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  simp only [pgqMeet]
  exact Iff.and (h₁ R₁ S₁ R₂ S₂ hTT hTF hFT hFF) (h₂ R₁ S₁ R₂ S₂ hTT hTF hFT hFF)

/-- `⟦at least n⟧` satisfies Quantity: truth depends only on |A ∩ B|. -/
theorem at_least_n_quantity (n : Nat) : Quantity (at_least_n_sem F n) := by
  intro R₁ S₁ R₂ S₂ hTT _ _ _
  simp only [at_least_n_sem]; omega

/-- `⟦at most n⟧` satisfies Quantity: truth depends only on |A ∩ B|. -/
theorem at_most_n_quantity (n : Nat) : Quantity (at_most_n_sem F n) := by
  intro R₁ S₁ R₂ S₂ hTT _ _ _
  simp only [at_most_n_sem]; omega

/-- `⟦exactly n⟧` satisfies Quantity. -/
theorem exactly_n_quantity (n : Nat) : Quantity (exactly_n_sem F n) := by
  rw [exactly_eq_meet_at_least_at_most]
  exact quantity_pgqMeet _ _ (at_least_n_quantity n) (at_most_n_quantity n)

/-- `⟦some⟧` satisfies Quantity. -/
theorem some_quantity : Quantity (some_sem F) := by
  rw [some_eq_at_least_1]; exact at_least_n_quantity 1

/-- `⟦no⟧` satisfies Quantity. -/
theorem no_quantity : Quantity (no_sem F) := by
  rw [no_eq_at_most_0]; exact at_most_n_quantity 0

/-- `⟦every⟧` satisfies Quantity. -/
private theorem every_quantityInvariant :
    PQuantityInvariant (every_sem F) := by
  intro A B A' B' f hBij hA hB
  simp only [every_sem]
  rw [forall_bij_inv f hBij]
  exact forall_congr' fun x => by rw [show A (f x) ↔ A' x from hA x,
                                       show B (f x) ↔ B' x from hB x]

theorem every_quantity : Quantity (every_sem F) := by
  sorry -- Requires quantity_of_quantityInvariant which itself is sorry'd

/-- `⟦most⟧` satisfies Quantity. -/
theorem most_quantity : Quantity (most_sem F) := by
  intro R₁ S₁ R₂ S₂ hTT hTF _ _
  simp only [most_sem]; omega

/-- `⟦few⟧` satisfies Quantity. -/
theorem few_quantity : Quantity (few_sem F) := by
  intro R₁ S₁ R₂ S₂ hTT hTF _ _
  simp only [few_sem]; omega

/-- Count decomposition: |R| = |R∩S| + |R\S|. -/
private theorem count_decompose (R S : F.Entity → Prop) [DecidablePred R] [DecidablePred S] :
    count (fun x : F.Entity => R x) =
    count (fun x : F.Entity => R x ∧ S x) +
    count (fun x : F.Entity => R x ∧ ¬S x) := by
  simp only [count]
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact ⟨fun hR => by by_cases hS : S x <;> simp [hR, hS],
           fun h => h.elim And.left And.left⟩
  · simp only [Finset.disjoint_filter]
    intro x _ ⟨_, h1⟩ ⟨_, h2⟩; exact h2 h1

/-- `⟦half⟧` satisfies Quantity. -/
theorem half_quantity : Quantity (half_sem F) := by
  intro R₁ S₁ R₂ S₂ hTT hTF _ _
  simp only [half_sem]
  constructor <;> intro h
  · have h₁ := count_decompose R₁ S₁; have h₂ := count_decompose R₂ S₂; omega
  · have h₁ := count_decompose R₁ S₁; have h₂ := count_decompose R₂ S₂; omega

-- ============================================================================
-- SatisfiesUniversals (@cite{van-de-pol-etal-2023})
-- ============================================================================

/-- `⟦some⟧` satisfies CONSERV ∧ Mon↑. -/
theorem some_satisfiesUniversals : PSatisfiesUniversals (some_sem F) :=
  ⟨some_conservative, Or.inl some_scope_up⟩

/-- `⟦every⟧` satisfies CONSERV ∧ Mon↑. -/
theorem every_satisfiesUniversals : PSatisfiesUniversals (every_sem F) :=
  ⟨every_conservative, Or.inl every_scope_up⟩

/-- `⟦no⟧` satisfies CONSERV ∧ Mon↓. -/
theorem no_satisfiesUniversals : PSatisfiesUniversals (no_sem F) :=
  ⟨no_conservative, Or.inr no_scope_down⟩

/-- `⟦most⟧` satisfies CONSERV ∧ Mon↑. -/
theorem most_satisfiesUniversals : PSatisfiesUniversals (most_sem F) :=
  ⟨most_conservative, Or.inl most_scope_up⟩

/-- `⟦few⟧` satisfies CONSERV ∧ Mon↓. -/
theorem few_satisfiesUniversals : PSatisfiesUniversals (few_sem F) :=
  ⟨few_conservative, Or.inr few_scope_down⟩

/-- `⟦at least n⟧` satisfies CONSERV ∧ Mon↑. -/
theorem at_least_n_satisfiesUniversals (n : Nat) :
    PSatisfiesUniversals (at_least_n_sem F n) :=
  ⟨at_least_n_conservative n, Or.inl (at_least_n_scope_up n)⟩

/-- `⟦at most n⟧` satisfies CONSERV ∧ Mon↓. -/
theorem at_most_n_satisfiesUniversals (n : Nat) :
    PSatisfiesUniversals (at_most_n_sem F n) :=
  ⟨at_most_n_conservative n, Or.inr (at_most_n_scope_down n)⟩

/-- `⟦exactly n⟧` satisfies CONSERV (but not MON for n ≥ 1). -/
theorem exactly_n_conservative_quantity (n : Nat) :
    PConservative (exactly_n_sem F n) :=
  exactly_n_conservative n

-- ============================================================================
-- Exceptive Quantifiers: "all but n" (@cite{peters-westerstahl-2006})
-- ============================================================================

/-- `⟦all but 0⟧ = ⟦every⟧`: zero exceptions means universal. -/
theorem all_but_0_eq_every :
    (all_but_n_sem F 0 : PropGQ F.Entity) = (every_sem F : PropGQ F.Entity) := by
  funext R S
  simp only [all_but_n_sem, every_sem]
  exact propext ⟨
    fun h x hR => by
      by_contra hS
      have : 0 < count (fun x : F.Entity => R x ∧ ¬S x) :=
        Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR, hS⟩⟩
      omega,
    fun h => by
      simp only [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ ⟨hR, hNS⟩; exact hNS (h x hR)⟩

/-- `⟦all but n⟧` is conservative. -/
theorem all_but_n_conservative (n : Nat) : PConservative (all_but_n_sem F n) := by
  intro R S; simp only [all_but_n_sem]
  constructor <;> intro h
  · rw [← count_neg_idem_any R S _ _]; exact h
  · rw [count_neg_idem_any R S _ _]; exact h

/-- `⟦all but n⟧` satisfies Quantity. -/
theorem all_but_n_quantity (n : Nat) : Quantity (all_but_n_sem F n) := by
  intro R₁ S₁ R₂ S₂ _ hTF _ _
  simp only [all_but_n_sem]; omega

/-- `⟦between n and k⟧` is conservative. -/
theorem between_n_m_conservative (n k : Nat) :
    PConservative (between_n_m_sem F n k) := by
  intro R S; simp only [between_n_m_sem, pgqMeet]
  exact Iff.and (at_least_n_conservative n R S) (at_most_n_conservative k R S)

/-- `⟦between n and k⟧` satisfies Quantity. -/
theorem between_n_m_quantity (n k : Nat) : Quantity (between_n_m_sem F n k) :=
  quantity_pgqMeet _ _ (at_least_n_quantity n) (at_most_n_quantity k)

-- ============================================================================
-- Proportional Quantifiers (@cite{peters-westerstahl-2006} §4.3)
-- ============================================================================

/-- Proportional: Q's truth value depends only on the ratio |A∩B|/|A\B|. -/
def Proportional (q : PropGQ F.Entity) : Prop :=
  ∀ (R₁ S₁ R₂ S₂ : F.Entity → Prop),
    let tt₁ := count (fun x : F.Entity => R₁ x ∧ S₁ x)
    let tf₁ := count (fun x : F.Entity => R₁ x ∧ ¬S₁ x)
    let tt₂ := count (fun x : F.Entity => R₂ x ∧ S₂ x)
    let tf₂ := count (fun x : F.Entity => R₂ x ∧ ¬S₂ x)
    0 < tt₁ + tf₁ → 0 < tt₂ + tf₂ →
    tt₁ * tf₂ = tt₂ * tf₁ →
    (q R₁ S₁ ↔ q R₂ S₂)

/-- Cross-ratio preserves strict inequality. -/
private theorem cross_ratio_preserves_gt (a₁ b₁ a₂ b₂ : Nat)
    (hne₂ : 0 < a₂ + b₂)
    (hcross : a₁ * b₂ = a₂ * b₁)
    (hgt : a₁ > b₁) :
    a₂ > b₂ := by
  by_contra hle
  push Not at hle
  rcases Nat.eq_zero_or_pos b₂ with rfl | hb₂pos
  · omega
  · have h1 : (b₁ + 1) * b₂ ≤ a₁ * b₂ := Nat.mul_le_mul_right b₂ hgt
    have h3 : a₂ * b₁ ≤ b₂ * b₁ := Nat.mul_le_mul_right b₁ hle
    rw [Nat.add_mul] at h1; rw [Nat.mul_comm b₂ b₁] at h3; omega

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

/-- `⟦most⟧` is proportional. -/
theorem most_proportional : Proportional (most_sem F) := by
  intro R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross
  simp only [most_sem]
  exact cross_ratio_gt_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross

/-- `⟦few⟧` is proportional. -/
theorem few_proportional : Proportional (few_sem F) := by
  intro R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross
  simp only [few_sem]
  exact cross_ratio_lt_iff a₁ b₁ a₂ b₂ hNE₁ hNE₂ hCross

/-- Core arithmetic for half_proportional. -/
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

theorem half_proportional : Proportional (half_sem F) := by
  intro R₁ S₁ R₂ S₂
  dsimp only []
  intro hNE₁ hNE₂ hCross
  simp only [half_sem]
  rw [count_decompose R₁ S₁, count_decompose R₂ S₂]
  exact half_prop_core _ _ _ _ hNE₁ hNE₂ hCross

end FintypeProofs

/-! ## Open conjectures (van de Pol et al. 2023)

`TODO`: Quantifiers satisfying the B&C semantic universals
(conservativity, quantity, monotonicity) have *strictly lower*
complexity (Lempel-Ziv on truth-table representations, or MDL in a
language-of-thought grammar) than violators.

`TODO`: Among the three universals, **monotonicity** is the strongest
predictor of complexity reduction; conservativity is intermediate;
quantity shows a weaker but robust effect.

Both were previously stubbed in the deleted `Core/Conjectures.lean`.
Formal content depends on choosing canonical complexity measures (LZ
over Boolean truth tables; MDL over LoT grammars) and connecting them
to the existing `SatisfiesUniversals` predicate. -/

end Semantics.Quantification.Quantifier
