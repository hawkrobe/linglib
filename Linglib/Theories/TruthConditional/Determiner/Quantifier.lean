import Linglib.Theories.TruthConditional.Basic
import Linglib.Core.Quantification

/-!
# Generalized Quantifiers

Determiners have type `(e→t) → ((e→t) → t)`:
- `⟦every⟧ = λR.λS. ∀x. R(x) → S(x)`
- `⟦some⟧  = λR.λS. ∃x. R(x) ∧ S(x)`
- `⟦no⟧    = λR.λS. ¬∃x. R(x) ∧ S(x)`

## Semantic Universals (Barwise & Cooper 1981)

Three properties conjectured to hold of all simple (lexicalized) determiners:
- **Conservativity**: `Q(A, B) ↔ Q(A, A ∩ B)` — only the restrictor matters
- **Quantity** (isomorphism closure): meaning depends only on cardinalities
  `|A ∩ B|`, `|A \ B|`, `|B \ A|`, `|M \ (A ∪ B)|`
- **Monotonicity**: Q is either upward or downward monotone in scope

Van de Pol et al. (2023) show quantifiers satisfying these universals have
shorter minimal description length, suggesting a simplicity bias explains
the universals.

## Organization

- **Generic GQ properties**: `Core.Quantification` — `Conservative`, `ScopeUpwardMono`,
  `ScopeDownwardMono`, `outerNeg`, `innerNeg`, `dualQ`, etc. (model-agnostic)
- `FiniteModelProofs`: Concrete proofs for specific denotations (requires FiniteModel)

`ScopeUpwardMono`/`ScopeDownwardMono` are equivalent to Mathlib's
`Monotone`/`Antitone` (see `Core.Quantification.scopeUpMono_iff_monotone`),
connecting to `TruthConditional.Core.Polarity.IsUpwardEntailing = Monotone`.

## References

- Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language.
- Keenan, E. & Stavi, J. (1986). A Semantic Characterization of Natural Language Determiners.
- van de Pol, I. et al. (2023). Quantifiers satisfying semantic universals have
  shorter minimal description length. Cognition 232, 105150.
-/

namespace TruthConditional.Determiner.Quantifier

open TruthConditional
open Core.Quantification

def Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

/-- A model with a computable finite domain. -/
class FiniteModel (m : Model) where
  elements : List m.Entity
  complete : ∀ x : m.Entity, x ∈ elements

def every_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    FiniteModel.elements.all (λ x => !restrictor x || scope x)

def some_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    FiniteModel.elements.any (λ x => restrictor x && scope x)

def no_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    FiniteModel.elements.all (λ x => !restrictor x || !scope x)

/-- `⟦most⟧(R)(S) = |R ∩ S| > |R \ S|` -/
def most_sem (m : Model) [FiniteModel m] : m.interpTy Ty.det :=
  λ restrictor => λ scope =>
    let inBoth := FiniteModel.elements.filter (λ x => restrictor x && scope x)
    let inROnly := FiniteModel.elements.filter (λ x => restrictor x && !scope x)
    decide (inBoth.length > inROnly.length)

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

#eval everyStudentSleeps  -- false

def someStudentSleeps : toyModel.interpTy .t :=
  some_sem toyModel student_sem sleeps_sem

#eval someStudentSleeps  -- true

def noStudentSleeps : toyModel.interpTy .t :=
  no_sem toyModel student_sem sleeps_sem

#eval noStudentSleeps  -- false

def everyStudentLaughs : toyModel.interpTy .t :=
  every_sem toyModel student_sem laughs_sem

#eval everyStudentLaughs  -- true

#eval some_sem toyModel student_sem laughs_sem  -- true

def everyPersonSleeps : toyModel.interpTy .t :=
  every_sem toyModel person_sem sleeps_sem

def somePersonSleeps : toyModel.interpTy .t :=
  some_sem toyModel person_sem sleeps_sem

#eval everyPersonSleeps  -- false
#eval somePersonSleeps   -- true

end Examples

-- ============================================================================
-- Finite Model Proofs (require FiniteModel for FiniteModel.elements)
-- ============================================================================

section FiniteModelProofs

variable {m : Model} [FiniteModel m]

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

-- === Quantity / Isomorphism Closure (Mostowski 1957) ===

/--
Quantity / Isomorphism closure (Mostowski 1957; van Benthem 1984):
Q(A, B) depends only on the four cardinalities
`|A ∩ B|`, `|A \ B|`, `|B \ A|`, `|M \ (A ∪ B)|`.

Equivalently: permuting the domain does not change the quantifier's
truth value. This is the property that makes generalized quantifiers
"logical" in Mostowski's sense.
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
Van de Pol et al. (2023) show these quantifiers have shorter MDL.
-/
def SatisfiesUniversals (q : m.interpTy Ty.det) : Prop :=
  Conservative q ∧ Quantity q ∧ (ScopeUpwardMono q ∨ ScopeDownwardMono q)

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

/-- Outer negation maps `some` to `no`: ~some = no.
    `¬(∃x. R(x) ∧ S(x))` = `∀x. R(x) → ¬S(x)`. -/
theorem outerNeg_some_eq_no : outerNeg (some_sem m) = no_sem m := by
  funext R S; simp only [outerNeg, some_sem, no_sem]
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

end FiniteModelProofs

end TruthConditional.Determiner.Quantifier
