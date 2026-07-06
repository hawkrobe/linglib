import Linglib.Semantics.Intensional.Defs

/-!
# Generalized Conjunction

[partee-rooth-1983]

Conjunction and disjunction defined recursively over the IL type structure:
- Base case (`t`): Boolean operations
- Function case (`⟨a,b⟩`): pointwise application
- Intension case (`⟨s,a⟩`): pointwise over indices
-/

namespace Intensional.Conjunction

open Intensional

example : Ty.isConjoinable .t = true := rfl
example : Ty.isConjoinable .e = false := rfl
example : Ty.isConjoinable (.fn .e .t) = true := rfl
example : Ty.isConjoinable (.fn .e (.fn .e .t)) = true := rfl
example : Ty.isConjoinable (.fn .e .e) = false := rfl
example : Ty.isConjoinable (.intens .t) = true := rfl
example : Ty.isConjoinable (.intens .e) = false := rfl
example : Ty.isConjoinable (.intens (.e ⇒ .t)) = true := rfl

/-- Generalized conjunction ([partee-rooth-1983] Definition 5).
    At intension types, conjunction is pointwise over indices. -/
def genConj (τ : Ty) (E W : Type) : Denot E W τ → Denot E W τ → Denot E W τ :=
  match τ with
  | .t => λ x y => x ∧ y
  | .e => λ x _ => x
  | .d => λ x _ => x
  | .fn _ τ' => λ f g => λ x => genConj τ' E W (f x) (g x)
  | .intens a => λ f g => λ i => genConj a E W (f i) (g i)

/-- Generalized disjunction. -/
def genDisj (τ : Ty) (E W : Type) : Denot E W τ → Denot E W τ → Denot E W τ :=
  match τ with
  | .t => λ x y => x ∨ y
  | .e => λ x _ => x
  | .d => λ x _ => x
  | .fn _ τ' => λ f g => λ x => genDisj τ' E W (f x) (g x)
  | .intens a => λ f g => λ i => genDisj a E W (f i) (g i)

/-- Generalized negation (pointwise complement) — the recursion form of `·ᶜ`,
    needed for negative coordination (`nor` = `¬(A ∨ B)`). Junk at `.e`. -/
def genNeg (τ : Ty) (E W : Type) : Denot E W τ → Denot E W τ :=
  match τ with
  | .t => λ p => ¬p
  | .e => λ x => x
  | .d => λ x => x
  | .fn _ τ' => λ f => λ x => genNeg τ' E W (f x)
  | .intens a => λ f => λ i => genNeg a E W (f i)

theorem genConj_at_t (E W : Type) (p q : Prop) :
    genConj .t E W p q = (p ∧ q) := rfl

theorem genConj_at_et (E W : Type) (f g : E → Prop) :
    genConj (.fn .e .t) E W f g = λ x => f x ∧ g x := rfl

theorem genConj_at_eet (E W : Type) (f g : E → E → Prop) :
    genConj (.fn .e (.fn .e .t)) E W f g = λ x y => f x y ∧ g x y := rfl

/-- At intension types, conjunction is pointwise over indices. -/
theorem genConj_at_intens (E W : Type) {a : Ty}
    (f g : Denot E W (.intens a)) :
    genConj (.intens a) E W f g = λ i => genConj a E W (f i) (g i) := rfl

theorem genConj_comm_t (E W : Type) (p q : Prop) :
    genConj .t E W p q = genConj .t E W q p := by
  simp only [genConj]; exact propext And.comm

theorem genConj_assoc_t (E W : Type) (p q r : Prop) :
    genConj .t E W (genConj .t E W p q) r = genConj .t E W p (genConj .t E W q r) := by
  simp only [genConj]; exact propext and_assoc

theorem genDisj_comm_t (E W : Type) (p q : Prop) :
    genDisj .t E W p q = genDisj .t E W q p := by
  simp only [genDisj]; exact propext Or.comm

/-!
## [partee-rooth-1983] Key Facts

- Fact 6a: `φ ∩ ψ = λz[φ(z) ∩ ψ(z)]`
- Fact 6b: `[φ ∩ ψ](α) = φ(α) ∩ ψ(α)`
- Fact 6c: `λv.φ ∩ λv.ψ = λv[φ ∩ ψ]`
-/

/-- Fact 6a: `φ ∩ ψ = λz[φ(z) ∩ ψ(z)]` -/
theorem genConj_pointwise {E W : Type} {σ τ : Ty}
    (f g : Denot E W (σ ⇒ τ)) :
    genConj (σ ⇒ τ) E W f g = λ x => genConj τ E W (f x) (g x) := rfl

/-- Fact 6b: `[φ ∩ ψ](α) = φ(α) ∩ ψ(α)` -/
theorem genConj_distributes_over_app {E W : Type} {σ τ : Ty}
    (f g : Denot E W (σ ⇒ τ)) (x : Denot E W σ) :
    genConj (σ ⇒ τ) E W f g x = genConj τ E W (f x) (g x) := rfl

/-- Fact 6c: `λv.φ ∩ λv.ψ = λv[φ ∩ ψ]` -/
theorem genConj_lambda_distribution {E W : Type} {σ τ : Ty}
    (f g : Denot E W σ → Denot E W τ) :
    genConj (σ ⇒ τ) E W f g = λ v => genConj τ E W (f v) (g v) := rfl

theorem genDisj_distributes_over_app {E W : Type} {σ τ : Ty}
    (f g : Denot E W (σ ⇒ τ)) (x : Denot E W σ) :
    genDisj (σ ⇒ τ) E W f g x = genDisj τ E W (f x) (g x) := rfl

theorem genDisj_lambda_distribution {E W : Type} {σ τ : Ty}
    (f g : Denot E W σ → Denot E W τ) :
    genDisj (σ ⇒ τ) E W f g = λ v => genDisj τ E W (f v) (g v) := rfl

-- ════════════════════════════════════════════════════════════════
-- § Type-Raising and Coordination
-- ════════════════════════════════════════════════════════════════

section TypeRaising

/-- Type-raise an entity to a GQ: `e ↦ λP.P(e)` -/
def typeRaise {E W : Type} (e : Denot E W .e) : Denot E W ((.e ⇒ .t) ⇒ .t) :=
  λ p => p e

/-- Coordinated entities: `λP. P(e₁) ∧ P(e₂)` -/
def coordEntities {E W : Type} (e1 e2 : Denot E W .e) : Denot E W ((.e ⇒ .t) ⇒ .t) :=
  genConj ((.e ⇒ .t) ⇒ .t) E W (typeRaise e1) (typeRaise e2)

theorem typeRaise_preserves {E W : Type} (e : Denot E W .e) (p : Denot E W (.e ⇒ .t)) :
    typeRaise e p = p e := rfl

theorem coordEntities_both_satisfy {E W : Type} (e1 e2 : Denot E W .e)
    (p : Denot E W (.e ⇒ .t)) :
    coordEntities e1 e2 p = (p e1 ∧ p e2) := rfl

end TypeRaising

-- ════════════════════════════════════════════════════════════════
-- § M&S Decomposition: ☉ + MU (INCL) + J
-- ════════════════════════════════════════════════════════════════

/-!
## [mitrovic-sauerland-2014] [mitrovic-sauerland-2016] Decomposition

DP conjunction decomposes into three operations:
- ☉ (`msShift`): individual → singleton set (= Partee's `ident`)
- MU (`typeRaise`): singleton set → GQ via subset inclusion (INCL)
- J (`genConj`): generalized conjunction on GQs
-/

section MSDecomposition

/-- ☉: M&S type-shifter. Individual → singleton property. -/
def msShift {E W : Type} (x : Denot E W .e) : Denot E W (.e ⇒ .t) :=
  λ y => x = y

/-- MU particle semantics = typeRaise. -/
abbrev inclFunc {E W : Type} (x : Denot E W .e) : Denot E W ((.e ⇒ .t) ⇒ .t) :=
  typeRaise x

/-- Full M&S derivation: J(MU(e₁), MU(e₂)) = coordEntities e₁ e₂. -/
theorem ms_full_derivation {E W : Type} (e1 e2 : Denot E W .e) :
    genConj ((.e ⇒ .t) ⇒ .t) E W (typeRaise e1) (typeRaise e2) =
    coordEntities e1 e2 := rfl

end MSDecomposition

end Intensional.Conjunction
