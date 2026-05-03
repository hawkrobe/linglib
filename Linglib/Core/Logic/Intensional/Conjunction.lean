import Linglib.Core.IntensionalLogic.Frame

/-!
# Generalized Conjunction

@cite{partee-rooth-1983}

Conjunction and disjunction defined recursively over the IL type structure:
- Base case (`t`): Boolean operations
- Function case (`⟨a,b⟩`): pointwise application
- Intension case (`⟨s,a⟩`): pointwise over indices
-/

namespace Core.IntensionalLogic.Conjunction

open Core.IntensionalLogic

example : Ty.isConjoinable .t = true := rfl
example : Ty.isConjoinable .e = false := rfl
example : Ty.isConjoinable (.fn .e .t) = true := rfl
example : Ty.isConjoinable (.fn .e (.fn .e .t)) = true := rfl
example : Ty.isConjoinable (.fn .e .e) = false := rfl
example : Ty.isConjoinable (.intens .t) = true := rfl
example : Ty.isConjoinable (.intens .e) = false := rfl
example : Ty.isConjoinable (.intens (.e ⇒ .t)) = true := rfl

/-- Generalized conjunction (@cite{partee-rooth-1983} Definition 5).
    At intension types, conjunction is pointwise over indices. -/
def genConj (τ : Ty) (F : Frame) : F.Denot τ → F.Denot τ → F.Denot τ :=
  match τ with
  | .t => λ x y => x ∧ y
  | .e => λ x _ => x
  | .fn _ τ' => λ f g => λ x => genConj τ' F (f x) (g x)
  | .intens a => λ f g => λ i => genConj a F (f i) (g i)

/-- Generalized disjunction. -/
def genDisj (τ : Ty) (F : Frame) : F.Denot τ → F.Denot τ → F.Denot τ :=
  match τ with
  | .t => λ x y => x ∨ y
  | .e => λ x _ => x
  | .fn _ τ' => λ f g => λ x => genDisj τ' F (f x) (g x)
  | .intens a => λ f g => λ i => genDisj a F (f i) (g i)

theorem genConj_at_t (F : Frame) (p q : Prop) :
    genConj .t F p q = (p ∧ q) := rfl

theorem genConj_at_et (F : Frame) (f g : F.Entity → Prop) :
    genConj (.fn .e .t) F f g = λ x => f x ∧ g x := rfl

theorem genConj_at_eet (F : Frame) (f g : F.Entity → F.Entity → Prop) :
    genConj (.fn .e (.fn .e .t)) F f g = λ x y => f x y ∧ g x y := rfl

/-- At intension types, conjunction is pointwise over indices. -/
theorem genConj_at_intens (F : Frame) {a : Ty}
    (f g : F.Denot (.intens a)) :
    genConj (.intens a) F f g = λ i => genConj a F (f i) (g i) := rfl

theorem genConj_comm_t (F : Frame) (p q : Prop) :
    genConj .t F p q = genConj .t F q p := by
  simp only [genConj]; exact propext And.comm

theorem genConj_assoc_t (F : Frame) (p q r : Prop) :
    genConj .t F (genConj .t F p q) r = genConj .t F p (genConj .t F q r) := by
  simp only [genConj]; exact propext and_assoc

theorem genDisj_comm_t (F : Frame) (p q : Prop) :
    genDisj .t F p q = genDisj .t F q p := by
  simp only [genDisj]; exact propext Or.comm

/-!
## @cite{partee-rooth-1983} Key Facts

- Fact 6a: `φ ∩ ψ = λz[φ(z) ∩ ψ(z)]`
- Fact 6b: `[φ ∩ ψ](α) = φ(α) ∩ ψ(α)`
- Fact 6c: `λv.φ ∩ λv.ψ = λv[φ ∩ ψ]`
-/

/-- Fact 6a: `φ ∩ ψ = λz[φ(z) ∩ ψ(z)]` -/
theorem genConj_pointwise {F : Frame} {σ τ : Ty}
    (f g : F.Denot (σ ⇒ τ)) :
    genConj (σ ⇒ τ) F f g = λ x => genConj τ F (f x) (g x) := rfl

/-- Fact 6b: `[φ ∩ ψ](α) = φ(α) ∩ ψ(α)` -/
theorem genConj_distributes_over_app {F : Frame} {σ τ : Ty}
    (f g : F.Denot (σ ⇒ τ)) (x : F.Denot σ) :
    genConj (σ ⇒ τ) F f g x = genConj τ F (f x) (g x) := rfl

/-- Fact 6c: `λv.φ ∩ λv.ψ = λv[φ ∩ ψ]` -/
theorem genConj_lambda_distribution {F : Frame} {σ τ : Ty}
    (f g : F.Denot σ → F.Denot τ) :
    genConj (σ ⇒ τ) F f g = λ v => genConj τ F (f v) (g v) := rfl

theorem genDisj_distributes_over_app {F : Frame} {σ τ : Ty}
    (f g : F.Denot (σ ⇒ τ)) (x : F.Denot σ) :
    genDisj (σ ⇒ τ) F f g x = genDisj τ F (f x) (g x) := rfl

theorem genDisj_lambda_distribution {F : Frame} {σ τ : Ty}
    (f g : F.Denot σ → F.Denot τ) :
    genDisj (σ ⇒ τ) F f g = λ v => genDisj τ F (f v) (g v) := rfl

-- ════════════════════════════════════════════════════════════════
-- § Type-Raising and Coordination
-- ════════════════════════════════════════════════════════════════

section TypeRaising

/-- Type-raise an entity to a GQ: `e ↦ λP.P(e)` -/
def typeRaise {F : Frame} (e : F.Denot .e) : F.Denot ((.e ⇒ .t) ⇒ .t) :=
  λ p => p e

/-- Coordinated entities: `λP. P(e₁) ∧ P(e₂)` -/
def coordEntities {F : Frame} (e1 e2 : F.Denot .e) : F.Denot ((.e ⇒ .t) ⇒ .t) :=
  genConj ((.e ⇒ .t) ⇒ .t) F (typeRaise e1) (typeRaise e2)

theorem typeRaise_preserves {F : Frame} (e : F.Denot .e) (p : F.Denot (.e ⇒ .t)) :
    typeRaise e p = p e := rfl

theorem coordEntities_both_satisfy {F : Frame} (e1 e2 : F.Denot .e)
    (p : F.Denot (.e ⇒ .t)) :
    coordEntities e1 e2 p = (p e1 ∧ p e2) := rfl

end TypeRaising

-- ════════════════════════════════════════════════════════════════
-- § M&S Decomposition: ☉ + MU (INCL) + J
-- ════════════════════════════════════════════════════════════════

/-!
## @cite{mitrovic-sauerland-2014} @cite{mitrovic-sauerland-2016} Decomposition

DP conjunction decomposes into three operations:
- ☉ (`msShift`): individual → singleton set (= Partee's `ident`)
- MU (`typeRaise`): singleton set → GQ via subset inclusion (INCL)
- J (`genConj`): generalized conjunction on GQs
-/

section MSDecomposition

/-- ☉: M&S type-shifter. Individual → singleton property. -/
def msShift {F : Frame} (x : F.Denot .e) : F.Denot (.e ⇒ .t) :=
  λ y => x = y

/-- MU particle semantics = typeRaise. -/
abbrev inclFunc {F : Frame} (x : F.Denot .e) : F.Denot ((.e ⇒ .t) ⇒ .t) :=
  typeRaise x

/-- Full M&S derivation: J(MU(e₁), MU(e₂)) = coordEntities e₁ e₂. -/
theorem ms_full_derivation {F : Frame} (e1 e2 : F.Denot .e) :
    genConj ((.e ⇒ .t) ⇒ .t) F (typeRaise e1) (typeRaise e2) =
    coordEntities e1 e2 := rfl

end MSDecomposition

end Core.IntensionalLogic.Conjunction
