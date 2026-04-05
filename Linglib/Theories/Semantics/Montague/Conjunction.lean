/-
# Generalized Conjunction

Conjunction and disjunction defined recursively over the type structure:
- Base case: Boolean operations at type `t`
- Recursive case: pointwise application at function types

-/

import Linglib.Theories.Semantics.Montague.Types

namespace Semantics.Montague

/-- A type is conjoinable if it "ends in `t`" (Definition 4). -/
def Ty.isConjoinable : Ty → Bool
  | .t => true
  | .e => false
  | .s => false
  | .fn _ τ => τ.isConjoinable

example : Ty.isConjoinable .t = true := rfl
example : Ty.isConjoinable .e = false := rfl
example : Ty.isConjoinable .s = false := rfl
example : Ty.isConjoinable (.fn .e .t) = true := rfl
example : Ty.isConjoinable (.fn .e (.fn .e .t)) = true := rfl
example : Ty.isConjoinable (.fn .e .e) = false := rfl
example : Ty.isConjoinable (.fn .s .t) = true := rfl

namespace Conjunction

/-- Generalized conjunction (Definition 5). -/
def genConj (τ : Ty) (m : Model) : m.interpTy τ → m.interpTy τ → m.interpTy τ :=
  match τ with
  | .t => λ x y => x && y
  | .e => λ x _ => x
  | .s => λ x _ => x
  | .fn _ τ' => λ f g => λ x => genConj τ' m (f x) (g x)

/-- Generalized disjunction. -/
def genDisj (τ : Ty) (m : Model) : m.interpTy τ → m.interpTy τ → m.interpTy τ :=
  match τ with
  | .t => λ x y => x || y
  | .e => λ x _ => x
  | .s => λ x _ => x
  | .fn _ τ' => λ f g => λ x => genDisj τ' m (f x) (g x)

theorem genConj_at_t (m : Model) (p q : Bool) :
    genConj .t m p q = (p && q) := rfl

theorem genConj_at_et (m : Model) (f g : m.Entity → Bool) :
    genConj (.fn .e .t) m f g = λ x => f x && g x := rfl

theorem genConj_at_eet (m : Model) (f g : m.Entity → m.Entity → Bool) :
    genConj (.fn .e (.fn .e .t)) m f g = λ x y => f x y && g x y := rfl

theorem genConj_comm_t (m : Model) (p q : Bool) :
    genConj .t m p q = genConj .t m q p := by
  simp [genConj, Bool.and_comm]

theorem genConj_assoc_t (m : Model) (p q r : Bool) :
    genConj .t m (genConj .t m p q) r = genConj .t m p (genConj .t m q r) := by
  simp [genConj, Bool.and_assoc]

theorem genDisj_comm_t (m : Model) (p q : Bool) :
    genDisj .t m p q = genDisj .t m q p := by
  simp [genDisj, Bool.or_comm]

/-!
## @cite{partee-rooth-1983} Key Facts
@cite{partee-rooth-1983}

- Fact 6a: `φ ∩ ψ = λz[φ(z) ∩ ψ(z)]`
- Fact 6b: `[φ ∩ ψ](α) = φ(α) ∩ ψ(α)`
- Fact 6c: `λv.φ ∩ λv.ψ = λv[φ ∩ ψ]`
-/

/-- Fact 6a: `φ ∩ ψ = λz[φ(z) ∩ ψ(z)]` -/
theorem genConj_pointwise {m : Model} {σ τ : Ty}
    (f g : m.interpTy (σ ⇒ τ)) :
    genConj (σ ⇒ τ) m f g = λ x => genConj τ m (f x) (g x) := rfl

/-- Fact 6b: `[φ ∩ ψ](α) = φ(α) ∩ ψ(α)` -/
theorem genConj_distributes_over_app {m : Model} {σ τ : Ty}
    (f g : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) :
    genConj (σ ⇒ τ) m f g x = genConj τ m (f x) (g x) := rfl

/-- Fact 6c: `λv.φ ∩ λv.ψ = λv[φ ∩ ψ]` -/
theorem genConj_lambda_distribution {m : Model} {σ τ : Ty}
    (f g : m.interpTy σ → m.interpTy τ) :
    genConj (σ ⇒ τ) m f g = λ v => genConj τ m (f v) (g v) := rfl

theorem genDisj_distributes_over_app {m : Model} {σ τ : Ty}
    (f g : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) :
    genDisj (σ ⇒ τ) m f g x = genDisj τ m (f x) (g x) := rfl

theorem genDisj_lambda_distribution {m : Model} {σ τ : Ty}
    (f g : m.interpTy σ → m.interpTy τ) :
    genDisj (σ ⇒ τ) m f g = λ v => genDisj τ m (f v) (g v) := rfl

section TypeRaising

/-- Type-raise an entity to a GQ: `e ↦ λP.P(e)` -/
def typeRaise {m : Model} (e : m.interpTy .e) : m.interpTy ((.e ⇒ .t) ⇒ .t) :=
  λ p => p e

/-- Coordinated entities: `λP. P(e₁) ∧ P(e₂)` -/
def coordEntities {m : Model} (e1 e2 : m.interpTy .e) : m.interpTy ((.e ⇒ .t) ⇒ .t) :=
  genConj ((.e ⇒ .t) ⇒ .t) m (typeRaise e1) (typeRaise e2)

theorem typeRaise_preserves {m : Model} (e : m.interpTy .e) (p : m.interpTy (.e ⇒ .t)) :
    typeRaise e p = p e := rfl

theorem coordEntities_both_satisfy {m : Model} (e1 e2 : m.interpTy .e)
    (p : m.interpTy (.e ⇒ .t)) :
    coordEntities e1 e2 p = (p e1 && p e2) := rfl

end TypeRaising

-- ============================================================================
-- § M&S Decomposition: ☉ + MU (INCL) + J
-- ============================================================================

/-!
## @cite{mitrovic-sauerland-2014} @cite{mitrovic-sauerland-2016} Decomposition

DP conjunction decomposes into three operations:
- ☉ (`msShift`): individual → singleton set (= Partee's `ident`)
- MU (`inclFunc`): singleton set → GQ via subset inclusion (INCL)
- J (`genConj`): generalized conjunction on GQs

The composition MU ∘ ☉ = `typeRaise`. The full derivation
"DP₁ and DP₂ VP" via ☉ + MU + J recovers `coordEntities`.

### Connection to @cite{link-1983} Distributivity

`coordEntities e1 e2 P = P(e1) ∧ P(e2)` is the two-atom instance of
Link's distributive inference: for distributive P, `*P(e1 ⊕ e2)` holds
iff P holds of every atom-part. Each MU application checks one atom;
J conjoins the checks. See `Semantics.Lexical.Plural.Link1983.distr_atom_part`.
-/

section MSDecomposition

/-- ☉: M&S type-shifter. Individual → singleton property.
    ☉(x) = λy.[y = x] = the characteristic function of {x}.
    Identical to @cite{partee-1987}'s `ident` in TypeShifting.lean. -/
def msShift {m : Model} (x : m.interpTy .e) : m.interpTy (.e ⇒ .t) :=
  λ y => @decide (x = y) (m.decEq x y)

/-- MU particle semantics: INCL (subset inclusion).
    For a singleton set from ☉(x), INCL({x})(P) = P(x).

    The general definition would be INCL(S)(P) = ∀y. S(y) → P(y),
    but M&S only apply MU to ☉-shifted individuals (singletons),
    where subset inclusion reduces to direct predicate application.
    We define `inclFunc` at this reduced type. -/
def inclFunc {m : Model} (x : m.interpTy .e) : m.interpTy ((.e ⇒ .t) ⇒ .t) :=
  λ P => P x

/-- MU ∘ ☉ = typeRaise: the M&S roundtrip through singleton
    formation and subset checking is just type-raising. -/
theorem ms_inclFunc_eq_typeRaise {m : Model} (x : m.interpTy .e) :
    inclFunc x = typeRaise x := rfl

/-- Full M&S derivation via named operations:
    J(MU(☉(e₁)), MU(☉(e₂))) = coordEntities e₁ e₂ -/
theorem ms_full_derivation {m : Model} (e1 e2 : m.interpTy .e) :
    genConj ((.e ⇒ .t) ⇒ .t) m (inclFunc e1) (inclFunc e2) =
    coordEntities e1 e2 := rfl

end MSDecomposition

section Examples

def tall_sem : toyModel.interpTy (.fn .e .t) :=
  λ x => match x with
    | .john => true
    | .mary => false
    | _ => false

def happy_sem : toyModel.interpTy (.fn .e .t) :=
  λ x => match x with
    | .john => true
    | .mary => true
    | _ => false

def tall_and_happy : toyModel.interpTy (.fn .e .t) :=
  genConj (.fn .e .t) toyModel tall_sem happy_sem

#guard tall_and_happy ToyEntity.john
#guard !tall_and_happy ToyEntity.mary

theorem tall_and_happy_is_pointwise :
    tall_and_happy = λ x => tall_sem x && happy_sem x := rfl

end Examples

end Semantics.Montague.Conjunction
