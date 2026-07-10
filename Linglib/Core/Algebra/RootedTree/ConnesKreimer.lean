/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option autoImplicit false

/-!
# Connes-Kreimer Hopf algebra carrier on n-ary rooted trees

The **Connes-Kreimer Hopf algebra** on a tree type `T`
([connes-kreimer-1998]; [foissy-introduction-hopf-algebras-trees] §1.2) is
the formal `R`-linear
span of forests (multisets of trees), with product = forest disjoint union
and coproduct = sum over admissible cuts (defined in `Coproduct/Pruning.lean`
for Δ^ρ, `Coproduct/Trace.lean` for Δ^c). This file provides the **carrier
and counit** generic over `T` — nothing here pattern-matches on the tree
carrier. Realized specializations:

* `T = RoseTree α` — planar n-ary rooted trees
  (`Core/Data/RoseTree/Basic.lean`); the sibling coproduct files
  instantiate here.
* `T = RootedTree.Nonplanar α` (`Quotient RoseTree.isSetoid`) — nonplanar
  rooted trees; the `Bialgebra`/`HopfAlgebra` instances live on this
  specialization (`Coproduct/PruningDuality.lean`,
  `HopfAlgebraNonplanar.lean`), and at `α = SOLabel` it carries the Merge
  workspace algebra of `Syntax/Minimalist/Workspace/Basic.lean`
  ([marcolli-chomsky-berwick-2025] §1.2).

## Main declarations

* `RootedTree.Forest`: forests as multisets of trees; multiset addition is
  disjoint union.
* `RootedTree.ConnesKreimer`: one-field wrapper around
  `AddMonoidAlgebra R (Forest T)`.
* `ConnesKreimer.single`, `ConnesKreimer.of'`, `ConnesKreimer.ofTree`,
  `ConnesKreimer.coeff`: basis embeddings and coefficient extraction.
* `ConnesKreimer.lift`, `ConnesKreimer.algHom_ext`,
  `ConnesKreimer.addHom_ext`, `ConnesKreimer.linearLift`: the
  wrapper-native hom API.
* `ConnesKreimer.counit`: the counit ε (coefficient of the empty forest)
  as an algebra hom.

## Implementation notes

`ConnesKreimer R T` wraps `AddMonoidAlgebra R (Forest T)` as a one-field
structure rather than a `def`-synonym, for the same reason mathlib's
`Polynomial R` wraps `AddMonoidAlgebra R ℕ`:

* the admissible-cut `Bialgebra` cannot live on the bare carrier —
  mathlib's group-like `AddMonoidAlgebra.instBialgebra` already occupies it;
* a `def`-synonym's forwarded instances leave the parent type's instance
  paths reachable, yielding an `SMul ℤ` diamond (two routes:
  `Algebra ℤ → Module ℤ → SMul ℤ` vs `AddCommGroup → SubNegMonoid → zsmul`).

All operations are defined on the `toFinsupp` field and the instance stack
is built by injective transport from a **single** bottom instance
(`instCommSemiring`; a separate `AddCommMonoid` bottom would itself be a
parallel path). The `CommRing`/`AddCommGroup` instance is a safe **global**
instance — its `zsmul` is the pulled-back structural operation and no
alternative path exists.

Consumers should speak the wrapper-native API — `of'`, `ofTree`, `single`,
`coeff`, `lift`, `algHom_ext`, `addHom_ext`, `counit`, and the
`toFinsupp_*` pushforward lemmas — rather than applying
`AddMonoidAlgebra`/`Finsupp` lemmas to `ConnesKreimer` values directly;
`toFinsuppAlgEquiv` is the bridge for wholesale transport.

`[UPSTREAM]` candidate; the upstream home would sit alongside
`Mathlib.RingTheory.HopfAlgebra`.
-/

noncomputable section

namespace RootedTree

/-! ## Forests

A **forest** is a multiset of trees. Multiset addition is the disjoint
union (forest concatenation). -/

/-- A forest of T-shaped trees: finite multiset. -/
abbrev Forest (T : Type*) : Type _ := Multiset T

/-! ## The carrier -/

/-- The **Connes-Kreimer Hopf algebra** on tree type T: a one-field wrapper
    around `AddMonoidAlgebra R (Forest T)`. As an algebra: product = forest
    disjoint union (commutative), unit = empty forest. The Bialgebra
    structure (coproduct + coassoc + counit laws) is in sibling files. -/
structure ConnesKreimer (R : Type*) [CommSemiring R] (T : Type*) where
  /-- Wrap an `AddMonoidAlgebra` as a Connes-Kreimer element. -/
  ofFinsupp ::
  /-- The underlying forest-indexed `Finsupp`. -/
  toFinsupp : AddMonoidAlgebra R (Forest T)

namespace ConnesKreimer

variable {R : Type*} [CommSemiring R] {T : Type*} {S S₁ S₂ : Type*}

theorem toFinsupp_injective :
    Function.Injective (toFinsupp : ConnesKreimer R T → AddMonoidAlgebra R (Forest T)) :=
  fun ⟨_⟩ ⟨_⟩ h => congrArg ofFinsupp h

@[simp] theorem toFinsupp_inj {p q : ConnesKreimer R T} :
    p.toFinsupp = q.toFinsupp ↔ p = q := toFinsupp_injective.eq_iff

@[ext] theorem ext {p q : ConnesKreimer R T} (h : p.toFinsupp = q.toFinsupp) : p = q :=
  toFinsupp_injective h

@[simp] theorem ofFinsupp_toFinsupp (p : ConnesKreimer R T) : ⟨p.toFinsupp⟩ = p := rfl

/-! ### Structural operations

Each operation is defined on the `toFinsupp` field; the `toFinsupp_*`
pushforward lemmas are all `rfl` and form the simp normal form. -/

instance : Zero (ConnesKreimer R T) := ⟨⟨0⟩⟩
instance : One (ConnesKreimer R T) := ⟨⟨1⟩⟩
instance : Add (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp + q.toFinsupp⟩⟩
instance : Mul (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp * q.toFinsupp⟩⟩
instance smulZeroClass [SMulZeroClass S (AddMonoidAlgebra R (Forest T))] :
    SMulZeroClass S (ConnesKreimer R T) where
  smul s p := ⟨s • p.toFinsupp⟩
  smul_zero s := ext (smul_zero s)
instance : NatCast (ConnesKreimer R T) :=
  ⟨fun n => ⟨(n : AddMonoidAlgebra R (Forest T))⟩⟩
instance : Pow (ConnesKreimer R T) ℕ := ⟨fun p n => ⟨p.toFinsupp ^ n⟩⟩

@[simp] theorem toFinsupp_zero : (0 : ConnesKreimer R T).toFinsupp = 0 := rfl
@[simp] theorem toFinsupp_one : (1 : ConnesKreimer R T).toFinsupp = 1 := rfl
@[simp] theorem toFinsupp_add (p q : ConnesKreimer R T) :
    (p + q).toFinsupp = p.toFinsupp + q.toFinsupp := rfl
@[simp] theorem toFinsupp_mul (p q : ConnesKreimer R T) :
    (p * q).toFinsupp = p.toFinsupp * q.toFinsupp := rfl
@[simp] theorem toFinsupp_smul [SMulZeroClass S (AddMonoidAlgebra R (Forest T))]
    (s : S) (p : ConnesKreimer R T) :
    (s • p).toFinsupp = s • p.toFinsupp := rfl
@[simp] theorem toFinsupp_pow (p : ConnesKreimer R T) (n : ℕ) :
    (p ^ n).toFinsupp = p.toFinsupp ^ n := rfl

/-! ### The instance stack

Built by injective transport from the single bottom `instCommSemiring`. -/

instance instCommSemiring : CommSemiring (ConnesKreimer R T) :=
  fast_instance% toFinsupp_injective.commSemiring _ toFinsupp_zero toFinsupp_one
    toFinsupp_add toFinsupp_mul (fun n p => toFinsupp_smul n p) toFinsupp_pow
    (fun _ => rfl)

/-! Granular action instances (mirroring `Polynomial`): keeping these one
synthesis step away from the underlying carrier lets nested-tensor goals
(`CK ⊗ (CK ⊗ CK)`) resolve without deep pending chains. -/

instance distribSMul [DistribSMul S (AddMonoidAlgebra R (Forest T))] :
    DistribSMul S (ConnesKreimer R T) where
  smul_add s p q := ext (smul_add s p.toFinsupp q.toFinsupp)

instance distribMulAction [Monoid S]
    [DistribMulAction S (AddMonoidAlgebra R (Forest T))] :
    DistribMulAction S (ConnesKreimer R T) where
  one_smul p := ext (one_smul S p.toFinsupp)
  mul_smul s t p := ext (mul_smul s t p.toFinsupp)
  smul_zero s := ext (smul_zero s)
  smul_add s p q := ext (smul_add s p.toFinsupp q.toFinsupp)

instance instModule [Semiring S]
    [Module S (AddMonoidAlgebra R (Forest T))] :
    Module S (ConnesKreimer R T) where
  add_smul s t p := ext (add_smul s t p.toFinsupp)
  zero_smul p := ext (zero_smul S p.toFinsupp)

instance smulCommClass
    [SMulZeroClass S₁ (AddMonoidAlgebra R (Forest T))]
    [SMulZeroClass S₂ (AddMonoidAlgebra R (Forest T))]
    [SMulCommClass S₁ S₂ (AddMonoidAlgebra R (Forest T))] :
    SMulCommClass S₁ S₂ (ConnesKreimer R T) :=
  ⟨fun s t p => ext (smul_comm s t p.toFinsupp)⟩

instance isScalarTower [SMul S₁ S₂]
    [SMulZeroClass S₁ (AddMonoidAlgebra R (Forest T))]
    [SMulZeroClass S₂ (AddMonoidAlgebra R (Forest T))]
    [IsScalarTower S₁ S₂ (AddMonoidAlgebra R (Forest T))] :
    IsScalarTower S₁ S₂ (ConnesKreimer R T) :=
  ⟨fun s t p => ext (smul_assoc s t p.toFinsupp)⟩

instance instAlgebra : Algebra R (ConnesKreimer R T) where
  algebraMap :=
    { toFun := fun r => ⟨algebraMap R (AddMonoidAlgebra R (Forest T)) r⟩
      map_one' := ext (map_one _)
      map_mul' := fun r s => ext (map_mul _ r s)
      map_zero' := ext (map_zero _)
      map_add' := fun r s => ext (map_add _ r s) }
  commutes' r x := ext (Algebra.commutes r x.toFinsupp)
  smul_def' r x := ext (Algebra.smul_def r x.toFinsupp)

@[simp] theorem toFinsupp_algebraMap (r : R) :
    (algebraMap R (ConnesKreimer R T) r).toFinsupp
      = algebraMap R (AddMonoidAlgebra R (Forest T)) r := rfl

/-- Coefficient lookup: a Connes-Kreimer element is a function from forests
    to coefficients. -/
instance instFunLike : FunLike (ConnesKreimer R T) (Forest T) R where
  coe p := (p.toFinsupp : Forest T →₀ R)
  coe_injective := fun _ _ h => ext (DFunLike.coe_injective (F := Forest T →₀ R) h)

/-! ### Global ring instance

`zsmul` is the pulled-back structural operation and no parent-type path to
`SMul ℤ` exists, so the instance is safely global. -/

section Ring
variable {R : Type*} [CommRing R] {T : Type*}

instance instNeg : Neg (ConnesKreimer R T) := ⟨fun p => ⟨-p.toFinsupp⟩⟩
instance instSub : Sub (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp - q.toFinsupp⟩⟩
instance instIntCast : IntCast (ConnesKreimer R T) :=
  ⟨fun z => ⟨(z : AddMonoidAlgebra R (Forest T))⟩⟩

@[simp] theorem toFinsupp_neg (p : ConnesKreimer R T) :
    (-p).toFinsupp = -p.toFinsupp := rfl
@[simp] theorem toFinsupp_sub (p q : ConnesKreimer R T) :
    (p - q).toFinsupp = p.toFinsupp - q.toFinsupp := rfl
instance instCommRing : CommRing (ConnesKreimer R T) :=
  fast_instance% toFinsupp_injective.commRing _ toFinsupp_zero toFinsupp_one
    toFinsupp_add toFinsupp_mul toFinsupp_neg toFinsupp_sub
    (fun n p => toFinsupp_smul n p) (fun z p => toFinsupp_smul z p)
    toFinsupp_pow (fun _ => rfl) (fun _ => rfl)

end Ring

/-! ### The algebra equivalence to the bare carrier -/

/-- `toFinsupp` as an `R`-algebra equivalence — the sanctioned bridge between
    the wrapper and the bare `AddMonoidAlgebra`. -/
def toFinsuppAlgEquiv :
    ConnesKreimer R T ≃ₐ[R] AddMonoidAlgebra R (Forest T) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add
  commutes' _ := rfl

@[simp] theorem toFinsuppAlgEquiv_apply (p : ConnesKreimer R T) :
    toFinsuppAlgEquiv p = p.toFinsupp := rfl

@[simp] theorem toFinsuppAlgEquiv_symm_apply (x : AddMonoidAlgebra R (Forest T)) :
    (toFinsuppAlgEquiv (R := R) (T := T)).symm x = ⟨x⟩ := rfl

/-! ## Basis embeddings -/

/-- Basis vector: coefficient `r` on the forest `F`. -/
def single (F : Forest T) (r : R) : ConnesKreimer R T :=
  ⟨Finsupp.single F r⟩

@[simp] theorem toFinsupp_single (F : Forest T) (r : R) :
    (single F r).toFinsupp = Finsupp.single F r := rfl

theorem smul_single_one (F : Forest T) (r : R) :
    single F r = r • single F (1 : R) := by
  ext; simp

/-- Linear induction: prove `p` at `0`, under `+`, and on every `single`. -/
@[elab_as_elim]
theorem induction_linear {p : ConnesKreimer R T → Prop} (x : ConnesKreimer R T)
    (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (single : ∀ (F : Forest T) (r : R), p (ConnesKreimer.single F r)) : p x := by
  have h : ∀ y : AddMonoidAlgebra R (Forest T), p ⟨y⟩ := fun y =>
    Finsupp.induction_linear y zero (fun f g hf hg => add ⟨f⟩ ⟨g⟩ hf hg) single
  exact h x.toFinsupp

/-- **Bare embedding**: a forest as the basis vector `single F 1`. -/
def of' (F : Forest T) : ConnesKreimer R T := single F 1

/-- **MonoidHom embedding**: `Multiplicative (Forest T) →* ConnesKreimer R T`,
    multiplicative by construction as `AddMonoidAlgebra.of` transported through
    the wrapper equivalence. -/
def of : Multiplicative (Forest T) →* ConnesKreimer R T :=
  (toFinsuppAlgEquiv (R := R) (T := T)).symm.toAlgHom.toMonoidHom'.comp
    (AddMonoidAlgebra.of R (Forest T))

/-- Embed a single tree as a singleton-forest basis vector. -/
def ofTree (t : T) : ConnesKreimer R T :=
  of' ({t} : Forest T)

theorem of_apply (F : Multiplicative (Forest T)) :
    (of (R := R) F : ConnesKreimer R T) = of' F.toAdd := rfl

theorem toFinsupp_of' (F : Forest T) :
    (of' (R := R) F : ConnesKreimer R T).toFinsupp = Finsupp.single F 1 := rfl

@[simp] theorem of'_zero :
    (of' (R := R) (0 : Forest T) : ConnesKreimer R T) = 1 :=
  (of (R := R) (T := T)).map_one

/-- Headline algebraic fact: forest disjoint union ↔ algebra product. -/
@[simp] theorem of'_add (F G : Forest T) :
    (of' (R := R) (F + G) : ConnesKreimer R T)
      = of' (R := R) F * of' (R := R) G :=
  (of (R := R) (T := T)).map_mul (Multiplicative.ofAdd F) (Multiplicative.ofAdd G)

@[simp] theorem of'_singleton (t : T) :
    (of' (R := R) ({t} : Forest T) : ConnesKreimer R T) = ofTree t := rfl

/-! ### Coefficients

`coeff` is the simp-normal spelling of coefficient extraction
(`Polynomial.coeff` analogue); the `FunLike` application `p F` reduces to it. -/

/-- The coefficient of the forest `F`. -/
def coeff (p : ConnesKreimer R T) (F : Forest T) : R := p.toFinsupp F

@[simp] theorem coe_apply (p : ConnesKreimer R T) (F : Forest T) :
    p F = p.coeff F := rfl

theorem coeff_def (p : ConnesKreimer R T) (F : Forest T) :
    p.coeff F = p.toFinsupp F := rfl

@[simp] theorem coeff_zero (F : Forest T) : (0 : ConnesKreimer R T).coeff F = 0 := rfl

@[simp] theorem coeff_add (p q : ConnesKreimer R T) (F : Forest T) :
    (p + q).coeff F = p.coeff F + q.coeff F :=
  Finsupp.add_apply p.toFinsupp q.toFinsupp F

@[simp] theorem coeff_smul [SMulZeroClass S R] (s : S)
    (p : ConnesKreimer R T) (F : Forest T) :
    (s • p).coeff F = s • p.coeff F :=
  Finsupp.smul_apply s p.toFinsupp F

theorem coeff_single (F G : Forest T) (r : R) [Decidable (F = G)] :
    (single F r).coeff G = if F = G then r else 0 := by
  rw [coeff_def, toFinsupp_single, Finsupp.single_apply]

@[simp] theorem coeff_single_same (F : Forest T) (r : R) :
    (single F r).coeff F = r := Finsupp.single_eq_same

theorem coeff_of' (F G : Forest T) [Decidable (F = G)] :
    (of' (R := R) F).coeff G = if F = G then 1 else 0 := coeff_single F G 1

/-- Elements agreeing coefficientwise are equal. -/
theorem ext_coeff {p q : ConnesKreimer R T} (h : ∀ F, p.coeff F = q.coeff F) : p = q :=
  ext (Finsupp.ext h)

/-- `coeff` bundled as a linear functional (`Polynomial.lcoeff` analogue). -/
def lcoeff (F : Forest T) : ConnesKreimer R T →ₗ[R] R where
  toFun p := p.coeff F
  map_add' p q := coeff_add p q F
  map_smul' s p := coeff_smul s p F

@[simp] theorem lcoeff_apply (F : Forest T) (p : ConnesKreimer R T) :
    lcoeff F p = p.coeff F := rfl

/-! ## Lifts and hom extensionality

Consumers use these instead of reaching for `AddMonoidAlgebra.lift` /
`Finsupp.addHom_ext` on the bare carrier. -/

section Lift
variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- Lift a monoid hom off the forest monoid to an algebra hom off the
    Connes-Kreimer algebra (the wrapper-native `AddMonoidAlgebra.lift`). -/
def lift (f : Multiplicative (Forest T) →* A) :
    ConnesKreimer R T →ₐ[R] A :=
  (AddMonoidAlgebra.lift R A (Forest T) f).comp toFinsuppAlgEquiv.toAlgHom

@[simp] theorem lift_of' (f : Multiplicative (Forest T) →* A) (F : Forest T) :
    lift f (of' (R := R) F) = f (Multiplicative.ofAdd F) := by
  show AddMonoidAlgebra.lift R A (Forest T) f (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]

/-- Algebra homs off `ConnesKreimer` agree if they agree on `of'`. -/
theorem algHom_ext {φ ψ : ConnesKreimer R T →ₐ[R] A}
    (h : ∀ F : Forest T, φ (of' F) = ψ (of' F)) : φ = ψ := by
  have key : φ.comp toFinsuppAlgEquiv.symm.toAlgHom
      = ψ.comp toFinsuppAlgEquiv.symm.toAlgHom :=
    AddMonoidAlgebra.algHom_ext fun F => h F
  ext p
  simpa using DFunLike.congr_fun key p.toFinsupp

end Lift

/-- `ofFinsupp` as an `AddMonoidHom` (transport vehicle for `addHom_ext`). -/
def ofFinsuppAddHom :
    AddMonoidAlgebra R (Forest T) →+ ConnesKreimer R T where
  toFun := ofFinsupp
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Additive homs off `ConnesKreimer` agree if they agree on `single`. -/
theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : ConnesKreimer R T →+ M}
    (h : ∀ (F : Forest T) (r : R), f (single F r) = g (single F r)) : f = g := by
  have key : f.comp ofFinsuppAddHom = g.comp ofFinsuppAddHom :=
    Finsupp.addHom_ext h
  ext p
  exact DFunLike.congr_fun key p.toFinsupp

section LinearApi
variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- Linear maps off `ConnesKreimer` agree if they agree on `single`. -/
theorem lhom_ext {f g : ConnesKreimer R T →ₗ[R] M}
    (h : ∀ (F : Forest T) (r : R), f (single F r) = g (single F r)) : f = g :=
  LinearMap.toAddMonoidHom_injective (addHom_ext h)

/-- Linear maps off `ConnesKreimer` agree if they agree on the basis `of'`. -/
theorem lhom_ext' {f g : ConnesKreimer R T →ₗ[R] M}
    (h : ∀ F : Forest T, f (of' F) = g (of' F)) : f = g :=
  lhom_ext fun F r => by
    rw [smul_single_one, map_smul, map_smul]
    exact congrArg (r • ·) (h F)

/-- Linearly extend a function off the forest basis
    (wrapper-native `Finsupp.lift`). -/
def linearLift (f : Forest T → M) : ConnesKreimer R T →ₗ[R] M :=
  (Finsupp.lift M R (Forest T) f).comp
    (toFinsuppAlgEquiv (R := R) (T := T)).toLinearEquiv.toLinearMap

@[simp] theorem linearLift_single (f : Forest T → M) (F : Forest T) (r : R) :
    linearLift f (single F r) = r • f F := by
  show Finsupp.lift M R (Forest T) f (Finsupp.single F r) = r • f F
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]

@[simp] theorem linearLift_of' (f : Forest T → M) (F : Forest T) :
    linearLift f (of' (R := R) F) = f F := by
  rw [of', linearLift_single, one_smul]

end LinearApi

/-- Transport a forest-monoid hom to an algebra hom between Connes-Kreimer
    algebras (wrapper-native `AddMonoidAlgebra.mapDomainAlgHom`). -/
def mapDomainAlgHom {T' : Type*} (f : Forest T →+ Forest T') :
    ConnesKreimer R T →ₐ[R] ConnesKreimer R T' :=
  ((toFinsuppAlgEquiv (R := R) (T := T')).symm.toAlgHom.comp
    (AddMonoidAlgebra.mapDomainAlgHom R R f)).comp
    (toFinsuppAlgEquiv (R := R) (T := T)).toAlgHom

@[simp] theorem mapDomainAlgHom_of' {T' : Type*} (f : Forest T →+ Forest T')
    (F : Forest T) :
    mapDomainAlgHom (R := R) f (of' F) = of' (f F) := by
  refine ext ?_
  show Finsupp.mapDomain f (Finsupp.single F 1) = Finsupp.single (f F) 1
  rw [Finsupp.mapDomain_single]

/-! ### The forest basis -/

/-- The forests, via `of'`, as an `R`-basis of the Connes-Kreimer algebra
    (`Polynomial.basisMonomials` analogue). -/
def basisSingleOne :
    Module.Basis (Forest T) R (ConnesKreimer R T) :=
  Module.Basis.map Finsupp.basisSingleOne
    (toFinsuppAlgEquiv (R := R) (T := T)).symm.toLinearEquiv

@[simp] theorem basisSingleOne_apply (F : Forest T) :
    (basisSingleOne : Module.Basis (Forest T) R (ConnesKreimer R T)) F = of' F := by
  simp only [basisSingleOne, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  rfl

/-! ## The counit

The counit ε : ConnesKreimer R T → R extracts the coefficient of the
empty forest, packaged as an algebra hom. -/

/-- The counit as a monoid hom: the indicator of the empty forest, expressed
    as `0 ^ card` (so `0 ^ 0 = 1`, `0 ^ n = 0`) — multiplicativity is
    `pow_add`, and no `DecidableEq T` is needed. -/
def counitMonoidHom : Multiplicative (Forest T) →* R where
  toFun F := 0 ^ F.toAdd.card
  map_one' := pow_zero 0
  map_mul' F G := by rw [toAdd_mul, Multiset.card_add, pow_add]

/-- The **counit** on `ConnesKreimer R T` as an algebra hom. -/
def counit : ConnesKreimer R T →ₐ[R] R :=
  lift counitMonoidHom

/-- `counit (of' F) = if F.card = 0 then 1 else 0`. The `card`
    formulation avoids needing `DecidableEq T`. -/
@[simp] theorem counit_of' (F : Forest T) :
    (counit : ConnesKreimer R T →ₐ[R] R) (of' F)
      = (if F.card = 0 then 1 else 0 : R) := by
  rw [counit, lift_of']
  exact zero_pow_eq F.card

@[simp] theorem counit_one :
    (counit : ConnesKreimer R T →ₐ[R] R) 1 = 1 := map_one _

@[simp] theorem counit_ofTree (t : T) :
    (counit : ConnesKreimer R T →ₐ[R] R) (ofTree t) = 0 := by
  rw [← of'_singleton, counit_of', Multiset.card_singleton, if_neg one_ne_zero]

end ConnesKreimer

end RootedTree

end
