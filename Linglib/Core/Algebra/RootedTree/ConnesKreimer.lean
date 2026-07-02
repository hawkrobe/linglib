import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Multiset.Basic

set_option autoImplicit false

/-!
# Connes-Kreimer Hopf algebra carrier on n-ary rooted trees
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The **Connes-Kreimer Hopf algebra** on a tree type T is the formal
R-linear combinations of forests (multisets of trees), with product =
forest disjoint union and coproduct = sum over admissible cuts (defined
in `Coproduct/Pruning.lean` for Δ^ρ, `Coproduct/Trace.lean` for Δ^c).

This file provides the **carrier and counit** generic over a tree type T
(parameterized over `Type*`) — nothing here pattern-matches on the tree
carrier. The intended specializations:

- `T = RoseTree α` — n-ary rooted trees (the root-level carrier in
  `Linglib/Core/Data/RoseTree/Basic.lean`; the sibling coproduct files
  instantiate here).
- `T = RootedTree.Nonplanar α` — n-ary nonplanar rooted trees
  (`Nonplanar α := Quotient RoseTree.instSetoid`, a quotient of `RoseTree α`).

The product structure (algebra) doesn't depend on which T is used —
forests are multisets, multiset addition is commutative (Hopf
algebra is commutative). The coproduct depends on the cut substrate
of T; see sibling files for specific instantiations.

## The one-field structure (`Polynomial` playbook)

`ConnesKreimer R T` wraps `AddMonoidAlgebra R (Forest T)` as a one-field
structure rather than a `def`-synonym, for the same reason mathlib's
`Polynomial R` wraps `AddMonoidAlgebra R ℕ`:

- the admissible-cut `Bialgebra` cannot live on the bare carrier —
  mathlib's group-like `AddMonoidAlgebra.instBialgebra` already occupies it;
- a `def`-synonym's forwarded instances leave the parent type's instance
  paths reachable, which produced a genuine `SMul ℤ` diamond (two routes:
  `Algebra ℤ → Module ℤ → SMul ℤ` vs `AddCommGroup → SubNegMonoid → zsmul`),
  previously worked around by a `noncomputable def addCommGroupOf` registered
  via `attribute [local instance]` at three consumer sites.

With the structure, all operations are defined on the `toFinsupp` field and
the instance stack is built by injective transport from a **single** bottom
instance (`instCommSemiring`; a separate `AddCommMonoid` bottom would itself
be a parallel path). The `CommRing`/`AddCommGroup` instance is now a safe
**global** instance — its `zsmul` is the pulled-back structural operation and
no alternative path exists, so the diamond is gone by construction.

Consumers should speak the self-contained API — `of'`, `ofTree`, `single`,
`lift`, `algHom_ext`, `addHom_ext`, `counit` — and never name
`AddMonoidAlgebra`/`Finsupp` on `ConnesKreimer` values; `toFinsuppAlgEquiv`
is the sanctioned escape hatch.

## Layer status

`[UPSTREAM]` candidate. No sorries.

## MCB anchor

[marcolli-chomsky-berwick-2025] §1.2 "Workspaces: Product and
Coproduct" introduces the Hopf algebra of workspaces; the carrier is
`V(𝔉_{SO_0}) = AddMonoidAlgebra R (Multiset (FCM α))`. This file
generalizes the carrier to arbitrary tree type T, with binary FCM as
one specialization (eventual Phase B target).

[foissy-introduction-hopf-algebras-trees] §1.2: "The Hopf algebra
H_R is the free associative commutative unitary K-algebra generated
by T", where T is the set of rooted trees. Same structure here, with
T parameterized.

## Naming

Type: `RootedTree.ConnesKreimer R T` with eponymous namespace
`RootedTree.ConnesKreimer`. Eponymous-type-and-namespace pattern matches
mathlib idiom (`Polynomial`, `WittVector`, `PowerSeries`, etc.) — no
abbreviation. The eventual upstream-mathlib home would be
`Mathlib.RingTheory.HopfAlgebra.RootedTree.ConnesKreimer` or similar.
-/

namespace RootedTree

/-! ## §1: Forest type alias

A **forest** is a multiset of trees. Multiset addition is the disjoint
union (forest concatenation). -/

/-- A forest of T-shaped trees: finite multiset. -/
abbrev Forest (T : Type*) : Type _ := Multiset T

/-! ## §2: The Connes-Kreimer Hopf algebra carrier -/

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

variable {R : Type*} [CommSemiring R] {T : Type*}

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

noncomputable instance : Zero (ConnesKreimer R T) := ⟨⟨0⟩⟩
noncomputable instance : One (ConnesKreimer R T) := ⟨⟨1⟩⟩
noncomputable instance : Add (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp + q.toFinsupp⟩⟩
noncomputable instance : Mul (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp * q.toFinsupp⟩⟩
noncomputable instance : SMul R (ConnesKreimer R T) := ⟨fun s p => ⟨s • p.toFinsupp⟩⟩
noncomputable instance : SMul ℕ (ConnesKreimer R T) := ⟨fun n p => ⟨n • p.toFinsupp⟩⟩
noncomputable instance : NatCast (ConnesKreimer R T) :=
  ⟨fun n => ⟨(n : AddMonoidAlgebra R (Forest T))⟩⟩
noncomputable instance : Pow (ConnesKreimer R T) ℕ := ⟨fun p n => ⟨p.toFinsupp ^ n⟩⟩

@[simp] theorem toFinsupp_zero : (0 : ConnesKreimer R T).toFinsupp = 0 := rfl
@[simp] theorem toFinsupp_one : (1 : ConnesKreimer R T).toFinsupp = 1 := rfl
@[simp] theorem toFinsupp_add (p q : ConnesKreimer R T) :
    (p + q).toFinsupp = p.toFinsupp + q.toFinsupp := rfl
@[simp] theorem toFinsupp_mul (p q : ConnesKreimer R T) :
    (p * q).toFinsupp = p.toFinsupp * q.toFinsupp := rfl
@[simp] theorem toFinsupp_smul (s : R) (p : ConnesKreimer R T) :
    (s • p).toFinsupp = s • p.toFinsupp := rfl
@[simp] theorem toFinsupp_nsmul (n : ℕ) (p : ConnesKreimer R T) :
    (n • p).toFinsupp = n • p.toFinsupp := rfl
@[simp] theorem toFinsupp_pow (p : ConnesKreimer R T) (n : ℕ) :
    (p ^ n).toFinsupp = p.toFinsupp ^ n := rfl

/-! ### The instance stack

Built by injective transport from the single bottom `instCommSemiring`. -/

noncomputable instance instCommSemiring : CommSemiring (ConnesKreimer R T) :=
  fast_instance% toFinsupp_injective.commSemiring _ toFinsupp_zero toFinsupp_one
    toFinsupp_add toFinsupp_mul toFinsupp_nsmul toFinsupp_pow (fun _ => rfl)

/-- `toFinsupp` bundled as an `AddMonoidHom` (transport vehicle). -/
noncomputable def toFinsuppAddHom :
    ConnesKreimer R T →+ AddMonoidAlgebra R (Forest T) where
  toFun := toFinsupp
  map_zero' := toFinsupp_zero
  map_add' := toFinsupp_add

noncomputable instance instModule : Module R (ConnesKreimer R T) :=
  fast_instance% toFinsupp_injective.module R toFinsuppAddHom toFinsupp_smul

noncomputable instance instAlgebra : Algebra R (ConnesKreimer R T) where
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
noncomputable instance instFunLike : FunLike (ConnesKreimer R T) (Forest T) R where
  coe p := (p.toFinsupp : Forest T →₀ R)
  coe_injective := fun _ _ h => ext (DFunLike.coe_injective (F := Forest T →₀ R) h)

@[simp] theorem coe_apply (p : ConnesKreimer R T) (F : Forest T) :
    p F = p.toFinsupp F := rfl

/-! ### Global ring instance (the diamond killer)

`zsmul` is the pulled-back structural operation; no parent-type path to
`SMul ℤ` exists, so the former `addCommGroupOf` local-instance hack is
unnecessary — and deleted. -/

section Ring
variable {R : Type*} [CommRing R] {T : Type*}

noncomputable instance instNeg : Neg (ConnesKreimer R T) := ⟨fun p => ⟨-p.toFinsupp⟩⟩
noncomputable instance instSub : Sub (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp - q.toFinsupp⟩⟩
noncomputable instance instSMulZ : SMul ℤ (ConnesKreimer R T) :=
  ⟨fun z p => ⟨z • p.toFinsupp⟩⟩
noncomputable instance instIntCast : IntCast (ConnesKreimer R T) :=
  ⟨fun z => ⟨(z : AddMonoidAlgebra R (Forest T))⟩⟩

@[simp] theorem toFinsupp_neg (p : ConnesKreimer R T) :
    (-p).toFinsupp = -p.toFinsupp := rfl
@[simp] theorem toFinsupp_sub (p q : ConnesKreimer R T) :
    (p - q).toFinsupp = p.toFinsupp - q.toFinsupp := rfl
@[simp] theorem toFinsupp_zsmul (z : ℤ) (p : ConnesKreimer R T) :
    (z • p).toFinsupp = z • p.toFinsupp := rfl

noncomputable instance instCommRing : CommRing (ConnesKreimer R T) :=
  fast_instance% toFinsupp_injective.commRing _ toFinsupp_zero toFinsupp_one
    toFinsupp_add toFinsupp_mul toFinsupp_neg toFinsupp_sub toFinsupp_nsmul
    toFinsupp_zsmul toFinsupp_pow (fun _ => rfl) (fun _ => rfl)

end Ring

/-! ### The algebra equivalence to the bare carrier -/

/-- `toFinsupp` as an `R`-algebra equivalence — the sanctioned bridge between
    the wrapper and the bare `AddMonoidAlgebra`. -/
noncomputable def toFinsuppAlgEquiv :
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

/-! ## §3: Basis embeddings — `single`, `of'`, `ofTree` -/

/-- Basis vector: coefficient `r` on the forest `F`. -/
noncomputable def single (F : Forest T) (r : R) : ConnesKreimer R T :=
  ⟨Finsupp.single F r⟩

@[simp] theorem toFinsupp_single (F : Forest T) (r : R) :
    (single F r).toFinsupp = Finsupp.single F r := rfl

theorem smul_single_one (F : Forest T) (r : R) :
    single F r = r • single F (1 : R) := by
  ext; simp

/-- Linear induction: prove `p` at `0`, under `+`, and on every `single`. -/
@[elab_as_elim]
theorem induction_linear {p : ConnesKreimer R T → Prop} (x : ConnesKreimer R T)
    (h0 : p 0) (hadd : ∀ f g, p f → p g → p (f + g))
    (hsingle : ∀ (F : Forest T) (r : R), p (single F r)) : p x := by
  have h : ∀ y : AddMonoidAlgebra R (Forest T), p ⟨y⟩ := fun y =>
    Finsupp.induction_linear y h0 (fun f g hf hg => hadd ⟨f⟩ ⟨g⟩ hf hg) hsingle
  exact h x.toFinsupp

/-- **Bare embedding**: a forest as the basis vector `single F 1`. -/
noncomputable def of' (F : Forest T) : ConnesKreimer R T := single F 1

/-- **MonoidHom embedding**: `Multiplicative (Forest T) →* ConnesKreimer R T`. -/
noncomputable def of : Multiplicative (Forest T) →* ConnesKreimer R T where
  toFun F := of' (R := R) F.toAdd
  map_one' := ext AddMonoidAlgebra.one_def.symm
  map_mul' F G := ext <| by
    show AddMonoidAlgebra.single (F.toAdd + G.toAdd) (1 : R)
      = AddMonoidAlgebra.single (R := R) (M := Forest T) F.toAdd 1
        * AddMonoidAlgebra.single (R := R) (M := Forest T) G.toAdd 1
    exact (AddMonoidAlgebra.single_mul_single (R := R) (M := Forest T)
      F.toAdd G.toAdd 1 1 |>.trans (by rw [mul_one])).symm

/-- Embed a single tree as a singleton-forest basis vector. -/
noncomputable def ofTree (t : T) : ConnesKreimer R T :=
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

/-! ## §4: `lift`, `algHom_ext`, `addHom_ext` — the self-contained hom API

Consumers use these instead of reaching for `AddMonoidAlgebra.lift` /
`Finsupp.addHom_ext` on the bare carrier. -/

section Lift
variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- Lift a monoid hom off the forest monoid to an algebra hom off the
    Connes-Kreimer algebra (the wrapper-native `AddMonoidAlgebra.lift`). -/
noncomputable def lift (f : Multiplicative (Forest T) →* A) :
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
noncomputable def ofFinsuppAddHom :
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
noncomputable def linearLift (f : Forest T → M) : ConnesKreimer R T →ₗ[R] M :=
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
noncomputable def mapDomainAlgHom {T' : Type*} (f : Forest T →+ Forest T') :
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
noncomputable def basisSingleOne :
    Module.Basis (Forest T) R (ConnesKreimer R T) :=
  Module.Basis.map Finsupp.basisSingleOne
    (toFinsuppAlgEquiv (R := R) (T := T)).symm.toLinearEquiv

@[simp] theorem basisSingleOne_apply (F : Forest T) :
    (basisSingleOne : Module.Basis (Forest T) R (ConnesKreimer R T)) F = of' F := by
  simp only [basisSingleOne, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  rfl

/-! ## §5: Counit

The counit ε : ConnesKreimer R T → R extracts the coefficient of the
empty forest, packaged as an algebra hom. -/

/-- The counit as a `Multiplicative (Forest T) →* R` monoid hom.

    Uses `Multiset.card_eq_zero` to avoid requiring `DecidableEq T`:
    test "is empty" via "has cardinality zero" (card is Nat, decidable). -/
noncomputable def counitMonoidHom :
    Multiplicative (Forest T) →* R where
  toFun F := if F.toAdd.card = 0 then 1 else 0
  map_one' := by
    show (if (0 : Forest T).card = 0 then (1 : R) else 0) = 1
    rw [Multiset.card_zero, if_pos rfl]
  map_mul' F G := by
    show (if (F.toAdd + G.toAdd).card = 0 then (1 : R) else 0)
       = (if F.toAdd.card = 0 then (1 : R) else 0)
       * (if G.toAdd.card = 0 then (1 : R) else 0)
    rw [Multiset.card_add]
    by_cases hF : F.toAdd.card = 0
    · by_cases hG : G.toAdd.card = 0
      · rw [if_pos hF, if_pos hG, if_pos (by rw [hF, hG]), mul_one]
      · rw [if_pos hF, if_neg hG, if_neg (by rw [hF, zero_add]; exact hG), one_mul]
    · by_cases hG : G.toAdd.card = 0
      · rw [if_neg hF, if_pos hG, if_neg (by rw [hG, Nat.add_zero]; exact hF), mul_one]
      · have h : ¬ (F.toAdd.card + G.toAdd.card = 0) :=
          fun h => hF (Nat.add_eq_zero_iff.mp h).1
        rw [if_neg hF, if_neg hG, if_neg h, mul_zero]

/-- The **counit** on `ConnesKreimer R T` as an algebra hom. -/
noncomputable def counit : ConnesKreimer R T →ₐ[R] R :=
  lift counitMonoidHom

/-- `counit (of' F) = if F.card = 0 then 1 else 0`. The `card`
    formulation avoids needing `DecidableEq T`. -/
@[simp] theorem counit_of' (F : Forest T) :
    (counit : ConnesKreimer R T →ₐ[R] R) (of' F)
      = (if F.card = 0 then 1 else 0 : R) := by
  rw [counit, lift_of']
  rfl

@[simp] theorem counit_one :
    (counit : ConnesKreimer R T →ₐ[R] R) 1 = 1 := map_one _

@[simp] theorem counit_ofTree (t : T) :
    (counit : ConnesKreimer R T →ₐ[R] R) (ofTree t) = 0 := by
  unfold ofTree
  rw [counit_of', Multiset.card_singleton]
  exact if_neg (by decide)

end ConnesKreimer

end RootedTree
