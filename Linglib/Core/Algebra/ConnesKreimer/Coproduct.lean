import Linglib.Core.Algebra.ConnesKreimer.Defs
import Linglib.Core.Combinatorics.RootedTree.AdmissibleCut
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Connes-Kreimer Coproduct on the Bialgebra of Decorated Forests
@cite{marcolli-chomsky-berwick-2025}

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.2.8, the
**contraction coproduct** on the syntactic forest bialgebra is

  Δ^c(T) := T ⊗ 1 + 1 ⊗ T + Σ_{F_v} F_v ⊗ T/^c F_v

where the sum is over all subforests `F_v ⊂ T` consisting of disjoint
accessible terms of T, and T/^c F_v is the contraction-with-trace
remainder (Definition 1.2.4).

Equivalently, identifying the empty cut with the `1 ⊗ T` term:

  Δ^c(T) = T ⊗ 1 + Σ_{c : CutShape T} (cutForest c) ⊗ (remainder c)

This file builds:

- `comulTree T : Hc ⊗[R] Hc` — the tree-level coproduct
- `comulForest F : Hc ⊗[R] Hc` — extension to forests by
  multiplicativity (Δ^c on a forest = product of Δ^c on components,
  per M-C-B `Δ^ω(F) = ⊔_a Δ(T_a)`)
- `comulAlgHom : Hc →ₐ[R] Hc ⊗[R] Hc` — algebra-hom lift via
  `AddMonoidAlgebra.lift` (the algebra-hom property is needed for the
  bialgebra structure per M-C-B Lemma 1.2.10)
- `counit : Hc →ₐ[R] R` — the counit (algebra hom selecting the
  empty-forest coefficient)
- `comulDelAlgHom : Hc →ₐ[R] Hc ⊗[R] Hc` — the deletion coproduct Δ^d
  used by the linguistic Merge action

Naming note: we use `comulAlgHom` rather than `comul` to leave the
short name `comul` available for the eventual `Coalgebra` typeclass
instance field (which takes `Hc →ₗ[R] Hc ⊗ Hc`, the linear-map
projection of `comulAlgHom.toLinearMap`).

The Coalgebra/Bialgebra typeclass instances are NOT declared here —
that's a separate file once coassoc is proven (Foissy-style cuts-of-
cuts bijection or via Lemma 1.2.10's appeal to Connes-Kreimer for
Feynman graphs). The Hopf algebra structure requires the additional
quotient by `(1 - α)` for `α ∈ SO_0` per Lemma 1.2.10.

## Layer status

`[UPSTREAM]` candidate. Future home is something like
`Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.Coproduct`. This file
is part of the Stage 0.5 hoist out of `Theories/Syntax/Minimalist/Hopf/`
(per `scratch/mcb_stage1_plan.md`).

## Mathlib infra leveraged

- `Hc = AddMonoidAlgebra R Forest = (Forest →₀ R)` (from `Defs.lean`)
- `TensorProduct R Hc Hc` with `⊗ₜ` notation
- `Finsupp.single F z : Hc` for basis elements
- `Finsupp.linearCombination` for linear extension from a function on
  basis elements
- `Multiset.prod` for the multiplicative-on-forests extension
- `Finsupp.lapply` for the counit (value at the empty-forest index)
-/

namespace Minimalist.Hopf

open scoped TensorProduct
open Finsupp

variable {R : Type*} [CommRing R] {α : Type} [DecidableEq α]

/-! ## §1: Tree-level coproduct

For a single tree `T : DecoratedTree α`, define the contraction
coproduct as the explicit primitive `T ⊗ 1` plus the sum over
admissible cuts:

  Δ^c(T) = T ⊗ 1 + Σ_{c : CutShape T} (single (cutForest c)) ⊗
                                       (single {remainder c})

The empty cut `CutShape.empty T` contributes the `1 ⊗ T` term
(cutForest = ∅, remainder = T). The explicit `T ⊗ 1` corresponds to
M-C-B's "T as a member of the workspace [T]" primitive — not an
admissible cut, since there is no edge above the root to remove. -/

/-- Inject a forest into the bialgebra as a basis element. The
    singleton-workspace embedding for a single tree `T` is
    `forestToHc {T}`. -/
noncomputable def forestToHc (F : Forest α) : Hc R α :=
  Finsupp.single F (1 : R)

/-- The tree-level Connes-Kreimer coproduct.
    Δ^c(T) = T ⊗ 1 + Σ_c (cutForest c) ⊗ ({remainder c}). -/
noncomputable def comulTree (T : DecoratedTree α) : Hc R α ⊗[R] Hc R α :=
  forestToHc (R := R) ({T} : Forest α) ⊗ₜ[R] (1 : Hc R α)
  +
  ∑ c : CutShape T,
    forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
    forestToHc (R := R) ({CutShape.remainder c} : Forest α)

/-! ## §2: Forest-level coproduct (multiplicative extension)

Per M-C-B equation just above (1.2.10): "The coproduct (1.2.8) is
extended to forests F = ⊔_a T_a in the form Δ^ω(F) = ⊔_a Δ(T_a)."

Multiplication on `Hc ⊗ Hc` is the tensor-product algebra
multiplication, which gives `(a ⊗ b) * (c ⊗ d) = (a*c) ⊗ (b*d)`.
On basis elements this is `single F₁ ⊗ single G₁ * single F₂ ⊗
single G₂ = single (F₁ + F₂) ⊗ single (G₁ + G₂)`. So the
multiplicative extension correctly distributes ⊔ on both channels. -/

/-- The forest-level Connes-Kreimer coproduct: product of tree-level
    coproducts over the components of the forest. -/
noncomputable def comulForest (F : Forest α) : Hc R α ⊗[R] Hc R α :=
  (F.map (comulTree (R := R))).prod

/-! ## §3: Multiplicativity of `comulForest`

Per M-C-B (text just above Lemma 1.2.10): the coproduct on a forest
is the product of coproducts on its components. With `comulForest`
defined as `Multiset.prod (F.map comulTree)`, this is structurally
true: `Multiset.prod` is multiplicative under `+ ↦ +`/`map ↦ map`. -/

@[simp] theorem comulForest_zero : comulForest (R := R) (0 : Forest α) = 1 := by
  simp only [comulForest, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForest_add (F G : Forest α) :
    comulForest (R := R) (F + G) =
      comulForest (R := R) F * comulForest (R := R) G := by
  unfold comulForest
  rw [Multiset.map_add, Multiset.prod_add]

/-! ## §4: Algebra-hom lift to `Hc`

`AddMonoidAlgebra.lift R A M` is the canonical equivalence
`(Multiplicative M →* A) ≃ (R[M] →ₐ[R] A)`. We construct the
multiplicative-monoid hom from `comulForest` and then lift to get an
algebra hom `Hc R α →ₐ[R] Hc R α ⊗ Hc R α`. The algebra-hom property
is exactly what's needed for the bialgebra structure per M-C-B
Lemma 1.2.10. -/

/-- `comulForest`, packaged as a `Multiplicative (Forest α) →* (Hc R α ⊗[R] Hc R α)`
    monoid hom. Multiplication on `Multiplicative (Forest α)`
    corresponds to addition on `Forest α` (disjoint union ⊔). -/
noncomputable def comulMonoidHom :
    Multiplicative (Forest α) →* (Hc R α ⊗[R] Hc R α) where
  toFun F := comulForest (R := R) F.toAdd
  map_one' := comulForest_zero
  map_mul' F G := comulForest_add F.toAdd G.toAdd

/-- The Connes-Kreimer coproduct on the bialgebra of decorated forests,
    as an **algebra hom**. M-C-B Definition 1.2.8 (with ω = c).

    Naming: short name `comul` is reserved for the eventual
    `Coalgebra` typeclass instance field, which takes the linear-map
    projection `comulAlgHom.toLinearMap`. -/
noncomputable def comulAlgHom : Hc R α →ₐ[R] Hc R α ⊗[R] Hc R α :=
  AddMonoidAlgebra.lift R ((Hc R α) ⊗[R] (Hc R α)) (Forest α)
    comulMonoidHom

/-! ## §5: Counit (also an algebra hom)

The counit ε : Hc R α → R extracts the coefficient of the empty
forest. For the bialgebra structure it must be an algebra hom; the
underlying monoid hom is `F ↦ if F = 0 then 1 else 0`, which is
multiplicative because `F + G = 0 ↔ F = 0 ∧ G = 0` for multisets. -/

/-- For multisets, the sum is zero iff both summands are zero
    (cardinality argument). -/
private lemma multiset_add_eq_zero_iff {β : Type*} (a b : Multiset β) :
    a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    rw [← Multiset.card_eq_zero, Multiset.card_add] at h
    exact ⟨Multiset.card_eq_zero.mp (by omega),
           Multiset.card_eq_zero.mp (by omega)⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb, add_zero]

/-- The counit, as a `Multiplicative (Forest α) →* R` monoid hom. -/
noncomputable def counitMonoidHom : Multiplicative (Forest α) →* R where
  toFun F := if F.toAdd = 0 then 1 else 0
  map_one' := by
    show (if (1 : Multiplicative (Forest α)).toAdd = 0 then (1 : R) else 0) = 1
    show (if (0 : Forest α) = 0 then (1 : R) else 0) = 1
    rw [if_pos rfl]
  map_mul' F G := by
    show (if (F * G).toAdd = 0 then (1 : R) else 0)
       = (if F.toAdd = 0 then (1 : R) else 0)
       * (if G.toAdd = 0 then (1 : R) else 0)
    show (if F.toAdd + G.toAdd = 0 then (1 : R) else 0)
       = (if F.toAdd = 0 then (1 : R) else 0)
       * (if G.toAdd = 0 then (1 : R) else 0)
    by_cases hF : F.toAdd = 0
    · by_cases hG : G.toAdd = 0
      · simp [hF, hG]
      · simp [hF, hG]
    · by_cases hG : G.toAdd = 0
      · simp [hF, hG]
      · have h : ¬ (F.toAdd + G.toAdd = 0) := fun h =>
          hF ((multiset_add_eq_zero_iff _ _).mp h).1
        simp [hF, hG, h]

/-- The counit on the bialgebra of decorated forests, as an
    **algebra hom**. -/
noncomputable def counit : Hc R α →ₐ[R] R :=
  AddMonoidAlgebra.lift R R (Forest α) counitMonoidHom

/-! ## §6: Δ^d (deletion coproduct)

Per M-C-B Def 1.2.8 with ω = d, Δ^d uses `remainderDeletion`
(removal + rebinarization) instead of `remainder` (contraction with
trace). Δ^d is what the linguistic Merge action uses (Definition 1.3.4 p. 42, "consider the coproduct Δ = Δ^d").
Algebraically Δ^d satisfies a weaker coassoc relation than Δ^c (per
Lemma 1.2.12, multiplicities differ at distance ≤ 1), but it's still
multiplicative on forests, so the algebra-hom lift works the same way.

When `remainderDeletion c = none` (the cut consumed the entire root
component — only happens for `CutShape.bothCut`), the right channel
of the coproduct term becomes `1` (the empty workspace). -/

/-- Helper: convert an `Option (DecoratedTree α)` remainder to the
    corresponding right-channel value in `Hc R α`. `Option.none` →
    `(1 : Hc R α)` (empty workspace); `Option.some t` → `forestToHc {t}`
    (singleton workspace). -/
private noncomputable def deletionRightChannel
    (m : Option (DecoratedTree α)) : Hc R α :=
  match m with
  | Option.none   => (1 : Hc R α)
  | Option.some t => forestToHc (R := R) ({t} : Forest α)

/-- The tree-level Δ^d coproduct.
    Δ^d(T) = T ⊗ 1 + Σ_c (cutForest c) ⊗ (deletion-remainder c). -/
noncomputable def comulTreeDel (T : DecoratedTree α) :
    Hc R α ⊗[R] Hc R α :=
  forestToHc (R := R) ({T} : Forest α) ⊗ₜ[R] (1 : Hc R α)
  +
  ∑ c : CutShape T,
    forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
    deletionRightChannel (R := R) (CutShape.remainderDeletion c)

/-- The forest-level Δ^d coproduct: product of tree-level coproducts
    over the components. Same multiplicative extension as Δ^c. -/
noncomputable def comulForestDel (F : Forest α) : Hc R α ⊗[R] Hc R α :=
  (F.map (comulTreeDel (R := R))).prod

@[simp] theorem comulForestDel_zero :
    comulForestDel (R := R) (0 : Forest α) = 1 := by
  simp only [comulForestDel, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForestDel_add (F G : Forest α) :
    comulForestDel (R := R) (F + G) =
      comulForestDel (R := R) F * comulForestDel (R := R) G := by
  unfold comulForestDel
  rw [Multiset.map_add, Multiset.prod_add]

/-- `comulForestDel`, packaged as a multiplicative monoid hom. -/
noncomputable def comulDelMonoidHom :
    Multiplicative (Forest α) →* (Hc R α ⊗[R] Hc R α) where
  toFun F := comulForestDel (R := R) F.toAdd
  map_one' := comulForestDel_zero
  map_mul' F G := comulForestDel_add F.toAdd G.toAdd

/-- The Δ^d coproduct as an **algebra hom** `Hc R α →ₐ[R] Hc R α ⊗ Hc R α`.
    M-C-B Definition 1.2.8 with ω = d. This is the coproduct used by
    the action of Merge per Definition 1.3.4 (p. 42).

    Algebraically Δ^d only satisfies a weaker coassoc relation than
    Δ^c (Lemma 1.2.12), so it does not directly give a Bialgebra
    instance — that comes from `comulAlgHom` (= Δ^c). But Δ^d is
    needed for the linguistic Merge operator, which lives elsewhere
    (next file: `MergeAction.lean`). -/
noncomputable def comulDelAlgHom : Hc R α →ₐ[R] Hc R α ⊗[R] Hc R α :=
  AddMonoidAlgebra.lift R ((Hc R α) ⊗[R] (Hc R α)) (Forest α)
    comulDelMonoidHom

end Minimalist.Hopf
