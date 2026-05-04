import Linglib.Core.Algebra.ConnesKreimer.Defs
import Linglib.Core.Combinatorics.RootedTree.AdmissibleCut
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Connes-Kreimer Coproduct on the Bialgebra of Trace-Anonymized Forests
@cite{marcolli-chomsky-berwick-2025}

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.2.8, the
**contraction coproduct** on the syntactic forest bialgebra is

  Δ^c(T) := T ⊗ 1 + 1 ⊗ T + Σ_{F_v} F_v ⊗ T/^c F_v

where the sum is over all subforests `F_v ⊂ T` consisting of disjoint
accessible terms of T, and T/^c F_v is the contraction-with-trace
remainder (Definition 1.2.4).

Equivalently, identifying the empty cut with the `1 ⊗ T` term:

  Δ^c(T) = T ⊗ 1 + Σ_{c : CutShape T} (cutForest c) ⊗ (remainder c)

## Carrier: TraceTree α Unit (not DecoratedTree α)

This file builds Δ^c on `TraceTree α Unit` (the trace-anonymized carrier),
NOT on `DecoratedTree α` (the linguistic-data carrier). Per
@cite{marcolli-skigin-2025} §10.1, the bialgebra structure requires
trace labels to be scalars from a disjoint marked copy of the leaf
alphabet (specialized here to `β = Unit`), not recursive subtrees.
The bialgebra instance lives on the object whose elements are the
equivalence classes — i.e., on the trace-anonymized carrier — per the
mathlib idiom that algebraic structures live on quotients, not on
preimages with projections.

Linguistic-layer code that maintains `DecoratedTree α` data should
project via `Forest.anon (fun _ => ())` at the boundary before invoking
`comulAlgHom`. See `Decorated.lean` for the projection.

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

- `Hc = AddMonoidAlgebra R (TraceForest α Unit) = (TraceForest α Unit →₀ R)` (from `Defs.lean`)
- `TensorProduct R Hc Hc` with `⊗ₜ` notation
- `Finsupp.single F z : Hc` for basis elements (F : TraceForest α Unit)
- `Finsupp.linearCombination` for linear extension from a function on
  basis elements
- `Multiset.prod` for the multiplicative-on-forests extension
- `Finsupp.lapply` for the counit (value at the empty-forest index)
-/

namespace ConnesKreimer

open scoped TensorProduct
open Finsupp

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ## §1: Tree-level coproduct

For a single tree `T : TraceTree α Unit`, define the contraction
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
    `forestToHc {T}`. Takes `TraceForest α Unit` (the bialgebra
    carrier basis); for `Forest α`-bearing callers, project via
    `Forest.anon (fun _ => ())` first. -/
noncomputable def forestToHc (F : TraceForest α Unit) : Hc R α :=
  Finsupp.single F (1 : R)

/-- The empty forest embeds as the multiplicative unit:
    `forestToHc 0 = (1 : Hc R α)`. Direct from `AddMonoidAlgebra.one_def`. -/
@[simp] lemma forestToHc_zero :
    (forestToHc (R := R) (0 : TraceForest α Unit) : Hc R α) = 1 := by
  show (Finsupp.single (0 : TraceForest α Unit) (1 : R)
          : AddMonoidAlgebra R (TraceForest α Unit))
     = (1 : AddMonoidAlgebra R (TraceForest α Unit))
  exact AddMonoidAlgebra.one_def.symm

/-- Disjoint union of forests corresponds to multiplication of their `forestToHc`
    images: `forestToHc (F + G) = forestToHc F * forestToHc G`.
    Direct from `AddMonoidAlgebra.single_mul_single` at coefficient 1. -/
@[simp] lemma forestToHc_add (F G : TraceForest α Unit) :
    forestToHc (R := R) (F + G) = forestToHc (R := R) F * forestToHc (R := R) G := by
  show (forestToHc (R := R) (F + G) : Hc R α)
     = (forestToHc (R := R) F * forestToHc (R := R) G : Hc R α)
  unfold forestToHc
  exact (AddMonoidAlgebra.single_mul_single
    (R := R) (M := TraceForest α Unit) F G 1 1
    |>.trans (by rw [mul_one])).symm

/-- The tree-level Connes-Kreimer coproduct.
    Δ^c(T) = T ⊗ 1 + Σ_c (cutForest c) ⊗ ({remainder c}). -/
noncomputable def comulTree (T : TraceTree α Unit) : Hc R α ⊗[R] Hc R α :=
  forestToHc (R := R) ({T} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)
  +
  ∑ c : CutShape T,
    forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
    forestToHc (R := R) ({CutShape.remainder c} : TraceForest α Unit)

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
noncomputable def comulForest (F : TraceForest α Unit) : Hc R α ⊗[R] Hc R α :=
  (F.map (comulTree (R := R))).prod

/-! ## §3: Multiplicativity of `comulForest`

Per M-C-B (text just above Lemma 1.2.10): the coproduct on a forest
is the product of coproducts on its components. With `comulForest`
defined as `Multiset.prod (F.map comulTree)`, this is structurally
true: `Multiset.prod` is multiplicative under `+ ↦ +`/`map ↦ map`. -/

@[simp] theorem comulForest_zero :
    comulForest (R := R) (0 : TraceForest α Unit) = 1 := by
  simp only [comulForest, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForest_add (F G : TraceForest α Unit) :
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

/-- `comulForest`, packaged as a `Multiplicative (TraceForest α Unit) →* (Hc R α ⊗[R] Hc R α)`
    monoid hom. Multiplication on `Multiplicative (TraceForest α Unit)`
    corresponds to addition on `TraceForest α Unit` (disjoint union ⊔).

    Public (not `private`) so `Bialgebra.lean`'s helper lemma
    `comulAlgHom_apply_single` can reference it. Downstream callers
    should generally use `comulAlgHom` (the `AlgHom`-shaped public API)
    rather than this monoid hom directly. -/
noncomputable def comulMonoidHom :
    Multiplicative (TraceForest α Unit) →* (Hc R α ⊗[R] Hc R α) where
  toFun F := comulForest (R := R) F.toAdd
  map_one' := comulForest_zero
  map_mul' F G := comulForest_add F.toAdd G.toAdd

/-- The Connes-Kreimer coproduct on the bialgebra of trace-anonymized forests,
    as an **algebra hom**. M-C-B Definition 1.2.8 (with ω = c).

    Naming: short name `comul` is reserved for the eventual
    `Coalgebra` typeclass instance field, which takes the linear-map
    projection `comulAlgHom.toLinearMap`. -/
noncomputable def comulAlgHom : Hc R α →ₐ[R] Hc R α ⊗[R] Hc R α :=
  AddMonoidAlgebra.lift R ((Hc R α) ⊗[R] (Hc R α)) (TraceForest α Unit)
    comulMonoidHom

/-- `comulAlgHom` applied to the basis vector `Finsupp.single F 1`
    equals `comulForest F`. Follows from `AddMonoidAlgebra.lift_single`. -/
@[simp] theorem comulAlgHom_apply_single (F : TraceForest α Unit) :
    comulAlgHom (R := R) (α := α) (Finsupp.single F 1) = comulForest F := by
  show AddMonoidAlgebra.lift R _ _ comulMonoidHom (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

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

/-- The counit, as a `Multiplicative (TraceForest α Unit) →* R` monoid hom.
    Public so `Bialgebra.lean`'s helper lemma `counit_apply_single`
    can reference it; downstream callers should generally use `counit`
    (the `AlgHom`-shaped public API). -/
noncomputable def counitMonoidHom : Multiplicative (TraceForest α Unit) →* R where
  toFun F := if F.toAdd = 0 then 1 else 0
  map_one' := by
    show (if (1 : Multiplicative (TraceForest α Unit)).toAdd = 0 then (1 : R) else 0) = 1
    show (if (0 : TraceForest α Unit) = 0 then (1 : R) else 0) = 1
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

/-- The counit on the bialgebra of trace-anonymized forests, as an
    **algebra hom**. -/
noncomputable def counit : Hc R α →ₐ[R] R :=
  AddMonoidAlgebra.lift R R (TraceForest α Unit) counitMonoidHom

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

/-- Helper: convert an `Option (TraceTree α Unit)` remainder to the
    corresponding right-channel value in `Hc R α`. `Option.none` →
    `(1 : Hc R α)` (empty workspace); `Option.some t` → `forestToHc {t}`
    (singleton workspace).

    Public because `comulTreeDel_eq_prim_add_sum` (the structural
    decomposition lemma below) names it in its statement: any consumer
    that uses that lemma to destructure `comulTreeDel` summands needs
    the symbol to be in scope. -/
noncomputable def deletionRightChannel
    (m : Option (TraceTree α Unit)) : Hc R α :=
  match m with
  | Option.none   => (1 : Hc R α)
  | Option.some t => forestToHc (R := R) ({t} : TraceForest α Unit)

/-- The tree-level Δ^d coproduct.
    Δ^d(T) = T ⊗ 1 + Σ_c (cutForest c) ⊗ (deletion-remainder c). -/
noncomputable def comulTreeDel (T : TraceTree α Unit) :
    Hc R α ⊗[R] Hc R α :=
  forestToHc (R := R) ({T} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)
  +
  ∑ c : CutShape T,
    forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
    deletionRightChannel (R := R) (CutShape.remainderDeletion c)

/-- The structural decomposition of `comulTreeDel T` into its primitive
    `T ⊗ 1` term and the sum of admissible-cut terms. Stated as a named
    `rfl` lemma so downstream proofs (e.g., the algebraic Merge bridge in
    `Theories/Syntax/Minimalist/Hopf/MergeAction.lean`) are robust under
    refactors of `comulTreeDel`'s body. Lives in `ConnesKreimer` (where
    `deletionRightChannel` is in scope) rather than at the consumer. -/
theorem comulTreeDel_eq_prim_add_sum (T : TraceTree α Unit) :
    comulTreeDel (R := R) T
      = forestToHc (R := R) ({T} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)
        + ∑ c : CutShape T,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c) := rfl

/-- The forest-level Δ^d coproduct: product of tree-level coproducts
    over the components. Same multiplicative extension as Δ^c. -/
noncomputable def comulForestDel (F : TraceForest α Unit) : Hc R α ⊗[R] Hc R α :=
  (F.map (comulTreeDel (R := R))).prod

@[simp] theorem comulForestDel_zero :
    comulForestDel (R := R) (0 : TraceForest α Unit) = 1 := by
  simp only [comulForestDel, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForestDel_add (F G : TraceForest α Unit) :
    comulForestDel (R := R) (F + G) =
      comulForestDel (R := R) F * comulForestDel (R := R) G := by
  unfold comulForestDel
  rw [Multiset.map_add, Multiset.prod_add]

/-- `comulForestDel`, packaged as a multiplicative monoid hom.
    Public so consistency with `comulMonoidHom` / `counitMonoidHom`
    (also public to support `Bialgebra.lean` helper lemmas).
    Downstream callers should generally use `comulDelAlgHom`
    (the `AlgHom`-shaped public API). -/
noncomputable def comulDelMonoidHom :
    Multiplicative (TraceForest α Unit) →* (Hc R α ⊗[R] Hc R α) where
  toFun F := comulForestDel (R := R) F.toAdd
  map_one' := comulForestDel_zero
  map_mul' F G := comulForestDel_add F.toAdd G.toAdd

/-- The Δ^d coproduct as an **algebra hom** `Hc R α →ₐ[R] Hc R α ⊗ Hc R α`.
    M-C-B Definition 1.2.8 with ω = d. This is the coproduct used by
    the action of Merge per Definition 1.3.4 (p. 42).

    **Δ^d is NOT a coassociative coalgebra** in the standard sense.
    M-C-B Lemma 1.2.12 (p. 39) proves only that the *terms* of `(1 ⊗ Δ^d) ∘
    Δ^d(T)` and `(Δ^d ⊗ 1) ∘ Δ^d(T)` match for cuts at distance ≤ 1 — but
    they appear "with different multiplicity" (Figure 1.3, p. 40), and pairs
    at distance > 1 differ. Remark 1.2.9 (p. 34) explicitly calls this "a
    weaker version of the coassociativity relation". The proper algebraic
    structure for Δ^d is deferred by M-C-B to Marcolli-Walton ("Generalized
    Quasi-Hopf Algebras and Merge", in preparation, ref [146]).

    Hence `comulDelAlgHom` is NOT registered as `Bialgebra.comul` for
    `Hc R α`. The `instBialgebraHc` typeclass uses `comulAlgHom` (= Δ^c,
    Connes-Kreimer canonical, Foissy 2002 ref [19]); see `Bialgebra.lean`.

    **Derivation from Δ^c (M-C-B p. 44):** Δ^d can be expressed as
    `Δ^d = (id ⊗ Π_{d,c}) ∘ Δ^c` where `Π_{d,c}` is the linear projection
    that removes `.trace` markers and edge-contracts. We currently define
    `comulDelAlgHom` directly (parallel to `comulAlgHom`) rather than
    deriving it via this projection — see TODO note in `Bialgebra.lean`
    for the future refactor.

    Δ^d is consumed by Minimalism's Merge operator
    (`Theories/Syntax/Minimalist/Hopf/Merge.lean`); it does NOT participate
    in the Bialgebra typeclass mediation. -/
noncomputable def comulDelAlgHom : Hc R α →ₐ[R] Hc R α ⊗[R] Hc R α :=
  AddMonoidAlgebra.lift R ((Hc R α) ⊗[R] (Hc R α)) (TraceForest α Unit)
    comulDelMonoidHom

/-- `comulDelAlgHom` applied to the basis vector `Finsupp.single F 1`
    equals `comulForestDel F`. Analog of `comulAlgHom_apply_single`.

    Not `@[simp]`: `AddMonoidAlgebra.lift_single` already fires on this
    LHS leaving `comulDelMonoidHom F.toAdd`, and rewriting through this
    lemma jumps several normalization steps in one move — fragile if
    callers are reasoning about partial unfoldings. Invoke explicitly. -/
theorem comulDelAlgHom_apply_single (F : TraceForest α Unit) :
    comulDelAlgHom (R := R) (α := α) (Finsupp.single F 1) = comulForestDel F := by
  show AddMonoidAlgebra.lift R _ _ comulDelMonoidHom (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-- `comulForestDel` on the singleton forest `{T}` reduces to `comulTreeDel T`. -/
@[simp] theorem comulForestDel_singleton (T : TraceTree α Unit) :
    comulForestDel (R := R) ({T} : TraceForest α Unit) = comulTreeDel T := by
  simp only [comulForestDel, Multiset.map_singleton, Multiset.prod_singleton]

/-- **Δ^d on a 2-tree workspace** (M-C-B Def 1.2.8 with ω = d, applied
    to `F = {T1, T2}`). Multiplicativity of `comulDelAlgHom` gives
    `Δ^d({T1, T2}) = Δ^d(T1) · Δ^d(T2)` — the load-bearing fact for
    the algebraic Merge bridge in `MergeAction.lean`. -/
theorem comulDelAlgHom_pair (T1 T2 : TraceTree α Unit) :
    comulDelAlgHom (R := R) (α := α)
        (forestToHc ({T1, T2} : TraceForest α Unit))
      = comulTreeDel T1 * comulTreeDel T2 := by
  show comulDelAlgHom (Finsupp.single ({T1, T2} : TraceForest α Unit) 1) = _
  rw [comulDelAlgHom_apply_single]
  show ((({T1, T2} : TraceForest α Unit)).map (comulTreeDel (R := R))).prod = _
  exact Multiset.prod_pair _ _

end ConnesKreimer
