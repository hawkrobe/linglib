import Linglib.Theories.Syntax.Minimalist.Hopf.Comul
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Merge Operator on the Bialgebra of Decorated Forests
@cite{marcolli-chomsky-berwick-2025}

Per M-C-B 2025 §1.3 (Definitions 1.3.1, 1.3.2, 1.3.4), the linguistic
**Merge operator** `M_{S,S'}` for a pair `(S, S') : DecoratedTree α`
of accessible terms is the composition

  M_{S,S'} = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^d

where:

- `Δ^d` is the deletion coproduct (`comulDelAlgHom`, M-C-B Def 1.2.8 with ω = d)
- `δ_{S,S'}` is the matching operator that selects coproduct terms whose
  left channel equals the 2-element forest `{S, S'}` (M-C-B Def 1.3.1)
- `B ⊗ id` applies grafting on the left channel: replaces the 2-element
  forest `{S, S'}` with the binary tree `.node S S'`
- `⊔` is the multiplication on `Hc R α` (forest disjoint union, the
  algebra structure of `Hc`)

This file builds the building blocks (`gammaMatch`, `deltaMatch`,
`graftBinary`) and assembles `mergeOp`. The bridge to the legacy
linguistic Merge (`Step.apply` from `Basic.lean`) lives in the next
file (`MergeAction.lean`, which will replace the legacy version).
-/

namespace Minimalist.Hopf

open scoped TensorProduct

variable {R : Type*} [CommRing R] {α : Type} [DecidableEq α]

/-! ## §1: γ_{S,S'} matching projection (M-C-B Def 1.3.1)

For a fixed pair `(S, S') : DecoratedTree α`, `gammaMatch S S'` is the
linear endomorphism of `Hc R α` that projects onto the basis element
`single {S, S'} 1`:

  gammaMatch S S' (single F r) = if F = {S, S'} then single F r else 0

Built as `Finsupp.lsingle ∘ Finsupp.lapply` on the matching forest. -/

/-- The matching projection γ_{S,S'} (M-C-B Def 1.3.1): keeps the
    coefficient of the `{S, S'}` basis element, sends everything else
    to zero. -/
noncomputable def gammaMatch (S S' : DecoratedTree α) :
    Hc R α →ₗ[R] Hc R α :=
  let target : Forest α := ({S, S'} : Multiset (DecoratedTree α))
  show (Forest α →₀ R) →ₗ[R] (Forest α →₀ R) from
    (Finsupp.lsingle target).comp (Finsupp.lapply target)

/-! ## §2: δ_{S,S'} matching on the left tensor channel (M-C-B Def 1.3.1)

`deltaMatch S S' = gammaMatch S S' ⊗ id` lifts the matching projection
to act on the left channel of `Hc R α ⊗ Hc R α`. -/

/-- The matching operator δ_{S,S'} on tensored coproduct output: applies
    `gammaMatch S S'` to the left channel and identity to the right. -/
noncomputable def deltaMatch (S S' : DecoratedTree α) :
    (Hc R α ⊗[R] Hc R α) →ₗ[R] (Hc R α ⊗[R] Hc R α) :=
  TensorProduct.map (gammaMatch (R := R) S S') LinearMap.id

/-! ## §3: B grafting for binary Merge (M-C-B Def 1.3.2 + Lemma 1.3.3)

`graftBinaryAt S S'` replaces the 2-element forest `{S, S'}` (basis
element of `Hc R α`) with the binary tree `.node S S'` (also a basis
element). All other basis elements map to zero — we only need this
specialized form because the Merge action's preceding `δ_{S,S'}` step
restricts the left channel to multiples of `{S, S'}` anyway. -/

/-- The grafting operator B specialized at the pair `(S, S')`: maps the
    basis element `{S, S'}` to `.node S S'`, all other basis elements
    to zero. M-C-B Lemma 1.3.3 for binary Merge. -/
noncomputable def graftBinaryAt (S S' : DecoratedTree α) :
    Hc R α →ₗ[R] Hc R α :=
  let source : Forest α := ({S, S'} : Multiset (DecoratedTree α))
  let target : Forest α := ({.node S S'} : Multiset (DecoratedTree α))
  show (Forest α →₀ R) →ₗ[R] (Forest α →₀ R) from
    (Finsupp.lsingle target).comp (Finsupp.lapply source)

/-! ## §4: Merge operator (M-C-B Def 1.3.4)

`mergeOp S S' = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^d`

The chain:

1. `Δ^d` extracts admissible cuts (deletion-with-rebinarization remainder)
2. `δ_{S,S'}` filters to terms where the cut forest equals `{S, S'}`
3. `(B ⊗ id)` grafts `{S, S'}` into `.node S S'` on the left channel
4. `⊔` multiplies the two channels back into a single workspace

When no admissible cut produces `{S, S'}` as its cut forest, all terms
are killed by `δ_{S,S'}` and `mergeOp S S' F = 0` (the empty workspace
in `Hc`'s sense). -/

/-- Multiplication on `Hc R α` lifted to a linear map `Hc R α ⊗[R] Hc R α →ₗ[R] Hc R α`.
    Wraps mathlib's `Algebra.TensorProduct.lmul'`, which gives the
    multiplication algebra-hom for any commutative R-algebra. -/
noncomputable def hcMulLin : Hc R α ⊗[R] Hc R α →ₗ[R] Hc R α :=
  (Algebra.TensorProduct.lmul' (S := Hc R α) R).toLinearMap

/-- The Merge operator `M_{S,S'}` per M-C-B Def 1.3.4. Composes
    `Δ^d`, `δ_{S,S'}`, `B ⊗ id`, and `⊔`. -/
noncomputable def mergeOp (S S' : DecoratedTree α) : Hc R α →ₗ[R] Hc R α :=
  hcMulLin (R := R) (α := α)
    ∘ₗ TensorProduct.map (graftBinaryAt (R := R) S S') LinearMap.id
    ∘ₗ deltaMatch (R := R) S S'
    ∘ₗ comulDelAlgHom.toLinearMap

end Minimalist.Hopf
