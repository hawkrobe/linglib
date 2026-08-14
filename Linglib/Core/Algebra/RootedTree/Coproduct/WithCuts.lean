import Linglib.Core.Algebra.BigOperators.Multiset
import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Combinatorics.RootedTree.Cut
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.RingTheory.Bialgebra.Basic

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# Generic admissible-cut coproduct on `ConnesKreimer R (Nonplanar α)`
[marcolli-chomsky-berwick-2025]

The three MCB coproducts — Δ^ρ (pruning), Δ^c (contraction/trace), Δ^d
(deletion) — share one shape: a primitive `ofTree T ⊗ 1` plus a sum over *cut
summands* `(crown, trunk)` of `of' crown ⊗ ofTree trunk`. They differ **only**
in the cut enumeration `cuts T`. This file factors that shape into a single
`cuts`-parameterized algebra hom `comulAlgHomNG`; the concrete coproducts are
its instantiations — Δ^ρ at `cuts := cutSummandsN`
(`Coproduct/Pruning.lean`) and Δ^c at `cuts := cutSummandsCN τ`
(`Coproduct/Trace.lean`, definitionally).

The cut-*enumeration* layer was already generic (`ConnesKreimer.cutSummandsG`,
over an extraction policy); this lifts that genericity to the coproduct
*operator*, so one Merge operator (`Minimalist.Merge.mergeOpG`, downstream)
serves every coproduct instead of one bespoke copy per Δ.

## Main definitions

* `comulTreeNG cuts` / `comulForestNG cuts` — the generic coproduct.
* `comulAlgHomNG cuts` — packaged as an `AlgHom`.
* `comulTreeNG_eq_sum` / `comulForestNG_eq_sum` — the coproduct as a single
  sum over the cut convolutions `treeCutsG`/`forestCutsG`
  (`Combinatorics/RootedTree/Cut.lean`).
* `WithCuts R cuts` — the policy-indexed carrier, with `Bialgebra` gated
  on `IsAdmissibleCuts cuts`.
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- The **generic admissible-cut coproduct** (tree level), parameterized by a cut
    enumeration `cuts`. Specializing `cuts` to `cutSummandsN` gives Δ^ρ, to
    `cutSummandsCN τ` gives Δ^c, to the deletion enumeration gives Δ^d. -/
noncomputable def comulTreeNG
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (T : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
  + ((cuts T).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-- Forest-level generic coproduct (multiplicative extension). -/
noncomputable def comulForestNG
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (F : Forest (Nonplanar α)) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (F.map (comulTreeNG (R := R) cuts)).prod

@[simp] theorem comulForestNG_zero
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α)) :
    comulForestNG (R := R) cuts (0 : Forest (Nonplanar α)) = 1 := by
  simp only [comulForestNG, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForestNG_add
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (F G : Forest (Nonplanar α)) :
    comulForestNG (R := R) cuts (F + G) =
      comulForestNG (R := R) cuts F * comulForestNG (R := R) cuts G := by
  unfold comulForestNG
  rw [Multiset.map_add, Multiset.prod_add]

@[simp] theorem comulForestNG_cons
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    comulForestNG (R := R) cuts (T ::ₘ F) =
      comulTreeNG (R := R) cuts T * comulForestNG (R := R) cuts F := by
  unfold comulForestNG
  rw [Multiset.map_cons, Multiset.prod_cons]

/-- Forest-level generic coproduct as a `MonoidHom` on the additive forest monoid. -/
noncomputable def comulMonoidHomNG
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α)) :
    Multiplicative (Forest (Nonplanar α)) →*
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) where
  toFun F := comulForestNG (R := R) cuts F.toAdd
  map_one' := comulForestNG_zero cuts
  map_mul' F G := comulForestNG_add cuts F.toAdd G.toAdd

/-- The **generic admissible-cut coproduct as an algebra hom**, parameterized by
    the cut enumeration `cuts`. -/
noncomputable def comulAlgHomNG
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α)) :
    ConnesKreimer R (Nonplanar α) →ₐ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.lift (comulMonoidHomNG cuts)

@[simp] theorem comulAlgHomNG_apply_of'
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (F : Forest (Nonplanar α)) :
    comulAlgHomNG (R := R) cuts (of' F) = comulForestNG cuts F := by
  rw [comulAlgHomNG, ConnesKreimer.lift_of']
  rfl

@[simp] theorem comulAlgHomNG_apply_ofTree
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (T : Nonplanar α) :
    comulAlgHomNG (R := R) cuts (ofTree T) = comulTreeNG cuts T := by
  rw [show (ofTree T : ConnesKreimer R (Nonplanar α)) = of' ({T} : Forest (Nonplanar α))
        from rfl, comulAlgHomNG_apply_of',
      show ({T} : Forest (Nonplanar α)) = T ::ₘ (0 : Forest (Nonplanar α)) from rfl,
      comulForestNG_cons, comulForestNG_zero, mul_one]

/-! ### The generic coproduct as a sum over cut convolutions

`treeCutsG`/`forestCutsG` (`Combinatorics/RootedTree/Cut.lean`) enumerate
the (crown, trunk-forest) pairs of a tree and their convolution over a
forest; `cutTensor` sends a pair to `of' crown ⊗ of' trunk`. These
single-sum expansions serve the Δ^ρ cocycle substrate
(`Coproduct/Pruning.lean`) and the Δ^c double-cut coassoc proof
(`Coproduct/Trace.lean`). -/

/-- Tensor-product factor of a (crown, trunk) cut pair. -/
noncomputable def cutTensor (p : Forest (Nonplanar α) × Forest (Nonplanar α)) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  of' (R := R) p.1 ⊗ₜ[R] of' p.2

/-- `cutTensor` is multiplicative over the cut convolution `combinerProjG`. -/
theorem cutTensor_combinerProjG (p q : Forest (Nonplanar α) × Forest (Nonplanar α)) :
    cutTensor (R := R) (combinerProjG (p, q)) = cutTensor p * cutTensor q := by
  obtain ⟨F1, m1⟩ := p
  obtain ⟨F2, m2⟩ := q
  show cutTensor (R := R) (F1 + F2, m1 + m2) = _
  unfold cutTensor
  simp only [of'_add, Algebra.TensorProduct.tmul_mul_tmul]

/-- `comulTreeNG` as a single multiset sum over `treeCutsG`. -/
theorem comulTreeNG_eq_sum
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (T : Nonplanar α) :
    comulTreeNG (R := R) cuts T =
      ((treeCutsG cuts T).map (cutTensor (R := R))).sum := by
  unfold comulTreeNG treeCutsG
  rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
  congr 1

/-- `comulForestNG` as a single multiset sum over `forestCutsG`. -/
theorem comulForestNG_eq_sum
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (F : Forest (Nonplanar α)) :
    comulForestNG (R := R) cuts F =
      ((forestCutsG cuts F).map (cutTensor (R := R))).sum := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestNG_zero, forestCutsG_zero, Multiset.map_singleton,
        Multiset.sum_singleton]
    show (1 : _) = of' (R := R) (0 : Forest (Nonplanar α)) ⊗ₜ[R] of' 0
    rw [of'_zero, Algebra.TensorProduct.one_def]
  | cons T F ih =>
    rw [comulForestNG_cons, comulTreeNG_eq_sum, ih, forestCutsG_cons,
        Multiset.map_map,
        show (cutTensor (R := R) ∘ combinerProjG) =
            (fun p => cutTensor (R := R) p.1 * cutTensor p.2) from by
          funext p
          obtain ⟨p₁, p₂⟩ := p
          exact cutTensor_combinerProjG p₁ p₂,
        Multiset.sum_map_product_mul]

/-! ### The policy-indexed carrier `WithCuts`

The `WithLp` pattern: a type synonym indexed by the cut policy, whose
`Bialgebra` instance is gated on an admissibility mixin. Δ^ρ keeps the plain
carrier (`instBialgebraRho`, the Hopf algebra of
[marcolli-chomsky-berwick-2025] Lemma 1.2.11); the marked variants live here. -/

set_option linter.unusedVariables false in
variable (R) in
/-- Type synonym for `ConnesKreimer R (Nonplanar α)` carrying the generic
admissible-cut coproduct at the fixed policy `cuts`. -/
def WithCuts (cuts : Nonplanar α → Multiset (Multiset (Nonplanar α) × Nonplanar α)) :
    Type _ :=
  ConnesKreimer R (Nonplanar α)

variable (cuts : Nonplanar α → Multiset (Multiset (Nonplanar α) × Nonplanar α))

noncomputable instance : CommSemiring (WithCuts R cuts) :=
  inferInstanceAs (CommSemiring (ConnesKreimer R (Nonplanar α)))

noncomputable instance : Algebra R (WithCuts R cuts) :=
  inferInstanceAs (Algebra R (ConnesKreimer R (Nonplanar α)))

/-- Admissibility of a cut policy: the generic coproduct `comulAlgHomNG cuts` is
coassociative and counital, uniformly in the coefficient ring. Gates the
`Bialgebra` instance on `WithCuts` (the `Fact`-style mixin of the `WithLp`
pattern). -/
class IsAdmissibleCuts : Prop where
  coassoc : ∀ (R : Type*) [CommRing R] [CharZero R] [NoZeroDivisors R],
    (Algebra.TensorProduct.assoc R R R
        (ConnesKreimer R (Nonplanar α)) (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHomNG (R := R) cuts)
        (AlgHom.id R (ConnesKreimer R (Nonplanar α)))).comp (comulAlgHomNG cuts)) =
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (comulAlgHomNG (R := R) cuts)).comp (comulAlgHomNG cuts)
  counit_rTensor : ∀ (R : Type*) [CommSemiring R],
    (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α)))).comp (comulAlgHomNG cuts) =
      (Algebra.TensorProduct.lid R (ConnesKreimer R (Nonplanar α))).symm.toAlgHom
  counit_lTensor : ∀ (R : Type*) [CommSemiring R],
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R))).comp (comulAlgHomNG cuts) =
      (Algebra.TensorProduct.rid R R (ConnesKreimer R (Nonplanar α))).symm.toAlgHom

/-- The generic admissible-cut bialgebra on the marked carrier: any admissible
policy yields `Bialgebra R (WithCuts R cuts)`. Δ^c is recovered at
`cuts := cutSummandsCN τ`. -/
noncomputable instance WithCuts.instBialgebra
    {R : Type*} [CommRing R] [CharZero R] [NoZeroDivisors R] [IsAdmissibleCuts cuts] :
    Bialgebra R (WithCuts R cuts) :=
  Bialgebra.ofAlgHom (A := WithCuts R cuts) (comulAlgHomNG cuts) counit
    (IsAdmissibleCuts.coassoc (cuts := cuts) R)
    (IsAdmissibleCuts.counit_rTensor (cuts := cuts) R)
    (IsAdmissibleCuts.counit_lTensor (cuts := cuts) R)

end ConnesKreimer
