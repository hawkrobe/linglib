import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar

set_option autoImplicit false

/-!
# Generic admissible-cut coproduct on `ConnesKreimer R (Nonplanar α)`
[marcolli-chomsky-berwick-2025]

The three MCB coproducts — Δ^ρ (pruning), Δ^c (contraction/trace), Δ^d
(deletion) — share one shape: a primitive `ofTree T ⊗ 1` plus a sum over *cut
summands* `(crown, trunk)` of `of' crown ⊗ ofTree trunk`. They differ **only**
in the cut enumeration `cuts T`. This file factors that shape into a single
`cuts`-parameterized algebra hom `comulAlgHomNG`, recovering the existing
`comulTreeN`/`comulAlgHomN` (Δ^ρ, `cuts := cutSummandsN`) and
`comulCTreeN`/`comulCAlgHomN τ` (Δ^c, `cuts := cutSummandsCN τ`) as instances —
the bridges are definitional (`rfl`).

The cut-*enumeration* layer was already generic (`ConnesKreimer.cutSummandsG`,
over an extraction policy); this lifts that genericity to the coproduct
*operator*, so one Merge operator (`Minimalist.Merge.mergeOpG`, downstream)
serves every coproduct instead of one bespoke copy per Δ.

## Main definitions

* `comulTreeNG cuts` / `comulForestNG cuts` — the generic coproduct.
* `comulAlgHomNG cuts` — packaged as an `AlgHom`.
* `comulTreeN_eq_G`, `comulCTreeN_eq_G`, `comulAlgHomN_eq_G`,
  `comulCAlgHomN_eq_G` — the Δ^ρ / Δ^c instance bridges.
-/

namespace RootedTree.ConnesKreimer

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

/-! ### Instance bridges (Δ^ρ, Δ^c) — definitional -/

/-- Δ^ρ is the generic coproduct at `cuts := cutSummandsN`. -/
theorem comulTreeN_eq_G (T : Nonplanar α) :
    comulTreeN (R := R) T = comulTreeNG (R := R) cutSummandsN T := rfl

/-- Δ^c is the generic coproduct at `cuts := cutSummandsCN τ`. -/
theorem comulCTreeN_eq_G {β : Type*} (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    comulCTreeN (R := R) τ T = comulTreeNG (R := R) (cutSummandsCN τ) T := rfl

theorem comulAlgHomN_eq_G :
    comulAlgHomN (R := R) (α := α) = comulAlgHomNG (R := R) cutSummandsN := rfl

theorem comulCAlgHomN_eq_G {β : Type*} (τ : Nonplanar (α ⊕ β) → β) :
    comulCAlgHomN (R := R) τ = comulAlgHomNG (R := R) (cutSummandsCN τ) := rfl

end RootedTree.ConnesKreimer
