/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.HopfAlgebraNonplanar
import Linglib.Core.Algebra.RotaBaxter

/-!
# Birkhoff factorization on the Connes–Kreimer Hopf algebra  `[UPSTREAM]`

[marcolli-chomsky-berwick-2025]'s renormalization of a character (Prop. 3.1.7): given a character
`φ : H → ℛ` from the Hopf algebra `H` of nonplanar rooted trees into a commutative algebra `ℛ`
carrying a weight-`-1` Rota–Baxter operator `R`, the **Bogolyubov recursion** splits `φ` into a
"meaningless part" `φ₋` and a renormalized, consistency-checked part `φ₊`. This is the algebraic
core of the "single map that recursively modifies an assignment of semantic values so as to
incorporate the consistency checking over all substructures."

The negative part `φ₋` is built by the *same* `cutSummandsN`/depth recursion as the Hopf antipode
`antipodeTreeN`, with two substitutions: the canonical embedding `ofTree rem` becomes the character
value `φ (ofTree rem) ∈ ℛ`, and the bare negation becomes `−R`. Indeed `antipodeTreeN` is the
`R = id`, canonical-character specialization of this recursion (`S(x) = −x − Σ S(x′)·x″`).

## Main definitions

- `birkhoffMinusTree φ R T`: the Bogolyubov negative part `φ₋` on a single tree.
- `birkhoffMinusMonoidHom φ R`: `φ₋` extended multiplicatively to forests.
- `birkhoffMinus φ R`: `φ₋` as an algebra hom `H →ₐ[R] ℛ` ([marcolli-chomsky-berwick-2025]:
  `φ₋` is an algebra hom into `range R = ℛ₋`).

## References

[marcolli-chomsky-berwick-2025] (Prop. 3.1.7, Def. 3.1.1)
-/

namespace RootedTree.ConnesKreimer

variable {R ℛ : Type*} [CommRing R] [CommRing ℛ] [Algebra R ℛ] {α : Type*}
  (φ : ConnesKreimer R (Nonplanar α) →ₗ[R] ℛ) (RB : RotaBaxter R ℛ (-1))

/-- **The Bogolyubov negative part `φ₋` on a single tree** ([marcolli-chomsky-berwick-2025]
    Prop. 3.1.7): `φ₋(T) = −R(Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem))`.
    Models `antipodeTreeN` with the character value `φ(ofTree rem)` in place of `ofTree rem` and
    the Rota–Baxter `−R` in place of bare negation; well-founded on `T.depth`. -/
noncomputable def birkhoffMinusTree (T : Nonplanar α) : ℛ :=
  - RB.op ((cutSummandsN T).attach.map (fun ⟨pf, h_mem⟩ =>
      (pf.1.attach.map (fun ⟨T_i, h_T_i⟩ => birkhoffMinusTree T_i)).prod * φ (ofTree pf.2))).sum
termination_by T.depth
decreasing_by exact cutSummandsN_subtree_depth_lt T pf.1 pf.2 h_mem T_i h_T_i

/-- **`φ₋` extended multiplicatively to forests**, as a `MonoidHom` on `Multiplicative (Forest …)`.
    Mirrors `antipodeMonoidHomN`. -/
noncomputable def birkhoffMinusMonoidHom :
    Multiplicative (Forest (Nonplanar α)) →* ℛ where
  toFun F := (F.toAdd.map (birkhoffMinusTree φ RB)).prod
  map_one' := by
    show ((0 : Forest (Nonplanar α)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F.toAdd + G.toAdd).map (birkhoffMinusTree φ RB)).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- **`φ₋` as an algebra hom** `H →ₐ[R] ℛ`, lifting `birkhoffMinusMonoidHom` via
    `AddMonoidAlgebra.lift`. Mirrors `antipodeAlgHomN`. -/
noncomputable def birkhoffMinus : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ :=
  AddMonoidAlgebra.lift R ℛ (Forest (Nonplanar α)) (birkhoffMinusMonoidHom φ RB)

/-! ### The Bogolyubov preparation and the renormalized part -/

/-- **The Bogolyubov preparation `φ̃`** ([marcolli-chomsky-berwick-2025] Rem. 3.1.8):
    `φ̃(T) = Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem)`, of which the
    negative part is `φ₋(T) = −R(φ̃(T))` and the renormalized part is `φ₊(T) = (1−R)(φ̃(T))`. -/
noncomputable def birkhoffPrepTree (T : Nonplanar α) : ℛ :=
  ((cutSummandsN T).attach.map (fun ⟨pf, _⟩ =>
      (pf.1.attach.map (fun ⟨T_i, _⟩ => birkhoffMinusTree φ RB T_i)).prod * φ (ofTree pf.2))).sum

/-- `φ₋(T) = −R(φ̃(T))`: the negative part is `−R` applied to the Bogolyubov preparation. -/
theorem birkhoffMinusTree_eq_neg_op_prep (T : Nonplanar α) :
    birkhoffMinusTree φ RB T = - RB.op (birkhoffPrepTree φ RB T) := by
  rw [birkhoffMinusTree, birkhoffPrepTree]

/-- **The renormalized part `φ₊` on a single tree** ([marcolli-chomsky-berwick-2025] Prop. 3.1.7):
    `φ₊(T) = (1−R)(φ̃(T)) = φ̃(T) − R(φ̃(T))` — the consistency-checked value. -/
noncomputable def birkhoffPlusTree (T : Nonplanar α) : ℛ :=
  birkhoffPrepTree φ RB T - RB.op (birkhoffPrepTree φ RB T)

/-- `φ₊(T) = φ̃(T) + φ₋(T)`: the renormalized and negative parts recover the preparation. -/
theorem birkhoffPlusTree_eq_prep_add_minus (T : Nonplanar α) :
    birkhoffPlusTree φ RB T = birkhoffPrepTree φ RB T + birkhoffMinusTree φ RB T := by
  rw [birkhoffPlusTree, birkhoffMinusTree_eq_neg_op_prep]; ring

end RootedTree.ConnesKreimer
