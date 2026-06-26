/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Merge.MinimalYieldCharacter
import Linglib.Core.Algebra.RootedTree.BirkhoffLaurent

/-!
# Birkhoff renormalization of the Minimal-Yield character (MCB Prop. 3.5.6)
[marcolli-chomsky-berwick-2025] §3.5.2.2

The payoff of MCB §3.5.2, instantiating the framework-agnostic Birkhoff-renormalization machinery of
`Core/Algebra/RootedTree/BirkhoffLaurent.lean` at the **Minimal-Yield character** `ϕt = gradingChar`.

By Lemma 3.5.5, `ϕt` is entirely nonpolar; in the Birkhoff language this means
**`birkhoffMinusTree(ϕt) = 0`** — there is no divergence to subtract, so `ϕt` is its own
renormalization. This is *exactly why* `ϕt` cannot separate Internal/External from Sideward Merge:
one must instead use the intermediate-derivation character `ψt` (Cor. 3.5.4, eq. 3.5.7), whose
nontrivial polar part the **full** Birkhoff factorization — not plain `1 − R`, since `R` is a
Rota–Baxter operator and *not* an algebra homomorphism — eliminates (Prop. 3.5.6). The renormalized
part always lands in the nonpolar subring `DM[[t]]` (`polarHahn_birkhoffPlus_of'`, in Core); for `ψt`
that is where the polar Sideward content is removed. Building `ψt` (a sum over all intermediate
derivation pairs `(F, F')`) is left to future work.

## Main results

- `birkhoffMinusTree_gradingChar`: `ϕt` is trivially renormalized (Lemma 3.5.5, Birkhoff form).
- `renormGradingChar`: the renormalized Minimal-Yield character `ϕt,+`.

## References

[marcolli-chomsky-berwick-2025] (Prop. 3.5.3, Lemma 3.5.5, Prop. 3.5.6)
-/

namespace Minimalist.Merge

open RootedTree RootedTree.ConnesKreimer LaurentSeries

variable {α : Type*} {R : Type*} [CommRing R]

/-! ### ϕt is trivially renormalized (MCB Lemma 3.5.5, Birkhoff form) -/

/-- **`ϕt` is its own renormalization** (MCB Lemma 3.5.5 in Birkhoff form): the Bogolyubov negative
    part of the Minimal-Yield character `ϕt = gradingChar` vanishes on every tree, because `ϕt` is
    nonpolar (`polarHahn_gradingChar_ofTree`). There is no divergence to subtract — which is why `ϕt`
    cannot detect Sideward Merge. -/
theorem birkhoffMinusTree_gradingChar (T : Nonplanar α) :
    birkhoffMinusTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T = 0 :=
  birkhoffMinusTree_eq_zero_of_nonpolar gradingChar (fun T => polarHahn_gradingChar_ofTree T) T

/-! ### The renormalized character -/

/-- The renormalized Minimal-Yield character `ϕt,+ = (1−R)ϕ̃t = birkhoffPlus(ϕt)`. -/
noncomputable def renormGradingChar : ConnesKreimer R (Nonplanar α) →ₐ[R] LaurentSeries R :=
  birkhoffPlus (gradingChar (R := R)).toLinearMap rotaBaxterPolar

/-- **`ϕt,+ = ϕ̃t`** on every tree: since `ϕt` carries no divergence (`birkhoffMinusTree_gradingChar`),
    the renormalized part of `ϕt` equals its Bogolyubov preparation — nothing is subtracted. The
    Birkhoff factorization does no work on `ϕt`, the concrete form of MCB Lemma 3.5.5. -/
theorem birkhoffPlusTree_gradingChar (T : Nonplanar α) :
    birkhoffPlusTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T
      = birkhoffPrepTree (gradingChar (R := R)).toLinearMap rotaBaxterPolar T := by
  rw [birkhoffPlusTree_eq_prep_add_minus, birkhoffMinusTree_gradingChar, add_zero]

end Minimalist.Merge
