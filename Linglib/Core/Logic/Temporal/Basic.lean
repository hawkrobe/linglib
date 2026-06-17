/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Logic.Temporal.Defs

/-!
# T × W tense-modal logic: the modal algebra of satisfaction
[von-kutschera-1997] [thomason-1984]

Basic semantic lemmas for `Core.Logic.Temporal` satisfaction: the satisfaction-clause `@[simp]`
lemmas, the dual operators (`M`/`dia`/`Fut`/`Pst`), the modality hierarchy `box ⊃ N ⊃ A`, and the
fact that historical necessity `N` and the all-worlds `box` are **S5** modalities (`N` because `∼ₜ`
is an equivalence; `box` because it quantifies over all worlds) ([von-kutschera-1997] A4, A5).

## Main results
* `sat_neg`/`sat_and`/`sat_G`/`sat_H`/`sat_N`/`sat_box` — satisfaction clauses (`@[simp]`).
* `sat_M` — historical possibility `M` is `∃` over `∼ₜ`-alternatives.
* `sat_box_imp_N`, `sat_N_imp_self`, `sat_box_imp_self` — the `box ⊃ N ⊃ A` hierarchy.
* `sat_N_imp_N_N`, `sat_M_imp_N_M` — `N` is S5 (axioms 4 and 5).
* `sat_box_imp_box_box`, `sat_dia_imp_box_dia` — `box` is S5.
-/

namespace Core.Logic.Temporal.TWFrame

variable {Time : Type*} {World : Type*} {Atom : Type*} [LinearOrder Time]
  (F : TWFrame Time World) (V : Atom → Time → World → Prop)

/-! ### Satisfaction clauses -/

@[simp] theorem sat_atom (p : Atom) (t : Time) (w : World) :
    F.sat V (.atom p) t w ↔ V p t w := Iff.rfl

@[simp] theorem sat_neg (a : OForm Atom) (t : Time) (w : World) :
    F.sat V (.neg a) t w ↔ ¬ F.sat V a t w := Iff.rfl

@[simp] theorem sat_and (a b : OForm Atom) (t : Time) (w : World) :
    F.sat V (.and a b) t w ↔ F.sat V a t w ∧ F.sat V b t w := Iff.rfl

@[simp] theorem sat_G (a : OForm Atom) (t : Time) (w : World) :
    F.sat V (.G a) t w ↔ ∀ t', t < t' → F.sat V a t' w := Iff.rfl

@[simp] theorem sat_H (a : OForm Atom) (t : Time) (w : World) :
    F.sat V (.H a) t w ↔ ∀ t', t' < t → F.sat V a t' w := Iff.rfl

@[simp] theorem sat_N (a : OForm Atom) (t : Time) (w : World) :
    F.sat V (.N a) t w ↔ ∀ w', F.sim t w w' → F.sat V a t w' := Iff.rfl

@[simp] theorem sat_box (a : OForm Atom) (t : Time) (w : World) :
    F.sat V (.box a) t w ↔ ∀ w', F.sat V a t w' := Iff.rfl

/-! ### Dual operators -/

@[simp] theorem sat_M (a : OForm Atom) (t : Time) (w : World) :
    F.sat V a.M t w ↔ ∃ w', F.sim t w w' ∧ F.sat V a t w' := by
  simp only [OForm.M, sat_neg, sat_N, not_forall, not_not, exists_prop]

@[simp] theorem sat_dia (a : OForm Atom) (t : Time) (w : World) :
    F.sat V a.dia t w ↔ ∃ w', F.sat V a t w' := by
  simp only [OForm.dia, sat_neg, sat_box, not_forall, not_not]

@[simp] theorem sat_Fut (a : OForm Atom) (t : Time) (w : World) :
    F.sat V a.Fut t w ↔ ∃ t', t < t' ∧ F.sat V a t' w := by
  simp only [OForm.Fut, sat_neg, sat_G, not_forall, not_not, exists_prop]

@[simp] theorem sat_Pst (a : OForm Atom) (t : Time) (w : World) :
    F.sat V a.Pst t w ↔ ∃ t', t' < t ∧ F.sat V a t' w := by
  simp only [OForm.Pst, sat_neg, sat_H, not_forall, not_not, exists_prop]

/-! ### The modality hierarchy `box ⊃ N ⊃ A`

Truth in all worlds implies truth at every historical alternative (a fortiori), which — since `∼ₜ` is
reflexive — implies truth here ([von-kutschera-1997] A7, A4a). -/

theorem sat_box_imp_N {a : OForm Atom} {t : Time} {w : World} :
    F.sat V (.box a) t w → F.sat V (.N a) t w :=
  fun h w' _ => h w'

theorem sat_N_imp_self {a : OForm Atom} {t : Time} {w : World} :
    F.sat V (.N a) t w → F.sat V a t w :=
  fun h => h w ((F.sim_equiv t).refl w)

theorem sat_box_imp_self {a : OForm Atom} {t : Time} {w : World} :
    F.sat V (.box a) t w → F.sat V a t w :=
  fun h => h w

/-! ### `N` is an S5 modality

Reflexivity gives the `T` axiom (`sat_N_imp_self`); transitivity gives `4`; symmetry gives `5`. -/

theorem sat_N_imp_N_N {a : OForm Atom} {t : Time} {w : World} :
    F.sat V (.N a) t w → F.sat V (.N (.N a)) t w :=
  fun h w' hww' w'' hw'w'' => h w'' ((F.sim_equiv t).trans hww' hw'w'')

theorem sat_M_imp_N_M {a : OForm Atom} {t : Time} {w : World} :
    F.sat V a.M t w → F.sat V a.M.N t w := by
  intro h w' hww'
  rw [sat_M] at h ⊢
  obtain ⟨w₀, hww₀, ha⟩ := h
  exact ⟨w₀, (F.sim_equiv t).trans ((F.sim_equiv t).symm hww') hww₀, ha⟩

/-! ### `box` is an S5 modality (universal accessibility) -/

theorem sat_box_imp_box_box {a : OForm Atom} {t : Time} {w : World} :
    F.sat V (.box a) t w → F.sat V (.box (.box a)) t w :=
  fun h _ => h

theorem sat_dia_imp_box_dia {a : OForm Atom} {t : Time} {w : World} :
    F.sat V a.dia t w → F.sat V a.dia.box t w := by
  intro h w'
  rw [sat_dia] at h ⊢
  obtain ⟨w₀, ha⟩ := h
  exact ⟨w₀, ha⟩

/-! ### The temporal adjunctions `Fut ⊣ H`, `Pst ⊣ G`

The tense operators are Galois-adjoint on each model's entailment preorder ([burgess-1984]): `Fut`
(future `∃`) is left adjoint to `H` (past `∀`), and `Pst` (past `∃`) to `G` (future `∀`). -/

theorem Fut_adjoint_H (a b : OForm Atom) :
    F.entails V a.Fut b ↔ F.entails V a (.H b) := by
  simp only [entails, sat_Fut, sat_H]
  constructor
  · intro h t w hat t' ht
    exact h t' w ⟨t, ht, hat⟩
  · rintro h t w ⟨u, htu, hau⟩
    exact h u w hau t htu

theorem Pst_adjoint_G (a b : OForm Atom) :
    F.entails V a.Pst b ↔ F.entails V a (.G b) := by
  simp only [entails, sat_Pst, sat_G]
  constructor
  · intro h t w hat t' ht
    exact h t' w ⟨t, ht, hat⟩
  · rintro h t w ⟨u, hut, hau⟩
    exact h u w hau t hut

end Core.Logic.Temporal.TWFrame
