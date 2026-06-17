/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Logic.Temporal.Basic

/-!
# T × W tense-modal logic: the `TW` calculus and soundness

The Hilbert calculus `TW` of [von-kutschera-1997] and its soundness for T × W frames
([thomason-1984]): every axiom is valid and every rule preserves validity. The distinctive rule is
Gabbay's irreflexivity rule `Provable.ir`, whose soundness rests on a coincidence lemma — a formula's
truth depends only on the valuation of the atoms it mentions.

## Main definitions
* `OForm.imp`, `OForm.or` — derived connectives.
* `OForm.mentions` — the atoms occurring in a formula.
* `Valid` — truth at every point of every T × W model.
* `Provable` — the `TW` Hilbert calculus.

## Main results
* `TWFrame.sat_iff_of_agree` — the coincidence lemma.
* `soundness` — `Provable a → Valid a`.
-/

namespace Core.Logic.Temporal

universe u v

variable {Atom : Type*}

/-! ### Derived connectives -/

/-- Material implication `a ⊃ b := ¬(a ∧ ¬b)`. -/
def OForm.imp (a b : OForm Atom) : OForm Atom := .neg (.and a (.neg b))

/-- Disjunction `a ∨ b := ¬(¬a ∧ ¬b)`. -/
def OForm.or (a b : OForm Atom) : OForm Atom := .neg (.and (.neg a) (.neg b))

/-- The sentential constants occurring in a formula. -/
def OForm.mentions : OForm Atom → Atom → Prop
  | .atom p,  q => p = q
  | .neg a,   q => a.mentions q
  | .and a b, q => a.mentions q ∨ b.mentions q
  | .G a,     q => a.mentions q
  | .H a,     q => a.mentions q
  | .N a,     q => a.mentions q
  | .box a,   q => a.mentions q

namespace TWFrame

variable {Time : Type*} {World : Type*} [LinearOrder Time]

@[simp] theorem sat_imp (F : TWFrame Time World) (V : Atom → Time → World → Prop)
    (a b : OForm Atom) (t : Time) (w : World) :
    F.sat V (a.imp b) t w ↔ (F.sat V a t w → F.sat V b t w) := by
  simp only [OForm.imp, sat_neg, sat_and, not_and, not_not]

@[simp] theorem sat_or (F : TWFrame Time World) (V : Atom → Time → World → Prop)
    (a b : OForm Atom) (t : Time) (w : World) :
    F.sat V (a.or b) t w ↔ (F.sat V a t w ∨ F.sat V b t w) := by
  simp only [OForm.or, sat_neg, sat_and, not_and_or, not_not]

/-! ### Coincidence lemma

A formula's truth at a point depends only on the valuation of the atoms it mentions. -/

theorem sat_iff_of_agree (F : TWFrame Time World) (V₁ V₂ : Atom → Time → World → Prop) :
    ∀ (a : OForm Atom), (∀ p, a.mentions p → ∀ t w, V₁ p t w ↔ V₂ p t w) →
      ∀ t w, (F.sat V₁ a t w ↔ F.sat V₂ a t w)
  | .atom p,  h, t, w => h p rfl t w
  | .neg a,   h, t, w => by
      simp only [sat_neg]; rw [sat_iff_of_agree F V₁ V₂ a h t w]
  | .and a b, h, t, w => by
      simp only [sat_and]
      rw [sat_iff_of_agree F V₁ V₂ a (fun p hp => h p (Or.inl hp)) t w,
          sat_iff_of_agree F V₁ V₂ b (fun p hp => h p (Or.inr hp)) t w]
  | .G a, h, t, w => by
      simp only [sat_G]
      exact forall_congr' fun t' => imp_congr_right fun _ => sat_iff_of_agree F V₁ V₂ a h t' w
  | .H a, h, t, w => by
      simp only [sat_H]
      exact forall_congr' fun t' => imp_congr_right fun _ => sat_iff_of_agree F V₁ V₂ a h t' w
  | .N a, h, t, w => by
      simp only [sat_N]
      exact forall_congr' fun w' => imp_congr_right fun _ => sat_iff_of_agree F V₁ V₂ a h t w'
  | .box a, h, t, w => by
      simp only [sat_box]
      exact forall_congr' fun w' => sat_iff_of_agree F V₁ V₂ a h t w'

end TWFrame

/-! ### Validity -/

/-- A formula is **valid** when it is true at every point of every T × W model. -/
def Valid (a : OForm Atom) : Prop :=
  ∀ {Time : Type u} {World : Type v} [LinearOrder Time]
    (F : TWFrame Time World) (V : Atom → Time → World → Prop) (t : Time) (w : World),
    F.sat V a t w

/-! ### The `TW` calculus -/

open OForm in
/-- The Hilbert calculus `TW` ([von-kutschera-1997]): propositional axioms, the tense axioms
`A1`–`A3`, the modal axioms `A4`–`A5`, the interaction axioms `A6`–`A8`, modus ponens, necessitation
for `H`/`N`/`□`, and Gabbay's irreflexivity rule. -/
inductive Provable : OForm Atom → Prop where
  /-- Propositional `K` combinator. -/
  | impK (a b : OForm Atom) : Provable (a.imp (b.imp a))
  /-- Propositional `S` combinator. -/
  | impS (a b c : OForm Atom) :
      Provable ((a.imp (b.imp c)).imp ((a.imp b).imp (a.imp c)))
  /-- Classical contraposition. -/
  | contra (a b : OForm Atom) : Provable (((a.neg).imp (b.neg)).imp (b.imp a))
  /-- Conjunction introduction. -/
  | andI (a b : OForm Atom) : Provable (a.imp (b.imp (a.and b)))
  /-- Conjunction elimination (left). -/
  | andL (a b : OForm Atom) : Provable ((a.and b).imp a)
  /-- Conjunction elimination (right). -/
  | andR (a b : OForm Atom) : Provable ((a.and b).imp b)
  /-- A1a — `K` axiom for `G`. -/
  | a1a (a b : OForm Atom) : Provable (((a.imp b).G.and a.G).imp b.G)
  /-- A1b — `K` axiom for `H`. -/
  | a1b (a b : OForm Atom) : Provable (((a.imp b).H.and a.H).imp b.H)
  /-- A1c — Prior conversion `A ⊃ HFA`. -/
  | a1c (a : OForm Atom) : Provable (a.imp a.Fut.H)
  /-- A1d — Prior conversion `A ⊃ GPA`. -/
  | a1d (a : OForm Atom) : Provable (a.imp a.Pst.G)
  /-- A2 — `4` axiom for `G` (transitivity). -/
  | a2 (a : OForm Atom) : Provable (a.G.imp a.G.G)
  /-- A3a — future linearity (`.3`). -/
  | a3a (a : OForm Atom) : Provable (a.Fut.imp (a.Fut.or (a.or a.Pst)).G)
  /-- A3b — past linearity (`.3`). -/
  | a3b (a : OForm Atom) : Provable (a.Pst.imp (a.Fut.or (a.or a.Pst)).H)
  /-- A4a — `T` axiom for `N`. -/
  | a4a (a : OForm Atom) : Provable (a.N.imp a)
  /-- A4b — `K` axiom for `N`. -/
  | a4b (a b : OForm Atom) : Provable (((a.imp b).N.and a.N).imp b.N)
  /-- A4c — `5` axiom for `N`. -/
  | a4c (a : OForm Atom) : Provable (a.M.imp a.M.N)
  /-- A5a — `K` axiom for `□`. -/
  | a5a (a b : OForm Atom) : Provable (((a.imp b).box.and a.box).imp b.box)
  /-- A5b — `5` axiom for `□`. -/
  | a5b (a : OForm Atom) : Provable (a.dia.imp a.dia.box)
  /-- A6 — past/necessity interaction `PNA ⊃ NPA`. -/
  | a6 (a : OForm Atom) : Provable (a.N.Pst.imp a.Pst.N)
  /-- A7 — `□` dominates `N` (`□A ⊃ NA`). -/
  | a7 (a : OForm Atom) : Provable (a.box.imp a.N)
  /-- A8a — past/`□` interaction `P□A ⊃ □PA`. -/
  | a8a (a : OForm Atom) : Provable (a.box.Pst.imp a.Pst.box)
  /-- A8b — future/`□` interaction `F□A ⊃ □FA`. -/
  | a8b (a : OForm Atom) : Provable (a.box.Fut.imp a.Fut.box)
  /-- Modus ponens. -/
  | mp {a b : OForm Atom} : Provable (a.imp b) → Provable a → Provable b
  /-- Necessitation for `H`. -/
  | necH {a : OForm Atom} : Provable a → Provable a.H
  /-- Necessitation for `N`. -/
  | necN {a : OForm Atom} : Provable a → Provable a.N
  /-- Necessitation for `□`. -/
  | necBox {a : OForm Atom} : Provable a → Provable a.box
  /-- Gabbay's irreflexivity rule: from `□(¬q ∧ Gq) ⊃ A` with `q` not in `A`, infer `A`. -/
  | ir {a : OForm Atom} (q : Atom) :
      Provable ((OForm.and (.neg (.atom q)) (.G (.atom q))).box.imp a) →
      ¬ a.mentions q → Provable a

/-! ### Soundness -/

open TWFrame
open Core.Logic.Modal (box_four self_imp_box_flip_diamond)

/-- **Soundness of `TW`** ([von-kutschera-1997]): every `TW`-provable formula is T × W-valid. -/
theorem soundness {a : OForm Atom} (h : Provable a) : Valid.{u, v} a := by
  intro Time World _ F V t w
  induction h generalizing V t w with
  | impK _ _ => simp only [sat_imp]; exact fun p _ => p
  | impS _ _ _ => simp only [sat_imp]; exact fun f g p => f p (g p)
  | contra _ _ => simp only [sat_imp, sat_neg]; exact fun f q => not_not.1 fun np => f np q
  | andI _ _ => simp only [sat_imp, sat_and]; exact fun p q => ⟨p, q⟩
  | andL _ _ => simp only [sat_imp, sat_and]; exact fun h => h.1
  | andR _ _ => simp only [sat_imp, sat_and]; exact fun h => h.2
  | a1a _ _ | a1b _ _ =>
      simp only [sat_imp, sat_and, sat_G, sat_H]
      exact fun h t' ht' => h.1 t' ht' (h.2 t' ht')
  | a4b _ _ =>
      simp only [sat_imp, sat_and, sat_N]; exact fun h w' hw' => h.1 w' hw' (h.2 w' hw')
  | a5a _ _ =>
      simp only [sat_imp, sat_and, sat_box]; exact fun h w' => h.1 w' (h.2 w')
  | a1c _ =>
      simp only [sat_imp, sat_H, sat_Fut]
      exact fun ha => self_imp_box_flip_diamond (· < ·) (fun t' => F.sat V _ t' w) t ha
  | a1d _ =>
      simp only [sat_imp, sat_G, sat_Pst]
      exact fun ha => self_imp_box_flip_diamond (· > ·) (fun t' => F.sat V _ t' w) t ha
  | a2 _ =>
      simp only [sat_imp]; exact fun h => box_four (· < ·) _ _ h
  | a3a _ | a3b _ =>
      simp only [sat_imp, sat_G, sat_H, sat_or, sat_Fut, sat_Pst]
      rintro ⟨t₀, _, ha⟩ t' _
      rcases lt_trichotomy t₀ t' with hlt | heq | hgt
      exacts [.inr (.inr ⟨t₀, hlt, ha⟩), .inr (.inl (heq ▸ ha)), .inl ⟨t₀, hgt, ha⟩]
  | a4a _ => simpa only [sat_imp] using sat_N_imp_self F V
  | a4c _ => simpa only [sat_imp] using sat_M_imp_N_M F V
  | a5b _ => simpa only [sat_imp] using sat_dia_imp_box_dia F V
  | a7 _ => simpa only [sat_imp] using sat_box_imp_N F V
  | a6 _ =>
      simp only [sat_imp, sat_N, sat_Pst]
      rintro ⟨t', ht', hN⟩ w' hw'
      exact ⟨t', ht', hN w' (F.sim_backward w w' ht'.le hw')⟩
  | a8a _ | a8b _ =>
      simp only [sat_imp, sat_box, sat_Pst, sat_Fut]
      rintro ⟨t', ht', hbox⟩ w'; exact ⟨t', ht', hbox w'⟩
  | mp _ _ ihab iha => exact (sat_imp F V _ _ t w).1 (ihab V t w) (iha V t w)
  | necH _ ih => exact fun t' _ => ih V t' w
  | necN _ ih => exact fun w' _ => ih V t w'
  | necBox _ ih => exact fun w' _ => ih V t w'
  | @ir a q _ hq ih =>
      classical
      let V' : Atom → Time → World → Prop := fun p t'' w'' => if p = q then t < t'' else V p t'' w''
      have hbox : F.sat V' (OForm.and (.neg (.atom q)) (.G (.atom q))).box t w := by
        intro w' _; refine ⟨?_, fun t' ht' => ?_⟩ <;> simp only [sat_neg, sat_atom, V']
        exacts [lt_irrefl t, ht']
      have hagree : ∀ p, a.mentions p → ∀ tt ww, V p tt ww ↔ V' p tt ww := by
        intro p hp tt ww
        have hpq : p ≠ q := fun e => hq (e ▸ hp)
        simp only [V', if_neg hpq]
      exact (sat_iff_of_agree F V V' a hagree t w).mpr ((sat_imp F V' _ _ t w).1 (ih V' t w) hbox)

end Core.Logic.Temporal
