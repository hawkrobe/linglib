import Linglib.Logic.PIP.Semantics

/-!
# Intensional models of PIP

This file defines the models of PIP whose atoms are worlds and entities. A
world is the singleton plurality of its atom, and a family of world-relative
relations on atoms is lifted distributively to relation symbols: a symbol holds
of a world and nonempty pluralities iff it holds at that world of every tuple
of their members, and it holds of nothing whose world argument is not a world.

## Main definitions

* `Atom`, `world` — worlds and entities as atoms; a world as a plurality.
* `Model.intensional` — the distributive lifting of world-relative relations.

## Main statements

* `Model.intensional_apply₁`, `Model.intensional_apply₂` — the lifting on one
  and two arguments.
* `exists_eq_singleton_iff` — a plurality of entities is a singleton iff
  exactly one entity satisfies its description.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
-/

namespace PIP

universe u v w

variable {V : Type u} {L : Type v} {P : ℕ → Type w} {α : Type*}

/-- The atoms of an intensional model: worlds and entities. -/
abbrev Atom (W E : Type*) := W ⊕ E

variable {W E : Type*}

/-- A world as a singleton plurality. -/
def world (w : W) : Set (Atom W E) := {Sum.inl w}

theorem world_inj {w w' : W} : (world w : Set (Atom W E)) = world w' ↔ w = w' :=
  Set.singleton_eq_singleton_iff.trans Sum.inl_injective.eq_iff

/-- The intensional model of a family of relations on atoms at each world: a
relation symbol holds of a world and nonempty pluralities iff it holds at that
world of every tuple of their members, and of nothing whose world argument is
not a world. -/
def Model.intensional (rel : ∀ {n : ℕ}, P n → W → (Fin n → Atom W E) → Prop) :
    Model P (Atom W E) where
  I r Wp ts := ∃ w, Wp = world w ∧ (∀ i, (ts i).Nonempty) ∧
    ∀ as, (∀ i, as i ∈ ts i) → rel r w as

variable {rel : ∀ {n : ℕ}, P n → W → (Fin n → Atom W E) → Prop}

theorem Model.intensional_apply₁ (r : P 1) (Wp X : Set (Atom W E)) :
    (Model.intensional rel).I r Wp ![X] ↔
      ∃ w, Wp = world w ∧ X.Nonempty ∧ ∀ a ∈ X, rel r w ![a] := by
  simp only [Model.intensional, Fin.forall_fin_one, Matrix.cons_val_zero]
  refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun H a ha => H ![a] ha
  · intro H as h
    have := H (as 0) h
    rwa [show ![as 0] = as from funext (Fin.forall_fin_one.2 rfl)] at this

theorem Model.intensional_apply₂ (r : P 2) (Wp X Y : Set (Atom W E)) :
    (Model.intensional rel).I r Wp ![X, Y] ↔
      ∃ w, Wp = world w ∧ X.Nonempty ∧ Y.Nonempty ∧
        ∀ a ∈ X, ∀ b ∈ Y, rel r w ![a, b] := by
  simp only [Model.intensional, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    and_assoc]
  refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun H a ha b hb => H ![a, b] ⟨ha, hb⟩
  · intro H as h
    have := H (as 0) h.1 (as 1) h.2
    rwa [show ![as 0, as 1] = as from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)] at this

/-- A plurality of entities is a singleton iff exactly one entity satisfies its
description. -/
theorem exists_eq_singleton_iff (Q : E → Prop) :
    (∃ a : Atom W E, {x | ∃ e, x = Sum.inr e ∧ Q e} = {a}) ↔ ∃! e, Q e := by
  simp only [Set.eq_singleton_iff_unique_mem, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ⟨e, rfl, he⟩, hu⟩
    exact ⟨e, he, fun e' he' => Sum.inr_injective (hu _ ⟨e', rfl, he'⟩)⟩
  · rintro ⟨e, he, hu⟩
    exact ⟨_, ⟨e, rfl, he⟩, fun x ⟨e', hx, he'⟩ => hx ▸ congrArg Sum.inr (hu e' he')⟩

end PIP
