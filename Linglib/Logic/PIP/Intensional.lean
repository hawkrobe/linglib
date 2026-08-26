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
* `Term.realize_sigma_world_eq`, `exists_mem_distributive_iff`,
  `exists_mem_singleton_iff`, `exists_singleton_iff`, `exists_distributive_iff` — the values of
  summations over worlds and over entities from characterizations of their
  bodies.
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

section Summation

variable [DecidableEq V] (M : Model P (Atom W E)) (g : V → Set (Atom W E))

/-- The value of a summation over a world variable whose body, on the assignments
agreeing outside the summation variable and its locals, holds iff the variable is a
world standing in the relation `B` to the value of the local `y`: the worlds so
related to some plurality. -/
theorem Term.realize_sigma_world_eq {x y : V} (hxy : y ≠ x) {φ : Formula V L P}
    {B : Set (Atom W E) → W → Prop}
    (hφ : ∀ g', Set.EqOn g' g {z | z ∉ φ.locals ∧ z ≠ x} →
      (Formula.Realize M g' φ ↔ ∃ w, g' x = world w ∧ B (g' y) w))
    (hy : y ∈ φ.locals) :
    Term.realize M g (.sigma x φ) = {a | ∃ w, a = Sum.inl w ∧ ∃ X, B X w} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g', hg, ha, hr⟩
    obtain ⟨w, hx, hB⟩ := (hφ g' hg).1 hr
    rw [hx] at ha
    exact ⟨w, ha, g' y, hB⟩
  · rintro ⟨w, rfl, X, hB⟩
    have hg : Set.EqOn (Function.update (Function.update g x (world w)) y X) g
        {z | z ∉ φ.locals ∧ z ≠ x} := fun z hz => by
      rw [Function.update_of_ne fun h : z = y => hz.1 (h ▸ hy), Function.update_of_ne hz.2]
    refine ⟨_, hg, by simp [Function.update_of_ne hxy.symm, world], (hφ _ hg).2 ⟨w, ?_, ?_⟩⟩
    · rw [Function.update_of_ne hxy.symm, Function.update_self]
    · rwa [Function.update_self]

end Summation

theorem exists_mem_distributive_iff {a : Atom W E} {Q : E → Prop} :
    (∃ X : Set (Atom W E), a ∈ X ∧ X.Nonempty ∧ ∀ b ∈ X, ∃ e, b = Sum.inr e ∧ Q e) ↔
      ∃ e, a = Sum.inr e ∧ Q e := by
  constructor
  · rintro ⟨X, ha, -, H⟩
    exact H a ha
  · rintro ⟨e, rfl, he⟩
    exact ⟨{Sum.inr e}, rfl, ⟨_, rfl⟩, fun b hb => ⟨e, hb, he⟩⟩

theorem exists_mem_singleton_iff {a : Atom W E} {Q : E → Prop} :
    (∃ X : Set (Atom W E), a ∈ X ∧ ∃ e, X = {Sum.inr e} ∧ Q e) ↔ ∃ e, a = Sum.inr e ∧ Q e := by
  constructor
  · rintro ⟨X, ha, e, rfl, he⟩
    exact ⟨e, ha, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨{Sum.inr e}, rfl, e, rfl, he⟩

theorem exists_singleton_iff {Q : E → Prop} :
    (∃ X : Set (Atom W E), ∃ e, X = {Sum.inr e} ∧ Q e) ↔ ∃ e, Q e :=
  ⟨fun ⟨_, e, _, he⟩ => ⟨e, he⟩, fun ⟨e, he⟩ => ⟨_, e, rfl, he⟩⟩

theorem exists_distributive_iff {Q : E → Prop} :
    (∃ X : Set (Atom W E), X.Nonempty ∧ ∀ b ∈ X, ∃ e, b = Sum.inr e ∧ Q e) ↔ ∃ e, Q e := by
  constructor
  · rintro ⟨X, ⟨b, hb⟩, H⟩
    exact (H b hb).imp fun e he => he.2
  · rintro ⟨e, he⟩
    exact ⟨{Sum.inr e}, ⟨_, rfl⟩, fun b hb => ⟨e, hb, he⟩⟩

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
