import Mathlib.Data.List.Basic

/-!
# Shared entailment schema

`Entails`/`Valid` over an abstract satisfaction relation `sat : Pt → Prp → Prop`, where the
*evaluation point* `Pt` is either a **world** (intra-model entailment, the dominant linglib
idiom `∀ w, p w → q w`) or a **model/structure** (logical consequence — see
`Core.Logic.Entailment.FirstOrder` for the mathlib first-order instance, where this schema
reduces to mathlib's `T ⊨ᵇ φ`).

This is the unmixed, single-mode core of `Core.Logic.Consequence.MixedConsequence`
([cobreros-etal-2012]); the mixed (different premise/conclusion mode) version lives there and
is what genuinely two-standard relations (Strawson entailment, tolerant/strict) instantiate.

## Main definitions

* `Entails` / `Valid` — the abstract schema and its premise-free specialization
* `propEntails` — the intra-model instance over propositions as world-sets (`W → Prop`),
  replacing the per-file `entails := (· ⊆ ·)` / `∀ w, p w → q w` definitions
-/

namespace Core.Logic.Entailment

variable {Pt Prp : Type*}

/-- `Entails sat Γ φ`: every evaluation point satisfying all premises also satisfies `φ`. -/
def Entails (sat : Pt → Prp → Prop) (Γ : List Prp) (φ : Prp) : Prop :=
  ∀ x : Pt, (∀ γ ∈ Γ, sat x γ) → sat x φ

/-- `Valid sat φ`: `φ` holds at every evaluation point (premise-free `Entails`). -/
def Valid (sat : Pt → Prp → Prop) (φ : Prp) : Prop :=
  ∀ x : Pt, sat x φ

theorem valid_iff_entails_nil (sat : Pt → Prp → Prop) (φ : Prp) :
    Valid sat φ ↔ Entails sat [] φ := by
  simp [Valid, Entails]

/-- Reflexivity: a premise entails itself. -/
theorem entails_self (sat : Pt → Prp → Prop) (φ : Prp) : Entails sat [φ] φ :=
  fun _ h => h φ (by simp)

/-- Premise monotonicity: a superset of premises entails at least as much. -/
theorem entails_mono_premises {sat : Pt → Prp → Prop} {Γ Δ : List Prp} {φ : Prp}
    (hsub : ∀ γ ∈ Γ, γ ∈ Δ) (h : Entails sat Γ φ) : Entails sat Δ φ :=
  fun x hΔ => h x (fun γ hγ => hΔ γ (hsub γ hγ))

/-- Cut: if every member of `Δ` follows from `Γ` and `φ` follows from `Δ`, then `φ`
    follows from `Γ`. -/
theorem entails_cut {sat : Pt → Prp → Prop} {Γ Δ : List Prp} {φ : Prp}
    (hΔ : ∀ δ ∈ Δ, Entails sat Γ δ) (h : Entails sat Δ φ) : Entails sat Γ φ :=
  fun x hΓ => h x (fun δ hδ => hΔ δ hδ x hΓ)

/-! ### Intra-model propositional entailment

The dominant linglib instance: `Pt := W` (worlds/indices), propositions are world-sets
`W → Prop`, and `sat w p := p w`. -/

/-- `p ⊨ q` over propositions-as-world-sets: `∀ w, p w → q w`. The canonical instance of
`Entails` with `Pt := W`, `sat w r := r w`. -/
def propEntails {W : Type*} (p q : W → Prop) : Prop :=
  Entails (Pt := W) (fun w r => r w) [p] q

theorem propEntails_iff {W : Type*} (p q : W → Prop) :
    propEntails p q ↔ ∀ w, p w → q w := by
  simp [propEntails, Entails]

@[refl] theorem propEntails_refl {W : Type*} (p : W → Prop) : propEntails p p :=
  (propEntails_iff p p).mpr fun _ h => h

theorem propEntails_trans {W : Type*} {p q r : W → Prop}
    (h₁ : propEntails p q) (h₂ : propEntails q r) : propEntails p r :=
  (propEntails_iff _ _).mpr fun w hp =>
    (propEntails_iff _ _).mp h₂ w ((propEntails_iff _ _).mp h₁ w hp)

end Core.Logic.Entailment
