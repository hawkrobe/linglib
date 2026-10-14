module

public import Linglib.Semantics.Possession.Relationalizer
public import Linglib.Semantics.Quantification.Basic

/-!
# Possessive quantifiers

The possessive determiner as a generalized quantifier, after Peters and Westerståhl.
`Poss Q₁ C Q₂ R` composes a possessor quantifier `Q₁` restricted by `C` (*every student's*), a
possessee quantifier `Q₂` (implicit in *John's bikes*, explicit in *several of John's CDs*) and a
possession relation `R`, narrowing the possessor domain to `dom A R`, those who possess an
`A`-thing. `PossNP` is the variant whose possessor is a type ⟨1⟩ noun phrase taken whole
(*John's*), with the narrowing conjunct inside the scope. Which `Q₂` a bare possessive carries,
universal, definite or existential, is the parameter the definiteness debate turns on, and
nothing here fixes it.

## Main definitions

* `Possession.Poss`: the possessive quantifier over a quantified possessor.
* `Possession.PossNP`: the possessive quantifier over a whole possessor noun phrase.

## Main statements

* `Possession.poss_conservative`: conservativity is inherited from `Q₂` alone.
* `Possession.poss_scopeUpMono_of_up_up` and its three sign variants: the scope monotonicity of
  `Poss` is the product of the signs of `Q₁` and `Q₂`.
* `Possession.poss_eq_possNP_restrict`: for a symmetric conservative `Q₁` narrowing is vacuous.
* `Possession.poss_not_quantityInvariant`: with `C` and `R` fixed, `Poss` is not
  isomorphism-invariant.

## References

* [peters-westerstahl-2006]
* [peters-westerstahl-2013]
* [barker-1995]
* [coppock-beaver-2015]
-/

@[expose] public section

namespace Possession

open Quantifier Quantifier.GQ Quantifier.NP

variable {α : Type*}

/-! ### Possessive operators -/

/-- The possessive quantifier of a type ⟨1,1⟩ possessor quantifier is
`Poss Q₁ C Q₂ R A B = Q₁ (C ∩ dom A R) {x | Q₂ (A ∩ Rₓ) B}` with `Rₓ y = R x y`, where narrowing to
`dom A R`, their (7.27), restricts the possessor domain to members of `C` who possess some
`A`-thing. Their (7.30), p. 255, the form of (7.28) for conservative, extensional `Q₁` and `Q₂`,
where the universe-extension clause is moot. -/
def Poss (Q₁ : GQ α) (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B ↦ Q₁ (fun x ↦ C x ∧ dom A R x) (fun x ↦ Q₂ (fun y ↦ A y ∧ R x y) B)

/-- The possessive quantifier of a type ⟨1⟩ possessor noun phrase taken whole (*John's*, *most
students'*, where the restrictor is not recoverable from `Q`) is
`PossNP Q Q₂ R A B = Q (dom A R ∩ {a | Q₂ (A ∩ Rₐ) B})`. The narrowing conjunct sits in the scope,
so *John's dogs bark* requires John to own a dog. Their (7.45), p. 260, the form of (7.44) for
extensional `Q` and conservative, extensional `Q₂`. -/
def PossNP (Q : NP α) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B ↦ Q (fun a ↦ dom A R a ∧ Q₂ (fun y ↦ A y ∧ R a y) B)

/-! ### Conservativity -/

/-- Conservativity inherits from `Q₂` for any `Q₁`, since the possessee restrictor `A ∩ Rₓ`
refines `A`, so a conservative `Q₂` cannot tell `B` from `A ∩ B` in the scope (the CONSERV half
of their (7.29), p. 255). -/
theorem poss_conservative {Q₁ Q₂ : GQ α} (C : α → Prop) (R : α → α → Prop)
    (h₂ : Conservative Q₂) : Conservative (Poss Q₁ C Q₂ R) := fun _ _ ↦
  iff_of_eq (congrArg (Q₁ _) (funext fun _ ↦ propext
    (Conservative.congr_scope h₂ fun _ hy ↦ (and_iff_right hy.1).symm)))

/-- Conservativity inheritance for the type ⟨1⟩ variant (their remark after (7.44)). -/
theorem possNP_conservative {Q : NP α} {Q₂ : GQ α} (R : α → α → Prop)
    (h₂ : Conservative Q₂) : Conservative (PossNP Q Q₂ R) := fun _ _ ↦
  iff_of_eq (congrArg Q (funext fun _ ↦ propext (and_congr_right fun _ ↦
    Conservative.congr_scope h₂ fun _ hy ↦ (and_iff_right hy.1).symm)))

/-! ### Scope monotonicity (Proposition 5, §7.13, p. 288)

`B` occurs only in `Q₂`'s scope, so monotonicity composes: same signs give Mon↑, opposite signs
give Mon↓. -/

/-- `Q₁` Mon↑, `Q₂` Mon↑ ⇒ `Poss` Mon↑ in scope. -/
theorem poss_scopeUpMono_of_up_up {Q₁ Q₂ : GQ α} (C : α → Prop)
    (R : α → α → Prop) (h₁ : ScopeMonotone Q₁) (h₂ : ScopeMonotone Q₂) :
    ScopeMonotone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hBB' ↦ h₁ _ fun _ ↦ h₂ _ hBB'

/-- `Q₁` Mon↑, `Q₂` Mon↓ ⇒ `Poss` Mon↓ in scope. -/
theorem poss_scopeDownMono_of_up_down {Q₁ Q₂ : GQ α} (C : α → Prop)
    (R : α → α → Prop) (h₁ : ScopeMonotone Q₁) (h₂ : ScopeAntitone Q₂) :
    ScopeAntitone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hBB' ↦ h₁ _ fun _ ↦ h₂ _ hBB'

/-- `Q₁` Mon↓, `Q₂` Mon↓ ⇒ `Poss` Mon↑ in scope. -/
theorem poss_scopeUpMono_of_down_down {Q₁ Q₂ : GQ α} (C : α → Prop)
    (R : α → α → Prop) (h₁ : ScopeAntitone Q₁) (h₂ : ScopeAntitone Q₂) :
    ScopeMonotone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hBB' ↦ h₁ _ fun _ ↦ h₂ _ hBB'

/-- `Q₁` Mon↓, `Q₂` Mon↑ ⇒ `Poss` Mon↓ in scope. -/
theorem poss_scopeDownMono_of_down_up {Q₁ Q₂ : GQ α} (C : α → Prop)
    (R : α → α → Prop) (h₁ : ScopeAntitone Q₁) (h₂ : ScopeMonotone Q₂) :
    ScopeAntitone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hBB' ↦ h₁ _ fun _ ↦ h₂ _ hBB'

/-! ### Narrowing vacuity (Fact 1, §7.8.1, p. 260) -/

/-- For a symmetric conservative possessor quantifier, domain narrowing is vacuous, so
`Poss Q₁ C Q₂ R` is `PossNP` at `Q₁` frozen to `C`; narrowing only matters for non-intersective
`Q₁`, such as the proportional *most students'*. -/
theorem poss_eq_possNP_restrict {Q₁ : GQ α} (hSym : Std.Symm Q₁) (hCons : Conservative Q₁)
    (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) :
    Poss Q₁ C Q₂ R = PossNP (restrict Q₁ C) Q₂ R :=
  funext fun _ ↦ funext fun _ ↦
    propext ((conserv_symm_iff_int Q₁ hCons).mp hSym _ _ _ _ fun _ ↦ and_assoc)

/-! ### Existential import -/

/-- *John's A B* carries existential import, since whatever `Q₂` is it entails that John
possesses an `A`-thing, the `dom` conjunct of (7.45). -/
theorem possNP_individual_existential_import {Q₂ : GQ α} {R : α → α → Prop}
    {a : α} {A B : α → Prop} (h : PossNP (individual a) Q₂ R A B) : dom A R a :=
  h.1

/-! ### Non-logicality -/

/-- With a fixed possession relation, possessive GQs are not isomorphism-invariant, since
permuting `Bool` by `not` flips `some (· = true)'s (·) (⊤)` from true to false because `R` does
not travel along the permutation. "Due to the presence of the fixed set C and relation R,
Poss(Q₁, C, Q₂, R) is almost never Isom" (p. 256); an operation closely related to `Poss` itself
is Isom (their Chapter 9.2). -/
theorem poss_not_quantityInvariant :
    ¬ QuantityInvariant
        (Poss (GQ.some (α := Bool)) (fun _ ↦ True) GQ.some
          (fun x y ↦ x = true ∧ y = true)) := by
  intro h
  have hiff := h (fun x ↦ x = true) (fun _ ↦ True) (fun x ↦ x = false)
    (fun _ ↦ True) Bool.not
    ((Function.Involutive.bijective fun b ↦ Bool.not_not b))
    (fun x ↦ by cases x <;> simp) (fun _ ↦ Iff.rfl)
  have hpos : Poss (GQ.some (α := Bool)) (fun _ ↦ True) GQ.some
      (fun x y ↦ x = true ∧ y = true) (fun x ↦ x = true) (fun _ ↦ True) :=
    ⟨true, ⟨trivial, true, rfl, rfl, rfl⟩, true, ⟨rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨x, ⟨-, b, hb, -, hb'⟩, -⟩ := hiff.mp hpos
  exact absurd (hb' ▸ hb) (by simp)

end Possession
