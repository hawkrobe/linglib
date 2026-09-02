import Linglib.Semantics.Possession.Basic
import Linglib.Semantics.Quantification.Basic

/-!
# Possessive quantifiers

The possessive determiner as a generalized quantifier, after [peters-westerstahl-2006] Chapter 7.
`Poss Q₁ C Q₂ R` composes a possessor quantifier `Q₁` restricted by `C` (*every student's*), a
possessee quantifier `Q₂` (implicit in *John's bikes*, explicit in *several of John's CDs*), and a
possession relation `R`, narrowing the possessor domain by `dom A R` to those who possess an
`A`-thing ([barker-1995]'s narrowing). `PossW` is the variant for a type ⟨1⟩ possessor taken whole
(*John's*), with the narrowing conjunct inside the scope. Which `Q₂` a bare possessive carries —
the universal reading, the definite `allei` of the "definiteness account", an existential — is the
parameter the definiteness debate turns on ([peters-westerstahl-2006] §7.8.2,
[coppock-beaver-2015] §4); nothing here fixes it.

## Main declarations

* `dom`, `Poss`, `PossW` — their (7.27), (7.30), (7.45).
* `Description.toGQ` — a description's possessor and relation, frozen at a situation, fed to
  `PossW`.

## Main statements

* `poss_conservative`, `possW_conservative` — conservativity inherits from `Q₂` alone (the CONSERV
  half of their (7.29), with no hypothesis on `Q₁`).
* `poss_scopeUpMono_of_up_up` and its three sign variants — Proposition 5 (§7.13): the right
  monotonicity of `Poss` is the product of the signs of `Q₁` and `Q₂`.
* `poss_eq_possW_restrict` — Fact 1 (§7.8.1): for a symmetric conservative `Q₁`, narrowing is
  vacuous.
* `possW_individual_existential_import`, `Description.toGQ_existential_import` — *John's A B*
  entails that John possesses an `A`-thing: the `dom` conjunct of (7.45).
* `asNPQ_iff_possW` — [barker-2011]'s type ⟨1⟩ possessive is `PossW` at a Montagovian individual
  with existential `Q₂`.
* `poss_not_quantityInvariant` — with `C` and `R` fixed, `Poss Q₁ C Q₂ R` is "almost never Isom"
  (p. 256).

## References

* [peters-westerstahl-2006], Chapter 7; [peters-westerstahl-2013] is the article-length
  treatment.
* [barker-1995], [barker-2011], [coppock-beaver-2015].
-/

namespace Possession

open Quantification

variable {α : Type*}

/-! ### Domain narrowing -/

/-- `dom A R = {a | ∃ b ∈ A, R a b}`, the possessors of at least one `A`-thing — their (7.27),
p. 254; `Ex (π A R)` at a fixed situation. -/
def dom (A : α → Prop) (R : α → α → Prop) : α → Prop :=
  fun a => ∃ b, A b ∧ R a b

/-! ### Possessive operators -/

/-- Possessive quantifier built from a type ⟨1,1⟩ possessor quantifier:
`Poss Q₁ C Q₂ R A B = Q₁ (C ∩ dom A R) (fun x => Q₂ (A ∩ Rₓ) B)` with `Rₓ y = R x y`; narrowing
restricts the possessor domain to members of `C` who possess some `A`-thing. Their (7.30), p. 255 —
the form of (7.28) for conservative, extensional `Q₁` and `Q₂`, where the universe-extension clause
is moot. -/
def Poss (Q₁ : GQ α) (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B => Q₁ (fun x => C x ∧ dom A R x) (fun x => Q₂ (fun y => A y ∧ R x y) B)

/-- Possessive quantifier built from a type ⟨1⟩ possessor NP taken whole (*John's*, *most
students'*, where the restrictor is not recoverable from `Q`):
`PossW Q Q₂ R A B = Q (dom A R ∩ {a | Q₂ (A ∩ Rₐ) B})`. The narrowing conjunct sits in the scope,
so *John's dogs bark* requires John to own a dog. Their (7.45), p. 260 — the form of (7.44) for
extensional `Q` and conservative, extensional `Q₂`. -/
def PossW (Q : Quantifier α) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B => Q (fun a => dom A R a ∧ Q₂ (fun y => A y ∧ R a y) B)

/-! ### Conservativity -/

/-- Conservativity inherits from `Q₂`, for any `Q₁`: the possessee restrictor `A ∩ Rₓ` refines
`A`, so a conservative `Q₂` cannot tell `B` from `A ∩ B` in the scope (the CONSERV half of their
(7.29), p. 255). -/
theorem poss_conservative {Q₁ Q₂ : GQ α} (C : α → Prop) (R : α → α → Prop)
    (h₂ : Conservative Q₂) : Conservative (Poss Q₁ C Q₂ R) := fun _ _ =>
  iff_of_eq (congrArg (Q₁ _) (funext fun _ => propext
    (Conservative.congr_scope h₂ fun _ hy => (and_iff_right hy.1).symm)))

/-- Conservativity inheritance for the type ⟨1⟩ variant (their remark after (7.44)). -/
theorem possW_conservative {Q : Quantifier α} {Q₂ : GQ α} (R : α → α → Prop)
    (h₂ : Conservative Q₂) : Conservative (PossW Q Q₂ R) := fun _ _ =>
  iff_of_eq (congrArg Q (funext fun _ => propext (and_congr_right fun _ =>
    Conservative.congr_scope h₂ fun _ hy => (and_iff_right hy.1).symm)))

/-! ### Scope monotonicity (Proposition 5, §7.13, p. 288)

`B` occurs only in `Q₂`'s scope, so monotonicity composes: same signs give Mon↑, opposite signs
give Mon↓. -/

/-- `Q₁` Mon↑, `Q₂` Mon↑ ⇒ `Poss` Mon↑ in scope. -/
theorem poss_scopeUpMono_of_up_up {Q₁ Q₂ : GQ α} (C : α → Prop)
    (R : α → α → Prop) (h₁ : ScopeUpwardMono Q₁) (h₂ : ScopeUpwardMono Q₂) :
    ScopeUpwardMono (Poss Q₁ C Q₂ R) :=
  fun _ B B' hBB' => h₁ _ _ _ fun _ => h₂ _ B B' hBB'

/-- `Q₁` Mon↑, `Q₂` Mon↓ ⇒ `Poss` Mon↓ in scope. -/
theorem poss_scopeDownMono_of_up_down {Q₁ Q₂ : GQ α} (C : α → Prop)
    (R : α → α → Prop) (h₁ : ScopeUpwardMono Q₁) (h₂ : ScopeDownwardMono Q₂) :
    ScopeDownwardMono (Poss Q₁ C Q₂ R) :=
  fun _ B B' hBB' => h₁ _ _ _ fun _ => h₂ _ B B' hBB'

/-- `Q₁` Mon↓, `Q₂` Mon↓ ⇒ `Poss` Mon↑ in scope. -/
theorem poss_scopeUpMono_of_down_down {Q₁ Q₂ : GQ α} (C : α → Prop)
    (R : α → α → Prop) (h₁ : ScopeDownwardMono Q₁) (h₂ : ScopeDownwardMono Q₂) :
    ScopeUpwardMono (Poss Q₁ C Q₂ R) :=
  fun _ B B' hBB' => h₁ _ _ _ fun _ => h₂ _ B B' hBB'

/-- `Q₁` Mon↓, `Q₂` Mon↑ ⇒ `Poss` Mon↓ in scope. -/
theorem poss_scopeDownMono_of_down_up {Q₁ Q₂ : GQ α} (C : α → Prop)
    (R : α → α → Prop) (h₁ : ScopeDownwardMono Q₁) (h₂ : ScopeUpwardMono Q₂) :
    ScopeDownwardMono (Poss Q₁ C Q₂ R) :=
  fun _ B B' hBB' => h₁ _ _ _ fun _ => h₂ _ B B' hBB'

/-! ### Narrowing vacuity (Fact 1, §7.8.1, p. 260) -/

/-- For a symmetric conservative possessor quantifier, domain narrowing is vacuous: `Poss Q₁ C Q₂ R`
is `PossW` at `Q₁` frozen to `C`. Narrowing only matters for non-intersective `Q₁` (proportionals
like *most students'*). -/
theorem poss_eq_possW_restrict {Q₁ : GQ α} (hSym : QSymmetric Q₁) (hCons : Conservative Q₁)
    (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) :
    Poss Q₁ C Q₂ R = PossW (restrict Q₁ C) Q₂ R :=
  funext fun _ => funext fun _ =>
    propext ((conserv_symm_iff_int Q₁ hCons).mp hSym _ _ _ _ fun _ => and_assoc)

/-! ### Existential import -/

/-- *John's A B* carries existential import: whatever `Q₂` is, it entails that John possesses an
`A`-thing — the `dom` conjunct of (7.45). -/
theorem possW_individual_existential_import {Q₂ : GQ α} {R : α → α → Prop}
    {a : α} {A B : α → Prop} (h : PossW (individual a) Q₂ R A B) :
    ∃ b, A b ∧ R a b :=
  h.1

/-! ### Denoting a description -/

/-- The quantificational denotation of a possessive description at a situation `s`: its possessor,
as an individual NP, and its relation frozen at `s`, fed to `PossW`; `Q₂` is the (usually covert)
possessee quantifier. -/
def Description.toGQ {E S : Type*} (d : Description E S) (Q₂ : GQ E) (s : S) : GQ E :=
  PossW (individual d.possessor) Q₂ (fun x y => d.relation x y s)

/-- A description's denotation carries existential import: if it holds of possessee class `A` and
scope `B`, the possessor stands in the relation to some `A`-thing. -/
theorem Description.toGQ_existential_import {E S : Type*} (d : Description E S) (Q₂ : GQ E)
    (s : S) {A B : E → Prop} (h : d.toGQ Q₂ s A B) : ∃ b, A b ∧ d.relation d.possessor b s :=
  possW_individual_existential_import h

/-! ### Barker's type ⟨1⟩ possessive -/

/-- [barker-2011]'s possessive quantifier `asNPQ` (`⟦John's⟧ = fun P => ∃ y, R j y ∧ P y`) is
`PossW` at a Montagovian individual with existential `Q₂` and trivial possessee restrictor — the
possessee class is folded into `R` by Barker's `π` shift. -/
theorem asNPQ_iff_possW (a : α) (R : α → α → Prop) (P : α → Prop) :
    asNPQ a R P ↔ PossW (individual a) some_sem R (fun _ => True) P := by
  simp only [asNPQ, PossW, dom, individual, some_sem, true_and]
  exact ⟨fun ⟨y, hR, hP⟩ => ⟨⟨y, hR⟩, y, hR, hP⟩, fun ⟨_, y, hR, hP⟩ => ⟨y, hR, hP⟩⟩

/-! ### Non-logicality -/

/-- With a fixed possession relation, possessive GQs are not isomorphism-invariant: permuting
`Bool` by `not` flips `some (· = true)'s (·) (⊤)` from true to false, because `R` does not travel
along the permutation. "Due to the presence of the fixed set C and relation R, Poss(Q₁, C, Q₂, R)
is almost never Isom" (p. 256); an operation closely related to `Poss` itself is Isom (their
Chapter 9.2). -/
theorem poss_not_quantityInvariant :
    ¬ QuantityInvariant
        (Poss (some_sem (α := Bool)) (fun _ => True) some_sem
          (fun x y => x = true ∧ y = true)) := by
  intro h
  have hiff := h (fun x => x = true) (fun _ => True) (fun x => x = false)
    (fun _ => True) Bool.not
    ((Function.Involutive.bijective fun b => Bool.not_not b))
    (fun x => by cases x <;> simp) (fun _ => Iff.rfl)
  have hpos : Poss (some_sem (α := Bool)) (fun _ => True) some_sem
      (fun x y => x = true ∧ y = true) (fun x => x = true) (fun _ => True) :=
    ⟨true, ⟨trivial, true, rfl, rfl, rfl⟩, true, ⟨rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨x, ⟨-, b, hb, -, hb'⟩, -⟩ := hiff.mp hpos
  exact absurd (hb' ▸ hb) (by simp)

end Possession
