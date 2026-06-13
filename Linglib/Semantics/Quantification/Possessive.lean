import Linglib.Semantics.ArgumentStructure.Relational

/-!
# Possessive Quantifiers
[peters-westerstahl-2006] [barker-2011]

`Poss Q₁ C Q₂ R` composes a possessor quantifier `Q₁` restricted by `C`
("every student's"), a possessee quantifier `Q₂` (typically covert), and a
possession relation `R`: "every student's cat sleeps" =
`Poss every student a own cat sleep`. The possessor restrictor is narrowed by
`dom A R` to those who possess an `A`-thing (narrowing: [barker-1995] p. 139);
`PossW` is the variant for type ⟨1⟩ possessor NPs taken whole ("John's"),
which keeps narrowing in the scope.

## Main declarations

- `dom`, `Poss`, `PossW`: P&W (7.27), (7.30), (7.44)–(7.45)
- `poss_conservative`, `possW_conservative`: conservativity inherits from `Q₂`
  (P&W (7.29))
- `poss_scopeUpMono_of_up_up` (and the three other sign combinations): scope
  monotonicity inheritance (P&W Proposition 5, §7.13)
- `poss_eq_possW_restrict`: narrowing is vacuous for symmetric conservative
  `Q₁` (P&W Fact 1, §7.8.1)
- `possW_individual_existential_import`: "John's A B" entails John possesses
  an A-thing ([peters-westerstahl-2013])
- `possessiveAsNPQ_iff_possW`: [barker-2011]'s type ⟨1⟩ possessive
  (`Relational.possessiveAsNPQ`) is `PossW` of a Montagovian individual with
  existential `Q₂`
- `poss_not_quantityInvariant`: possessive GQs with a fixed `R` are not
  isomorphism-invariant (P&W p. 256)
-/

namespace Semantics.Quantification.Possessive

open Core.Quantification

variable {α : Type*}

/-! ### Domain narrowing -/

/-- `dom A R = {a | ∃ b ∈ A, R a b}` — the possessors of at least one
    `A`-thing (the `α → Prop`-valued relative of `Rel.preimage`).
    [peters-westerstahl-2006] (7.27), p. 254. -/
def dom (A : α → Prop) (R : α → α → Prop) : α → Prop :=
  fun a => ∃ b, A b ∧ R a b

/-! ### Possessive operators -/

/-- Possessive quantifier built from a type ⟨1,1⟩ possessor quantifier:

    `Poss Q₁ C Q₂ R A B = Q₁ (C ∩ dom A R) (fun x => Q₂ (A ∩ Rₓ) B)`

    where `Rₓ y = R x y`. Domain narrowing restricts the possessor domain to
    members of `C` who possess some `A`-thing.
    [peters-westerstahl-2006] (7.30), p. 256 — the CONSERV+EXT form of (7.28);
    on a fixed carrier the universe-extension clause is moot. -/
def Poss (Q₁ : GQ α) (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B => Q₁ (fun x => C x ∧ dom A R x) (fun x => Q₂ (fun y => A y ∧ R x y) B)

/-- Possessive quantifier built from a type ⟨1⟩ possessor NP taken whole
    ("John's", "most students'" — the restrictor is not recoverable from `Q`):

    `PossW Q Q₂ R A B = Q (dom A R ∩ {a | Q₂ (A ∩ Rₐ) B})`

    Narrowing stays in the scope, preserving possessive existential import
    ("John's dogs bark" requires John to own a dog).
    [peters-westerstahl-2006] (7.44)–(7.45), pp. 259–260 (Possʷ). -/
def PossW (Q : NPQ α) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B => Q (fun a => dom A R a ∧ Q₂ (fun y => A y ∧ R a y) B)

/-! ### Conservativity (P&W (7.29)) -/

/-- The possessee restrictor `A ∩ Rₓ` refines `A`, so a conservative `Q₂`
    cannot tell `B` from `A ∩ B` in the scope. -/
private theorem inner_conservative_congr {Q₂ : GQ α} (h₂ : Conservative Q₂)
    (A B : α → Prop) (R : α → α → Prop) (x : α) :
    Q₂ (fun y => A y ∧ R x y) B ↔
      Q₂ (fun y => A y ∧ R x y) (fun y => A y ∧ B y) := by
  have e : (fun y => (A y ∧ R x y) ∧ B y)
      = (fun y => (A y ∧ R x y) ∧ (A y ∧ B y)) := by
    funext y
    exact propext ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  calc Q₂ (fun y => A y ∧ R x y) B
      ↔ Q₂ (fun y => A y ∧ R x y) (fun y => (A y ∧ R x y) ∧ B y) := h₂ _ B
    _ ↔ Q₂ (fun y => A y ∧ R x y) (fun y => (A y ∧ R x y) ∧ (A y ∧ B y)) := by
        rw [e]
    _ ↔ Q₂ (fun y => A y ∧ R x y) (fun y => A y ∧ B y) := (h₂ _ _).symm

/-- Conservativity inheritance: if `Q₂` is conservative, so is
    `Poss Q₁ C Q₂ R`, for any `Q₁`. [peters-westerstahl-2006] (7.29), p. 255. -/
theorem poss_conservative {Q₁ Q₂ : GQ α} (C : α → Prop) (R : α → α → Prop)
    (h₂ : Conservative Q₂) : Conservative (Poss Q₁ C Q₂ R) := by
  intro A B
  unfold Poss
  rw [funext fun x => propext (inner_conservative_congr h₂ A B R x)]

/-- Conservativity inheritance for the type ⟨1⟩ variant.
    [peters-westerstahl-2006] remark after (7.44). -/
theorem possW_conservative {Q : NPQ α} {Q₂ : GQ α} (R : α → α → Prop)
    (h₂ : Conservative Q₂) : Conservative (PossW Q Q₂ R) := by
  intro A B
  unfold PossW
  rw [funext fun a => propext
    (and_congr_right fun _ => inner_conservative_congr h₂ A B R a)]

/-! ### Scope monotonicity (P&W Proposition 5, §7.13)

`B` occurs only in `Q₂`'s scope, so monotonicity composes: same signs give
Mon↑, opposite signs give Mon↓. -/

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

/-! ### Narrowing vacuity (P&W Fact 1, §7.8.1) -/

/-- For a symmetric conservative possessor quantifier, domain narrowing is
    vacuous: `Poss Q₁ C Q₂ R` agrees with `PossW` at `Q₁` frozen to `C`.
    Narrowing only matters for non-intersective `Q₁` (proportionals like
    "most students'"). [peters-westerstahl-2006] Fact 1, §7.8.1, p. 260. -/
theorem poss_eq_possW_restrict {Q₁ : GQ α} (hSym : QSymmetric Q₁)
    (hCons : Conservative Q₁) (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) :
    Poss Q₁ C Q₂ R = PossW (restrict Q₁ C) Q₂ R := by
  have key : ∀ X Y : α → Prop,
      Q₁ X Y ↔ Q₁ (fun x => X x ∧ Y x) (fun x => X x ∧ Y x) := by
    intro X Y
    have h3 := hCons (fun x => X x ∧ Y x) X
    rw [show (fun x => (X x ∧ Y x) ∧ X x) = (fun x => X x ∧ Y x) from
      funext fun x => propext ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩] at h3
    exact (hCons X Y).trans ((hSym X _).trans h3)
  funext A B
  refine propext (((key _ _).trans ?_).trans (key _ _).symm)
  rw [show (fun x => (C x ∧ dom A R x) ∧ Q₂ (fun y => A y ∧ R x y) B)
      = (fun x => C x ∧ (dom A R x ∧ Q₂ (fun y => A y ∧ R x y) B)) from
    funext fun _ => propext and_assoc]

/-! ### Existential import -/

/-- "John's A B" carries existential import: whatever `Q₂` is, it entails
    that John possesses an `A`-thing — the `dom` conjunct of (7.45).
    [peters-westerstahl-2013]'s headline thesis, at the individual instance. -/
theorem possW_individual_existential_import {Q₂ : GQ α} {R : α → α → Prop}
    {a : α} {A B : α → Prop} (h : PossW (individual a) Q₂ R A B) :
    ∃ b, A b ∧ R a b :=
  h.1

/-! ### Bridge to Barker's type ⟨1⟩ possessive -/

/-- [barker-2011]'s possessive NPQ (`⟦John's⟧ = fun P => ∃ y, R j y ∧ P y`,
    `Relational.possessiveAsNPQ`) is `PossW` at a Montagovian individual with
    existential `Q₂` and trivial possessee restrictor — the possessee class is
    folded into `R` by Barker's π shift. -/
theorem possessiveAsNPQ_iff_possW {E : Type*} (a : E) (R : E → E → Bool)
    (P : E → Prop) :
    Semantics.ArgumentStructure.Relational.possessiveAsNPQ a R P ↔
      PossW (individual a) some_sem (fun x y => R x y = true)
        (fun _ => True) P := by
  unfold Semantics.ArgumentStructure.Relational.possessiveAsNPQ PossW dom
    individual some_sem
  constructor
  · rintro ⟨y, hR, hP⟩
    exact ⟨⟨y, trivial, hR⟩, y, ⟨trivial, hR⟩, hP⟩
  · rintro ⟨-, y, ⟨-, hR⟩, hP⟩
    exact ⟨y, hR, hP⟩

/-! ### Non-logicality -/

/-- Possessive GQs with a fixed possession relation are not
    isomorphism-invariant: permuting `Bool` by `not` flips
    `some (· = true)'s (·) (⊤)` from true to false, because `R` does not
    travel along the permutation. [peters-westerstahl-2006] p. 256 ("due to
    the presence of the fixed set C and relation R, Poss(Q₁,C,Q₂,R) is almost
    never Isom"; the four-argument *operation* `Poss` itself is Isom, Ch 9.2.3). -/
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

end Semantics.Quantification.Possessive
