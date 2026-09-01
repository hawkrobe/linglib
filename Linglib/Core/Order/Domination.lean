import Mathlib.Data.Set.Basic

/-!
# Lifting a relation from points to sets

Two lifts of a relation `r` on `α` to `Set α`: the ∀∃ **domination lift**
(`dominationLift r A B`: every `b ∈ B` is `r`-dominated by some `a ∈ A` — for a
preorder this is the Smyth, or upper-powerdomain, preorder) and the injective
**matching lift** (`matchingLift`: the dominators can be chosen distinct — the
Gale order when `r` is a linear order). Two closure properties of set relations,
`RightUnion` and `DeterminedBySingletons`, and the fact that the domination lift
has both.
-/

section

variable {α : Type*}

/-- Right-union: `r A B → r A C → r A (B ∪ C)`. -/
def RightUnion (r : Set α → Set α → Prop) : Prop :=
  ∀ A B C, r A B → r A C → r A (B ∪ C)

/-- Determination by singletons: `r A {b} → ∃ a ∈ A, r {a} {b}`. -/
def DeterminedBySingletons (r : Set α → Set α → Prop) : Prop :=
  ∀ (A : Set α) (b : α), r A {b} → ∃ a ∈ A, r {a} {b}

/-- The domination lift: every `b ∈ B` is `r`-dominated by some `a ∈ A`. -/
def dominationLift (r : α → α → Prop) (A B : Set α) : Prop :=
  ∀ b, b ∈ B → ∃ a, a ∈ A ∧ r a b

/-- The matching lift: some injection `f : B ↪ A` dominates pointwise. -/
def matchingLift (r : α → α → Prop) (A B : Set α) : Prop :=
  ∃ (f : α → α),
    (∀ b, b ∈ B → f b ∈ A ∧ r (f b) b) ∧
    (∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → f b₁ = f b₂ → b₁ = b₂)

variable {r : α → α → Prop}

/-- The domination lift is right-union closed. -/
theorem dominationLift_rightUnion : RightUnion (dominationLift r) :=
  fun _ _ _ hAB hAC b hb => hb.elim (hAB b) (hAC b)

/-- The domination lift is determined by singletons. -/
theorem dominationLift_determinedBySingletons : DeterminedBySingletons (dominationLift r) :=
  fun _ b hAb =>
    let ⟨a, ha, hab⟩ := hAb b rfl
    ⟨a, ha, fun _b' hb' => ⟨a, rfl, hb' ▸ hab⟩⟩

end
