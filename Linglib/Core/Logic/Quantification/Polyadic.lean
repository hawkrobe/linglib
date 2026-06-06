import Linglib.Core.Logic.Quantification.Defs

/-!
# Polyadic Quantifiers
[peters-westerstahl-2006] [hintikka-1996]

Three mechanisms for building polyadic (multi-sorted) quantifiers from
monadic (type ⟨1,1⟩) ones:

1. **Iteration**: Q₁x Q₂y R(x,y) — nested quantification
2. **Resumption**: Qx R(x,x) — a single quantifier on the diagonal
3. **Branching**: Hintikka's partially ordered quantifiers

These capture the semantic content of multi-quantifier sentences at the
model-theoretic level, complementing linglib's syntactic scope mechanisms
in `Semantics/Composition/Scope.lean` and `Studies/HeimKratzer1998.lean`.
-/

namespace Core.Quantification.Polyadic

open Core.Quantification

variable {α : Type*}

/-! ### Core Operations -/

/-- Iteration: Q₁x Q₂y R(x,y). Nested quantification where Q₂ is in the
    scope of Q₁.

    "Every student read some book" =
    iterate(every, student, some, book)(read)
    = every(student, λx. some(book, λy. read(x,y)))

    [peters-westerstahl-2006] Ch 10. -/
def iterate (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  Q₁ A (λ x => Q₂ B (λ y => R x y))

/-- Resumption: one quantifier binding two argument positions.

    "Most students like themselves" =
    resume(most, student)(like)
    = most(student, λx. like(x,x))

    Resumption only accesses the diagonal of R.
    [peters-westerstahl-2006] Ch 10. -/
def resume (Q : GQ α) (A : α → Prop) (R : α → α → Prop) : Prop :=
  Q A (λ x => R x x)

/-- Branching (Hintikka) quantifier: Q₁ and Q₂ are evaluated independently
    (neither is in the scope of the other).

    The Skolem-function characterization: there exist choice functions
    witnessing both quantifiers simultaneously.

    "Some relative of each villager and some friend of each townsman
     hate each other" — the two quantifiers don't scope over each other.

    Simplified Barwise (1979) version:
    branch(Q₁, A, Q₂, B)(R) ↔ ∃f g. Q₁(A, λx. R(x, f(x))) ∧ Q₂(B, λy. R(g(y), y))

    [hintikka-1996] [peters-westerstahl-2006] Ch 10. -/
def branch (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  ∃ (f g : α → α),
    Q₁ A (λ x => B (f x) ∧ R x (f x)) ∧
    Q₂ B (λ y => A (g y) ∧ R (g y) y)

/-! ### Scope Order and Iteration -/

/-- Surface scope = iterate(Q₁, A, Q₂, B)(R).
    Inverse scope = iterate(Q₂, B, Q₁, A)(flip R).
    These are the two "linear" readings of a two-quantifier sentence.
    [peters-westerstahl-2006] Ch 10. -/
def surfaceScope (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  iterate Q₁ Q₂ A B R

def inverseScope (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  iterate Q₂ Q₁ B A (λ y x => R x y)

/-! ### Monotonicity Inheritance -/

/-- Iteration preserves scope monotonicity: if both Q₁ and Q₂ are Mon↑,
    then iterate(Q₁, A, Q₂, B) is monotone in R (pointwise).
    [peters-westerstahl-2006] Ch 10. -/
theorem iterate_mono_in_R (Q₁ Q₂ : GQ α) (A B : α → Prop)
    (R R' : α → α → Prop)
    (h₁ : ScopeUpwardMono Q₁) (h₂ : ScopeUpwardMono Q₂)
    (hR : ∀ x y, R x y → R' x y)
    (hIt : iterate Q₁ Q₂ A B R) :
    iterate Q₁ Q₂ A B R' := by
  unfold iterate at *
  apply h₁ A _ _ _ hIt
  intro x hx
  exact h₂ B _ _ (λ y => hR x y) hx

/-- Resumption preserves scope monotonicity. -/
theorem resume_mono_in_R (Q : GQ α) (A : α → Prop)
    (R R' : α → α → Prop)
    (hUp : ScopeUpwardMono Q)
    (hR : ∀ x, R x x → R' x x)
    (hRes : resume Q A R) :
    resume Q A R' := by
  unfold resume at *
  exact hUp A _ _ hR hRes

end Core.Quantification.Polyadic
