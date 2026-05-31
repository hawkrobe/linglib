import Mathlib.Logic.Function.Basic

/-!
# Combinatory logic primitives

The basis combinators `B`, `T`, `S`, `I`, `K`, `C` of combinatory logic, with the
standard identities relating them (`I = S K K`, `B = S (K _) _`, `T = C I`).

These are framework-agnostic substrate: CCG's combinatory rules correspond to them
(forward composition to `B`, type-raising to `T`, the substitution rule to `S`;
@cite{steedman-2000}), but variable-free composition elsewhere — continuation and
applicative composition, Jacobson-style binding — uses the same algebra, so it lives
in `Core/` rather than inside the CCG files.

## Main definitions

- `Combinator.B`, `Combinator.T`, `Combinator.S`, `Combinator.I`, `Combinator.K`,
  `Combinator.C`

## Main statements

- `Combinator.B_comp` — `B` is function composition
- `Combinator.I_eq_SKK`, `Combinator.B_eq_S_K`, `Combinator.T_eq_CI` — the basis
  identities of combinatory logic

## References

- @cite{curry-feys-1958}
- @cite{smullyan-1985}
-/

namespace Combinator

variable {α β γ : Type*}

/-- `B` (composition): `B f g x = f (g x)`. -/
def B (f : β → γ) (g : α → β) : α → γ := λ x => f (g x)

/-- `T` (type-raising): `T x f = f x`. -/
def T (x : α) : (α → β) → β := λ f => f x

/-- `S` (substitution): `S f g x = f x (g x)`. -/
def S (f : α → β → γ) (g : α → β) : α → γ := λ x => f x (g x)

/-- `I` (identity): `I x = x`. -/
def I : α → α := λ x => x

/-- `K` (constant): `K x y = x`. -/
def K (x : α) : β → α := λ _ => x

/-- `C` (commutation): `C f x y = f y x`. -/
def C (f : α → β → γ) (x : β) (y : α) : γ := f y x

@[simp] theorem B_apply (f : β → γ) (g : α → β) (x : α) : B f g x = f (g x) := rfl

@[simp] theorem T_apply (x : α) (f : α → β) : T x f = f x := rfl

@[simp] theorem S_apply (f : α → β → γ) (g : α → β) (x : α) : S f g x = f x (g x) := rfl

@[simp] theorem I_apply (x : α) : (I : α → α) x = x := rfl

@[simp] theorem K_apply (x : α) (y : β) : K x y = x := rfl

@[simp] theorem C_apply (f : α → β → γ) (x : β) (y : α) : C f x y = f y x := rfl

/-- `B` is function composition. -/
theorem B_comp (f : β → γ) (g : α → β) : B f g = f ∘ g := rfl

/-- `I = S K K`: identity is derivable from `S` and `K`. -/
theorem I_eq_SKK : (I : α → α) = S (K : α → (α → α) → α) (K : α → α → α) := by
  funext x; rfl

/-- `B = S (K _) _`: composition is derivable from `S` and `K`. -/
theorem B_eq_S_K (f : β → γ) (g : α → β) : B f g = S (K f) g := by
  funext x; rfl

/-- `T = C I`: type-raising is `C` applied to the identity. -/
theorem T_eq_CI (x : α) : (T x : (α → β) → β) = C (I : (α → β) → α → β) x := by
  funext f; rfl

/-- `C f x y = B (T x) f y`: `C` is derivable from `B` and `T`. -/
theorem C_eq_B_T (f : α → β → γ) (x : β) (y : α) : C f x y = B (T x) f y := rfl

end Combinator
