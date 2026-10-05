module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Semantic types and denotation domains

The semantic types of the composition engine and their denotation domains. `Ty` is the type
grammar —
`e`, `t`, `⟨a,b⟩`, `⟨s,a⟩`, and the degree, cardinality and eventuality sorts of later
work — and `Ty.Domain E W ty` computes the domain of possible denotations of each type from an
entity type `E` and an index type `W`: functions denote in function spaces and intensions
in `W`-indexed families, so a denotation is an ordinary Lean term and composition is
function application.

`Ty.Domain` is reducible: a denotation of type `⟨e,t⟩` *is* an `E → Prop` to every tactic and
instance, and the pointwise Boolean algebra of a type that ends in `t` is mathlib's `Pi`
instance. `Ty.Domain.completeBooleanAlgebra?` computes that algebra, which is complete, by
recursion on the type, for the composition engine's runtime type dispatch.

## Main definitions

* `Ty`: semantic types.
* `Ty.Domain E W ty`: the denotation domain of `ty`.
* `Denotation E W M`: a semantic type with an `M`-computation in its domain.
* `Ty.Domain.completeBooleanAlgebra?`: the pointwise complete Boolean algebra of a conjoinable
  type, `none` on a type that does not end in `t`.
* `Ty.apply?`, `Ty.intensionalApplication?`, `Ty.predicateModification?`,
  `Ty.eventIdentification?`: the type each binary composition mode composes from its
  daughters' types, `none` when the mode does not apply.

## References

* [D. Dowty, R. Wall, S. Peters, *Introduction to Montague Semantics*
  (1981)][dowty-wall-peters-1981]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
* [B. Partee, M. Rooth, *Generalized Conjunction and Type Ambiguity* (1983)][partee-rooth-1983]
-/

@[expose] public section

namespace Semantics.Composition

/-- The semantic types are Montague's `e`, `t`, `fn a b` (⟨a,b⟩) and `intens a` (⟨s,a⟩), the
degree sort `d` ([heim-2001], [wellwood-2015]), the cardinality sort `n` ([sudo-2016],
[scontras-2014], [little-moroney-royer-2022]), and the eventuality sorts `v` (events) and
`s` (states) ([davidson-1967], [parsons-1990], [yu-ausensi-smith-2023]). -/
inductive Ty where
  | e | t
  /-- Degrees, denoting in the model's scale. -/
  | d
  /-- Cardinalities, denoting in `ℕ`. -/
  | n
  /-- Events. -/
  | v
  /-- States (not the index sort, which is `intens`). -/
  | s
  /-- Functions `⟨a,b⟩`. -/
  | fn : Ty → Ty → Ty
  /-- Intensions `⟨s,a⟩`. -/
  | intens : Ty → Ty
  deriving Repr, DecidableEq

@[inherit_doc] infixr:25 " ⇒ " => Ty.fn

/-- `⟨e,t⟩`, properties of individuals. -/
abbrev Ty.et : Ty := .e ⇒ .t
/-- `⟨e,⟨e,t⟩⟩`, relations between individuals. -/
abbrev Ty.eet : Ty := .e ⇒ .e ⇒ .t
/-- `⟨⟨e,t⟩,t⟩`, generalized quantifiers. -/
abbrev Ty.ett : Ty := (.e ⇒ .t) ⇒ .t
/-- `⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩`, determiners. -/
abbrev Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

/-- The types of [heim-kratzer-1998]'s extensional fragment, built from `e`, `t` and
functions. -/
inductive Ty.Extensional : Ty → Prop
  | e : Extensional .e
  | t : Extensional .t
  | fn {a b : Ty} : Extensional a → Extensional b → Extensional (.fn a b)

/-- The type `e` denotes in `E`, `t` in `Prop`, `d` in the scale `D`, `n` in
`ℕ`, `⟨a,b⟩` in `Ty.Domain a → Ty.Domain b` and `⟨s,a⟩` in `W → Ty.Domain a`. The eventuality sorts
have the empty domain, since nothing here constructs event-typed denotations. -/
abbrev Ty.Domain (E W : Type) (ty : Ty) (D : Type := ℝ) : Type :=
  match ty with
  | .e => E
  | .t => Prop
  | .d => D
  | .n => ℕ
  | .v => Empty
  | .s => Empty
  | .fn a b => Ty.Domain E W a D → Ty.Domain E W b D
  | .intens a => W → Ty.Domain E W a D

/-- A denotation in the Montague type system is a semantic type together with an `M`-computation
in the domain of that type. `M := Id` is the pure [heim-kratzer-1998] carrier; effectful
denotations supply `M`. -/
abbrev Denotation (E W : Type) (M : Type → Type := Id) (D : Type := ℝ) : Type :=
  (ty : Ty) × M (Ty.Domain E W ty D)

/-- The domain of a conjoinable type carries the pointwise complete Boolean algebra
([partee-rooth-1983]), computed by recursion on the type and `none` exactly when the type does
not end in `t`. At a concrete type it is the instance `Pi.instCompleteBooleanAlgebra` finds
statically. -/
def Ty.Domain.completeBooleanAlgebra? (E W : Type) (ty : Ty) (D : Type := ℝ) :
    Option (CompleteBooleanAlgebra (Ty.Domain E W ty D)) :=
  match ty with
  | .t => some inferInstance
  | .fn _ b =>
    (completeBooleanAlgebra? E W b D).map fun (i : CompleteBooleanAlgebra (Ty.Domain E W b D)) =>
      letI := i; inferInstance
  | .intens a =>
    (completeBooleanAlgebra? E W a D).map fun (i : CompleteBooleanAlgebra (Ty.Domain E W a D)) =>
      letI := i; inferInstance
  | _ => none

/-! ### The types the composition modes compose

A binary composition mode composes a type from its daughters' types alone. These functions
compute it; the composition engines' modes agree with them on types. -/

/-- `σ.apply? τ` is the type of applying a denotation of type `σ` to one of type `τ`, which is
the codomain of `σ` when `σ` is a function type from `τ` and `none` otherwise. -/
def Ty.apply? : Ty → Ty → Option Ty
  | .fn σ τ, σ' => if σ = σ' then some τ else none
  | _, _ => none

/-- `σ.intensionalApplication? τ` is the type intensional functional application composes, a
daughter expecting an intension applying to the constant intension of its sister, with `σ`
tried as the function first. -/
def Ty.intensionalApplication? : Ty → Ty → Option Ty
  | .fn (.intens σ) τ, t₂ =>
    if σ = t₂ then some τ else
      match t₂ with
      | .fn (.intens σ') τ' => if σ' = .fn (.intens σ) τ then some τ' else none
      | _ => none
  | t₁, .fn (.intens σ) τ => if σ = t₁ then some τ else none
  | _, _ => none

/-- `σ.predicateModification? τ` is the type predicate modification composes, `⟨e,t⟩` from two
predicates of that type. -/
def Ty.predicateModification? : Ty → Ty → Option Ty
  | .fn .e .t, .fn .e .t => some (.fn .e .t)
  | _, _ => none

/-- `σ.eventIdentification? τ` is the type event identification composes, `⟨e,⟨e,t⟩⟩` from a role
head of that type and an eventuality predicate of type `⟨e,t⟩`, in either order. -/
def Ty.eventIdentification? : Ty → Ty → Option Ty
  | .fn .e (.fn .e .t), .fn .e .t => some (.e ⇒ .e ⇒ .t)
  | .fn .e .t, .fn .e (.fn .e .t) => some (.e ⇒ .e ⇒ .t)
  | _, _ => none

/-- No type is its own argument type, so a type never applies to a function type from
itself. -/
theorem Ty.apply?_fn_self (σ τ : Ty) : σ.apply? (σ ⇒ τ) = none := by
  cases σ with
  | fn a b =>
    simp only [Ty.apply?]
    split_ifs with h
    · have := congrArg sizeOf h
      simp only [Ty.fn.sizeOf_spec] at this
      omega
    · rfl
  | _ => rfl

/-- Intensional application never applies to extensional types. -/
theorem Ty.intensionalApplication?_eq_none {σ τ : Ty} (h₁ : σ.Extensional)
    (h₂ : τ.Extensional) : σ.intensionalApplication? τ = none := by
  rcases h₁ with _ | _ | ⟨ha, _⟩ <;> rcases h₂ with _ | _ | ⟨ha', _⟩ <;>
    (try rcases ha with _ | _ | _) <;> (try rcases ha' with _ | _ | _) <;> rfl

end Semantics.Composition
