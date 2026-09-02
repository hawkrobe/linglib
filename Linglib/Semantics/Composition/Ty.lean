import Mathlib.Data.Real.Basic
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Semantic types and denotation domains

The semantic types of the composition engine and their denotation domains. `Ty` is the type
grammar —
`e`, `t`, `⟨a,b⟩`, `⟨s,a⟩`, and the degree, cardinality and eventuality sorts of later
work — and `Denot E W ty` computes the domain of possible denotations of each type from an
entity type `E` and an index type `W`: functions denote in function spaces and intensions
in `W`-indexed families, so a denotation is an ordinary Lean term and composition is
function application.

`Denot` is reducible: a denotation of type `⟨e,t⟩` *is* an `E → Prop` to every tactic and
instance, and the pointwise Boolean algebra of a type that ends in `t` is mathlib's `Pi`
instance. `Denot.booleanAlgebra?` computes that algebra by recursion on the type, for the
composition engine's runtime type dispatch.

## Main definitions

* `Ty`: semantic types.
* `Denot E W ty`: the denotation domain of `ty`.
* `Denot.booleanAlgebra?`: the pointwise Boolean algebra of a conjoinable type, `none` on
  a type that does not end in `t`.

## References

* [D. Dowty, R. Wall, S. Peters, *Introduction to Montague Semantics*
  (1981)][dowty-wall-peters-1981]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
* [B. Partee, M. Rooth, *Generalized Conjunction and Type Ambiguity* (1983)][partee-rooth-1983]
-/

namespace Semantics.Composition

/-- Semantic types: Montague's `e`, `t`, `fn a b` (⟨a,b⟩) and `intens a` (⟨s,a⟩), the
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

/-- Denotation domains: `e` denotes in `E`, `t` in `Prop`, `d` in the scale `D`, `n` in
`ℕ`, `⟨a,b⟩` in `Denot a → Denot b` and `⟨s,a⟩` in `W → Denot a`. The eventuality sorts
have the empty domain: nothing here constructs event-typed denotations. -/
abbrev Denot (E W : Type) (ty : Ty) (D : Type := ℝ) : Type :=
  match ty with
  | .e => E
  | .t => Prop
  | .d => D
  | .n => ℕ
  | .v => Empty
  | .s => Empty
  | .fn a b => Denot E W a D → Denot E W b D
  | .intens a => W → Denot E W a D

/-- The pointwise Boolean algebra of a conjoinable type ([partee-rooth-1983]), computed by
recursion on the type: `none` exactly when the type does not end in `t`. At a concrete
type this is the instance `Pi.instBooleanAlgebra` finds statically. -/
def Denot.booleanAlgebra? (E W : Type) (ty : Ty) (D : Type := ℝ) :
    Option (BooleanAlgebra (Denot E W ty D)) :=
  match ty with
  | .t => some inferInstance
  | .fn _ b =>
    (booleanAlgebra? E W b D).map fun (i : BooleanAlgebra (Denot E W b D)) =>
      letI := i; inferInstance
  | .intens a =>
    (booleanAlgebra? E W a D).map fun (i : BooleanAlgebra (Denot E W a D)) =>
      letI := i; inferInstance
  | _ => none

end Semantics.Composition
