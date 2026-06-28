import Linglib.Core.Computability.Subregular.Logic.WordModel

/-!
# Quantifier-free logic over word models

The quantifier-free (QF) fragment of the logic of word models. Terms are built from a variable
by applying the successor/predecessor partial functions; formulas are boolean combinations of
atomic label/equality/definedness tests. Because successor is a *function*, a QF term reaches a
*bounded* neighbourhood of its variable with no quantifiers — the syntactic counterpart of
strict locality (an existential like `∃w,y[succ w x ∧ succ x y ∧ …]` collapses to the
quantifier-free `… (pred x) ∧ … (succ x)`). The locality bridge (`Logic/LocalityBridge.lean`)
makes this precise: QF-definable transductions are exactly the Input-Strictly-Local functions of
`Subregular` ([chandlee-2014], [chandlee-jardine-2019]).

## Main definitions

* `Subregular.Logic.Term` — QF terms (`var`, `succ`, `pred`); `Term.eval` interprets them.
* `Subregular.Logic.Atom` / `QF` — atomic and quantifier-free formulas.
* `Atom.Realize` / `QF.Realize` — satisfaction in a word model under an assignment, decidable.
* `QF.initial` / `QF.final` — edge positions, derived from definedness of `pred`/`succ`.

## Implementation notes

`Realize` is `Prop`-valued (mathlib's model-theory idiom) with a derived `Decidable` instance,
so worked examples close by `decide`. A `Term` evaluates to `Option ℕ`, `none` once it falls off
an edge; atoms over an undefined term are false.
-/

namespace Subregular.Logic

variable {α V : Type*}

/-- Quantifier-free **terms**: a variable, or the successor/predecessor of a term. The
`succ`/`pred` chains give bounded-window reach without quantifiers. -/
inductive Term (V : Type*) where
  | var : V → Term V
  | succ : Term V → Term V
  | pred : Term V → Term V
  deriving DecidableEq

namespace Term

/-- Interpret a term in a word model under an assignment `ρ` of variables to positions;
`none` if it falls off an edge. -/
def eval (w : WordModel α) (ρ : V → ℕ) : Term V → Option ℕ
  | .var v  => if w.Mem (ρ v) then some (ρ v) else none
  | .succ t => (eval w ρ t).bind w.succ?
  | .pred t => (eval w ρ t).bind w.pred?

end Term

/-- Atomic quantifier-free formulas: a label test, an equality of positions, or a
definedness test on a term. -/
inductive Atom (α V : Type*) where
  | label : α → Term V → Atom α V
  | eq : Term V → Term V → Atom α V
  | defined : Term V → Atom α V

/-- Quantifier-free formulas: boolean combinations of atoms (no quantifiers). -/
inductive QF (α V : Type*) where
  | atom : Atom α V → QF α V
  | tru : QF α V
  | fls : QF α V
  | neg : QF α V → QF α V
  | conj : QF α V → QF α V → QF α V
  | disj : QF α V → QF α V → QF α V

variable [DecidableEq α]

/-- Satisfaction of an atom in `w` under assignment `ρ`. -/
def Atom.Realize (w : WordModel α) (ρ : V → ℕ) : Atom α V → Prop
  | .label a t => (t.eval w ρ).bind w.label? = some a
  | .eq t₁ t₂  => t₁.eval w ρ = t₂.eval w ρ ∧ t₁.eval w ρ ≠ none
  | .defined t => t.eval w ρ ≠ none

instance (w : WordModel α) (ρ : V → ℕ) (a : Atom α V) : Decidable (a.Realize w ρ) := by
  cases a <;> unfold Atom.Realize <;> infer_instance

/-- Satisfaction of a quantifier-free formula in `w` under assignment `ρ`. -/
def QF.Realize (w : WordModel α) (ρ : V → ℕ) : QF α V → Prop
  | .atom a   => a.Realize w ρ
  | .tru      => True
  | .fls      => False
  | .neg φ    => ¬ φ.Realize w ρ
  | .conj φ ψ => φ.Realize w ρ ∧ ψ.Realize w ρ
  | .disj φ ψ => φ.Realize w ρ ∨ ψ.Realize w ρ

instance QF.instDecidableRealize (w : WordModel α) (ρ : V → ℕ) :
    (φ : QF α V) → Decidable (φ.Realize w ρ)
  | .atom a   => inferInstanceAs (Decidable (a.Realize w ρ))
  | .tru      => isTrue trivial
  | .fls      => isFalse not_false
  | .neg φ    => @instDecidableNot _ (QF.instDecidableRealize w ρ φ)
  | .conj φ ψ => @instDecidableAnd _ _ (QF.instDecidableRealize w ρ φ) (QF.instDecidableRealize w ρ ψ)
  | .disj φ ψ => @instDecidableOr _ _ (QF.instDecidableRealize w ρ φ) (QF.instDecidableRealize w ρ ψ)

/-- `t` is an initial position: in-domain with no predecessor. -/
def QF.initial (t : Term V) : QF α V :=
  .conj (.atom (.defined t)) (.neg (.atom (.defined t.pred)))

/-- `t` is a final position: in-domain with no successor. -/
def QF.final (t : Term V) : QF α V :=
  .conj (.atom (.defined t)) (.neg (.atom (.defined t.succ)))

/-! ### Worked example -/

section Example

private inductive Sym | a | b deriving DecidableEq

/-- `x` is flanked by `a`s — a bounded two-sided context stated quantifier-free via `succ`/`pred`
terms, with no existential. -/
private def flankedByA : QF Sym Unit :=
  .conj (.atom (.label .a (.pred (.var ())))) (.atom (.label .a (.succ (.var ()))))

private def aba : WordModel Sym := [Sym.a, Sym.b, Sym.a]

-- Position 1 (the `b`) is flanked by `a`s; position 0 is not (no predecessor).
example : flankedByA.Realize aba (fun _ => 1) := by decide
example : ¬ flankedByA.Realize aba (fun _ => 0) := by decide
-- The edge predicates compute as expected.
example : (QF.initial (α := Sym) (.var ())).Realize aba (fun _ => 0) := by decide
example : (QF.final (α := Sym) (.var ())).Realize aba (fun _ => 2) := by decide

end Example

end Subregular.Logic
