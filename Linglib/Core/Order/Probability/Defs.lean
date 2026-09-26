module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Defs.Unbundled

/-!
# Qualitative probability orders

Comparative probability reads a relation `r a b` on a Boolean algebra `α` as "`a` is at
least as likely as `b`". This file states the axioms of the subject as unbundled mixin
classes on such a relation, in the style of `IsTrans`, and bundles de Finetti's system,
the standard base of comparative probability that [kraft-pratt-seidenberg-1959] and
[scott-1964] build on, as `QualitativeProbability`: total, transitive, monotone,
non-trivial, and qualitatively additive (`a ≼ b ↔ a \ b ≼ b \ a`). The bundled relation
is stored as `le` and stated in `≤`-vocabulary; the literature's `≿` is the derived `ge`,
mathlib's `GE.ge` pattern, with scoped notation `a ≼[sys] b` / `a ≿[sys] b`, and it is
`ge` that carries the mixins.

## Main definitions

* `IsLikelihoodMono`, `IsQualitativeAdditive`, `IsNontrivial`, `IsComplementReversing` —
  the axiom mixins on a relation; `Strict r` — its asymmetric part `a ≻ b`.
* `QualitativeProbability` — the bundled order, with `ge`, `refl`, `mono`, `trans`,
  `bot_le`, `le_top`, and the mixin instances for `ge`.

## Main statements

* `instComplementReversingOfQualitativeAdditive` — qualitative additivity implies
  complement reversal, via `bᶜ \ aᶜ = a \ b` (`compl_sdiff_compl`).

`[UPSTREAM]` candidate for `Mathlib/Order/Probability/`: order theory with a
probabilistic reading — no measures occur; the representation theory lives in the
sibling files (`Content.lean`, `Scott.lean`, `Representability.lean`, `Completeness.lean`).

## References

* [kraft-pratt-seidenberg-1959]
* [scott-1964]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α]

/-! ### The axioms as mixins -/

/-- Monotonicity: larger events are at least as likely. -/
class IsLikelihoodMono (r : α → α → Prop) : Prop where
  mono : ∀ a b : α, a ≤ b → r b a

/-- Complement reversal: `a ≽ b → bᶜ ≽ aᶜ`. -/
class IsComplementReversing (r : α → α → Prop) : Prop where
  complRev : ∀ a b : α, r a b → r bᶜ aᶜ

/-- Qualitative additivity, de Finetti's axiom: `a ≽ b ↔ (a \ b) ≽ (b \ a)`. -/
class IsQualitativeAdditive (r : α → α → Prop) : Prop where
  qadd : ∀ a b : α, r a b ↔ r (a \ b) (b \ a)

/-- Non-triviality: `⊥` is not at least as likely as `⊤`. -/
class IsNontrivial (r : α → α → Prop) : Prop where
  bot_not_ge_top : ¬ r ⊥ ⊤

export IsLikelihoodMono (mono)
export IsComplementReversing (complRev)
export IsQualitativeAdditive (qadd)

/-- `Strict r a b` ("`a ≻ b`"): the asymmetric part of `r`. -/
def Strict (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ¬ r b a

instance {r : α → α → Prop} [DecidableRel r] : DecidableRel (Strict r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Qualitative additivity implies complement reversal: `bᶜ \ aᶜ = a \ b` and
`aᶜ \ bᶜ = b \ a` turn the additivity equivalence for `bᶜ, aᶜ` into the one for `a, b`. -/
instance (priority := 100) instComplementReversingOfQualitativeAdditive
    {r : α → α → Prop} [h : IsQualitativeAdditive r] : IsComplementReversing r where
  complRev a b hab := by
    rw [h.qadd bᶜ aᶜ, compl_sdiff_compl, compl_sdiff_compl]
    exact (h.qadd a b).mp hab

/-! ### The bundled order -/

/-- A **qualitative probability** order on a Boolean algebra `α`: total,
transitive, monotone, non-trivial, and qualitatively additive — the standard
base system for comparative probability since de Finetti. Every such order on a
finite carrier is represented by a qualitatively additive measure
(`exists_qualAddMeasure_repr`), but by a finitely additive one only below five
atoms ([kraft-pratt-seidenberg-1959]; `Completeness.lean`). Reflexivity and
`⊥ ≼ a` are consequences of monotonicity (`refl`, `bot_le`), not fields. -/
structure QualitativeProbability (α : Type*) [BooleanAlgebra α] where
  /-- The "at most as likely as" relation. -/
  le : α → α → Prop
  /-- Monotonicity: `a ≤ b → a ≼ b`. Use the lemma `mono`. -/
  mono' : ∀ a b : α, a ≤ b → le a b
  /-- Non-triviality: `⊤` is not at most as likely as `⊥`. -/
  nonTrivial : ¬ le ⊤ ⊥
  /-- Totality: any two elements are comparable. -/
  total : ∀ a b : α, le a b ∨ le b a
  /-- Transitivity. Use the lemma `trans`. -/
  trans' : ∀ a b c : α, le a b → le b c → le a c
  /-- Qualitative additivity: `a ≼ b ↔ a \ b ≼ b \ a`. -/
  additive : ∀ a b : α, le a b ↔ le (a \ b) (b \ a)

namespace QualitativeProbability

variable {α : Type*} [BooleanAlgebra α] (sys : QualitativeProbability α)

/-- `sys.ge a b` (`a ≿ b`): `a` is at least as likely as `b` — the converse of
`le`, mathlib's `GE.ge` pattern. This is the relation the logic layer
(`Logic/ComparativeProbability/`) and the literature read. -/
def ge (a b : α) : Prop := sys.le b a

@[inherit_doc le] scoped notation:50 a:51 " ≼[" sys "] " b:51 => QualitativeProbability.le sys a b
@[inherit_doc ge] scoped notation:50 a:51 " ≿[" sys "] " b:51 => QualitativeProbability.ge sys a b

@[simp] theorem ge_iff_le {a b : α} : sys.ge a b ↔ sys.le b a := Iff.rfl

/-- Monotonicity. -/
theorem mono {a b : α} (h : a ≤ b) : sys.le a b := sys.mono' a b h

/-- Transitivity. -/
theorem trans {a b c : α} (hab : sys.le a b) (hbc : sys.le b c) : sys.le a c :=
  sys.trans' a b c hab hbc

/-- Reflexivity, from monotonicity. -/
theorem refl (a : α) : sys.le a a := sys.mono le_rfl

protected theorem bot_le (a : α) : sys.le ⊥ a := sys.mono bot_le

protected theorem le_top (a : α) : sys.le a ⊤ := sys.mono le_top

/-! `ge` carries the mixins, so results proved from the axioms transfer by instance
resolution. -/

instance : IsLikelihoodMono sys.ge := ⟨sys.mono'⟩

instance : Std.Refl sys.ge := ⟨sys.refl⟩

instance : IsTrans α sys.ge := ⟨fun _ _ _ hab hbc ↦ sys.trans hbc hab⟩

instance : Std.Total sys.ge := ⟨fun a b ↦ sys.total b a⟩

instance : IsQualitativeAdditive sys.ge := ⟨fun a b ↦ sys.additive b a⟩

instance : IsNontrivial sys.ge := ⟨sys.nonTrivial⟩

end QualitativeProbability

end ComparativeProbability
