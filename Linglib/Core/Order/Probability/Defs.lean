import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Qualitative probability orders

A **qualitative probability** order on a Boolean algebra `α` — de Finetti's
axioms for "at most as likely as": total, transitive, monotone, non-trivial,
and qualitatively additive (`a ≼ b ↔ a \\ b ≼ b \\ a`). The relation is stored as
`le` and stated in `≤`-vocabulary; the literature's `≿` is the derived `ge`,
mathlib's `GE.ge` pattern, with scoped notation `a ≼[sys] b` / `a ≿[sys] b`.

## Main definitions

* `QualitativeProbability` — the bundled order, with `ge`, `refl`, `mono`,
  `trans`, `bot_le`, `le_top`.

`[UPSTREAM]` candidate for `Mathlib/Order/Probability/`: order theory with a
probabilistic reading — no measures occur; the representation theory lives in
the sibling files (`Content.lean`, `Scott.lean`, `Representability.lean`,
`Completeness.lean`).

## References

[kraft-pratt-seidenberg-1959]
-/

namespace ComparativeProbability

/-! ### The order -/

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

end QualitativeProbability

end ComparativeProbability
