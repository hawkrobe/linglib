module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Defs.Unbundled

/-!
# Qualitative probability orders

Comparative probability reads a relation `r a b` on a Boolean algebra `α` as "`a` is at
least as likely as `b`". This file states the axioms of the subject as unbundled mixin
classes on such a relation, in the style of `IsTrans`, and bundles de Finetti's system,
the standard base of comparative probability that Kraft, Pratt and Seidenberg and
Scott build on, as `QualitativeProbability`: total, transitive, monotone,
non-trivial, and qualitatively additive (`a ≼ b ↔ a \ b ≼ b \ a`). The bundled relation
is stored as `le` and stated in `≤`-vocabulary; the literature's `≿` is the derived `ge`,
mathlib's `GE.ge` pattern, with scoped notation `a ≼[sys] b` / `a ≿[sys] b`, and it is
`ge` that carries the mixins.

A likelihood order also defines *probably*: `△a` holds when `a` is strictly more likely than
its complement, as in the logics of comparative probability that Holliday and Icard compare.
Over a monotone order the contradiction is never probable and, when the order is non-trivial,
the tautology always is; over a monotone transitive order *probably* is upward closed.
`RightUnion` is Halpern's union property `J`.

## Main definitions

* `IsLikelihoodMono`, `IsQualitativeAdditive`, `IsNontrivial`, `IsComplementReversing`: the
  axiom mixins on a relation; `Strict r` is its asymmetric part `a ≻ b`, which a transitive
  `r` absorbs on either side (`strict_of_strict_of_rel`, `strict_of_rel_of_strict`).
* `QualitativeProbability`: the bundled order, with `ge`, `refl`, `mono`, `trans`, `bot_le`,
  `le_top`, and the mixin instances for `ge`.
* `Probably`, `RightUnion`: *probably* and Halpern's union property.

## Main statements

* `instComplementReversingOfQualitativeAdditive`: qualitative additivity implies complement
  reversal, via `bᶜ \ aᶜ = a \ b` (`compl_sdiff_compl`).

## References

* [kraft-pratt-seidenberg-1959]
* [scott-1964]
* [holliday-icard-2013]
* [halpern-2003]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α]

/-! ### The axioms as mixins -/

/-- A relation is monotone when every event is at least as likely as its subevents. -/
class IsLikelihoodMono (r : α → α → Prop) : Prop where
  mono : ∀ a b : α, a ≤ b → r b a

/-- A relation reverses complements when `a ≽ b` gives `bᶜ ≽ aᶜ`. -/
class IsComplementReversing (r : α → α → Prop) : Prop where
  complRev : ∀ a b : α, r a b → r bᶜ aᶜ

/-- A relation is qualitatively additive, de Finetti's axiom, when `a ≽ b` holds exactly when
`a \ b ≽ b \ a`. -/
class IsQualitativeAdditive (r : α → α → Prop) : Prop where
  qadd : ∀ a b : α, r a b ↔ r (a \ b) (b \ a)

/-- A relation is non-trivial when `⊥` is not at least as likely as `⊤`. -/
class IsNontrivial (r : α → α → Prop) : Prop where
  bot_not_ge_top : ¬ r ⊥ ⊤

export IsLikelihoodMono (mono)
export IsComplementReversing (complRev)
export IsQualitativeAdditive (qadd)

/-- `Strict r a b` ("`a ≻ b`") is the asymmetric part of `r`. -/
def Strict (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ¬ r b a

instance {r : α → α → Prop} [DecidableRel r] : DecidableRel (Strict r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

section Strict

omit [BooleanAlgebra α]

variable {r : α → α → Prop} [IsTrans α r] {a b c : α}

theorem strict_of_strict_of_rel (hab : Strict r a b) (hbc : r b c) : Strict r a c :=
  ⟨_root_.trans hab.1 hbc, fun hca ↦ hab.2 (_root_.trans hbc hca)⟩

theorem strict_of_rel_of_strict (hab : r a b) (hbc : Strict r b c) : Strict r a c :=
  ⟨_root_.trans hab hbc.1, fun hca ↦ hbc.2 (_root_.trans hca hab)⟩

end Strict

/-- Qualitative additivity implies complement reversal, since `bᶜ \ aᶜ = a \ b` and
`aᶜ \ bᶜ = b \ a` turn the additivity equivalence for `bᶜ, aᶜ` into the one for `a, b`. -/
instance (priority := 100) instComplementReversingOfQualitativeAdditive
    {r : α → α → Prop} [h : IsQualitativeAdditive r] : IsComplementReversing r where
  complRev a b hab := by
    rw [h.qadd bᶜ aᶜ, compl_sdiff_compl, compl_sdiff_compl]
    exact (h.qadd a b).mp hab

/-! ### The bundled order -/

/-- A **qualitative probability** order on a Boolean algebra `α` is a total,
transitive, monotone, non-trivial and qualitatively additive relation, the standard
base system for comparative probability since de Finetti. Every such order on a
finite carrier is represented by a qualitatively additive measure
(`exists_qualAddMeasure_repr`), but by a probability measure only below five
atoms (Kraft, Pratt and Seidenberg; `Completeness.lean`). Reflexivity and
`⊥ ≼ a` are consequences of monotonicity (`refl`, `bot_le`), not fields. -/
structure QualitativeProbability (α : Type*) [BooleanAlgebra α] where
  /-- `le a b` says that `a` is at most as likely as `b`. -/
  le : α → α → Prop
  /-- A subevent is at most as likely as the event. Use the lemma `mono`. -/
  mono' : ∀ a b : α, a ≤ b → le a b
  /-- `⊤` is not at most as likely as `⊥`. -/
  nonTrivial : ¬ le ⊤ ⊥
  /-- Any two elements are comparable. -/
  total : ∀ a b : α, le a b ∨ le b a
  /-- The relation is transitive. Use the lemma `trans`. -/
  trans' : ∀ a b c : α, le a b → le b c → le a c
  /-- `a ≼ b` holds exactly when `a \ b ≼ b \ a`. -/
  additive : ∀ a b : α, le a b ↔ le (a \ b) (b \ a)

namespace QualitativeProbability

variable {α : Type*} [BooleanAlgebra α] (sys : QualitativeProbability α)

/-- `sys.ge a b` (`a ≿ b`) says that `a` is at least as likely as `b`. It is the converse
of `le`, as `GE.ge` is in mathlib, and the relation the literature reads. -/
def ge (a b : α) : Prop := sys.le b a

@[inherit_doc le] scoped notation:50 a:51 " ≼[" sys "] " b:51 => QualitativeProbability.le sys a b
@[inherit_doc ge] scoped notation:50 a:51 " ≿[" sys "] " b:51 => QualitativeProbability.ge sys a b

@[simp] theorem ge_iff_le {a b : α} : sys.ge a b ↔ sys.le b a := Iff.rfl

/-- A subevent is at most as likely as the event. -/
theorem mono {a b : α} (h : a ≤ b) : sys.le a b := sys.mono' a b h

/-- `sys.le` is transitive. -/
theorem trans {a b c : α} (hab : sys.le a b) (hbc : sys.le b c) : sys.le a c :=
  sys.trans' a b c hab hbc

/-- `sys.le` is reflexive, by monotonicity. -/
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

/-! ### *Probably* -/

/-- `Probably r a` ("`△a`") says that `a` is strictly more likely than its complement. -/
def Probably (r : α → α → Prop) (a : α) : Prop := Strict r a aᶜ

/-- A relation is right-union closed, Halpern's axiom `J`, when `a ≽ b` and `a ≽ c` give
`a ≽ (b ⊔ c)`. This union property separates the l-lifting from the additive semantics. -/
def RightUnion {β : Type*} [SemilatticeSup β] (r : β → β → Prop) : Prop :=
  ∀ a b c, r a b → r a c → r a (b ⊔ c)

variable {r : α → α → Prop} {a b : α}

/-- *Probably* is upward closed over a monotone transitive order, since a larger event is at
least as likely and its complement at most as likely. -/
theorem Probably.mono [IsLikelihoodMono r] [IsTrans α r] (hab : a ≤ b) (ha : Probably r a) :
    Probably r b :=
  strict_of_strict_of_rel (strict_of_rel_of_strict (IsLikelihoodMono.mono _ _ hab) ha)
    (IsLikelihoodMono.mono _ _ (compl_le_compl hab))

theorem probably_top [IsLikelihoodMono r] [IsNontrivial r] : Probably r ⊤ := by
  rw [Probably, compl_top]
  exact ⟨mono _ _ bot_le, IsNontrivial.bot_not_ge_top⟩

theorem not_probably_bot [IsLikelihoodMono r] : ¬ Probably r ⊥ := fun h ↦
  h.2 (by rw [compl_bot]; exact mono _ _ le_top)

end ComparativeProbability
