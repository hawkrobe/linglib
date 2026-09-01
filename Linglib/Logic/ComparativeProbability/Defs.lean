import Linglib.Core.Order.Probability.Content
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Defs.Unbundled

/-!
# Comparative probability orders on a Boolean algebra

This file develops the abstract theory of *comparative (qualitative) probability*:
a relation `r a b` read "`a` is at least as likely as `b`" on a Boolean algebra
`α`, following [holliday-icard-2013]. The axioms of the paper's logics are stated
as **unbundled mixin `Prop`-classes** on the relation, so the validity patterns
(`ComparativeProbability.Patterns`) can be proved once at the weakest hypotheses
and reused by every concrete model — finitely-additive measures, qualitatively-
additive measures, world-ordering lifts — through instances.

Transitivity reuses mathlib's `IsTrans`; only the genuinely Boolean-algebra-flavored
axioms (monotonicity, complement reversal, qualitative additivity, non-triviality)
get bespoke classes.

## Main definitions
* `ComparativeProbability.Strict`, `Probably`, `Possibly` — the derived operators
  `a ≻ b`, `△a`, `◇a`.
* `IsLikelihoodMono`, `IsComplementReversing`, `IsQualitativeAdditive`,
  `IsNontrivial` — the axiom mixin classes.

## Main statements
* `instComplementReversingOfQualitativeAdditive` — qualitative additivity implies
  complement reversal, via `bᶜ \ aᶜ = a \ b` (`compl_sdiff_compl`).
* The instances registering a `QualitativeProbability`'s `ge` (and a measure's
  `inducedGe`) as carriers of the mixins: `QualitativeProbability` on `Set W` is
  [holliday-icard-2013]'s logic FA, sound and complete for qualitatively additive
  measure semantics (Theorem 6; [van-der-hoek-1996]) and strictly weaker than
  finite additivity for `|W| ≥ 5` (Theorem 8, after [kraft-pratt-seidenberg-1959]).
-/

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α]

/-- `Strict r a b` ("`a ≻ b`"): `a` is at least as likely as `b` but not conversely. -/
def Strict (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ¬ r b a

instance {r : α → α → Prop} [DecidableRel r] : DecidableRel (Strict r) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `Probably r a` ("`△a`"): `a` is strictly more likely than its complement. -/
def Probably (r : α → α → Prop) (a : α) : Prop := Strict r a aᶜ

/-- `Possibly r a` ("`◇a`"): `a` is not certainly impossible (`¬ ⊥ ≽ a`). -/
def Possibly (r : α → α → Prop) (a : α) : Prop := ¬ r ⊥ a

/-- Axiom T (monotonicity): larger events are at least as likely. -/
class IsLikelihoodMono (r : α → α → Prop) : Prop where
  mono : ∀ a b : α, a ≤ b → r b a

/-- Axiom C (complement reversal): `a ≽ b → bᶜ ≽ aᶜ`. -/
class IsComplementReversing (r : α → α → Prop) : Prop where
  complRev : ∀ a b : α, r a b → r bᶜ aᶜ

/-- Axiom A (qualitative additivity): `a ≽ b ↔ (a \ b) ≽ (b \ a)`. -/
class IsQualitativeAdditive (r : α → α → Prop) : Prop where
  qadd : ∀ a b : α, r a b ↔ r (a \ b) (b \ a)

/-- Axiom BT (non-triviality): `⊥` is not at least as likely as `⊤`. -/
class IsNontrivial (r : α → α → Prop) : Prop where
  bot_not_ge_top : ¬ r ⊥ ⊤

export IsLikelihoodMono (mono)
export IsComplementReversing (complRev)
export IsQualitativeAdditive (qadd)

/-- Qualitative additivity implies complement reversal: `bᶜ \ aᶜ = a \ b` and
    `aᶜ \ bᶜ = b \ a` turn the additivity equivalence for `bᶜ, aᶜ` into the one
    for `a, b`. -/
instance (priority := 100) instComplementReversingOfQualitativeAdditive
    {r : α → α → Prop} [h : IsQualitativeAdditive r] : IsComplementReversing r where
  complRev a b hab := by
    rw [h.qadd bᶜ aᶜ, compl_sdiff_compl, compl_sdiff_compl]
    exact (h.qadd a b).mp hab

/-! ### Qualitative probability orders carry the mixins

`QualitativeProbability.ge` is defeq the mixin classes' relation, so the instances
below register it as a comparative-probability order, and the validity patterns
V1–V13 (`Patterns.lean`) transfer by instance resolution. -/

section

variable {α : Type*} [BooleanAlgebra α] (sys : QualitativeProbability α)

instance : IsLikelihoodMono sys.ge := ⟨sys.mono'⟩

instance : IsTrans α sys.ge := ⟨fun _ _ _ hab hbc => sys.trans hbc hab⟩

instance : IsQualitativeAdditive sys.ge := ⟨fun a b => sys.additive b a⟩

instance : IsNontrivial sys.ge := ⟨sys.nonTrivial⟩

end

/-! ### Connection to the `ComparativeProbability` theory

Every finitely-additive measure's induced order is a comparative-probability
order (monotone, transitive, qualitatively additive, non-trivial), so the
validity patterns V1–V13 transfer for free from `ComparativeProbability.Patterns`
by instance resolution — no per-measure arithmetic. -/

section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {W : Type*}
  (m : FinAddMeasure K W)

instance : ComparativeProbability.IsLikelihoodMono m.inducedGe :=
  ⟨m.toQualitativeProbability.mono'⟩

instance : IsTrans (Set W) m.inducedGe :=
  ⟨fun _ _ _ hab hbc => m.toQualitativeProbability.trans hbc hab⟩

instance : ComparativeProbability.IsQualitativeAdditive m.inducedGe :=
  ⟨fun A B => m.toQualitativeProbability.additive B A⟩

instance : ComparativeProbability.IsNontrivial m.inducedGe :=
  ⟨m.toQualitativeProbability.nonTrivial⟩

end


end ComparativeProbability
