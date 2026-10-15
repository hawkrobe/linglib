module

public import Linglib.Syntax.Mereological.Parthood

/-!
# Angular Locality

Angular Locality is the locality principle of mereological syntax: a part `γ` may subjoin to
`β` only if `γ` is an `n`-part of some object `α` that is a 1-part of `β`. Since parthood is
transitive within a dimension only, a subjunction path may turn through at most one angle, from
dimension `n` into dimension 1. Everything the classical theory stipulates about cyclic domains
and their escape hatches follows: 2-parts are the locality domains, and an object leaves a 2-part
just when it is a 2-part of it.

This file defines `Parthood.CanSubjoin`, decidable on a finite structure, and proves the
consequences that hold in every structure: the target must contain the mover, so lowering,
sideward, and parallel subjunction are ruled out; an immediate 1-part cannot resubjoin to its
whole (antilocality); and an object inside a 2-part reaches an object outside it exactly when it
lies on the 2-part's own 2-part chain.

## Main definitions

* `Parthood.CanSubjoin γ β` — Angular Locality for subjunction of `γ` to `β`.

## Main statements

* `Parthood.descendant_of_canSubjoin` — the target contains the mover.
* `Parthood.not_canSubjoin_of_imm_one` — antilocality, from irreflexivity of parthood.
* `Parthood.canSubjoin_iff_nPart_two` — locality domains are 2-parts, with escape along the
  2-part chain.

## References

* [adger-2025]
-/

@[expose] public section

namespace MereologicalSyntax.Parthood

open Relation

variable {α : Type*} {P : Parthood α}

/-- Angular Locality allows `γ` to subjoin to `β` only if `γ` is an `n`-part of some 1-part of
`β`. -/
def CanSubjoin (P : Parthood α) (γ β : α) : Prop := ∃ n a, P.NPart n γ a ∧ P.NPart .one a β

/-- Decided by running through the 1-parts of `β` first, which most objects are not. -/
instance [Fintype α] [DecidableEq α] : DecidableRel P.CanSubjoin := fun γ β ↦
  decidable_of_iff (∃ a, P.NPart .one a β ∧ ∃ n, P.NPart n γ a)
    ⟨fun ⟨a, ha, n, hn⟩ ↦ ⟨n, a, hn, ha⟩, fun ⟨n, a, hn, ha⟩ ↦ ⟨a, ha, n, hn⟩⟩

/-! ### The target contains the mover -/

/-- Lowering, sideward, and parallel subjunction are ruled out, since the target must contain the
mover. -/
theorem descendant_of_canSubjoin {γ β : α} (h : P.CanSubjoin γ β) : P.Descendant γ β :=
  let ⟨_, _, h₁, h₂⟩ := h
  (descendant_of_nPart h₁).trans (descendant_of_nPart h₂)

/-! ### Antilocality -/

/-- An immediate 1-part cannot resubjoin to its whole, since the only object it is a part of is
the whole, which is not a 1-part of itself. -/
theorem not_canSubjoin_of_imm_one (hacyc : ∀ x, ¬ P.Descendant x x) {γ β : α}
    (h : P.Imm .one γ β) : ¬ P.CanSubjoin γ β := by
  rintro ⟨_, a, hγa, haβ⟩
  obtain ⟨c, hac, hcβ⟩ := TransGen.tail'_iff.1 haβ
  obtain rfl : c = γ := Option.some_injective _ (hcβ.symm.trans h)
  rcases reflTransGen_iff_eq_or_transGen.1 hac with rfl | hac
  · exact hacyc _ (descendant_of_nPart hγa)
  · exact hacyc _ ((descendant_of_nPart hγa).trans (descendant_of_nPart hac))

/-! ### Locality domains are 2-parts -/

section Domain

variable {S : Set α} {b : α}

/-- Nothing inside the 2-part `b` other than its own 2-parts subjoins outside `b`. -/
theorem not_canSubjoin_of_not_nPart_two (hS : ∀ x ∈ S, x ≠ b → ∀ n y, P.Imm n x y → y ∈ S)
    (hb : ∀ n y, P.Imm n b y → n = .two) {γ β : α} (hγ : γ ∈ S) (hγb : γ ≠ b) (hβ : β ∉ S)
    (hn : ¬ P.NPart .two γ b) : ¬ P.CanSubjoin γ β := by
  rintro ⟨_, a, hγa, haβ⟩
  by_cases ha : a ∈ S
  · exact absurd (exit_of_nPart hS hb haβ ha hβ).1 (by decide)
  · obtain ⟨rfl, h⟩ := exit_of_nPart hS hb hγa hγ ha
    exact h.elim hγb hn

/-- A 2-part of the 2-part `b` of `d` subjoins to anything `d` is a 1-part of. -/
theorem canSubjoin_of_nPart_two {γ b d β : α} (hγ : P.NPart .two γ b) (hbd : P.Imm .two b d)
    (hd : P.NPart .one d β) : P.CanSubjoin γ β :=
  ⟨.two, d, hγ.tail hbd, hd⟩

/-- From inside the 2-part `b` of `d`, an object reaches an object above `d` in `d`'s extended
projection exactly when it is a 2-part of `b`, which is the escape hatch. -/
theorem canSubjoin_iff_nPart_two (hS : ∀ x ∈ S, x ≠ b → ∀ n y, P.Imm n x y → y ∈ S)
    (hb : ∀ n y, P.Imm n b y → n = .two) {γ β d : α} (hbd : P.Imm .two b d)
    (hd : P.NPart .one d β) (hγ : γ ∈ S) (hγb : γ ≠ b) (hβ : β ∉ S) :
    P.CanSubjoin γ β ↔ P.NPart .two γ b :=
  ⟨fun h ↦ by_contra fun hn ↦ not_canSubjoin_of_not_nPart_two hS hb hγ hγb hβ hn h,
    fun h ↦ canSubjoin_of_nPart_two h hbd hd⟩

end Domain

end MereologicalSyntax.Parthood
