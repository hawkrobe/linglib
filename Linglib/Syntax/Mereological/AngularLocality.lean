import Linglib.Syntax.Mereological.Parthood

/-!
# Angular Locality

Angular Locality is the locality principle of mereological syntax: a part `γ` may subjoin to
`β` only if `γ` is an `n`-part of some object `α` that is a 1-part of `β`. Since parthood is
transitive within a dimension only, a subjunction path may turn through at most one angle, from
dimension `n` into dimension 1. Everything the classical theory stipulates about cyclic domains
and their escape hatches follows: 2-parts are the locality domains, and an object leaves a 2-part
just when it is a 2-part of it.

This file defines `Parthood.CanSubjoin` and proves the consequences that hold in every
structure: the target must contain the mover, so lowering, sideward, and parallel subjunction
are ruled out; an immediate 1-part cannot resubjoin to its whole (antilocality); and an object
inside a 2-part reaches an object outside it exactly when it lies on the 2-part's own 2-part
chain.

## Main definitions

* `Parthood.CanSubjoin γ β` — Angular Locality for subjunction of `γ` to `β`.

## Main statements

* `Parthood.descendant_of_canSubjoin`, `Parthood.not_canSubjoin_of_le` — the target contains
  the mover.
* `Parthood.not_canSubjoin_of_imm_one` — antilocality, from irreflexivity of parthood.
* `Parthood.canSubjoin_iff_nPart_two` — locality domains are 2-parts, with escape along the
  2-part chain.

## References

* [adger-2025]
-/

namespace MereologicalSyntax.Parthood

variable {α : Type*} {P : Parthood α}

/-- Angular Locality: `γ` may subjoin to `β` only if `γ` is an `n`-part of some 1-part of `β`. -/
def CanSubjoin (P : Parthood α) (γ β : α) : Prop := ∃ a, P.WithinDim γ a ∧ P.NPart .one a β

/-! ### The target contains the mover -/

theorem descendant_of_canSubjoin {γ β : α} (h : P.CanSubjoin γ β) : P.Descendant γ β :=
  let ⟨_, h₁, h₂⟩ := h
  (descendant_of_withinDim h₁).trans (descendant_of_nPart h₂)

/-- Lowering, sideward, and parallel subjunction: no subjunction to an object of no greater
rank. -/
theorem not_canSubjoin_of_le (rank : α → ℕ) (hrank : ∀ n x y, P.Imm n x y → rank x < rank y)
    {γ β : α} (h : rank β ≤ rank γ) : ¬ P.CanSubjoin γ β :=
  fun hc => not_descendant_of_le rank hrank h (descendant_of_canSubjoin hc)

/-! ### Antilocality -/

/-- An immediate 1-part cannot resubjoin to its whole: the only candidate `α` is the part
itself, and parthood is irreflexive. -/
theorem not_canSubjoin_of_imm_one (hacyc : ∀ x, ¬ P.Descendant x x) {γ β : α}
    (h : P.Imm .one γ β) : ¬ P.CanSubjoin γ β := by
  rintro ⟨a, hγa, haβ⟩
  obtain ⟨c, hac, hcβ⟩ := Relation.TransGen.tail'_iff.1 haβ
  obtain rfl : c = γ := Option.some_injective _ (hcβ.symm.trans h)
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hac with rfl | hac
  · exact hacyc _ (descendant_of_withinDim hγa)
  · exact hacyc _ ((descendant_of_withinDim hγa).trans (descendant_of_nPart hac))

/-! ### Locality domains are 2-parts -/

section Domain

variable {S : Set α} {b : α}

/-- Nothing inside the 2-part `b` other than its own 2-parts subjoins outside `b`. -/
theorem not_canSubjoin_of_not_nPart_two (hS : ∀ x ∈ S, x ≠ b → ∀ n y, P.Imm n x y → y ∈ S)
    (hb : ∀ n y, P.Imm n b y → n = .two) {γ β : α} (hγ : γ ∈ S) (hγb : γ ≠ b) (hβ : β ∉ S)
    (hn : ¬ P.NPart .two γ b) : ¬ P.CanSubjoin γ β := by
  rintro ⟨a, hγa, haβ⟩
  by_cases ha : a ∈ S
  · exact absurd (exit_of_nPart hS hb haβ ha hβ).1 (by decide)
  · rcases hγa with hγa | hγa
    · exact absurd (exit_of_nPart hS hb hγa hγ ha).1 (by decide)
    · exact (exit_of_nPart hS hb hγa hγ ha).2.elim hγb hn

/-- A 2-part of the 2-part `b` of `d` subjoins to anything `d` is a 1-part of. -/
theorem canSubjoin_of_nPart_two {γ b d β : α} (hγ : P.NPart .two γ b) (hbd : P.Imm .two b d)
    (hd : P.NPart .one d β) : P.CanSubjoin γ β :=
  ⟨d, .inr (hγ.tail hbd), hd⟩

/-- The escape hatch: from inside the 2-part `b` of `d`, an object reaches an object above `d`
in `d`'s extended projection exactly when it is a 2-part of `b`. -/
theorem canSubjoin_iff_nPart_two (hS : ∀ x ∈ S, x ≠ b → ∀ n y, P.Imm n x y → y ∈ S)
    (hb : ∀ n y, P.Imm n b y → n = .two) {γ β d : α} (hbd : P.Imm .two b d)
    (hd : P.NPart .one d β) (hγ : γ ∈ S) (hγb : γ ≠ b) (hβ : β ∉ S) :
    P.CanSubjoin γ β ↔ P.NPart .two γ b :=
  ⟨fun h => by_contra fun hn => not_canSubjoin_of_not_nPart_two hS hb hγ hγb hβ hn h,
    fun h => canSubjoin_of_nPart_two h hbd hd⟩

end Domain

/-! ### Subjoin -/

variable (P) in
/-- Subjoin `x` to `y`: the first subjunction gives a 1-part, the second a 2-part, and there is
no third (Dimensionality); nothing subjoins to itself. -/
def subjoin [DecidableEq α] (x y : α) : Option (Parthood α) :=
  if x = y then none
  else
    match P.onePart y with
    | none => some { P with onePart := Function.update P.onePart y (some x) }
    | some _ =>
      match P.twoPart y with
      | none => some { P with twoPart := Function.update P.twoPart y (some x) }
      | some _ => none

theorem subjoin_eq_none_of_full [DecidableEq α] {x y : α} (h₁ : (P.onePart y).isSome)
    (h₂ : (P.twoPart y).isSome) : P.subjoin x y = none := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h₁
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h₂
  simp [subjoin, ha, hb]

end MereologicalSyntax.Parthood
