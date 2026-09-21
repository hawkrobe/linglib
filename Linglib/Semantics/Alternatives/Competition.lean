module

public import Mathlib.Data.Set.Basic

/-!
# Pragmatic competition

An expression is blocked when one of its alternatives is strictly stronger along a dimension
of content. This file defines that relation, `Blocked`, for any alternative source `S → Set S`
and any content function `S → Set W`, together with the source combinator `sameAssertion`,
which keeps the alternatives with the same at-issue content. The neo-Gricean conversational
principle is `Blocked` along at-issue content over the weakly assertable alternatives
([katzir-2007]), Maximize Presupposition is `Blocked` along presuppositional content over
`sameAssertion` (`Presupposition.MaximizePresupposition.Blocked`, [heim-1991]), and Maximize
Conventional Implicatures is `Blocked` along conventional-implicature content
([lo-guercio-2025]). The relation is a property of the alternative set and carries no theory
of why blocking obtains, so pragmatic and grammatical accounts of each principle state their
disagreement over one definition without either importing the other.

## Main definitions

* `Alternatives.Blocked` — some alternative is strictly stronger along the content dimension.
* `Alternatives.sameAssertion` — the alternatives with the same at-issue content.

## Main results

* `Alternatives.Blocked.mono` — blocking is monotone in the source.
* `Alternatives.not_blocked_of_forall_subset` — an expression at least as strong as each of
  its alternatives is not blocked.

## References

* [katzir-2007]
* [heim-1991]
* [lo-guercio-2025]
-/

@[expose] public section

namespace Alternatives

variable {S W : Type*} {alts alts' : S → Set S} {content assertion : S → Set W} {φ φ' : S}

/-- `φ` is blocked when some alternative in `alts φ` has strictly stronger `content`. -/
def Blocked (alts : S → Set S) (content : S → Set W) (φ : S) : Prop :=
  ∃ φ' ∈ alts φ, content φ' ⊂ content φ

/-- Blocking is monotone in the alternative source. -/
theorem Blocked.mono (h : alts ≤ alts') (hb : Blocked alts content φ) :
    Blocked alts' content φ :=
  let ⟨φ', hφ', hss⟩ := hb; ⟨φ', h φ hφ', hss⟩

/-- An expression at least as strong as each of its alternatives is not blocked. -/
theorem not_blocked_of_forall_subset (h : ∀ φ' ∈ alts φ, content φ ⊆ content φ') :
    ¬ Blocked alts content φ :=
  λ ⟨φ', hφ', hss⟩ => hss.not_subset (h φ' hφ')

/-- The alternatives of `φ` with the same at-issue content, the competitors Maximize
Presupposition compares. -/
def sameAssertion (assertion : S → Set W) (alts : S → Set S) (φ : S) : Set S :=
  {φ' ∈ alts φ | assertion φ' = assertion φ}

@[simp] theorem mem_sameAssertion :
    φ' ∈ sameAssertion assertion alts φ ↔ φ' ∈ alts φ ∧ assertion φ' = assertion φ :=
  Iff.rfl

theorem sameAssertion_le (assertion : S → Set W) (alts : S → Set S) :
    sameAssertion assertion alts ≤ alts :=
  λ _ _ h => h.1

end Alternatives
