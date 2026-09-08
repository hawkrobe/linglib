import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Semantics.Exhaustification.InnocentInclusion

/-!
# Presuppositional exhaustification

This file defines the presuppositional exhaustivity operator `pex^{IE+II}` of
[delpinal-bassi-sauerland-2024], after the `pex^{IE}` of [bassi-delpinal-sauerland-2021]: it
asserts its prejacent alone and presupposes the negation of the relevant innocently excludable
alternatives together with homogeneity over the relevant innocently includable alternatives
of [bar-lev-fox-2020]. Where `exh^{IE+II}` returns one flat proposition, `pex` returns a
`PartialProp` whose two components project differently: negation denies the assertion and
leaves the presupposition in place, and on a prejacent without relevant includable
alternatives the presupposition is the negated excludable alternatives alone, (11a).

## References

* [delpinal-bassi-sauerland-2024]
* [bassi-delpinal-sauerland-2021]
* [bar-lev-fox-2020]
-/

namespace Exhaustification.Presuppositional

open Exhaustification Presupposition

variable {World : Type*}

/-- Homogeneity: every proposition of the set has the same truth value at `w`. -/
def homogeneous (S : Set (Set World)) (w : World) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, (α w ↔ β w)

/-- Homogeneity over a pair is their biconditional. -/
theorem homogeneous_pair (p q : Set World) (w : World) :
    homogeneous {p, q} w ↔ (p w ↔ q w) := by
  constructor
  · intro h
    exact h p (Set.mem_insert _ _) q (Set.mem_insert_of_mem _ rfl)
  · intro hiff α hα β hβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
      first | exact Iff.rfl | exact hiff | exact hiff.symm

/-- `pex^{IE+II}`, (9): assert the prejacent, presuppose that the relevant innocently
excludable alternatives are false and that the relevant innocently includable alternatives
are homogeneous. -/
def pexIEII (ALT : Set (Set World)) (φ : Set World) (Rc : Set (Set World)) :
    PartialProp World where
  assertion := φ
  presup := λ w =>
    (∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → ¬ψ w) ∧ homogeneous {α ∈ II ALT φ | α ∈ Rc} w

/-- `pex^{IE+II}` with every alternative relevant. -/
def pexIEII_full (ALT : Set (Set World)) (φ : Set World) : PartialProp World :=
  pexIEII ALT φ ALT

variable (ALT : Set (Set World)) (φ : Set World) (Rc : Set (Set World))

theorem pex_assertion_eq : (pexIEII ALT φ Rc).assertion = φ := rfl

theorem pex_holds_entails_prejacent (w : World) (h : (pexIEII ALT φ Rc).holds w) : φ w :=
  h.2

/-- Negation denies the assertion. -/
theorem pex_neg_assertion : (pexIEII ALT φ Rc).neg.assertion = λ w => ¬φ w := rfl

/-- Negation leaves the presupposition in place. -/
theorem pex_neg_presup : (pexIEII ALT φ Rc).neg.presup = (pexIEII ALT φ Rc).presup := rfl

/-- (11a): with no relevant includable alternative, as for a basic scalar sentence, the
presupposition is the negated excludable alternatives alone. -/
theorem pex_basic_scalar (hII : ∀ α, α ∈ II ALT φ → α ∈ Rc → False) (w : World) :
    (pexIEII ALT φ Rc).presup w ↔ ∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → ¬ψ w :=
  ⟨λ ⟨hIE, _⟩ => hIE, λ hIE => ⟨hIE, λ α ⟨hα, hRc⟩ => absurd hRc λ h => hII α hα h⟩⟩

end Exhaustification.Presuppositional
