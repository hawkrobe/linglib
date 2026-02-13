/-
# Dynamic Predicate Logic (Groenendijk & Stokhof 1991)

Stub for Dynamic Predicate Logic (DPL), the foundational dynamic semantic
theory that treats meanings as relations between assignments.

## Key Ideas

In DPL:
- Sentences denote relations between input and output assignments
- Existential quantification introduces new discourse referents
- Conjunction is relation composition (dynamic!)
- Negation is a test (doesn't change assignment)

## Semantic Type

⟦φ⟧ : Assignment → Assignment → Prop

(A sentence maps input assignment to output assignment)

## Key Properties

1. Scope extension: ∃x(φ ∧ ψ) ≡ (∃xφ) ∧ ψ if x not free in ψ
2. Anaphora: variables persist across conjunction
3. DNE failure: ¬¬φ ≠ φ for anaphora (negation is a test)

## References

- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic. L&P 14:39-100.
- Groenendijk, J. & Stokhof, M. (1990). Dynamic Montague Grammar.
-/

import Linglib.Theories.DynamicSemantics.Core.Update

namespace DynamicSemantics.DPL

open DynamicSemantics.Core

-- Placeholder: Full implementation TODO

/--
DPL semantic type: relation between assignments.

⟦φ⟧(g, h) means: starting from assignment g, the formula φ can
update to assignment h.
-/
def DPLRel (E : Type*) := (Nat → E) → (Nat → E) → Prop

/--
Atomic predicate in DPL: tests without changing assignment.
-/
def DPLRel.atom {E : Type*} (p : (Nat → E) → Prop) : DPLRel E :=
  λ g h => g = h ∧ p g

/--
DPL conjunction: relation composition.

⟦φ ∧ ψ⟧(g, h) iff ∃k. ⟦φ⟧(g, k) ∧ ⟦ψ⟧(k, h)
-/
def DPLRel.conj {E : Type*} (φ ψ : DPLRel E) : DPLRel E :=
  λ g h => ∃ k, φ g k ∧ ψ k h

/--
DPL existential: random assignment then scope.

⟦∃x.φ⟧(g, h) iff ∃d. ⟦φ⟧(g[x↦d], h)
-/
def DPLRel.exists_ {E : Type*} (x : Nat) (φ : DPLRel E) : DPLRel E :=
  λ g h => ∃ d : E, φ (λ n => if n = x then d else g n) h

/--
DPL negation: test without changing assignment.

⟦¬φ⟧(g, h) iff g = h ∧ ¬∃k. ⟦φ⟧(g, k)

Note: this does not validate DNE.
-/
def DPLRel.neg {E : Type*} (φ : DPLRel E) : DPLRel E :=
  λ g h => g = h ∧ ¬∃ k, φ g k

-- Key Theorems (TODO: Prove)

/--
DPL does not validate DNE for anaphora.

¬¬∃x.φ is not equivalent to ∃x.φ because negation resets the output assignment:
`neg(neg(exists_ x φ)) g h` forces `g = h` (it's a test), while `exists_ x φ`
can change the assignment to export a witness.

Requires `Nontrivial E` (at least 2 elements): for `Unit`, all assignments are
identical and DNE holds vacuously.
-/
theorem dpl_dne_fails_anaphora {E : Type*} [Nontrivial E] :
    ∃ (x : Nat) (φ : DPLRel E),
      DPLRel.neg (DPLRel.neg (DPLRel.exists_ x φ)) ≠ DPLRel.exists_ x φ := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨0, λ g h => g = h, ?_⟩
  intro heq
  -- exists_ 0 (=) at (λ _ => e₁, λ n => if n=0 then e₂ else e₁) is true (d = e₂)
  -- neg(neg(exists_ 0 (=))) at same args requires g = h, which fails (e₁ ≠ e₂)
  have hrhs : (DPLRel.exists_ 0 (λ (g h : Nat → E) => g = h))
              (λ _ => e₁) (λ n => if n = 0 then e₂ else e₁) :=
    ⟨e₂, rfl⟩
  rw [← heq] at hrhs
  have h_eq := congr_fun hrhs.1 0
  simp at h_eq
  exact hne h_eq

/--
Scope extension theorem: ∃x(φ ∧ ψ) ≡ (∃xφ) ∧ ψ when x not free in ψ.

"Not free in ψ" means ψ is invariant under reassigning x in both input and output
assignments. Under this condition, the existential can scope out past conjunction.

TODO: Prove by extensionality and reordering existential quantifiers.
-/
theorem scope_extension {E : Type*} (x : Nat) (φ ψ : DPLRel E)
    (_hfree : ∀ (g h : Nat → E) (d : E),
      ψ g h ↔ ψ (λ n => if n = x then d else g n) (λ n => if n = x then d else h n)) :
    DPLRel.exists_ x (DPLRel.conj φ ψ) = DPLRel.conj (DPLRel.exists_ x φ) ψ := by
  funext g h
  simp only [DPLRel.exists_, DPLRel.conj, eq_iff_iff]
  constructor
  · rintro ⟨d, k, hφ, hψ⟩
    exact ⟨k, ⟨d, hφ⟩, hψ⟩
  · rintro ⟨k, ⟨d, hφ⟩, hψ⟩
    exact ⟨d, k, hφ, hψ⟩

end DynamicSemantics.DPL
