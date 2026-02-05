/-
# Dynamic Ty2: The Unification Point for Dynamic Semantics

Following Muskens (1996) and Brasoveanu (2007), Dynamic Ty2 is the
type-logical foundation into which ALL dynamic semantic systems embed.

## Core Idea (Muskens 1991)

"Instead of modeling discourse referents as atomic entities (variables)
and info states as functions taking dref's as arguments (i.e. variable
assignments), we model info states as atomic entities (of type s) and
dref's as functions taking info states as arguments."

## Type System

| Type | Description | Lean |
|------|-------------|------|
| `s` | Assignments (atomic) | `S` parameter |
| `e` | Individuals | `E` parameter |
| `t` | Truth values | `Prop` |
| `sτ` | Drefs (for static τ) | `S → τ` |
| `s(st)` | DRS meanings | `S → S → Prop` |

## Embeddings

- DPL: variables xᵢ ↦ λs. s(i) (projection functions)
- PLA: variables + pronouns via resolution
- DRT: isomorphic to CDRT (box notation)
- BUS: Dynamic Ty2 + bilateral (pos/neg) structure

## References

- Muskens, R. (1996). Combining Montague Semantics and Discourse Representation.
- Brasoveanu, A. (2007). Structured Nominal and Modal Reference. Ch. 3.
- Gallin, D. (1975). Intensional and Higher-Order Modal Logic.
-/

import Mathlib.Data.Set.Basic

namespace Theories.DynamicSemantics.Core.DynamicTy2


/-!
Dynamic Ty2 is parameterized by:
- `S`: The type of "assignments" (info states as atomic entities)
- `E`: The type of individuals

This follows Muskens's insight: instead of assignments being functions,
they are atomic, and drefs are functions FROM assignments.
-/

/-- Discourse referent for individuals: type `se` in Dynamic Ty2 -/
abbrev Dref (S E : Type*) := S → E

/-- DRS meaning: type `s(st)` - binary relation on assignments -/
abbrev DRS (S : Type*) := S → S → Prop

/-- Condition: type `st` - property of assignments -/
abbrev Condition (S : Type*) := S → Prop


section Abbreviations

variable {S E : Type*}

/-- Dynamic negation: ~D is true at i iff no j satisfies D from i -/
def dneg (D : DRS S) : Condition S :=
  λ i => ¬∃ k, D i k

notation "∼" D => dneg D

/-- Test: lift a condition to a DRS (identity on assignments) -/
def test (C : Condition S) : DRS S :=
  λ i j => i = j ∧ C j

notation "[" C "]" => test C

/-- Dynamic conjunction (sequencing): D₁ ; D₂ -/
def dseq (D₁ D₂ : DRS S) : DRS S :=
  λ i j => ∃ h, D₁ i h ∧ D₂ h j

infixl:65 " ⨟ " => dseq  -- semicolon-like

/-- Dynamic implication: D₁ → D₂ -/
def dimpl (D₁ D₂ : DRS S) : Condition S :=
  λ i => ∀ h, D₁ i h → ∃ k, D₂ h k

/-- Dynamic disjunction: D₁ ∨ D₂ -/
def ddisj (D₁ D₂ : DRS S) : Condition S :=
  λ i => ∃ k, D₁ i k ∨ D₂ i k

/-- Anaphoric closure: !D = ∃output state -/
def closure (D : DRS S) : Condition S :=
  λ i => ∃ k, D i k

notation "!" D => closure D

end Abbreviations


/--
Random assignment axiom structure.

In Dynamic Ty2, we need axioms ensuring S behaves like assignments.
This structure captures the "Enough Assignments" axiom:

  ∀i ∀u ∀f. udref(u) → ∃j. i[u]j ∧ uj = f

We model this via an `extend` operation.
-/
class AssignmentStructure (S E : Type*) where
  /-- Extend assignment i at dref u to value e, giving j -/
  extend : S → (S → E) → E → S
  /-- The extended assignment has the new value at u -/
  extend_at : ∀ (i : S) (u : S → E) (e : E), u (extend i u e) = e
  /-- The extended assignment agrees elsewhere -/
  extend_other : ∀ (i : S) (u v : S → E) (e : E), u ≠ v → v (extend i u e) = v i

namespace AssignmentStructure

variable {S E : Type*} [AssignmentStructure S E]

/-- Random assignment DRS: [u] introduces dref u -/
def randomAssign (u : S → E) : DRS S :=
  λ i j => ∃ e : E, j = extend i u e

notation "[" u "]ᵈʳᵉᶠ" => randomAssign u

/-- Existential DRS: ∃u(D) = [u]; D -/
def dexists (u : S → E) (D : DRS S) : DRS S :=
  dseq (randomAssign u) D

notation "∃'" u "(" D ")" => dexists u D

/-- Universal condition: ∀u(D) = ~∃u(~D) -/
def dforall (u : S → E) (D : DRS S) : Condition S :=
  dneg (dexists u (test (dneg D)))

notation "∀'" u "(" D ")" => dforall u D

end AssignmentStructure


section Atomic

variable {S E : Type*}

/-- Atomic condition from a predicate and drefs -/
def atom1 (P : E → Prop) (u : Dref S E) : Condition S :=
  λ i => P (u i)

def atom2 (P : E → E → Prop) (u v : Dref S E) : Condition S :=
  λ i => P (u i) (v i)

def atom3 (P : E → E → E → Prop) (u v w : Dref S E) : Condition S :=
  λ i => P (u i) (v i) (w i)

/-- Equality condition -/
def eq' (u v : Dref S E) : Condition S :=
  λ i => u i = v i

end Atomic


/-!
## Translating DPL into Dynamic Ty2

DPL variables xₙ become drefs uₙ : S → E (projection functions).

| DPL | Dynamic Ty2 |
|-----|-------------|
| R(x₁,...,xₙ) | [λi. R(u₁i,...,uₙi)] |
| x₁ = x₂ | [λi. u₁i = u₂i] |
| φ ; ψ | TR(φ) ⨟ TR(ψ) |
| ~φ | [∼TR(φ)] |
| [x] | [uₓ] (random assignment) |

DPL's assignment functions g : Var → E
become "flipped" to drefs u : S → E, where S plays the role
of the assignment itself.
-/


section ProperNames

variable {S E : Type*}

/--
Specific dref: constant function (for proper names).

John := λi. john

A proper name denotes the same individual regardless of assignment.
-/
def specificDref (e : E) : Dref S E := λ _ => e

/--
Proper name introduction (indefinite-like analysis).

Johnu ↝ [u | u = John]

This introduces an unspecific dref constrained to equal the specific one.
-/
def properName [AssignmentStructure S E] (u : S → E) (e : E) : DRS S :=
  AssignmentStructure.dexists u (test (eq' u (specificDref e)))

end ProperNames


section Truth

variable {S : Type*}

/-- A DRS D is true relative to input i iff some output j satisfies D -/
def trueAt (D : DRS S) (i : S) : Prop := ∃ j, D i j

/-- A DRS D is valid iff true at all inputs -/
def valid (D : DRS S) : Prop := ∀ i, trueAt D i

/-- Dynamic entailment: D₁ ⊨ D₂ iff D₁ ; D₂ has same outputs as D₁ -/
def entails (D₁ D₂ : DRS S) : Prop :=
  ∀ i, (∃ j, D₁ i j) → ∀ j, D₁ i j → ∃ k, D₂ j k

notation D₁ " ⊨ " D₂ => entails D₁ D₂

end Truth


section Theorems

variable {S : Type*}

/-- Sequencing is associative -/
theorem dseq_assoc (D₁ D₂ D₃ : DRS S) :
    (D₁ ⨟ D₂) ⨟ D₃ = D₁ ⨟ (D₂ ⨟ D₃) := by
  funext i j
  simp only [dseq, eq_iff_iff]
  constructor
  · intro ⟨h, ⟨h', hD₁, hD₂⟩, hD₃⟩
    exact ⟨h', hD₁, h, hD₂, hD₃⟩
  · intro ⟨h', hD₁, h, hD₂, hD₃⟩
    exact ⟨h, ⟨h', hD₁, hD₂⟩, hD₃⟩

/-- Test is left identity for sequencing (when condition holds everywhere) -/
theorem test_dseq (C : Condition S) (D : DRS S) (hC : ∀ i, C i) :
    test C ⨟ D = D := by
  funext i j
  simp only [dseq, test, eq_iff_iff]
  constructor
  · intro ⟨h, ⟨hih, _⟩, hD⟩
    subst hih
    exact hD
  · intro hD
    exact ⟨i, ⟨rfl, hC i⟩, hD⟩

/-- Double negation for tests -/
theorem dneg_dneg_test (C : Condition S) :
    dneg (test (dneg (test C))) = C := by
  funext i
  simp only [dneg, test, eq_iff_iff]
  constructor
  · intro h
    by_contra hC
    apply h
    use i
    constructor
    · rfl
    · intro ⟨k, hik, hCk⟩
      subst hik
      exact hC hCk
  · intro hC ⟨j, hji, hNeg⟩
    apply hNeg
    use i
    exact ⟨hji.symm, hC⟩

/-- Closure is idempotent -/
theorem closure_closure (D : DRS S) :
    closure (test (closure D)) = closure D := by
  funext i
  simp only [closure, test, eq_iff_iff]
  constructor
  · intro ⟨j, hij, k, hD⟩
    subst hij
    exact ⟨k, hD⟩
  · intro ⟨k, hD⟩
    exact ⟨i, rfl, k, hD⟩

/-- Sequencing distributes over closure -/
theorem dseq_closure (D₁ D₂ : DRS S) :
    closure (D₁ ⨟ D₂) = λ i => ∃ h, D₁ i h ∧ closure D₂ h := by
  funext i
  simp only [closure, dseq, eq_iff_iff]
  constructor
  · intro ⟨j, h, hD₁, hD₂⟩
    exact ⟨h, hD₁, j, hD₂⟩
  · intro ⟨h, hD₁, j, hD₂⟩
    exact ⟨j, h, hD₁, hD₂⟩

end Theorems


end Theories.DynamicSemantics.Core.DynamicTy2
