/-
# Dynamic Ty2: Compositional Dynamic Semantics
@cite{muskens-1996} @cite{brasoveanu-2007}

The compositional layer that @cite{muskens-1996} adds on top of the
core dynamic algebra (defined in `Core.DRS`): discourse referents as
functions from states (`Dref S E = S → E`), the `AssignmentStructure`
class for random assignment, and atomic condition constructors.

## Core Idea

Instead of modeling discourse referents as atomic entities (variables)
and info states as functions taking dref's as arguments (i.e. variable
assignments), we model info states as atomic entities (of type s) and
dref's as functions taking info states as arguments.

## Type System

| Type | Description | Lean |
|------|-------------|------|
| `s` | Assignments (atomic) | `S` parameter |
| `e` | Individuals | `E` parameter |
| `t` | Truth values | `Prop` |
| `sτ` | Drefs (for static τ) | `S → τ` |
| `s(st)` | DRS meanings | `DRS S` (from `Core.DRS`) |

## Embeddings

- DPL: variables xᵢ ↦ λs. s(i) (projection functions)
- PLA: variables + pronouns via resolution
- DRT: isomorphic to CDRT (box notation)
- BUS: Dynamic Ty2 + bilateral (pos/neg) structure

-/

import Linglib.Theories.Semantics.Dynamic.Connectives.Defs

namespace Semantics.Dynamic.Core

-- Re-export the DRS algebra so downstream code that opens
-- Semantics.Dynamic.Core continues to see DRS, Condition, dseq, test, etc.
export DynProp (DRS Condition
  dseq test dneg dimpl ddisj closure
  trueAt valid entails
  dseq_assoc test_dseq dneg_dneg_test closure_closure dseq_closure)

/-!
Dynamic Ty2 is parameterized by:
- `S`: The type of "assignments" (info states as atomic entities)
- `E`: The type of individuals

This follows Muskens's insight: instead of assignments being functions,
they are atomic, and drefs are functions FROM assignments.
-/

/-- Discourse referent for individuals: type `se` in Dynamic Ty2 -/
abbrev Dref (S E : Type*) := S → E


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
| φ; ψ | TR(φ) ⨟ TR(ψ) |
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


/-!
## Axioms AX2–AX4: Variable vs Constant Registers
@cite{muskens-1996} p. 156

AX1 is captured by `AssignmentStructure.extend` above. The remaining axioms:

- **AX2** (`VAR(u)`): classifies registers as *variable* (unspecific) or *constant* (specific).
  In the formalization, variable drefs are arbitrary `S → E` functions; constant drefs
  are `specificDref e = λ _ => e`.

- **AX3** (`uₙ ≠ uₘ`): distinct variable registers are distinct as functions.
  This is ensured by `extend_other`: updating one dref preserves others.

- **AX4** (`∀i v(Tom)(i) = tom`): constant registers return the same value in all states.
  This is `specificDref_constant` below.
-/

/-- AX4: Specific (constant) drefs return the same value regardless of state. -/
theorem specificDref_constant {S E : Type*} (e : E) (i j : S) :
    specificDref (S := S) e i = specificDref e j := rfl

/-- Specific drefs are invariant under `extend` (consequence of AX1 + AX4). -/
theorem specificDref_extend_invariant {S E : Type*} [AssignmentStructure S E]
    (e : E) (u : S → E) (d : E) (i : S) (h : specificDref e ≠ u) :
    specificDref e (AssignmentStructure.extend i u d) = e := by
  exact AssignmentStructure.extend_other i u (specificDref e) d h.symm


end Semantics.Dynamic.Core
