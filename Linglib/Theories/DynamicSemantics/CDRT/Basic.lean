/-
# Compositional DRT (Muskens 1996)

Stub for Compositional DRT, which combines DRT with Montague grammar
for fully compositional dynamic semantics.

## Key Ideas

Muskens' CDRT:
- Uses type-theoretic framework compatible with Montague semantics
- DRSs are encoded as state transformers
- Fully compositional: meanings combine via function application
- Bridges static (Montague) and dynamic (DRT) semantics

## Semantic Architecture

Instead of DRS boxes, CDRT uses:
- State type: assignment sequences
- Dynamic propositions: relations between states
- Compositional combination rules

## Type System

| Type | Meaning |
|------|---------|
| e | Entities |
| t | Truth values |
| s | States (registers/assignments) |
| s → t | Dynamic propositions |
| (s → t) → s → t | Sentence meanings |

## References

- Muskens, R. (1996). Combining Montague Semantics and Discourse Representation.
- Linguistics and Philosophy 19:143-186.
-/

import Linglib.Theories.DynamicSemantics.Core.Basic

namespace Theories.DynamicSemantics.CDRT

-- ============================================================================
-- Core Types
-- ============================================================================

/--
CDRT state: a register/assignment function.

Registers are indexed by natural numbers and store entity values.
-/
abbrev Register (E : Type*) := Nat → E

/--
Dynamic proposition: relates input and output states.

⟦φ⟧ : Register E → Register E → Prop
-/
def DProp (E : Type*) := Register E → Register E → Prop

/--
Static proposition (for embedding classical logic).
-/
def SProp (E : Type*) := Register E → Prop

-- ============================================================================
-- Basic Constructions
-- ============================================================================

/--
Embed a static proposition as a dynamic one (test).

⟦p⟧(i, o) iff i = o ∧ p(i)
-/
def DProp.ofStatic {E : Type*} (p : SProp E) : DProp E :=
  fun i o => i = o ∧ p i

/--
Dynamic conjunction: relational composition.

⟦φ ; ψ⟧(i, o) iff ∃k. ⟦φ⟧(i, k) ∧ ⟦ψ⟧(k, o)
-/
def DProp.seq {E : Type*} (φ ψ : DProp E) : DProp E :=
  fun i o => ∃ k, φ i k ∧ ψ k o

infixl:65 " ;; " => DProp.seq

/--
New discourse referent introduction.

[new n] extends the register at position n with an arbitrary value.
-/
def DProp.new {E : Type*} (n : Nat) : DProp E :=
  fun i o => ∃ e : E, o = fun m => if m = n then e else i m

/--
Dynamic negation: test for failure.

⟦¬φ⟧(i, o) iff i = o ∧ ¬∃k. ⟦φ⟧(i, k)
-/
def DProp.neg {E : Type*} (φ : DProp E) : DProp E :=
  fun i o => i = o ∧ ¬∃ k, φ i k

/--
Dynamic implication: if φ succeeds, ψ must succeed.

⟦φ → ψ⟧(i, o) iff i = o ∧ ∀k. (⟦φ⟧(i, k) → ∃m. ⟦ψ⟧(k, m))
-/
def DProp.impl {E : Type*} (φ ψ : DProp E) : DProp E :=
  fun i o => i = o ∧ ∀ k, φ i k → ∃ m, ψ k m

-- ============================================================================
-- Compositional Semantics
-- ============================================================================

/--
Entity type: individuals.
-/
abbrev CDRTEntity (E : Type*) := E

/--
Generalized quantifier type.
-/
def GQ (E : Type*) := (E → DProp E) → DProp E

/--
Indefinite "a/an": introduces dref and applies predicate.

⟦a⟧ = λP.λQ. new n ; P(rn) ; Q(rn)

where rn is the register lookup at n.
-/
def indefinite {E : Type*} (n : Nat) (p : E → DProp E) (q : E → DProp E) : DProp E :=
  DProp.new n ;; (fun i o => ∃ k, p (i n) i k ∧ q (k n) k o)

/--
Pronoun: lookup register value.

⟦heₙ⟧ = rn (returns the value at register n)
-/
def pronoun {E : Type*} (n : Nat) : Register E → E :=
  fun r => r n

-- ============================================================================
-- Truth and Entailment
-- ============================================================================

/--
A dynamic proposition is TRUE at state i if it can transition somewhere.
-/
def DProp.true_at {E : Type*} (φ : DProp E) (i : Register E) : Prop :=
  ∃ o, φ i o

/--
Dynamic entailment: φ entails ψ if ψ is true after φ.
-/
def DProp.entails {E : Type*} (φ ψ : DProp E) : Prop :=
  ∀ i o, φ i o → ψ.true_at o

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Will Provide

### Core Types
- `Register E`: State as assignment function
- `DProp E`: Dynamic propositions (state relations)
- `SProp E`: Static propositions (for embedding)
- `GQ E`: Generalized quantifiers

### Operations
- `ofStatic`: Embed static as dynamic
- `seq` (;;): Dynamic conjunction
- `new`: Discourse referent introduction
- `neg`: Dynamic negation
- `impl`: Dynamic implication

### Compositional Rules
- `indefinite`: "a/an" semantics
- `pronoun`: Pronoun resolution

### Relations
- `true_at`: Truth at a state
- `entails`: Dynamic entailment

## Key Feature: Compositionality

Unlike standard DRT, CDRT meanings combine compositionally:
- NPs have type (e → DProp) → DProp
- VPs have type e → DProp
- Sentences have type DProp

## TODO

Full implementation including:
- Full fragment (VP, NP, S rules)
- Presupposition handling
- Connection to Core.Basic InfoState
- Proof of equivalence with DRT
-/

end Theories.DynamicSemantics.CDRT
