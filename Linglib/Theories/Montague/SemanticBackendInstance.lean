/-
# Montague Semantics as a SemanticBackend

This module shows how Montague semantics connects to the RSA pragmatics interface.

## The Connection

- World = Model (determines extensions of predicates)
- Utterance = Sentence with meaning (type t denotation)
- φ(u, w) = 1 if ⟦u⟧_w = true, 0 otherwise

This demonstrates that compositional semantics can provide the literal
semantics layer for RSA pragmatic reasoning.
-/

import Linglib.Core.SemanticBackend
import Linglib.Theories.Montague.Basic

namespace Montague

-- ============================================================================
-- Utterances as Typed Meanings
-- ============================================================================

/--
An utterance in Montague semantics is a sentence with its denotation.
We represent this as a function from models to truth values.
-/
structure MontagueSentence where
  /-- The string form of the sentence -/
  form : String
  /-- The semantic interpretation (a proposition) -/
  meaning : toyModel.interpTy .t

-- ============================================================================
-- Worlds as Model States
-- ============================================================================

/-- A world state (for now, just a placeholder) -/
inductive ToyWorld where
  | actual  -- The actual world as defined by toyModel
  deriving DecidableEq, Repr

-- ============================================================================
-- The Agreement Function φ
-- ============================================================================

/-- Evaluate a sentence's truth in a world -/
def evaluate (s : MontagueSentence) (w : ToyWorld) : Bool :=
  match w with
  | .actual => s.meaning

/-- The semantic agreement function: 1.0 if true, 0.0 if false -/
def montaguePhi (s : MontagueSentence) (w : ToyWorld) : Float :=
  if evaluate s w then 1.0 else 0.0

-- ============================================================================
-- Example Sentences
-- ============================================================================

open ToyLexicon in
/-- "John sleeps" as a MontagueSentence -/
def johnSleepsSent : MontagueSentence :=
  { form := "John sleeps"
  , meaning := apply sleeps_sem john_sem
  }

open ToyLexicon in
/-- "Mary sleeps" as a MontagueSentence -/
def marySleepsSent : MontagueSentence :=
  { form := "Mary sleeps"
  , meaning := apply sleeps_sem mary_sem
  }

open ToyLexicon in
/-- "John sees Mary" as a MontagueSentence -/
def johnSeesMary : MontagueSentence :=
  { form := "John sees Mary"
  , meaning := apply (apply sees_sem mary_sem) john_sem
  }

-- ============================================================================
-- Verify Agreement Function Behavior
-- ============================================================================

/-- "John sleeps" has φ = 1 in the actual world -/
theorem john_sleeps_phi : montaguePhi johnSleepsSent .actual = 1.0 := rfl

/-- "Mary sleeps" has φ = 0 in the actual world -/
theorem mary_sleeps_phi : montaguePhi marySleepsSent .actual = 0.0 := rfl

/-- "John sees Mary" has φ = 1 in the actual world -/
theorem john_sees_mary_phi : montaguePhi johnSeesMary .actual = 1.0 := rfl

-- ============================================================================
-- Summary: The Montague-RSA Connection
-- ============================================================================

/-
## The Interface

Montague semantics provides everything RSA's literal listener (L₀) needs:

1. **Utterances**: Sentences with compositional meanings
2. **Worlds**: Model states determining predicate extensions
3. **φ function**: Truth indicator (1.0 if true, 0.0 if false)

## How L₀ Uses This

Given utterance u and world w:
- L₀(w | u) ∝ P(w) × φ(u, w)
- True sentences get weight proportional to prior
- False sentences get weight 0

## Compositional Advantage

The key insight: φ is computed COMPOSITIONALLY:
- φ("John sleeps", w) = ⟦sleeps⟧_w(⟦John⟧_w)
- φ("John sees Mary", w) = ⟦sees⟧_w(⟦Mary⟧_w)(⟦John⟧_w)

The meanings of parts determine the meaning of the whole,
which determines truth, which determines φ.

## Full Instance

A complete SemanticBackend instance would require proving
boundedness of φ (which involves Float arithmetic proofs).
The structure above demonstrates the conceptual connection;
see Core/SemanticBackend.lean for the full interface.
-/

end Montague
