import Linglib.Theories.Semantics.Tense.TemporalConnectives.Basic
import Linglib.Theories.Semantics.Tense.TemporalConnectives.EventBridge

/-!
# Temporal Connective Infrastructure

Shared infrastructure for temporal connective semantics. Study-specific
analyses live in `Phenomena/TemporalConnectives/Studies/`:

- `Anscombe1964.lean`: Point-level and event-level ∃∀/∃∃ semantics
- `Karttunen1974.lean`: *When*, *while*, *until*, *till*, *since*, *by*
- `Rett2020.lean`: Antonymy + aspectual coercion + ambidirectionality
- `BeaverCondoravdi2003.lean`: Intensional uniform analysis with `earliest`
- `OgiharaST2024.lean` (in `Phenomena/TenseAspect/Studies/`): Critique of B&C, eventuality-relative equivalence

## Submodules

- `Basic.lean`: Shared types (SentDenotation, timeTrace, denotation patterns)
- `EventBridge.lean`: The eventDenotation projection (Level 3 → Level 2)

-/
