/-
# Exhaustification Interface for Pragmatic Models

Re-exports the unified exhaustification interface from `Unified.lean`.

## Migration Note

This file previously defined `Exhaustifiable` directly. It now re-exports
from `Unified.lean` which provides:
- Unified `ExhOperator` enum (IE, MW)
- `applyExh` and `applyExhAtParse` entry points
- `Exhaustifiable` typeclass with position-dependent alternatives

## Architecture

```
Core/Parse.lean
├── Parse (general grammatical ambiguity)
├── scopeParses (surface/inverse)
└── exhParses (lit/M/O/I/...)

NeoGricean/Exhaustivity/Basic.lean
├── exhIE, exhMW (core operators)
└── Prop' World, ALT sets

NeoGricean/Exhaustivity/Unified.lean
├── ExhOperator enum
├── applyExh, applyExhAtParse
└── Exhaustifiable typeclass

NeoGricean/Exhaustivity/Interface.lean (this file)
└── Re-exports from Unified.lean
```

## References

- Fox (2007). "Free choice and the theory of scalar implicatures"
- Chierchia, Fox & Spector (2012). "Scalar implicature as a grammatical phenomenon"
- Spector (2016). "Comparing exhaustivity operators"
- Franke & Bergen (2020). "Theory-driven statistical modeling"
-/

import Linglib.Theories.NeoGricean.Exhaustivity.Unified

namespace NeoGricean.Exhaustivity.Interface

-- Re-export everything from Unified
export NeoGricean.Exhaustivity.Unified (
  ExhOperator
  applyExh
  AlternativesAtPosition
  applyExhAtParse
  literal_parse_is_identity
  Exhaustifiable
  getParses
  toRSAMeaning
)

-- Re-export Parse types from Core
export Core (Parse ExhPosition exhParses scopeParses)

-- Re-export core operators from Basic
export NeoGricean.Exhaustivity (Prop' exhIE exhMW)

end NeoGricean.Exhaustivity.Interface
