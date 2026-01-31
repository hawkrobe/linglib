/-
# Aspect Module

Public API for aspectual classification.

This module re-exports the core types and theory for aspectual analysis:
- `Telicity`, `Duration`, `Dynamicity` — Core features
- `VendlerClass` — Four-way classification
- `AspectualProfile` — Feature bundle with operations

## Usage

```lean
import Linglib.Theories.Montague.Lexicon.Aspect

-- Classify a verb
def runProfile : AspectualProfile := activityProfile
#eval runProfile.toVendlerClass  -- .activity

-- Model aspectual shift: "run a mile"
def runMileProfile := runProfile.telicize
#eval runMileProfile.toVendlerClass  -- .accomplishment
```

## Connection to Other Modules

- `OntologicalPreconditions.lean`: Uses `Telicity` for CoS verbs
- `Fragments/Verbs.lean`: `VerbEntry` can include aspectual profile
- `Phenomena/Aspect/Diagnostics.lean`: Empirical tests for classification
-/

import Linglib.Theories.Montague.Lexicon.Aspect.Basic
import Linglib.Theories.Montague.Lexicon.Aspect.Theory

namespace Montague.Lexicon.Aspect

-- Re-export everything from Basic and Theory
-- (Lean 4 automatically exports namespace contents)

end Montague.Lexicon.Aspect
