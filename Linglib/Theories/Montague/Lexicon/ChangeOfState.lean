/-
# Change-of-State Predicate Module

Re-exports `Montague.Lexicon.ChangeOfState.Theory`.

## Usage

```lean
import Linglib.Theories.Montague.Lexicon.ChangeOfState

open Montague.Lexicon.ChangeOfState

-- Get semantics for "stop smoking"
def stopSmokingSemantics := cosSemantics .cessation smokingPred
```
-/

import Linglib.Theories.Montague.Lexicon.ChangeOfState.Theory
