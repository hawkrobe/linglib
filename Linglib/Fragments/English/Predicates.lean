/-
# English Predicate Lexicon

Re-exports verbal and adjectival predicate entries.

## Modules

- `Predicates.Verbal` — Verbal predicates (know, believe, hope, run, kick...)
- `Predicates.Adjectival` — Adjectival predicates (tall, happy, full...)

## Usage

```lean
import Linglib.Fragments.English.Predicates

-- Verbal predicates
#check Predicates.Verbal.know
#check Predicates.Verbal.hope

-- Adjectival predicates
#check Predicates.Adjectival.tall
#check Predicates.Adjectival.happy
```
-/

import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival

namespace Fragments.English.Predicates

-- Re-export for convenience
export Verbal (
  -- Types
  VerbClass PresupTriggerType ComplementType ThetaRole ControlType VerbEntry
  PreferentialBuilder
  -- Functions
  getCoSSemantics presupposesComplement isPresupTrigger
  isPreferentialAttitude isAntiRogative canEmbedQuestion
  allVerbs antiRogativeVerbs questionEmbeddingVerbs
  toWord3sg toWordBase
)

export Adjectival (
  AdjectivalPredicateEntry
  allEntries
)

end Fragments.English.Predicates
