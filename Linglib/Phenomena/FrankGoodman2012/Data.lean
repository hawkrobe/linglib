/-
# Frank & Goodman (2012) - Empirical Data

"Predicting Pragmatic Reasoning in Language Games"
Science 336(6084): 998

Empirical data for simple reference games:
- A context: set of objects varying on dimensions (color, shape)
- Utterances: words describing features
- Task: speaker refers to target object, listener identifies it
-/

import Linglib.Phenomena.EmpiricalData

namespace FrankGoodman2012

open Phenomena

-- ============================================================================
-- Study Metadata
-- ============================================================================

/-- Citation for this study -/
def citation : String := "Frank, M.C. & Goodman, N.D. (2012). Predicting Pragmatic Reasoning in Language Games. Science 336(6084): 998."

/-- Speaker choice measure: forced choice reference game (production) -/
def speakerMeasure : MeasureSpec :=
  { scale := .proportion, task := .forcedChoice, unit := "probability 0-1" }

/-- Listener interpretation measure: forced choice (comprehension) -/
def listenerMeasure : MeasureSpec :=
  { scale := .proportion, task := .forcedChoice, unit := "probability 0-1" }


-- ============================================================================
-- Data Structures
-- ============================================================================

/-- A reference game datum with empirical measurements -/
structure RefGameDatum where
  description : String
  objects : List String
  utterances : List String
  targetObject : String
  humanSpeakerChoice : Option (String × Float)  -- (word, probability)
  humanListenerChoice : Option (String × Float) -- (object, probability given word)
  citation : Option String

-- ============================================================================
-- Classic Examples from Frank & Goodman (2012)
-- ============================================================================

/-- The classic blue/green square/circle example from Figure 1 -/
def blueGreenContext : RefGameDatum := {
  description := "Three objects: blue square, blue circle, green square"
  objects := ["blue_square", "blue_circle", "green_square"]
  utterances := ["blue", "green", "square", "circle"]
  targetObject := "blue_square"
  humanSpeakerChoice := some ("blue", 0.50)  -- roughly equal between blue/square
  humanListenerChoice := some ("blue_square", 0.67)  -- given "square", prefer blue_square
  citation := some "Frank & Goodman (2012), Figure 1"
}

/-- Key finding: hearing "square" → listeners infer blue_square over green_square -/
def squareImplicature : RefGameDatum := {
  description := "Listener hearing 'square' infers blue_square over green_square"
  objects := ["blue_square", "blue_circle", "green_square"]
  utterances := ["blue", "green", "square", "circle"]
  targetObject := "blue_square"  -- what listener should infer
  humanSpeakerChoice := none
  humanListenerChoice := some ("blue_square", 0.67)
  citation := some "Frank & Goodman (2012)"
}

-- ============================================================================
-- Phenomenon Description
-- ============================================================================

/--
## The Reference Game Phenomenon

In reference games, pragmatic listeners use speaker informativeness to
disambiguate references.

**Setup:** Context = {blue square, blue circle, green square}

**Literal semantics:**
- "blue" → {blue_square, blue_circle}
- "green" → {green_square}
- "square" → {blue_square, green_square}
- "circle" → {blue_circle}

**Pragmatic reasoning:**
1. If speaker wants green_square, "green" uniquely identifies it
2. If speaker says "square" instead, they probably don't mean green_square
3. Therefore: "square" → blue_square (pragmatic inference)

**Key empirical observation:** Listeners reason about *why* speakers
chose particular words, not just what words literally mean.
-/
def phenomenonDescription : String :=
  "Reference games demonstrate pragmatic disambiguation via speaker rationality"

end FrankGoodman2012
