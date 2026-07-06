/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Harmony.Basic

/-!
# Tongue-root systems and the [ATR]-inventory correlation

Casali's typology of tongue-root harmony systems ([casali-2024-inventory], the
inventory-structure chapter of [ritter-vanderhulst-2024]; [casali-2003],
[casali-2008]): systems with a tongue-root contrast in high vowels (`/2IU/`) are
characteristically [+ATR]-dominant (69 of 72 surveyed), while systems contrasting
tongue root only in non-high vowels (`/1IU/`) show [+ATR] inertness and [−ATR]
dominance indicators. Whether the feature is binary [±ATR] or privative
[ATR]/[RTR] is explicitly open in the source; the value type here is neutral
between the two readings.

The correlation is a defeasible typological tendency, never a theorem: Casali's
own chapter records /1IU/ exceptions (Legbo, Ikoma), a questionable /2IU/
exception (Kimatuumbi), and a dominance-reversal class (Kinande, Komo, Lango,
Turkana, …) where [+ATR] dominance is overridden in identifiable contexts.
Per-language rows live with fragments and studies, not here.

## Main definitions

* `ATR`: the tongue-root feature value.
* `InventoryClass`: Casali's `/2IU/` vs `/1IU/` classification (applies only to
  systems with a tongue-root contrast at all — five-vowel systems are excluded).
* `DominanceIndicator`: the five evidence types for a dominant value.
* `TongueRootProfile`, `InventoryClass.predictedDominant`: a language's row
  schema and the correlation as a prediction function; conformance is stated
  inline at use sites (`∀ v ∈ p.dominant, v = p.inventoryClass.predictedDominant`).
-/

namespace Phonology.TongueRoot

/-- The tongue-root feature value: `[+ATR]` or `[−ATR]`. Neutral between binary
    and privative readings ([casali-2024-inventory]). -/
inductive ATR where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The opposite value. -/
def ATR.opp : ATR → ATR
  | .plus => .minus
  | .minus => .plus

@[simp] theorem ATR.opp_opp (v : ATR) : v.opp.opp = v := by cases v <;> rfl

/-- Casali's inventory classification: where the tongue-root contrast lives.
    Only systems with a contrast at all are classified (five-vowel `/i e a o u/`
    systems fall outside the typology, [casali-2024-inventory] fn. 1). -/
inductive InventoryClass where
  /-- Contrast in high vowels (possibly elsewhere too): nine-vowel Akan/Maasai,
      seven-vowel Kinande, ten-vowel Guébie. -/
  | twoIU
  /-- Contrast only in non-high vowels: the common seven-vowel
      `/i u e ɛ o ɔ a/` type (Yoruba, Wolof). -/
  | oneIU
  deriving DecidableEq, Repr

/-- The five evidence types for a dominant [ATR] value
    ([casali-2024-inventory] §15.2.1, following [casali-2003]). -/
inductive DominanceIndicator where
  /-- Invariant dominant affixes spreading onto roots (Maasai `/íé/`). -/
  | dominantAffix
  /-- Spreading across word boundaries or between compound members. -/
  | crossWordSpreading
  /-- Systematic preservation of one value in vowel coalescence. -/
  | coalescencePreservation
  /-- A phonemically unpaired vowel with a predictable harmonized allophone. -/
  | allophonicDominance
  /-- Harmonizing affixes surfacing with one value where harmony is inapplicable. -/
  | weakAssimilatory
  deriving DecidableEq, Repr

/-- A language's tongue-root row: inventory class, control type
    (`Phonology.Harmony.ControlType` — cross-cutting the inventory
    classification: root-controlled Degema and Guébie vs dominant-recessive
    Maasai), and the observed dominant value with its evidence (`none` =
    symmetric/inert patterning). -/
structure TongueRootProfile where
  inventoryClass : InventoryClass
  control        : Harmony.ControlType ATR
  dominant       : Option ATR
  evidence       : List DominanceIndicator := []
  deriving DecidableEq, Repr

/-- The dominant value the [ATR]-inventory correlation predicts from inventory
    structure ([casali-2024-inventory]): `/2IU/` systems tend to [+ATR]
    dominance, `/1IU/` systems to [−ATR] dominance. A defeasible tendency —
    the chapter records the exceptions — so studies state per-language
    conformance inline (`∀ v ∈ p.dominant, v = p.inventoryClass.predictedDominant`),
    never as a universal theorem. -/
def InventoryClass.predictedDominant : InventoryClass → ATR
  | .twoIU => .plus
  | .oneIU => .minus

end Phonology.TongueRoot
