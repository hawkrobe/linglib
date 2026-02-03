/-
# Farsi Determiner and Indefinite Lexicon

Lexical entries for Farsi determiners, focusing on *yek-i* DPs as
Existential Free Choice Items (EFCIs).

## The Key Item: *yek-i*

*yek-i* literally means "one" (numeral) + indefiniteness marker.
As a DP, *yek-i az NP* ("one of the NPs") behaves as an EFCI:
- Plain existential in DE contexts
- Free choice under deontic modals
- Modal variation under epistemic modals
- Uniqueness in root contexts

## References

- Alonso-Ovalle & Moghiseh (2025). Existential free choice items. S&P 18.
- Jasbi (2016). Three types of indefinites in Persian.
-/

import Linglib.Core.Basic
import Mathlib.Data.Rat.Defs

namespace Fragments.Farsi.Determiners

-- ============================================================================
-- PART 1: EFCI Properties
-- ============================================================================

/--
EFCI rescue mechanism type.
Determines how the item rescues itself from the exhaustification contradiction.
-/
inductive EFCIRescue where
  /-- No rescue available (ungrammatical in UE root) -/
  | none
  /-- Can insert covert epistemic modal -/
  | modalInsertion
  /-- Can do partial exhaustification (prune one alternative type) -/
  | partialExhaustification
  /-- Both mechanisms available -/
  | both
  deriving DecidableEq, BEq, Repr

/--
The reading an EFCI yields in different contexts.
-/
inductive EFCIReading where
  /-- Plain existential (DE contexts) -/
  | plainExistential
  /-- Exactly one satisfies P (uniqueness) -/
  | uniqueness
  /-- For each x, it's permitted that P(x) -/
  | freeChoice
  /-- At least two x's are epistemically possible for P -/
  | modalVariation
  /-- Speaker doesn't know/care which x satisfies P -/
  | epistemicIgnorance
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- PART 2: Indefinite Entry
-- ============================================================================

/--
A Farsi indefinite DP entry.

Captures syntactic and semantic properties including EFCI behavior.
-/
structure IndefiniteEntry where
  /-- Surface form (Persian script) -/
  form : String
  /-- Romanization -/
  romanization : String
  /-- Gloss -/
  gloss : String
  /-- Is this an EFCI? -/
  isEFCI : Bool := false
  /-- EFCI rescue mechanism (if EFCI) -/
  efciRescue : Option EFCIRescue := none
  /-- Requires partitive 'az' construction? -/
  requiresPartitive : Bool := false
  /-- Can occur with mass nouns? -/
  allowsMass : Bool := false
  /-- Conveys speaker ignorance/indifference in root? -/
  speakerIgnorance : Bool := false
  /-- Conveys uniqueness in root? -/
  uniqueness : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- PART 3: Yek-i Entry
-- ============================================================================

/--
*yek-i*: Farsi existential free choice item.

Key properties:
- EFCI with partial exhaustification rescue
- Requires partitive 'az NP' ("one of the NPs")
- Yields uniqueness in root contexts (no modal insertion)
- Yields free choice under deontic modals
- Yields modal variation under epistemic modals
- Plain existential in DE contexts
-/
def yeki : IndefiniteEntry :=
  { form := "یکی"
  , romanization := "yek-i"
  , gloss := "one-INDF"
  , isEFCI := true
  , efciRescue := some .partialExhaustification
  , requiresPartitive := true
  , allowsMass := false
  , speakerIgnorance := false  -- NO modal component in root
  , uniqueness := true          -- Yields "exactly one" in root
  }

/--
*yek* (plain numeral): "one"

Not an EFCI - just a numeral. Contrast with *yek-i*.
-/
def yek : IndefiniteEntry :=
  { form := "یک"
  , romanization := "yek"
  , gloss := "one"
  , isEFCI := false
  , requiresPartitive := false
  , allowsMass := false
  }

/--
Indefinite suffix *-i*: Indefiniteness marker.

Attaches to nouns to create indefinites.
-/
def indef_i : IndefiniteEntry :=
  { form := "ـی"
  , romanization := "-i"
  , gloss := "-INDF"
  , isEFCI := false
  , requiresPartitive := false
  , allowsMass := true
  }

-- ============================================================================
-- PART 4: Context-Dependent Reading
-- ============================================================================

/--
Modal flavor type for context specification.
-/
inductive ModalFlavor where
  | deontic   -- Permission, obligation
  | epistemic -- Knowledge, belief
  deriving DecidableEq, BEq, Repr

/--
Context for determining EFCI reading.
-/
structure EFCIContext where
  /-- Is the context downward-entailing? -/
  isDE : Bool
  /-- Modal flavor if under a modal -/
  modalFlavor : Option ModalFlavor
  deriving Repr, BEq

/--
Root context (no modal, not DE).
-/
def rootContext : EFCIContext :=
  { isDE := false, modalFlavor := none }

/--
Deontic modal context.
-/
def deonticContext : EFCIContext :=
  { isDE := false, modalFlavor := some .deontic }

/--
Epistemic modal context.
-/
def epistemicContext : EFCIContext :=
  { isDE := false, modalFlavor := some .epistemic }

/--
Downward-entailing context.
-/
def deContext : EFCIContext :=
  { isDE := true, modalFlavor := none }

/--
Get the reading for an EFCI in a given context.
-/
def getReading (entry : IndefiniteEntry) (ctx : EFCIContext) : Option EFCIReading :=
  if !entry.isEFCI then
    -- Non-EFCI: just plain existential everywhere
    some .plainExistential
  else if ctx.isDE then
    -- DE contexts: always plain existential
    some .plainExistential
  else match ctx.modalFlavor with
    | some .deontic => some .freeChoice
    | some .epistemic => some .modalVariation
    | none =>
      -- Root context: depends on rescue mechanism
      match entry.efciRescue with
      | some .partialExhaustification => some .uniqueness
      | some .modalInsertion => some .epistemicIgnorance
      | some .both => some .uniqueness  -- Default
      | some .none => none  -- Ungrammatical
      | none => some .plainExistential  -- Not EFCI

-- ============================================================================
-- PART 5: Yek-i Readings
-- ============================================================================

/-- Yek-i in root context yields uniqueness -/
theorem yeki_root : getReading yeki rootContext = some .uniqueness := rfl

/-- Yek-i under deontic modal yields free choice -/
theorem yeki_deontic : getReading yeki deonticContext = some .freeChoice := rfl

/-- Yek-i under epistemic modal yields modal variation -/
theorem yeki_epistemic : getReading yeki epistemicContext = some .modalVariation := rfl

/-- Yek-i in DE context yields plain existential -/
theorem yeki_de : getReading yeki deContext = some .plainExistential := rfl

-- ============================================================================
-- PART 6: Cross-Linguistic EFCI Comparison
-- ============================================================================

/--
German *irgendein*: EFCI with modal insertion available.
-/
def irgendein_de : IndefiniteEntry :=
  { form := "irgendein"
  , romanization := "irgendein"
  , gloss := "IRGEND.a"
  , isEFCI := true
  , efciRescue := some .both  -- Both mechanisms available
  , requiresPartitive := false
  , speakerIgnorance := true   -- Has epistemic component
  , uniqueness := false
  }

/--
Romanian *vreun*: EFCI with no rescue mechanism.
-/
def vreun_ro : IndefiniteEntry :=
  { form := "vreun"
  , romanization := "vreun"
  , gloss := "VREUN"
  , isEFCI := true
  , efciRescue := some .none  -- No rescue!
  , requiresPartitive := false
  }

/--
Irgendein in root yields epistemic ignorance (or uniqueness with partial exh).
-/
theorem irgendein_root : getReading irgendein_de rootContext = some .uniqueness := rfl

/--
Vreun in root is ungrammatical (no rescue).
-/
theorem vreun_root_ungrammatical : getReading vreun_ro rootContext = none := rfl

-- ============================================================================
-- PART 7: The Lexicon
-- ============================================================================

/-- All Farsi indefinite entries -/
def allIndefinites : List IndefiniteEntry :=
  [yeki, yek, indef_i]

/-- Lookup by romanization -/
def lookup (romanization : String) : Option IndefiniteEntry :=
  allIndefinites.find? fun e => e.romanization == romanization

-- ============================================================================
-- PART 8: Semantic Properties
-- ============================================================================

/--
The uniqueness component of yek-i.

In root contexts, yek-i conveys: ∃!x. P(x) = "exactly one x satisfies P"

This comes from partial exhaustification of pre-exhaustified domain alternatives.
-/
def uniquenessSemantics : String :=
  "∃x. P(x) ∧ ∀y. y ≠ x → ¬P(y)"

/--
The free choice component under deontic modals.

Under ◇_deo, yek-i conveys: ∀x. ◇_deo[P(x) ∧ ∀y≠x. ¬P(y)]
"For each x, you may uniquely satisfy P with x"
-/
def freeChoiceSemantics : String :=
  "∀x ∈ D. ◇_deo[P(x) ∧ ∀y ∈ D. y ≠ x → ¬P(y)]"

/--
The modal variation component under epistemic modals.

Under ◇_epi, yek-i conveys: |{x : ◇_epi[P(x) ∧ ∀y≠x. ¬P(y)]}| ≥ 2
"At least two individuals are epistemic possibilities for uniquely satisfying P"
-/
def modalVariationSemantics : String :=
  "|{x ∈ D : ◇_epi[P(x) ∧ ∀y ∈ D. y ≠ x → ¬P(y)]}| ≥ 2"

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Types
- `EFCIRescue`: Rescue mechanism types (none, modalInsertion, partialExhaustification, both)
- `EFCIReading`: Reading types (plainExistential, uniqueness, freeChoice, modalVariation, epistemicIgnorance)
- `IndefiniteEntry`: Lexical entry for Farsi indefinites
- `EFCIContext`: Context specification for reading determination

### Key Lexical Entries
- `yeki`: Farsi *yek-i* (EFCI with partial exhaustification)
- `yek`: Farsi *yek* (plain numeral, not EFCI)
- `irgendein_de`: German *irgendein* (EFCI with both mechanisms)
- `vreun_ro`: Romanian *vreun* (EFCI with no rescue)

### Functions
- `getReading`: Determine EFCI reading from entry and context

### Key Theorems
- `yeki_root`: Root → uniqueness
- `yeki_deontic`: Deontic → free choice
- `yeki_epistemic`: Epistemic → modal variation
- `yeki_de`: DE → plain existential
- `vreun_root_ungrammatical`: Vreun root → ungrammatical

### The Yek-i Pattern

| Context | Reading | Semantics |
|---------|---------|-----------|
| Root | Uniqueness | ∃!x. P(x) |
| Deontic | Free choice | ∀x. ◇[P(x) ∧ only x] |
| Epistemic | Modal variation | ≥2 epistemic possibilities |
| DE | Plain existential | ∃x. P(x) |

### References
- Alonso-Ovalle & Moghiseh (2025). Existential free choice items. S&P 18.
- Kratzer & Shimoyama (2002). Indeterminate pronouns.
- Fălăuș (2014). (Non)exhaustivity in unconditionals.
-/

end Fragments.Farsi.Determiners
