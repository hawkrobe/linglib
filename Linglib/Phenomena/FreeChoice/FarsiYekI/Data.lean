/-
# Farsi *yek-i* DPs: Empirical Data

Empirical patterns for Farsi *yek-i* DPs as Existential Free Choice Items (EFCIs).

## The Key Pattern

*yek-i* DPs behave as:
- Plain existentials in DE contexts
- Free choice items under deontic modals
- Modal variation items under epistemic modals
- Uniqueness in root contexts (no modal component)

## Source

Alonso-Ovalle, L. & Moghiseh, S. (2025). Existential free choice items:
The case of Farsi *yek-i* DPs. Semantics & Pragmatics 18.
-/

namespace Phenomena.FreeChoice.FarsiYekI

-- ============================================================================
-- PART 1: Basic Yek-i DP Data
-- ============================================================================

/--
A judgment about a Farsi *yek-i* DP sentence.
-/
structure YekIDatum where
  /-- The Farsi sentence -/
  farsi : String
  /-- English gloss -/
  gloss : String
  /-- English translation -/
  translation : String
  /-- The context type -/
  contextType : String
  /-- The modal flavor (if any) -/
  modalFlavor : Option String
  /-- Primary reading -/
  primaryReading : String
  /-- Is free choice available? -/
  freeChoiceAvailable : Bool
  /-- Is modal variation available? -/
  modalVariationAvailable : Bool
  /-- Is uniqueness conveyed? -/
  uniqueness : Bool
  /-- Source example number -/
  exampleNum : String
  deriving Repr

-- ============================================================================
-- PART 2: Root Context (No Modal) - Uniqueness
-- ============================================================================

/-!
## Root Contexts: Uniqueness

In root contexts without modals, *yek-i* DPs convey UNIQUENESS:
"exactly one individual satisfies the predicate"

This is NOT a free choice reading - there's no permission or epistemic possibility.
The uniqueness is part of the core meaning.

Alonso-Ovalle & Moghiseh argue this comes from exhaustification of domain
alternatives (pre-exhaustified), conveying that for most individuals, the
predicate does NOT hold.
-/

/-- Example (15): Root context with uniqueness -/
def rootUniqueness : YekIDatum :=
  { farsi := "yek-i az dānešju-hā umæd."
  , gloss := "one-INDF of student-PL came"
  , translation := "One of the students came."
  , contextType := "root (no modal)"
  , modalFlavor := none
  , primaryReading := "Exactly one student came"
  , freeChoiceAvailable := false
  , modalVariationAvailable := false
  , uniqueness := true
  , exampleNum := "15"
  }

-- ============================================================================
-- PART 3: Deontic Modals - Free Choice
-- ============================================================================

/-!
## Deontic Modals: Free Choice Effect

Under deontic modals (permission), *yek-i* DPs yield FREE CHOICE:
"for each individual, it is permitted to VP"

Example: "You may take one of the apples"
Reading: You may take THIS apple, you may take THAT apple, etc.
-/

/-- Example (17): Deontic free choice -/
def deonticFreeChoice : YekIDatum :=
  { farsi := "mituni yek-i az in sib-ā-ro bardāri."
  , gloss := "can.2SG one-INDF of this apple-PL-RA pick.2SG"
  , translation := "You can pick one of these apples."
  , contextType := "deontic modal"
  , modalFlavor := some "permission"
  , primaryReading := "For each apple x, you may pick x"
  , freeChoiceAvailable := true
  , modalVariationAvailable := false
  , uniqueness := true  -- Still embedded uniqueness
  , exampleNum := "17"
  }

/-- Deontic context with books -/
def deonticBooks : YekIDatum :=
  { farsi := "mituni yek-i az in ketāb-hā-ro bekhuni."
  , gloss := "can.2SG one-INDF of this book-PL-RA read.2SG"
  , translation := "You can read one of these books."
  , contextType := "deontic modal"
  , modalFlavor := some "permission"
  , primaryReading := "For each book x, you may read x"
  , freeChoiceAvailable := true
  , modalVariationAvailable := false
  , uniqueness := true
  , exampleNum := "—"
  }

-- ============================================================================
-- PART 4: Epistemic Modals - Modal Variation
-- ============================================================================

/-!
## Epistemic Modals: Modal Variation Effect

Under epistemic modals, *yek-i* DPs yield MODAL VARIATION:
"at least two individuals are epistemically possible"

Example: "One of the students might have stolen the book"
Reading: It's possible it was THIS student, it's possible it was THAT student...

This is WEAKER than free choice - not every individual is a possibility,
but at least TWO are.
-/

/-- Example (22): Epistemic modal variation -/
def epistemicModalVariation : YekIDatum :=
  { farsi := "yek-i az dānešju-hā ketāb-o dozid-e."
  , gloss := "one-INDF of student-PL book-RA stole-3SG"
  , translation := "One of the students (might have) stolen the book."
  , contextType := "epistemic modal"
  , modalFlavor := some "epistemic possibility"
  , primaryReading := "At least two students are possible thieves"
  , freeChoiceAvailable := false
  , modalVariationAvailable := true
  , uniqueness := true
  , exampleNum := "22"
  }

/-- Epistemic with explicit modal -/
def epistemicExplicit : YekIDatum :=
  { farsi := "momken-e yek-i az dānešju-hā biyād."
  , gloss := "possible-is one-INDF of student-PL come.3SG"
  , translation := "It's possible that one of the students will come."
  , contextType := "epistemic modal"
  , modalFlavor := some "epistemic possibility"
  , primaryReading := "At least two students are possible comers"
  , freeChoiceAvailable := false
  , modalVariationAvailable := true
  , uniqueness := true
  , exampleNum := "—"
  }

-- ============================================================================
-- PART 5: DE Contexts - Plain Existential
-- ============================================================================

/-!
## DE Contexts: Plain Existential

In downward-entailing contexts (negation, antecedent of conditional),
*yek-i* DPs behave as PLAIN EXISTENTIALS (like English "any"):

"I didn't see one of the students" = "I didn't see any student"
-/

/-- DE context: negation -/
def deNegation : YekIDatum :=
  { farsi := "yek-i az dānešju-hā-ro nadid-æm."
  , gloss := "one-INDF of student-PL-RA not.see-1SG"
  , translation := "I didn't see any of the students."
  , contextType := "DE (negation)"
  , modalFlavor := none
  , primaryReading := "I saw no student"
  , freeChoiceAvailable := false
  , modalVariationAvailable := false
  , uniqueness := false  -- No uniqueness under negation
  , exampleNum := "—"
  }

/-- DE context: conditional antecedent -/
def deConditional : YekIDatum :=
  { farsi := "ægær yek-i az dānešju-hā biyād, xošhāl mišæm."
  , gloss := "if one-INDF of student-PL come.3SG happy become.1SG"
  , translation := "If any of the students comes, I'll be happy."
  , contextType := "DE (conditional)"
  , modalFlavor := none
  , primaryReading := "If any student comes..."
  , freeChoiceAvailable := false
  , modalVariationAvailable := false
  , uniqueness := false
  , exampleNum := "—"
  }

-- ============================================================================
-- PART 6: Yek-i vs Irgendein Contrast
-- ============================================================================

/-!
## Cross-linguistic Contrast: Yek-i vs Irgendein

A key empirical contrast from the paper:

**German *irgendein*** in root contexts: MODAL COMPONENT
- "Irgendjemand hat angerufen" = "Somebody (or other) called"
- Speaker conveys epistemic uncertainty/indifference

**Farsi *yek-i*** in root contexts: NO MODAL COMPONENT
- "Yek-i zæng zæd" = "Exactly one person called"
- No epistemic uncertainty, just uniqueness

This contrast motivates the typology of rescue mechanisms:
- Irgendein: can insert covert epistemic modal → rescues in root
- Yek-i: cannot insert covert modal → uniqueness only
-/

/-- EFCI contrast data -/
structure EFCIContrastDatum where
  /-- The language -/
  language : String
  /-- The EFCI item -/
  item : String
  /-- Example sentence -/
  sentence : String
  /-- Root context reading -/
  rootReading : String
  /-- Has modal component in root? -/
  hasModalInRoot : Bool
  /-- Source -/
  source : String
  deriving Repr

/-- German irgendein: modal component -/
def irgendeinRoot : EFCIContrastDatum :=
  { language := "German"
  , item := "irgendein"
  , sentence := "Irgendjemand hat angerufen."
  , rootReading := "Somebody (the speaker doesn't know/care who) called"
  , hasModalInRoot := true
  , source := "Kratzer & Shimoyama 2002"
  }

/-- Farsi yek-i: no modal component -/
def yekiRoot : EFCIContrastDatum :=
  { language := "Farsi"
  , item := "yek-i"
  , sentence := "Yek-i zæng zæd."
  , rootReading := "Exactly one person called"
  , hasModalInRoot := false
  , source := "Alonso-Ovalle & Moghiseh 2025"
  }

/-- Romanian vreun: ungrammatical in root -/
def vreunRoot : EFCIContrastDatum :=
  { language := "Romanian"
  , item := "vreun"
  , sentence := "*Vreun student a venit."
  , rootReading := "(Ungrammatical)"
  , hasModalInRoot := false  -- N/A - ungrammatical
  , source := "Fălăuș 2014"
  }

-- ============================================================================
-- PART 7: Embedded Uniqueness
-- ============================================================================

/-!
## Embedded Uniqueness

A distinctive feature of *yek-i*: uniqueness is preserved even under modals.

"You may take one of the apples" conveys:
1. FREE CHOICE: For each apple, you may take it
2. UNIQUENESS: ...but only take ONE apple total

This embedded uniqueness comes from exhaustification happening below the modal.
-/

/-- Embedded uniqueness with explicit continuation -/
def embeddedUniqueness : YekIDatum :=
  { farsi := "mituni yek-i az in sib-ā-ro bardāri, #væli do-tā væli næ."
  , gloss := "can.2SG one-INDF of this apple-PL-RA pick.2SG but two-CL but not"
  , translation := "You can pick one of these apples, #but not two."
  , contextType := "deontic modal"
  , modalFlavor := some "permission"
  , primaryReading := "FC + uniqueness (continuation is redundant)"
  , freeChoiceAvailable := true
  , modalVariationAvailable := false
  , uniqueness := true
  , exampleNum := "—"
  }

-- ============================================================================
-- PART 8: Summary Data Collections
-- ============================================================================

/-- All yek-i examples -/
def allYekIData : List YekIDatum :=
  [ rootUniqueness
  , deonticFreeChoice
  , deonticBooks
  , epistemicModalVariation
  , epistemicExplicit
  , deNegation
  , deConditional
  , embeddedUniqueness
  ]

/-- All EFCI contrast data -/
def efciContrastData : List EFCIContrastDatum :=
  [ irgendeinRoot
  , yekiRoot
  , vreunRoot
  ]

-- ============================================================================
-- PART 9: EFCI Typology
-- ============================================================================

/--
EFCI rescue mechanism typology from Alonso-Ovalle & Moghiseh (2025).
-/
inductive EFCIType where
  /-- Neither rescue mechanism (e.g., Romanian vreun) -/
  | vreun
  /-- Modal insertion available (e.g., German irgendein) -/
  | irgendein
  /-- Partial exhaustification available (e.g., Farsi yek-i) -/
  | yeki
  deriving DecidableEq, BEq, Repr

/-- EFCI typology data -/
structure EFCITypologyDatum where
  /-- The EFCI type -/
  efciType : EFCIType
  /-- Example language -/
  language : String
  /-- The item -/
  item : String
  /-- Can insert covert modal? -/
  canInsertModal : Bool
  /-- Can do partial exhaustification? -/
  canPartialExh : Bool
  /-- Grammatical in root contexts? -/
  grammaticalInRoot : Bool
  /-- Root context reading -/
  rootReading : String
  deriving Repr

/-- vreun-type: neither rescue -/
def vreunTypology : EFCITypologyDatum :=
  { efciType := .vreun
  , language := "Romanian"
  , item := "vreun"
  , canInsertModal := false
  , canPartialExh := false
  , grammaticalInRoot := false
  , rootReading := "(Ungrammatical)"
  }

/-- irgendein-type: modal insertion -/
def irgendeinTypology : EFCITypologyDatum :=
  { efciType := .irgendein
  , language := "German"
  , item := "irgendein"
  , canInsertModal := true
  , canPartialExh := true  -- Also allows partial exh
  , grammaticalInRoot := true
  , rootReading := "Epistemic modal (speaker ignorance/indifference)"
  }

/-- yek-i-type: partial exhaustification only -/
def yekiTypology : EFCITypologyDatum :=
  { efciType := .yeki
  , language := "Farsi"
  , item := "yek-i"
  , canInsertModal := false
  , canPartialExh := true
  , grammaticalInRoot := true
  , rootReading := "Uniqueness (exactly one)"
  }

/-- Full EFCI typology -/
def efciTypology : List EFCITypologyDatum :=
  [ vreunTypology
  , irgendeinTypology
  , yekiTypology
  ]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data Types
- `YekIDatum`: Judgment about a Farsi yek-i sentence
- `EFCIContrastDatum`: Cross-linguistic EFCI contrast
- `EFCITypologyDatum`: EFCI rescue mechanism typology

### Key Empirical Patterns

| Context | Reading | FC? | MV? | Uniqueness? |
|---------|---------|-----|-----|-------------|
| Root (no modal) | Exactly one | ✗ | ✗ | ✓ |
| Deontic | Free choice | ✓ | ✗ | ✓ |
| Epistemic | Modal variation | ✗ | ✓ | ✓ |
| DE contexts | Plain existential | ✗ | ✗ | ✗ |

### EFCI Typology

| Type | +Modal insertion | +Partial exh | Root reading |
|------|-----------------|--------------|--------------|
| vreun | ✗ | ✗ | *Ungrammatical |
| irgendein | ✓ | ✓ | Epistemic modal |
| yek-i | ✗ | ✓ | Uniqueness |

### References
- Alonso-Ovalle & Moghiseh (2025). Existential free choice items. S&P 18.
- Kratzer & Shimoyama (2002). Indeterminate pronouns.
- Fălăuș (2014). (Non)exhaustivity in unconditionals.
-/

end Phenomena.FreeChoice.FarsiYekI
