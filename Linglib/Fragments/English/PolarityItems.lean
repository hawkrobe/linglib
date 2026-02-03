/-
# English Polarity-Sensitive Items

Theory-neutral lexical entries for polarity-sensitive items:
- Negative Polarity Items (NPIs): any, ever, yet, at all, lift a finger
- Free Choice Items (FCIs): any (FC use), whatever, whichever
- Positive Polarity Items (PPIs): some, already, somewhat

## Key Properties Captured

1. **Licensing contexts**: Where the item can appear
2. **Strength**: Weak (DE) vs strong (anti-additive) NPIs
3. **Base quantificational force**: Underlying semantic type
4. **Domain alternatives**: Obligatory vs optional activation

## Theoretical Analyses (in Theories/)

- `Theories/NeoGricean/Exhaustivity/EFCI.lean`: Chierchia's exhaustification analysis
- `Phenomena/NPIs/Data.lean`: Empirical distribution data

## References

- Ladusaw (1979). Polarity sensitivity as inherent scope relations.
- Kadmon & Landman (1993). Any. L&P 16.
- Chierchia (2013). Logic in Grammar.
- Giannakidou (1998). Polarity Sensitivity as (Non)Veridical Dependency.
-/

import Linglib.Core.Basic

namespace Fragments.English.PolarityItems

-- ============================================================================
-- Licensing Contexts
-- ============================================================================

/--
Contexts that can license polarity-sensitive items.

These are characterized by their logical properties:
- DE (Downward Entailing): Reverses entailment direction
- Anti-additive: DE + distributes over disjunction
- Anti-morphic: Anti-additive + distributes over conjunction (= negation)
-/
inductive LicensingContext where
  | negation          -- "not", "never", "without"
  | nobody            -- "nobody", "nothing" (negative quantifiers)
  | few               -- "few NPs" (weak DE, controversial)
  | atMost            -- "at most n"
  | conditional_ant   -- Antecedent of conditional
  | before_clause     -- "before" clauses
  | without_clause    -- "without" PPs
  | only_focus        -- Focus of "only"
  | question          -- Questions (for some NPIs)
  | comparative       -- "more than", "less than"
  | superlative       -- "the most", "the least"
  | too_to            -- "too ADJ to VP"
  | modal_possibility -- Possibility modals (for FCIs)
  | modal_necessity   -- Necessity modals
  | imperative        -- Imperatives (for FCIs)
  | generic           -- Generic contexts (for FCIs)
  | free_relative     -- Free relatives: "whatever", "whoever"
  deriving DecidableEq, BEq, Repr

/--
Strength of downward entailingness.
-/
inductive DEStrength where
  | weak           -- Plain DE (licenses weak NPIs)
  | antiAdditive   -- DE + ∨-distributive (licenses strong NPIs)
  | antiMorphic    -- Anti-additive + ∧-distributive (= negation)
  deriving DecidableEq, BEq, Repr

/--
Get the DE strength of a licensing context.
-/
def LicensingContext.strength : LicensingContext → DEStrength
  | .negation => .antiMorphic
  | .nobody => .antiAdditive
  | .without_clause => .antiAdditive
  | .few => .weak  -- Controversial: some say not even DE
  | .atMost => .weak
  | .conditional_ant => .weak
  | .before_clause => .weak
  | .only_focus => .weak
  | .question => .weak  -- Non-monotonic, but licenses weak NPIs
  | .comparative => .weak
  | .superlative => .weak
  | .too_to => .weak
  | .modal_possibility => .weak  -- Not DE, but licenses FCIs
  | .modal_necessity => .weak
  | .imperative => .weak
  | .generic => .weak
  | .free_relative => .weak

-- ============================================================================
-- Polarity Item Types
-- ============================================================================

/--
Type of polarity sensitivity.
-/
inductive PolarityType where
  | npiWeak      -- Weak NPI: licensed by DE contexts
  | npiStrong    -- Strong NPI: requires anti-additive
  | fci          -- Free Choice Item: modal/generic/imperative
  | npi_fci      -- Dual use: NPI in DE, FCI under modals (= "any")
  | ppi          -- Positive Polarity Item: blocked in DE
  deriving DecidableEq, BEq, Repr

/--
Base quantificational force (when interpretable).
-/
inductive BaseForce where
  | existential   -- ∃ (any, some)
  | universal     -- ∀ (every)
  | degree        -- Degree/extent (at all, in the least)
  | temporal      -- Time reference (ever, yet)
  | manner        -- Manner/way (whatsoever)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Polarity Item Entry
-- ============================================================================

/--
A lexical entry for a polarity-sensitive item.

Theory-neutral: captures distributional facts without committing
to a particular analysis (exhaustification, domain widening, etc.).
-/
structure PolarityItemEntry where
  /-- Surface form -/
  form : String
  /-- Type of polarity sensitivity -/
  polarityType : PolarityType
  /-- Base quantificational/semantic force -/
  baseForce : BaseForce
  /-- Contexts where licensed (empty = needs positive) -/
  licensingContexts : List LicensingContext
  /-- Minimum DE strength required (for NPIs) -/
  minStrength : DEStrength := .weak
  /-- Has obligatory domain alternatives? (for Chierchia analysis) -/
  obligatoryDomainAlts : Bool := false
  /-- Can be rescued by modals? -/
  modalRescue : Bool := false
  /-- Notes -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- The Polarity Item Lexicon
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Weak NPIs
-- ----------------------------------------------------------------------------

/-- "any" - the prototypical NPI/FCI -/
def any : PolarityItemEntry :=
  { form := "any"
  , polarityType := .npi_fci
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .nobody, .conditional_ant, .question
      , .modal_possibility, .modal_necessity, .imperative, .generic ]
  , minStrength := .weak
  , obligatoryDomainAlts := true  -- Key to Chierchia's analysis
  , modalRescue := true
  , notes := "Dual NPI/FCI; obligatory domain alternatives yield universal-like FC"
  }

/-- "ever" - temporal NPI -/
def ever : PolarityItemEntry :=
  { form := "ever"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts :=
      [ .negation, .nobody, .conditional_ant, .question
      , .superlative, .comparative ]
  , minStrength := .weak
  , notes := "Temporal NPI; also in superlatives ('best ever')"
  }

/-- "yet" - temporal NPI (different from "ever") -/
def yet : PolarityItemEntry :=
  { form := "yet"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation, .question]
  , minStrength := .weak
  , notes := "Restricted distribution; requires relevance to 'now'"
  }

/-- "anymore" - temporal NPI -/
def anymore : PolarityItemEntry :=
  { form := "anymore"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , minStrength := .weak
  , notes := "Very restricted; mainly with negation"
  }

/-- "at all" - degree NPI -/
def atAll : PolarityItemEntry :=
  { form := "at all"
  , polarityType := .npiWeak
  , baseForce := .degree
  , licensingContexts :=
      [.negation, .nobody, .conditional_ant, .question]
  , minStrength := .weak
  , notes := "Degree emphasis; 'Did you sleep at all?'"
  }

/-- "in the least" - degree NPI -/
def inTheLeast : PolarityItemEntry :=
  { form := "in the least"
  , polarityType := .npiWeak
  , baseForce := .degree
  , licensingContexts := [.negation, .question]
  , minStrength := .weak
  , notes := "Formal register"
  }

/-- "a single" - emphatic existential NPI -/
def aSingle : PolarityItemEntry :=
  { form := "a single"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .without_clause]
  , minStrength := .weak
  , notes := "'I didn't see a single person'"
  }

/-- "whatsoever" - emphatic NPI (post-nominal) -/
def whatsoever : PolarityItemEntry :=
  { form := "whatsoever"
  , polarityType := .npiWeak
  , baseForce := .manner
  , licensingContexts := [.negation, .nobody]
  , minStrength := .weak
  , notes := "Post-nominal: 'no reason whatsoever'"
  }

-- ----------------------------------------------------------------------------
-- Strong NPIs (require anti-additive)
-- ----------------------------------------------------------------------------

/-- "lift a finger" - idiomatic strong NPI -/
def liftAFinger : PolarityItemEntry :=
  { form := "lift a finger"
  , polarityType := .npiStrong
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .without_clause]
  , minStrength := .antiAdditive
  , notes := "Idiomatic; requires anti-additive (*few people lifted a finger)"
  }

/-- "budge an inch" - idiomatic strong NPI -/
def budgeAnInch : PolarityItemEntry :=
  { form := "budge an inch"
  , polarityType := .npiStrong
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody, .without_clause]
  , minStrength := .antiAdditive
  , notes := "Idiomatic strong NPI"
  }

/-- "in years" - temporal strong NPI -/
def inYears : PolarityItemEntry :=
  { form := "in years"
  , polarityType := .npiStrong
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody]
  , minStrength := .antiAdditive
  , notes := "'I haven't seen him in years' (*Few people have seen him in years)"
  }

/-- "until" - temporal strong NPI (in some analyses) -/
def until_ : PolarityItemEntry :=
  { form := "until"
  , polarityType := .npiStrong
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , minStrength := .antiAdditive
  , notes := "Durative 'until' is NPI: 'didn't leave until 5'"
  }

-- ----------------------------------------------------------------------------
-- Free Choice Items
-- ----------------------------------------------------------------------------

/-- "whatever" - free relative FCI -/
def whatever : PolarityItemEntry :=
  { form := "whatever"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modal_possibility, .modal_necessity, .imperative, .generic, .free_relative]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "Free relative; 'Read whatever you want'"
  }

/-- "whoever" - free relative FCI -/
def whoever : PolarityItemEntry :=
  { form := "whoever"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modal_possibility, .modal_necessity, .imperative, .generic, .free_relative]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "Free relative; 'Invite whoever you like'"
  }

/-- "whichever" - free relative FCI -/
def whichever : PolarityItemEntry :=
  { form := "whichever"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modal_possibility, .modal_necessity, .imperative, .generic, .free_relative]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "Free relative with restriction; 'whichever book you prefer'"
  }

-- ----------------------------------------------------------------------------
-- Positive Polarity Items (blocked in DE)
-- ----------------------------------------------------------------------------

/-- "some" (stressed) - PPI reading -/
def some_ppi : PolarityItemEntry :=
  { form := "some (stressed)"
  , polarityType := .ppi
  , baseForce := .existential
  , licensingContexts := []  -- Empty = requires positive
  , notes := "Stressed 'some' is PPI: '*I didn't see SOME students'"
  }

/-- "already" - temporal PPI -/
def already : PolarityItemEntry :=
  { form := "already"
  , polarityType := .ppi
  , baseForce := .temporal
  , licensingContexts := []
  , notes := "PPI: '*I didn't already finish' (on temporal reading)"
  }

/-- "somewhat" - degree PPI -/
def somewhat : PolarityItemEntry :=
  { form := "somewhat"
  , polarityType := .ppi
  , baseForce := .degree
  , licensingContexts := []
  , notes := "PPI: '*I'm not somewhat tired'"
  }

/-- "rather" - degree PPI -/
def rather : PolarityItemEntry :=
  { form := "rather"
  , polarityType := .ppi
  , baseForce := .degree
  , licensingContexts := []
  , notes := "PPI (in degree sense): '*I don't rather like it'"
  }

-- ============================================================================
-- Lexicon Access
-- ============================================================================

/-- All weak NPIs -/
def weakNPIs : List PolarityItemEntry :=
  [any, ever, yet, anymore, atAll, inTheLeast, aSingle, whatsoever]

/-- All strong NPIs -/
def strongNPIs : List PolarityItemEntry :=
  [liftAFinger, budgeAnInch, inYears, until_]

/-- All NPIs (weak + strong) -/
def allNPIs : List PolarityItemEntry := weakNPIs ++ strongNPIs

/-- All FCIs -/
def allFCIs : List PolarityItemEntry :=
  [any, whatever, whoever, whichever]

/-- All PPIs -/
def allPPIs : List PolarityItemEntry :=
  [some_ppi, already, somewhat, rather]

/-- All polarity items -/
def allPolarityItems : List PolarityItemEntry :=
  weakNPIs ++ strongNPIs ++ [whatever, whoever, whichever] ++ allPPIs

/-- Lookup by form -/
def lookup (form : String) : Option PolarityItemEntry :=
  allPolarityItems.find? fun p => p.form == form

-- ============================================================================
-- Licensing Predicates
-- ============================================================================

/--
Check if a context licenses a polarity item.
-/
def isLicensedIn (item : PolarityItemEntry) (ctx : LicensingContext) : Bool :=
  item.licensingContexts.contains ctx &&
  ctx.strength.ctorIdx >= item.minStrength.ctorIdx

/--
Check if an item is an NPI (weak or strong).
-/
def PolarityItemEntry.isNPI (p : PolarityItemEntry) : Bool :=
  match p.polarityType with
  | .npiWeak | .npiStrong | .npi_fci => true
  | _ => false

/--
Check if an item is an FCI.
-/
def PolarityItemEntry.isFCI (p : PolarityItemEntry) : Bool :=
  match p.polarityType with
  | .fci | .npi_fci => true
  | _ => false

/--
Check if an item is a PPI.
-/
def PolarityItemEntry.isPPI (p : PolarityItemEntry) : Bool :=
  p.polarityType == .ppi

-- ============================================================================
-- Verification
-- ============================================================================

-- "any" is both NPI and FCI
#guard any.isNPI
#guard any.isFCI

-- "ever" is NPI but not FCI
#guard ever.isNPI
#guard !ever.isFCI

-- "whatever" is FCI but not (plain) NPI
#guard whatever.isFCI
#guard whatever.polarityType == .fci

-- Strong NPIs require anti-additive
#guard liftAFinger.minStrength == .antiAdditive

-- PPIs have empty licensing contexts
#guard already.licensingContexts.isEmpty

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Types
- `LicensingContext`: Contexts that license polarity items
- `DEStrength`: weak < anti-additive < anti-morphic
- `PolarityType`: npiWeak, npiStrong, fci, npi_fci, ppi
- `BaseForce`: existential, universal, degree, temporal, manner

### Lexical Entries
- `PolarityItemEntry`: Theory-neutral polarity item representation
- `any`, `ever`, `yet`, `anymore`: Weak NPIs
- `liftAFinger`, `budgeAnInch`, `inYears`: Strong NPIs
- `whatever`, `whoever`, `whichever`: FCIs
- `some_ppi`, `already`, `somewhat`: PPIs

### Key Properties of "any"
- `polarityType = .npi_fci` (dual use)
- `obligatoryDomainAlts = true` (key to Chierchia analysis)
- `modalRescue = true` (FC reading under modals)
- Licensed in: negation, questions, conditionals, modals, generics

### Lexicon Access
- `weakNPIs`, `strongNPIs`, `allNPIs`
- `allFCIs`, `allPPIs`, `allPolarityItems`
- `lookup`: Find by form
- `isLicensedIn`: Check licensing

### References
- Ladusaw (1979). Polarity sensitivity as inherent scope relations.
- Kadmon & Landman (1993). Any.
- Chierchia (2013). Logic in Grammar.
-/

end Fragments.English.PolarityItems
