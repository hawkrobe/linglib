/-!
# Polarity Item Infrastructure
@cite{lahiri-1998} @cite{lee-horn-1994} @cite{haspelmath-1997} @cite{chierchia-2006}
@cite{israel-1996} @cite{israel-2011} @cite{schwab-2022}

Language-neutral types for polarity-sensitive items, shared across all
language fragments. These capture cross-linguistic generalizations about
polarity types, licensing contexts, scalar direction, morphological
composition, and alternative types.
-/

namespace Core.Lexical.PolarityItem

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
  | adversative       -- "sorry", "surprised", "regret" (factive + DE)
  | since_temporal    -- "it's been five years since" (Iatridou)
  | free_relative     -- Free relatives: "whatever", "whoever"
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Scalar Direction (@cite{israel-1996}, 2011; @cite{schwab-2022})
-- ============================================================================

/-- Scalar direction: does this item strengthen or attenuate the assertion?
    Orthogonal to PolarityType (weak vs strong DE requirement).

    - **Strengthening** items (ever, any, jemals) make the assertion stronger
      than its scalar alternatives (Israel's "emphatic" polarity items).
    - **Attenuating** items (all that, so recht, long) make the assertion weaker
      than its scalar alternatives (Israel's "understating" polarity items).
    - **NonScalar** items (lift a finger) are idiomatic, not scalar.

    @cite{israel-1996}. Polarity sensitivity as lexical semantics. L&P 19(6).
    @cite{israel-2011}. The Grammar of Polarity. CUP.
    @cite{schwab-2022}. Lexical variation in NPI illusions. -/
inductive ScalarDirection where
  | strengthening  -- ever, any, jemals: assertion stronger than alternatives
  | attenuating    -- all that, so recht, long: assertion weaker than alternatives
  | nonScalar      -- lift a finger: idiomatic, not scalar
  | unknown        -- not yet verified for this item
  deriving DecidableEq, BEq, Repr

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
-- Morphological Composition (@cite{lahiri-1998}, @cite{lee-horn-1994})
-- ============================================================================

/-- Morphological composition of a polarity-sensitive item.
    @cite{lahiri-1998} shows Hindi NPIs are transparently `indefinite + even`.
    @cite{lee-horn-1994} document this pattern cross-linguistically. -/
inductive NPIMorphology where
  | indefPlusEven  -- indefinite + 'even' particle (Hindi bhii, Korean -do/-na)
  | indefPlusNeg   -- indefinite + negation (Hindi nahiiN, Italian n-words)
  | plain          -- morphologically simple (English 'any', 'ever')
  | idiomatic      -- frozen idiom ('lift a finger')
  deriving DecidableEq, BEq, Repr

/-- Type of alternatives introduced by the focused element.
    @cite{lahiri-1998} §8: *ek bhii* introduces cardinality alternatives,
    *koii bhii* introduces contextually salient property alternatives.
    @cite{chierchia-2006}: subdomain (D-)alternatives for domain widening. -/
inductive AlternativeType where
  | cardinality        -- {one, two, three, ...}: entailment-ordered
  | contextualProperty -- {P₁, P₂, ...}: contextually determined
  | domain             -- subdomain alternatives (Chierchia 2006 D-alternatives)
  | unspecified         -- not yet analyzed
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
  /-- Scalar direction: strengthening, attenuating, or non-scalar -/
  scalarDirection : ScalarDirection := .unknown
  /-- Morphological composition (@cite{lahiri-1998}) -/
  morphology : NPIMorphology := .plain
  /-- Type of alternatives introduced -/
  alternativeType : AlternativeType := .unspecified
  /-- Notes -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Predicates
-- ============================================================================

/--
Check if a context licenses a polarity item.

An item is licensed if the context is explicitly listed in `licensingContexts`.
-/
def isLicensedIn (item : PolarityItemEntry) (ctx : LicensingContext) : Bool :=
  item.licensingContexts.contains ctx

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

end Core.Lexical.PolarityItem
