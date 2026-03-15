/-!
# Polarity Item Infrastructure
@cite{lahiri-1998} @cite{lee-horn-1994} @cite{haspelmath-1997} @cite{chierchia-2006}
@cite{israel-1996} @cite{israel-2001} @cite{israel-2011} @cite{schwab-2022}

Language-neutral types for polarity-sensitive items, shared across all
language fragments. These capture cross-linguistic generalizations about
polarity types, licensing contexts, scalar direction, scalar value,
canonicity, likelihood effect, morphological composition, and alternative types.

## The Scalar Model of Polarity (@cite{israel-1996}, @cite{israel-2001})

Polarity items are characterized by two orthogonal scalar features:
- **ScalarValue** (high/low): where the item sits on its scale
- **ScalarDirection** (strengthening/attenuating): rhetorical force

These interact with **LikelihoodEffect** — whether the item's referent
facilitates or impedes the event — to predict **Canonicity**
(canonical vs inverted). See `Phenomena/Polarity/Studies/Israel2001.lean`.
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
-- Scalar Value (@cite{israel-2001} Figure 1)
-- ============================================================================

/-- Where the polarity item sits on its scale, relative to the scalar norm.

    @cite{israel-2001}: polarity items conventionally encode a fixed position
    on a scalar ordering. Emphatic NPIs typically denote LOW values
    (*a wink*, *an inch*), while emphatic PPIs typically denote HIGH values
    (*tons*, *utterly*). Inverted items reverse this pattern. -/
inductive ScalarValue where
  | high     -- denotes high scalar value (tons, utterly, wild horses)
  | low      -- denotes low scalar value (a wink, an inch, a pittance)
  | unknown  -- not yet classified
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Scalar Direction (@cite{israel-1996}, @cite{israel-2001}; @cite{schwab-2022})
-- ============================================================================

/-- Rhetorical force: does this item strengthen or attenuate the assertion?
    Orthogonal to both PolarityType and ScalarValue.

    - **Strengthening** items (ever, any, jemals) make the assertion stronger
      than its scalar alternatives (@cite{israel-2001}'s "emphatic" items).
    - **Attenuating** items (all that, so recht, long) make the assertion weaker
      than its scalar alternatives (@cite{israel-2001}'s "understating" items).
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
-- Canonicity (@cite{israel-2001} §3, Figure 3)
-- ============================================================================

/-- Whether a polarity item is canonical or inverted.

    **Canonical** items have the expected correlation between scalar value
    and polarity type:
    - Canonical emphatic NPIs denote LOW values (*a wink*, *an inch*)
    - Canonical emphatic PPIs denote HIGH values (*tons*, *utterly*)

    **Inverted** items reverse this:
    - Inverted emphatic NPIs denote HIGH values (*wild horses*, *all the tea in China*)
    - Inverted emphatic PPIs denote LOW values (*at the drop of a hat*, *for a pittance*)

    @cite{israel-2001} §3–4 shows inversion tracks propositional role:
    canonical items fill impeding roles (patient/theme); inverted items
    fill facilitating roles (stimulus/instrument/reward). -/
inductive Canonicity where
  | canonical  -- scalar value tracks polarity type in the default way
  | inverted   -- scalar value is opposite to what polarity type predicts
  | unknown    -- not yet classified
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Likelihood Effect (@cite{israel-2001} §4)
-- ============================================================================

/-- How increasing the scalar value of an item's referent affects the
    likelihood of the proposition being true.

    This is the key to @cite{israel-2001}'s resolution of the
    maximizer/minimizer puzzle:

    - **Facilitating** roles (agent, stimulus, instrument, reward):
      bigger/more → event more likely → scale is inverted
      (e.g., *wild horses* — more powerful force → more likely to move you)

    - **Impeding** roles (patient, theme, increment, resource/expense):
      bigger/more → event less likely → scale is canonical
      (e.g., *lift a finger* — more effort required → less likely to act)

    The pecuniary paradox dissolves: *a red cent* (NPI, resource = impeding)
    vs *for peanuts* (PPI, reward = facilitating) — same monetary domain,
    different propositional roles. -/
inductive LikelihoodEffect where
  | facilitating  -- bigger → event more likely (agent, stimulus, reward)
  | impeding      -- bigger → event less likely (patient, theme, expense)
  | unknown       -- not yet classified
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
  /-- Scalar value: high or low on the relevant scale (@cite{israel-2001}) -/
  scalarValue : ScalarValue := .unknown
  /-- Canonical or inverted (@cite{israel-2001} §3) -/
  canonicity : Canonicity := .unknown
  /-- Propositional role's likelihood effect (@cite{israel-2001} §4) -/
  likelihoodEffect : LikelihoodEffect := .unknown
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

/--
Israel's prediction: canonical/inverted is determined by likelihood effect.

Facilitating roles produce inverted items (high-value NPIs, low-value PPIs).
Impeding roles produce canonical items (low-value NPIs, high-value PPIs). -/
def predictCanonicity (le : LikelihoodEffect) (pt : PolarityType) (sv : ScalarValue) : Canonicity :=
  match le, pt, sv with
  -- Impeding + low NPI = canonical (a wink, an inch)
  | .impeding, .npiWeak,  .low | .impeding, .npiStrong, .low
  | .impeding, .npi_fci,  .low => .canonical
  -- Impeding + high PPI = canonical (tons, utterly)
  | .impeding, .ppi, .high => .canonical
  -- Facilitating + high NPI = inverted (wild horses, all the tea in China)
  | .facilitating, .npiWeak,  .high | .facilitating, .npiStrong, .high
  | .facilitating, .npi_fci,  .high => .inverted
  -- Facilitating + low PPI = inverted (for a pittance, in a jiffy)
  | .facilitating, .ppi, .low => .inverted
  -- Attenuating NPIs/PPIs follow the same logic
  | .impeding, .npiWeak,  .high | .impeding, .npiStrong, .high
  | .impeding, .npi_fci,  .high => .canonical
  | .impeding, .ppi, .low => .canonical
  | .facilitating, .npiWeak,  .low | .facilitating, .npiStrong, .low
  | .facilitating, .npi_fci,  .low => .inverted
  | .facilitating, .ppi, .high => .inverted
  | _, _, _ => .unknown

/-- Check if a polarity item's stated canonicity agrees with the prediction. -/
def PolarityItemEntry.canonicityConsistent (p : PolarityItemEntry) : Bool :=
  p.canonicity == .unknown ||
  p.likelihoodEffect == .unknown ||
  p.scalarValue == .unknown ||
  p.canonicity == predictCanonicity p.likelihoodEffect p.polarityType p.scalarValue

end Core.Lexical.PolarityItem
