import Linglib.Core.Logic.NaturalLogic

/-!
# Polarity Item Infrastructure
@cite{lahiri-1998} @cite{lee-horn-1994} @cite{haspelmath-1997} @cite{chierchia-2006}
@cite{israel-1996} @cite{israel-2001} @cite{israel-2011} @cite{schwab-2022}
@cite{ladusaw-1979} @cite{kadmon-landman-1993} @cite{zwarts-1998}

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
  | conditionalAntecedent   -- Antecedent of conditional
  | beforeClause     -- "before" clauses
  | withoutClause    -- "without" PPs
  | onlyFocus        -- Focus of "only"
  | question          -- Questions (for some NPIs)
  | comparativeNP     -- "taller than NP" — Boolean homomorphism (@cite{hoeksema-1983})
  | comparativeS      -- "taller than S is" — anti-additive (@cite{hoeksema-1983} Fact 5)
  | superlative       -- "the most", "the least"
  | tooTo            -- "too ADJ to VP"
  | modalPossibility -- Possibility modals (for FCIs)
  | modalNecessity   -- Necessity modals
  | imperative        -- Imperatives (for FCIs)
  | generic           -- Generic contexts (for FCIs)
  | adversative       -- "sorry", "surprised", "regret" (factive + DE)
  | sinceTemporal    -- "it's been five years since" (Iatridou)
  | freeRelative     -- Free relatives: "whatever", "whoever"
  | universalRestrictor -- Restrictor of universal: "everyone who saw anyone"
  | doubtVerb         -- DE attitude verbs: "I doubt anyone came"
  | denyVerb          -- Anti-additive attitude verbs: "She denied seeing anyone"
  deriving DecidableEq, Repr

-- ============================================================================
-- Licensing Mechanism (@cite{kadmon-landman-1993})
-- ============================================================================

/-- The mechanism by which a context licenses NPIs.

    @cite{kadmon-landman-1993} unify NPI licensing under domain widening +
    strengthening. Three categories cover the attested licensing contexts:

    - `byStrengthening` — DE contexts where widening strengthens the assertion.
      Covers @cite{ladusaw-1979}'s monotonicity-based licensing.
    - `byGenericIndefinite` — Non-DE contexts (modals, generics, free relatives)
      where *any* surfaces as the generic indefinite (FC any).
    - `byOtherMechanism` — entropy-based (questions), Strawson-DE
      (superlatives), or other contributions outside K&L's two-pronged proposal. -/
inductive LicensingMechanism where
  | byStrengthening
  | byGenericIndefinite
  | byOtherMechanism
  deriving DecidableEq, Repr

-- ============================================================================
-- Context Properties (single source of truth)
-- ============================================================================

/-- The bundle of theory-relevant facts about a licensing context.

    Every classification of `LicensingContext` (DE strength, K&L mechanism,
    canonical example, citation lineage) projects out of this single record.
    Per-paper classifiers (`Ladusaw1979.licensingStrength`,
    `KadmonLandman1993.klExplanation`) are derivations from `contextProperties`,
    not parallel stipulations. -/
structure ContextProperties where
  /-- Icard signature: locates the context in the natural-logic lattice. -/
  signature : Core.NaturalLogic.EntailmentSig
  /-- K&L mechanism: how this context licenses NPIs. -/
  mechanism : LicensingMechanism
  /-- A canonical English example. -/
  prototype : String
  /-- BibTeX keys for the works that established this classification. -/
  citations : List String
  deriving Repr

/-- Canonical map from licensing contexts to their theoretical properties.

    The signature follows @cite{ladusaw-1979} + @cite{zwarts-1998} +
    @cite{partee-westerstaahl-2007} (P&W Prop 13: every-restrictor is LAA).
    The mechanism follows @cite{kadmon-landman-1993}. -/
def contextProperties : LicensingContext → ContextProperties
  | .negation =>
      { signature := .antiAddMult, mechanism := .byStrengthening
      , prototype := "Mary didn't see anyone."
      , citations := ["ladusaw-1979", "kadmon-landman-1993", "zwarts-1998"] }
  | .nobody =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Nobody saw anyone."
      , citations := ["ladusaw-1979", "zwarts-1998"] }
  | .withoutClause =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "She left without saying anything."
      , citations := ["ladusaw-1979", "zwarts-1998"] }
  | .denyVerb =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "She denied seeing anyone."
      , citations := ["zwarts-1998"] }
  | .universalRestrictor =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Everyone who saw anyone was questioned."
      , citations := ["ladusaw-1979", "partee-westerstaahl-2007"] }
  | .few =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "Few students saw anyone."
      , citations := ["ladusaw-1979"] }
  | .atMost =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "At most three students saw anyone."
      , citations := ["ladusaw-1979"] }
  | .conditionalAntecedent =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "If anyone calls, take a message."
      , citations := ["ladusaw-1979", "kadmon-landman-1993"] }
  | .beforeClause =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "She left before anyone arrived."
      , citations := ["ladusaw-1979"] }
  | .onlyFocus =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "Only Mary saw anyone."
      , citations := ["horn-1996", "von-fintel-1999"] }
  | .tooTo =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "He was too tired to say anything."
      , citations := ["ladusaw-1979"] }
  | .comparativeNP =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Mary is taller than anyone in the class."
      , citations := ["ladusaw-1979", "hoeksema-1983"] }
  | .comparativeS =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Mary is taller than anyone is."
      , citations := ["ladusaw-1979", "hoeksema-1983"] }
  | .adversative =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "I'm sorry I said anything."
      , citations := ["kadmon-landman-1993"] }
  | .sinceTemporal =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "It's been five years since anyone visited."
      , citations := ["iatridou-1990"] }
  | .doubtVerb =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "I doubt anyone came."
      , citations := ["zwarts-1998"] }
  | .modalPossibility =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "You may take any cookie."
      , citations := ["kadmon-landman-1993", "dayal-1998"] }
  | .modalNecessity =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Anyone can solve this."
      , citations := ["dayal-1998"] }
  | .imperative =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Pick any card."
      , citations := ["kadmon-landman-1993"] }
  | .generic =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Any owl hunts mice."
      , citations := ["kadmon-landman-1993", "dayal-1998"] }
  | .freeRelative =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Pick whichever you like."
      , citations := ["dayal-1997"] }
  | .question =>
      { signature := .mono, mechanism := .byOtherMechanism
      , prototype := "Did anyone call?"
      , citations := ["van-rooy-2003"] }
  | .superlative =>
      { signature := .mono, mechanism := .byOtherMechanism
      , prototype := "The tallest student who saw anyone..."
      , citations := ["herdan-sharvit-2006"] }

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  | npiFci      -- Dual use: NPI in DE, FCI under modals (= "any")
  | ppi          -- Positive Polarity Item: blocked in DE
  deriving DecidableEq, Repr

/--
Base quantificational force (when interpretable).
-/
inductive BaseForce where
  | existential   -- ∃ (any, some)
  | universal     -- ∀ (every)
  | degree        -- Degree/extent (at all, in the least)
  | temporal      -- Time reference (ever, yet)
  | manner        -- Manner/way (whatsoever)
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

/-- Type of alternatives introduced by the focused element.
    @cite{lahiri-1998} §8: *ek bhii* introduces cardinality alternatives,
    *koii bhii* introduces contextually salient property alternatives.
    @cite{chierchia-2006}: subdomain (D-)alternatives for domain widening. -/
inductive AlternativeType where
  | cardinality        -- {one, two, three, ...}: entailment-ordered
  | contextualProperty -- {P₁, P₂, ...}: contextually determined
  | domain             -- subdomain alternatives (Chierchia 2006 D-alternatives)
  | unspecified         -- not yet analyzed
  deriving DecidableEq, Repr

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
abbrev isLicensedIn (item : PolarityItemEntry) (ctx : LicensingContext) : Prop :=
  ctx ∈ item.licensingContexts

/--
Check if an item is an NPI (weak or strong).
-/
abbrev PolarityItemEntry.isNPI (p : PolarityItemEntry) : Prop :=
  p.polarityType = .npiWeak ∨ p.polarityType = .npiStrong ∨ p.polarityType = .npiFci

/--
Check if an item is an FCI.
-/
abbrev PolarityItemEntry.isFCI (p : PolarityItemEntry) : Prop :=
  p.polarityType = .fci ∨ p.polarityType = .npiFci

/--
Check if an item is a PPI.
-/
abbrev PolarityItemEntry.isPPI (p : PolarityItemEntry) : Prop :=
  p.polarityType = .ppi

/--
Israel's prediction (@cite{israel-2001} §4): canonical/inverted is determined
solely by likelihood effect (propositional role).

- Impeding roles → canonical items
- Facilitating roles → inverted items

This holds for both NPIs and PPIs, regardless of scalar value. Scalar value
determines WHERE on the scale an item sits; likelihood effect determines
WHETHER the item is canonical or inverted. -/
def predictCanonicity (le : LikelihoodEffect) (pt : PolarityType) : Canonicity :=
  match le, pt with
  | _, .fci => .unknown  -- pure FCIs don't have canonicity
  | .impeding, _ => .canonical
  | .facilitating, _ => .inverted
  | .unknown, _ => .unknown

/-- Check if a polarity item's stated canonicity agrees with the prediction.
    Holds if canonicity or likelihood effect is unknown (insufficient data),
    or if the stated canonicity matches the prediction from likelihood effect. -/
abbrev PolarityItemEntry.canonicityConsistent (p : PolarityItemEntry) : Prop :=
  p.canonicity = .unknown ∨
  p.likelihoodEffect = .unknown ∨
  p.canonicity = predictCanonicity p.likelihoodEffect p.polarityType

end Core.Lexical.PolarityItem
