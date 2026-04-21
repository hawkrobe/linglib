import Linglib.Phenomena.Polarity.Typology
import Linglib.Core.Lexical.PolarityItem
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Fragments.German.PolarityItems
import Linglib.Theories.Semantics.Exhaustification.FreeChoice
import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
import Linglib.Theories.Semantics.Exhaustification.Operators.Antiexhaustive
import Linglib.Phenomena.Polarity.Studies.AlonsoOvalleMoghiseh2025

/-!
# Chierchia 2006: Domain Widening and the PSI Typology
@cite{chierchia-2006} @cite{chierchia-2013} @cite{fox-2007} @cite{bar-lev-fox-2020}
@cite{haspelmath-1997} @cite{kadmon-landman-1993} @cite{alonso-ovalle-moghiseh-2025}

Formalizes the lasting contributions of @cite{chierchia-2006} "Broaden Your Views:
Implicatures of Domain Widening and the 'Logicality' of Language."

## What survived to 2026 consensus

The paper's central contribution is the **parametric decomposition** of
polarity-sensitive items (PSIs) along two dimensions:

1. **Domain alternative grain**: MAX (large subdomains only, even-like) vs
   MIN (all subdomains including singletons, antiexhaustive)
2. **Strengthening requirement**: whether exhaustification must yield
   *proper* strengthening (result strictly stronger than plain meaning)

The specific operators (O/E/O⁻, σ/σ̃) have been superseded by Innocent
Exclusion + Innocent Inclusion (@cite{fox-2007}, @cite{bar-lev-fox-2020}),
but the parametric space endures as the standard cross-linguistic PSI
classification.

## What was superseded

- **O/E/O⁻ enrichment operators** → replaced by IE + II
- **σ/σ̃ as LF operators with feature checking** → replaced by
  obligatory exhaustification and closure properties
- **Recursive pragmatics as sole mechanism** → pluralistic consensus
  (grammatical exh + RSA + team semantics)

## Key result

Each PSI class maps to a **contiguous region** on @cite{haspelmath-1997}'s
implicational map, explaining *why* indefinite pronoun series cover
contiguous function ranges cross-linguistically.

## Theoretical engine

The mechanism behind PSI licensing is **domain widening reversal**
(@cite{kadmon-landman-1993}, proved in `Exhaustification.FreeChoice`):
widening strengthens in DE but weakens in UE. The PSI parameter space
refines this into D-MAX (even-like) vs D-MIN (antiexhaustive) enrichment.
-/

namespace Chierchia2006

open Phenomena.Polarity.Typology
open AlonsoOvalleMoghiseh2025 (FCIFlavor EFCIRescue)

-- ============================================================================
-- §1. The PSI Parameter Space
-- ============================================================================

/-- Domain alternative grain size.

    @cite{chierchia-2006} table (76)/(94):
    - `max`: Only large subdomains. Triggers even-like enrichment (E):
      the speaker chose the strongest alternative she has evidence for.
      Pure NPIs (*alcuno*, *mai*, *ever*).
    - `min`: All subdomains including singletons. Triggers antiexhaustive
      enrichment (O⁻ in 2006; IE+II in 2026): every subdomain must be
      satisfiable, yielding universal-like force.
      FCIs (*any*, *qualsiasi*, *irgendein*). -/
inductive DomainAltGrain where
  | max  -- Pure NPIs: large D-alternatives → even-like
  | min  -- FCIs: all D-alternatives → antiexhaustive
  deriving DecidableEq, Repr

/-- The PSI profile: the 2026-consensus distillation of
    @cite{chierchia-2006}'s parametric PSI typology.

    The original paper used σ (weak) vs σ̃ (presuppositional) for
    implicature freezing, and O/E/O⁻ for enrichment. These specific
    operators have been superseded by IE+II (@cite{bar-lev-fox-2020}),
    but the *parameters* they encode remain the standard way to
    classify PSIs cross-linguistically. -/
structure PSIProfile where
  /-- Domain alternative grain (MAX vs MIN) -/
  grain : DomainAltGrain
  /-- Whether domain alternatives are obligatorily active -/
  obligatoryDomainAlts : Bool
  /-- Whether exhaustification must yield proper strengthening
      (corresponds to @cite{chierchia-2006}'s presuppositional σ̃) -/
  requiresProperStrengthening : Bool
  /-- Whether scalar alternatives are also activated -/
  hasScalarAlts : Bool
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. The Five PSI Classes (table (94))
-- ============================================================================

/-- Pure NPIs: *alcuno* (Italian), *mai* (Italian), *ever* (English).
    D-MAX, obligatory, weak σ, no scalar. -/
def pureNPI : PSIProfile :=
  { grain := .max
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := false
  , hasScalarAlts := false }

/-- NPI/FCIs: English *any*.
    D-MIN, obligatory, weak σ, no scalar.
    NPI in DE (exhaustification vacuous), FCI under modals. -/
def npiFCI : PSIProfile :=
  { grain := .min
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := false
  , hasScalarAlts := false }

/-- Pure universal FCIs: Italian *qualsiasi/qualunque*.
    D-MIN, obligatory, presuppositional σ̃, no scalar.
    Positive polarity: proper strengthening fails in DE. -/
def pureFCI : PSIProfile :=
  { grain := .min
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := true
  , hasScalarAlts := false }

/-- Existential FCI (NPI/FCI): German *irgendein*.
    D-MIN, obligatory, weak σ, with scalar alts.
    Like *any* but with scalar implicatures; needs rescue mechanisms. -/
def efciNpiFci : PSIProfile :=
  { grain := .min
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := false
  , hasScalarAlts := true }

/-- Existential pure FCI: Italian *uno qualsiasi*.
    D-MIN, obligatory, presuppositional σ̃, with scalar alts. -/
def efciPureFci : PSIProfile :=
  { grain := .min
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := true
  , hasScalarAlts := true }

-- ============================================================================
-- §3. Predicted Haspelmath Functions
-- ============================================================================

/-!
## Connecting PSI Theory to Distributional Typology

Each PSI class predicts an **eligible region** on @cite{haspelmath-1997}'s
implicational map — the set of functions where items of that class can
appear. The eligible region is **derived** from the PSI parameters and the
monotonicity classification of Haspelmath functions (`isDE`, `isFC`),
not hardcoded.

The derivation:
- **No obligatory alts** (plain indefinites): No polarity sensitivity →
  eligible only where neither DE licensing nor FC licensing is required.
- **D-MAX, weak σ** (pure NPIs): Even-like enrichment (E) is informative
  only in DE contexts → filter to DE functions.
- **D-MAX, σ̃**: Contradictory — even-like enrichment requires DE, but σ̃'s
  proper strengthening fails in DE (`sigma_bold_fails_in_de`) → empty.
- **D-MIN, weak σ** (NPI/FCIs): In DE, exhaustification is vacuous → NPI;
  under modals, antiexhaustive → FC. Also usable in irrealis. Filter to
  DE ∪ FC ∪ irrealis.
- **D-MIN, σ̃** (pure FCIs): Proper strengthening fails in DE → filter to
  FC only.
-/

/-- The Haspelmath functions predicted by a PSI class.

    Derived from PSI parameters via the monotonicity classification of
    Haspelmath functions (`IndefiniteFunction.isDE`, `IndefiniteFunction.isFC`).
    Each branch filters `IndefiniteFunction.all` by the semantic property
    that the PSI class's enrichment mechanism targets. -/
def PSIProfile.predictedFunctions (p : PSIProfile) : List IndefiniteFunction :=
  IndefiniteFunction.all.filter (λ f =>
    if !p.obligatoryDomainAlts then
      -- Plain indefinites: no polarity sensitivity, no FC
      !f.isDE && !f.isFC
    else match p.grain, p.requiresProperStrengthening with
      -- D-MAX, weak σ: even-like enrichment informative only in DE
      | .max, false => f.isDE
      -- D-MAX, σ̃: contradictory (DE + proper strengthening = ⊥)
      | .max, true  => false
      -- D-MIN, weak σ: NPI in DE + FCI under modals + irrealis
      | .min, false => f.isDE || f.isFC || f == .irrealis
      -- D-MIN, σ̃: proper strengthening fails in DE → FC only
      | .min, true  => f.isFC)

-- ============================================================================
-- §4. Contiguity Theorems
-- ============================================================================

/-!
## Each PSI class maps to a contiguous Haspelmath region

This is the central bridge between @cite{chierchia-2006}'s exhaustification
theory and @cite{haspelmath-1997}'s typological generalization. It explains
*why* indefinite pronoun series cover contiguous function ranges: each
PSI class's eligible region is contiguous, and surface forms cover
contiguous subsets of their class's region.
-/

/-- Pure NPI region {question..directNeg} is contiguous. -/
theorem pureNPI_contiguous :
    isContiguous pureNPI.predictedFunctions = true := by decide

/-- NPI/FCI region {irrealis..freeChoice} is contiguous. -/
theorem npiFCI_contiguous :
    isContiguous npiFCI.predictedFunctions = true := by decide

/-- Pure FCI region {comparative, freeChoice} is contiguous. -/
theorem pureFCI_contiguous :
    isContiguous pureFCI.predictedFunctions = true := by decide

/-- EFCI NPI/FCI has same eligible region as NPI/FCI (scalar alts don't
    change distributional range, only add uniqueness readings). -/
theorem efciNpiFci_contiguous :
    isContiguous efciNpiFci.predictedFunctions = true := by decide

/-- EFCI pure FCI has same eligible region as pure FCI. -/
theorem efciPureFci_contiguous :
    isContiguous efciPureFci.predictedFunctions = true := by decide

/-- All five PSI classes have contiguous predicted function ranges. -/
theorem all_psi_classes_contiguous :
    [pureNPI, npiFCI, pureFCI, efciNpiFci, efciPureFci].all
      (λ p => isContiguous p.predictedFunctions) = true := by decide

/-- D-MAX + presuppositional is unattested: the combination of requiring
    DE contexts (D-MAX) and proper strengthening (σ̃) is contradictory,
    since DE contexts are exactly where strengthening fails. -/
theorem dMax_presuppositional_empty :
    ({ grain := .max, obligatoryDomainAlts := true,
       requiresProperStrengthening := true, hasScalarAlts := false
       : PSIProfile }).predictedFunctions = [] := rfl

-- ============================================================================
-- §5. Cross-Linguistic Verification (derived from Typology.lean)
-- ============================================================================

/-!
## Matching cross-linguistic data to PSI predictions

Each surface form's actual Haspelmath functions (from
@cite{haspelmath-1997}'s typological data in `Typology.lean`) should be
a subset of its PSI class's predicted (eligible) region.

**All function lists are derived from `Typology.lean` profiles** — not
hardcoded — so changes to the typological data will break exactly the
theorems they should.
-/

private def functionsSubset (actual predicted : List IndefiniteFunction) : Bool :=
  actual.all (λ f => predicted.contains f)

/-- Extract Haspelmath functions for a named series from a language profile. -/
private def seriesFunctions (profile : IndefinitePronounProfile) (form : String)
    : List IndefiniteFunction :=
  match profile.series.find? (λ s => s.form == form) with
  | some s => s.functions
  | none => []

-- Italian: nessuno = pure NPI
theorem italian_nessuno_matches :
    functionsSubset (seriesFunctions italian "nessuno")
      pureNPI.predictedFunctions = true := by decide

-- Italian: qualunque/qualsiasi = pure FCI
theorem italian_qualsiasi_matches :
    functionsSubset (seriesFunctions italian "qualunque/qualsiasi")
      pureFCI.predictedFunctions = true := by decide

-- Italian: qualcuno = plain indefinite
theorem italian_qualcuno_matches :
    functionsSubset (seriesFunctions italian "qualcuno")
      ({ grain := .max, obligatoryDomainAlts := false,
         requiresProperStrengthening := false, hasScalarAlts := false
         : PSIProfile }).predictedFunctions = true := by decide

-- English: any (NPI) ⊆ NPI/FCI eligible region
theorem english_anyNPI_matches :
    functionsSubset (seriesFunctions english "any- (NPI)")
      npiFCI.predictedFunctions = true := by decide

-- English: any (FC) ⊆ NPI/FCI eligible region
theorem english_anyFC_matches :
    functionsSubset (seriesFunctions english "any- (FC)")
      npiFCI.predictedFunctions = true := by decide

-- German: irgendwer ⊆ EFCI NPI/FCI eligible region
theorem german_irgendwer_matches :
    functionsSubset (seriesFunctions german "irgendwer")
      efciNpiFci.predictedFunctions = true := by decide

-- Mandarin: 谁 covers the full NPI/FCI eligible region
theorem mandarin_shei_matches :
    functionsSubset (seriesFunctions mandarin "shéi (谁, non-interrog.)")
      npiFCI.predictedFunctions = true := by decide

-- ============================================================================
-- §6. The qualsiasi/any Contrast Under Negation
-- ============================================================================

/-!
## Deriving the core empirical contrast

@cite{chierchia-2006}'s most striking prediction: Italian *qualsiasi*
and English *any* differ under negation.

- "I didn't see any student" — grammatical (NPI reading)
- "Non ho visto qualsiasi studente" — marginal, only rhetorical ¬∀

This follows from `requiresProperStrengthening`: *any* (weak σ) allows
vacuous exhaustification in DE; *qualsiasi* (presuppositional σ̃) requires
proper strengthening, which fails in DE since the exhaustified meaning
is not strictly stronger than the plain meaning.

The paper derives two LF representations for *any* under negation:
1. σ scopes above ¬ → freeze implicature, then negate → rhetorical reading
2. σ scopes below ¬ → negate, then check implicature → NPI reading
   (implicature is entailed by assertion, so it vanishes)

For *qualsiasi*, only option (1) is available: σ̃ requires proper
strengthening, which option (2) cannot deliver (the implicature is
vacuous in DE). This is formalized as the `requiresProperStrengthening`
parameter blocking DE eligibility.
-/

/-- Every DE Haspelmath function is in the NPI/FCI eligible region.
    D-MIN + weak σ: exhaustification is vacuous in DE (NPI reading). -/
theorem npiFCI_eligible_in_all_de :
    (IndefiniteFunction.all.filter (·.isDE)).all
      (npiFCI.predictedFunctions.contains ·) = true := by decide

/-- No DE Haspelmath function is in the pure FCI eligible region.
    D-MIN + σ̃: proper strengthening fails in DE (`sigma_bold_fails_in_de`). -/
theorem pureFCI_not_eligible_in_any_de :
    (IndefiniteFunction.all.filter (·.isDE)).all
      (λ f => !pureFCI.predictedFunctions.contains f) = true := by decide

/-- Every DE function is in the pure NPI eligible region.
    D-MAX + weak σ: even-like enrichment is informative in DE. -/
theorem pureNPI_eligible_in_all_de :
    (IndefiniteFunction.all.filter (·.isDE)).all
      (pureNPI.predictedFunctions.contains ·) = true := by decide

/-- No FC function is in the pure NPI eligible region.
    D-MAX items lack antiexhaustive enrichment. -/
theorem pureNPI_not_eligible_in_fc :
    (IndefiniteFunction.all.filter (·.isFC)).all
      (λ f => !pureNPI.predictedFunctions.contains f) = true := by decide

/-- The *qualsiasi*/*any* contrast: among D-MIN items, every DE function
    is included by weak σ (*any*) and excluded by σ̃ (*qualsiasi*). -/
theorem dMin_sigma_determines_de :
    (IndefiniteFunction.all.filter (·.isDE)).all
      (λ f => npiFCI.predictedFunctions.contains f &&
              !pureFCI.predictedFunctions.contains f) = true := by decide

-- ============================================================================
-- §7. Bridge to EFCI Theory
-- ============================================================================

/-!
## Connection to @cite{alonso-ovalle-moghiseh-2025}

PSI profiles predict which EFCI rescue mechanism is available:
- Items with `hasScalarAlts = true` activate both scalar and domain
  alternatives, creating the EFCI contradiction.
- `requiresProperStrengthening` constrains rescue: presuppositional σ̃
  limits to partial exhaustification (proper strengthening preserved).
-/

/-- Map PSI profiles to EFCI rescue type (none if not an EFCI). -/
def PSIProfile.toEFCIRescue (p : PSIProfile) : Option EFCIRescue :=
  if !p.hasScalarAlts then none
  else if p.requiresProperStrengthening then some .partialExh
  else some .both

/-- Map PSI profiles to FCI flavor (none if not an FCI).
    Only D-MIN items are FCIs — D-MAX items are pure NPIs. -/
def PSIProfile.toFCIFlavor (p : PSIProfile) : Option FCIFlavor :=
  if !p.obligatoryDomainAlts then none
  else match p.grain with
    | .max => none  -- D-MAX = pure NPI, not an FCI
    | .min => if p.hasScalarAlts then some .existential else some .universal

-- *irgendein* = existential FCI
theorem irgendein_is_existential :
    efciNpiFci.toFCIFlavor = some .existential := rfl

-- *any* = universal FCI
theorem any_is_universal :
    npiFCI.toFCIFlavor = some .universal := rfl

-- *qualsiasi* = universal FCI
theorem qualsiasi_is_universal :
    pureFCI.toFCIFlavor = some .universal := rfl

-- Pure NPIs are NOT FCIs (D-MAX → not an FCI)
theorem pureNPI_not_fci :
    pureNPI.toFCIFlavor = none := rfl

-- *irgendein* allows both rescue mechanisms
theorem irgendein_rescue_both :
    efciNpiFci.toEFCIRescue = some .both := rfl

-- Non-EFCI items don't need rescue
theorem pureNPI_no_rescue :
    pureNPI.toEFCIRescue = none := rfl

-- ============================================================================
-- §8. Fragment Bridges (PSIProfile → PolarityType)
-- ============================================================================

/-!
## Bridging PSI profiles to Fragment entries

`Core.Lexical.PolarityItem.PolarityType` is a 5-way distributional
classification. `PSIProfile` is a 4-parameter theoretical decomposition.
Each PSI class predicts exactly one `PolarityType`, and each Fragment
entry's `polarityType` should match its PSI profile's predicted type.
-/

open Core.Lexical.PolarityItem
open Fragments.English.PolarityItems (any ever)
open Fragments.Italian.PolarityItems
  (mai qualsiasi nessuno qualunque uno_qualsiasi alcuno)
open Fragments.German.PolarityItems (irgendein)

/-- Map a PSI profile to the expected PolarityType. -/
def PSIProfile.toPolarityType (p : PSIProfile) : PolarityType :=
  if !p.obligatoryDomainAlts then .ppi  -- no obligatory alts = plain indefinite/PPI
  else match p.grain, p.requiresProperStrengthening with
    | .max, false => .npiWeak    -- D-MAX, weak σ → pure NPI
    | .max, true  => .npiStrong  -- D-MAX, presuppositional → strong NPI (unattested)
    | .min, false => .npiFci    -- D-MIN, weak σ → NPI/FCI (any)
    | .min, true  => .fci        -- D-MIN, presuppositional σ̃ → pure FCI (qualsiasi)

-- Verify the mapping is correct for all five named classes
theorem pureNPI_polarityType : pureNPI.toPolarityType = .npiWeak := rfl
theorem npiFCI_polarityType : npiFCI.toPolarityType = .npiFci := rfl
theorem pureFCI_polarityType : pureFCI.toPolarityType = .fci := rfl
theorem efciNpiFci_polarityType : efciNpiFci.toPolarityType = .npiFci := rfl
theorem efciPureFci_polarityType : efciPureFci.toPolarityType = .fci := rfl

-- Fragment entries match their PSI profile's predicted PolarityType
theorem any_profile_consistent :
    any.polarityType = npiFCI.toPolarityType := rfl
theorem ever_profile_consistent :
    ever.polarityType = pureNPI.toPolarityType := rfl
theorem mai_profile_consistent :
    mai.polarityType = pureNPI.toPolarityType := rfl
theorem alcuno_profile_consistent :
    alcuno.polarityType = pureNPI.toPolarityType := rfl
theorem nessuno_profile_consistent :
    nessuno.polarityType = pureNPI.toPolarityType := rfl
theorem qualsiasi_profile_consistent :
    qualsiasi.polarityType = pureFCI.toPolarityType := rfl
theorem qualunque_profile_consistent :
    qualunque.polarityType = pureFCI.toPolarityType := rfl
theorem uno_qualsiasi_profile_consistent :
    uno_qualsiasi.polarityType = efciPureFci.toPolarityType := rfl
theorem irgendein_profile_consistent :
    irgendein.polarityType = efciNpiFci.toPolarityType := rfl

-- ============================================================================
-- §10. Exhaustification Theory: σ̃, SI Vacuity, and O⁻
-- ============================================================================

/-!
## Exercising the Exhaustification theory layer

This section connects @cite{chierchia-2006}'s PSI typology to the formal
results in `Exhaustification.FreeChoice` and `Exhaustification.Operators`.

### σ̃: Presuppositional implicature freezing (§3.3, §5.3)

σ "freezes" the implicature; σ̃ adds a **presupposition** that the frozen
meaning is **strictly stronger** than the plain meaning (definition (72)).
`sigma_bold_fails_in_de` delegates to `entailment_reversal_in_de`.

### SI vacuity in DE (§4.1)

D-MAX (even-like) enrichment is an SI. SIs are vacuous in DE
(`si_vacuous_in_de`), explaining why pure NPIs are confined to DE.

### O⁻ yields universal force (§5.1)

Antiexhaustive enrichment of ∃x∈D.P(x) with D-MIN alternatives gives
∀a∈D. P(a) (`antiexh_yields_universal`). This is the "birth of universal
readings" behind FCI universal force.
-/

section SigmaOperators

variable {World : Type*}

open Exhaustification.FreeChoice (entailment_reversal_in_de si_vacuous_in_de)
open Exhaustification (oMinus antiexh_yields_universal)

/-- σ̃'s presupposition: the enriched meaning is **strictly stronger**
    than the plain meaning. @cite{chierchia-2006} definition (72).

    This must hold for σ̃ to be defined (felicitous). Items selecting σ̃
    (*qualsiasi*, *qualunque*) require proper strengthening; items selecting
    plain σ (*any*, *ever*) don't. -/
def sigmaBoldDefined (plain enriched : World → Prop) : Prop :=
  (∀ w, enriched w → plain w) ∧ ¬(∀ w, plain w → enriched w)

/-- **σ̃'s presupposition fails in DE contexts.**

    @cite{chierchia-2006} §5.3: This is the formal content of the
    *qualsiasi*/*any* contrast. If enrichment properly strengthens at the
    base level (enriched ⊂ plain), then embedding in a DE context
    *reverses* the entailment: C(plain) ⊆ C(enriched), making the
    enriched meaning under C strictly WEAKER, not stronger.

    Delegates to `Exhaustification.FreeChoice.entailment_reversal_in_de`:
    the DE reversal gives C(plain) ⊆ C(enriched), which contradicts σ̃'s
    requirement that C(enriched) be strictly stronger than C(plain). -/
theorem sigma_bold_fails_in_de
    (C : (World → Prop) → (World → Prop))
    (hDE : ∀ (p q : World → Prop), (∀ w, p w → q w) → (∀ w, C q w → C p w))
    (plain enriched : World → Prop)
    (h_stronger : ∀ w, enriched w → plain w) :
    ¬sigmaBoldDefined (C plain) (C enriched) :=
  fun ⟨_, hnotrev⟩ =>
    hnotrev (entailment_reversal_in_de C hDE plain enriched h_stronger)

/-- **SI vacuity in DE blocks D-MAX enrichment in UE.**

    @cite{chierchia-2006} §4.1: D-MAX items (pure NPIs) trigger
    even-like (E) enrichment, which is an SI. SIs are vacuous in DE
    (`si_vacuous_in_de`), so E enrichment is informative only in
    non-DE contexts — but D-MAX items *require* DE. This is why
    pure NPIs are confined to DE contexts.

    Instantiates `Exhaustification.FreeChoice.si_vacuous_in_de`. -/
theorem dMax_enrichment_vacuous_in_de
    (C : (World → Prop) → (World → Prop))
    (hDE : ∀ (p q : World → Prop), (∀ w, p w → q w) → (∀ w, C q w → C p w))
    (weak strong : World → Prop) (h_ent : ∀ w, strong w → weak w) :
    ∀ w, ¬(C weak w ∧ ¬C strong w) :=
  si_vacuous_in_de C hDE weak strong h_ent

/-- **O⁻ yields universal force from existential base (§5.1).**

    D-MIN items (FCIs) activate all subdomain alternatives. When
    antiexhaustive enrichment (O⁻) is applied to ∃x∈D.P(x) with
    D-MIN alternatives, the result entails ∀a∈D. P(a).

    This is the "birth of universal readings" — re-exported from
    `Exhaustification.antiexh_yields_universal`. -/
theorem fci_universal_from_oMinus
    {Entity : Type*}
    (D : List Entity) (P : Entity → World → Prop) (w : World)
    (h : oMinus (Exhaustification.dMinAlts D P) (Exhaustification.existsIn D P) w) :
    ∀ a ∈ D, P a w :=
  antiexh_yields_universal D P w h

end SigmaOperators

-- ============================================================================
-- §11. Italian FCI Empirical Data
-- ============================================================================

/-!
## Italian FCI judgment data from @cite{chierchia-2006} §2

These observations are the core empirical motivations:

1. **Two FCI constructions**: [qualsiasi/qualunque N] (universal FCI) vs
   [un N qualsiasi/qualunque] (existential FCI)
2. **Quantificational force contrast**: universal FCI → ∀; existential FCI → ∃
3. **Subtrigging**: bare universal FCIs are marginal in episodic contexts;
   adding a relative clause modifier restores grammaticality
4. **Negation scope**: universal FCIs under negation yield only ¬∀
   (rhetorical reading), not NPI ¬∃
-/

/-- Grammaticality judgment for Italian FCI constructions. -/
inductive Judgment where
  | grammatical     -- fully acceptable
  | marginal        -- ? or ?? — degraded but parseable
  | ungrammatical   -- * — not acceptable
  deriving DecidableEq, Repr

/-- Quantificational force of the FCI reading. -/
inductive QForce where
  | universal    -- ∀ reading
  | existential  -- ∃ reading
  | ambiguous    -- both readings available
  deriving DecidableEq, Repr

/-- FCI construction type: [qualsiasi N] vs [un N qualsiasi]. -/
inductive FCIType where
  | universal    -- [qualsiasi/qualunque N]: universal force
  | existential  -- [un N qualsiasi/qualunque]: existential force
  deriving DecidableEq, Repr

/-- Embedding context for FCI observations. -/
inductive FCIContext where
  | future              -- future tense (10a-b)
  | imperative          -- imperative mood (10c-d)
  | episodic_bare       -- bare episodic, no modifier (11a, 11c)
  | episodic_subtrigged -- episodic + relative clause (11b, 11d)
  | negation_bare       -- under negation, no modifier (12/73a)
  | negation_subtrigged -- under negation + relative clause (73b)
  deriving DecidableEq, Repr

/-- An Italian FCI observation from @cite{chierchia-2006} §2. -/
structure FCIObservation where
  /-- The sentence (schematic) -/
  sentence : String
  /-- Example number in the paper -/
  exampleNum : String
  /-- FCI construction type -/
  fciType : FCIType
  /-- Embedding context -/
  context : FCIContext
  /-- Available quantificational force -/
  force : QForce
  /-- Grammaticality judgment -/
  judgment : Judgment
  deriving Repr

-- §2 data: universal vs existential FCI contrast

/-- (10a): "Domani interrogherò qualsiasi studente" (future, universal FCI)
    — Both ∀ and ∃ readings available. -/
def obs_10a : FCIObservation :=
  { sentence := "Domani interrogherò qualsiasi studente"
  , exampleNum := "(10a)"
  , fciType := .universal
  , context := .future
  , force := .ambiguous
  , judgment := .grammatical }

/-- (10b): "Domani interrogherò uno studente qualsiasi" (future, existential FCI)
    — Only ∃ reading. -/
def obs_10b : FCIObservation :=
  { sentence := "Domani interrogherò uno studente qualsiasi"
  , exampleNum := "(10b)"
  , fciType := .existential
  , context := .future
  , force := .existential
  , judgment := .grammatical }

/-- (10c): "Prendi qualunque dolce" (imperative, universal FCI)
    — Both ∀ and ∃ readings available. -/
def obs_10c : FCIObservation :=
  { sentence := "Prendi qualunque dolce"
  , exampleNum := "(10c)"
  , fciType := .universal
  , context := .imperative
  , force := .ambiguous
  , judgment := .grammatical }

/-- (10d): "Prendi un dolce qualunque" (imperative, existential FCI)
    — Only ∃ reading. -/
def obs_10d : FCIObservation :=
  { sentence := "Prendi un dolce qualunque"
  , exampleNum := "(10d)"
  , fciType := .existential
  , context := .imperative
  , force := .existential
  , judgment := .grammatical }

-- §2 data: subtrigging

/-- (11a): "Ieri ho parlato con un qualsiasi filosofo" (bare episodic, EFCI)
    — Marginal without modifier. -/
def obs_11a : FCIObservation :=
  { sentence := "Ieri ho parlato con un qualsiasi filosofo"
  , exampleNum := "(11a)"
  , fciType := .existential
  , context := .episodic_bare
  , force := .existential
  , judgment := .marginal }

/-- (11b): "Ieri ho parlato con un qualsiasi filosofo che fosse interessato"
    — Marginal; the paper notes RC "if anything, makes things worse" for
    existential FCIs. Subtrigging does not rescue EFCIs. -/
def obs_11b : FCIObservation :=
  { sentence := "Ieri ho parlato con un qualsiasi filosofo che fosse interessato"
  , exampleNum := "(11b)"
  , fciType := .existential
  , context := .episodic_subtrigged
  , force := .existential
  , judgment := .marginal }

/-- (11c): "Ieri ho parlato con qualsiasi filosofo" (bare episodic, universal FCI)
    — Marginal without modifier. -/
def obs_11c : FCIObservation :=
  { sentence := "Ieri ho parlato con qualsiasi filosofo"
  , exampleNum := "(11c)"
  , fciType := .universal
  , context := .episodic_bare
  , force := .universal
  , judgment := .marginal }

/-- (11d): "Ieri ho parlato con qualsiasi filosofo che fosse interessato"
    — Fully grammatical: subtrigging rescues universal FCIs. -/
def obs_11d : FCIObservation :=
  { sentence := "Ieri ho parlato con qualsiasi filosofo che fosse interessato"
  , exampleNum := "(11d)"
  , fciType := .universal
  , context := .episodic_subtrigged
  , force := .universal
  , judgment := .grammatical }

-- §5.3 / §2: negation scope

/-- (12)/(73a): "Non leggerò qualunque libro" (negation + bare universal FCI)
    — Only ¬∀ (rhetorical) reading; NOT the NPI ¬∃ reading. -/
def obs_12 : FCIObservation :=
  { sentence := "Non leggerò qualunque libro"
  , exampleNum := "(12)/(73a)"
  , fciType := .universal
  , context := .negation_bare
  , force := .universal
  , judgment := .grammatical }

/-- (73b): "Non leggerò qualunque libro che mi consiglierà Gianni"
    — With RC under negation: ∀¬ or ¬∃ readings become available. -/
def obs_73b : FCIObservation :=
  { sentence := "Non leggerò qualunque libro che mi consiglierà Gianni"
  , exampleNum := "(73b)"
  , fciType := .universal
  , context := .negation_subtrigged
  , force := .ambiguous
  , judgment := .grammatical }

-- Verification theorems: the judgment data encodes the key contrasts

/-- Subtrigging contrast: bare universal FCI is marginal in episodic;
    subtrigged universal FCI is grammatical. -/
theorem subtrigging_rescues_universal :
    obs_11c.judgment = .marginal ∧ obs_11d.judgment = .grammatical := ⟨rfl, rfl⟩

/-- Subtrigging does NOT rescue existential FCIs in episodic contexts. -/
theorem subtrigging_no_help_existential :
    obs_11a.judgment = .marginal ∧ obs_11b.judgment = .marginal := ⟨rfl, rfl⟩

/-- Universal FCIs always admit ∀ (and sometimes ∃): force is ambiguous. -/
theorem universal_fci_ambiguous_force :
    [obs_10a, obs_10c].all (·.force == .ambiguous) = true := by decide

/-- Existential FCIs have ∃ force only. -/
theorem existential_fci_existential_force :
    [obs_10b, obs_10d].all (·.force == .existential) = true := by decide

/-- Under negation, bare universal FCI yields only ¬∀ (rhetorical), not NPI ¬∃.
    This is the *qualsiasi*/*any* contrast: *qualsiasi* under negation ≠ NPI. -/
theorem negation_rhetorical_only :
    obs_12.force = .universal := rfl

end Chierchia2006
