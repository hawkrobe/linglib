import Linglib.Phenomena.Polarity.Typology
import Linglib.Core.Lexical.PolarityItem
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Fragments.German.PolarityItems
import Linglib.Theories.Semantics.Exhaustification.FreeChoice
import Linglib.Theories.Semantics.Exhaustification.Operators
import Linglib.Phenomena.Polarity.Studies.AlonsoOvalleMoghiseh2025

/-!
# Chierchia 2006: Domain Widening and the PSI Typology
@cite{chierchia-2006} @cite{chierchia-2013} @cite{fox-2007} @cite{bar-lev-fox-2020}
@cite{haspelmath-1997} @cite{alonso-ovalle-moghiseh-2025}

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

namespace Phenomena.Polarity.Studies.Chierchia2006

open Phenomena.Polarity.Typology
open Phenomena.Polarity.Studies.AlonsoOvalleMoghiseh2025 (FCIFlavor EFCIRescue)

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2. The Five PSI Classes (table (94))
-- ============================================================================

/-- Pure NPIs: *alcuno* (Italian), *mai* (Italian), *ever* (English).
    D-MAX, obligatory, weak σ, no scalar. -/
def pureNPI : PSIProfile :=
  ⟨.max, true, false, false⟩

/-- NPI/FCIs: English *any*.
    D-MIN, obligatory, weak σ, no scalar.
    NPI in DE (exhaustification vacuous), FCI under modals. -/
def npiFCI : PSIProfile :=
  ⟨.min, true, false, false⟩

/-- Pure universal FCIs: Italian *qualsiasi/qualunque*.
    D-MIN, obligatory, presuppositional σ̃, no scalar.
    Positive polarity: proper strengthening fails in DE. -/
def pureFCI : PSIProfile :=
  ⟨.min, true, true, false⟩

/-- Existential FCI (NPI/FCI): German *irgendein*.
    D-MIN, obligatory, weak σ, with scalar alts.
    Like *any* but with scalar implicatures; needs rescue mechanisms. -/
def efciNpiFci : PSIProfile :=
  ⟨.min, true, false, true⟩

/-- Existential pure FCI: Italian *uno qualsiasi*.
    D-MIN, obligatory, presuppositional σ̃, with scalar alts. -/
def efciPureFci : PSIProfile :=
  ⟨.min, true, true, true⟩

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
    isContiguous pureNPI.predictedFunctions = true := by native_decide

/-- NPI/FCI region {irrealis..freeChoice} is contiguous. -/
theorem npiFCI_contiguous :
    isContiguous npiFCI.predictedFunctions = true := by native_decide

/-- Pure FCI region {comparative, freeChoice} is contiguous. -/
theorem pureFCI_contiguous :
    isContiguous pureFCI.predictedFunctions = true := by native_decide

/-- EFCI NPI/FCI has same eligible region as NPI/FCI (scalar alts don't
    change distributional range, only add uniqueness readings). -/
theorem efciNpiFci_contiguous :
    isContiguous efciNpiFci.predictedFunctions = true := by native_decide

/-- EFCI pure FCI has same eligible region as pure FCI. -/
theorem efciPureFci_contiguous :
    isContiguous efciPureFci.predictedFunctions = true := by native_decide

/-- All five PSI classes have contiguous predicted function ranges. -/
theorem all_psi_classes_contiguous :
    [pureNPI, npiFCI, pureFCI, efciNpiFci, efciPureFci].all
      (λ p => isContiguous p.predictedFunctions) = true := by native_decide

/-- D-MAX + presuppositional is unattested: the combination of requiring
    DE contexts (D-MAX) and proper strengthening (σ̃) is contradictory,
    since DE contexts are exactly where strengthening fails. -/
theorem dMax_presuppositional_empty :
    (PSIProfile.mk .max true true false).predictedFunctions = [] := rfl

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
      pureNPI.predictedFunctions = true := by native_decide

-- Italian: qualunque/qualsiasi = pure FCI
theorem italian_qualsiasi_matches :
    functionsSubset (seriesFunctions italian "qualunque/qualsiasi")
      pureFCI.predictedFunctions = true := by native_decide

-- Italian: qualcuno = plain indefinite
theorem italian_qualcuno_matches :
    functionsSubset (seriesFunctions italian "qualcuno")
      (PSIProfile.mk .max false false false).predictedFunctions = true := by native_decide

-- English: any (NPI) ⊆ NPI/FCI eligible region
theorem english_anyNPI_matches :
    functionsSubset (seriesFunctions english "any- (NPI)")
      npiFCI.predictedFunctions = true := by native_decide

-- English: any (FC) ⊆ NPI/FCI eligible region
theorem english_anyFC_matches :
    functionsSubset (seriesFunctions english "any- (FC)")
      npiFCI.predictedFunctions = true := by native_decide

-- German: irgendwer ⊆ EFCI NPI/FCI eligible region
theorem german_irgendwer_matches :
    functionsSubset (seriesFunctions german "irgendwer")
      efciNpiFci.predictedFunctions = true := by native_decide

-- Mandarin: 谁 covers the full NPI/FCI eligible region
theorem mandarin_shei_matches :
    functionsSubset (seriesFunctions mandarin "shéi (谁, non-interrog.)")
      npiFCI.predictedFunctions = true := by native_decide

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
      (npiFCI.predictedFunctions.contains ·) = true := by native_decide

/-- No DE Haspelmath function is in the pure FCI eligible region.
    D-MIN + σ̃: proper strengthening fails in DE (`sigma_bold_fails_in_de`). -/
theorem pureFCI_not_eligible_in_any_de :
    (IndefiniteFunction.all.filter (·.isDE)).all
      (λ f => !pureFCI.predictedFunctions.contains f) = true := by native_decide

/-- Every DE function is in the pure NPI eligible region.
    D-MAX + weak σ: even-like enrichment is informative in DE. -/
theorem pureNPI_eligible_in_all_de :
    (IndefiniteFunction.all.filter (·.isDE)).all
      (pureNPI.predictedFunctions.contains ·) = true := by native_decide

/-- No FC function is in the pure NPI eligible region.
    D-MAX items lack antiexhaustive enrichment. -/
theorem pureNPI_not_eligible_in_fc :
    (IndefiniteFunction.all.filter (·.isFC)).all
      (λ f => !pureNPI.predictedFunctions.contains f) = true := by native_decide

/-- The *qualsiasi*/*any* contrast: among D-MIN items, every DE function
    is included by weak σ (*any*) and excluded by σ̃ (*qualsiasi*). -/
theorem dMin_sigma_determines_de :
    (IndefiniteFunction.all.filter (·.isDE)).all
      (λ f => npiFCI.predictedFunctions.contains f &&
              !pureFCI.predictedFunctions.contains f) = true := by native_decide

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
-- §8. Fragment Bridges
-- ============================================================================

/-!
## Connecting Fragment entries to PSI theory

Fragment entries store observable distributional properties (polarityType,
licensingContexts); PSI profiles encode theoretical parameters
(obligatoryDomainAlts, grain, scalar alternatives). Bridge theorems verify
consistency between the two layers via polarityType.
-/

open Core.Lexical.PolarityItem
open Fragments.English.PolarityItems (any ever)
open Fragments.Italian.PolarityItems
  (mai qualsiasi nessuno qualunque uno_qualsiasi alcuno)
open Fragments.German.PolarityItems (irgendein)

-- English *any* is npi_fci → matches npiFCI profile
theorem any_fragment_matches_npiFCI :
    any.polarityType = .npi_fci := rfl

-- English *ever* is npiWeak → matches pureNPI profile
theorem ever_fragment_matches_pureNPI :
    ever.polarityType = .npiWeak := rfl

-- Italian *mai* is npiWeak → matches pureNPI
theorem mai_fragment_matches_pureNPI :
    mai.polarityType = .npiWeak := rfl

-- Italian *alcuno* is npiWeak → matches pureNPI
theorem alcuno_fragment_matches_pureNPI :
    alcuno.polarityType = .npiWeak := rfl

-- Italian *nessuno* is npiWeak → matches pureNPI
theorem nessuno_fragment_matches_pureNPI :
    nessuno.polarityType = .npiWeak := rfl

-- Italian *qualsiasi* is fci → matches pureFCI profile
theorem qualsiasi_fragment_matches_pureFCI :
    qualsiasi.polarityType = .fci := rfl

-- Italian *qualunque* is fci → matches pureFCI profile
theorem qualunque_fragment_matches_pureFCI :
    qualunque.polarityType = .fci := rfl

-- Italian *uno qualsiasi* is fci → matches efciPureFci profile
theorem uno_qualsiasi_fragment_matches_efciPureFci :
    uno_qualsiasi.polarityType = .fci := rfl

-- German *irgendein* is npi_fci → matches efciNpiFci profile (table (94))
theorem irgendein_fragment_matches_efciNpiFci :
    irgendein.polarityType = .npi_fci := rfl

-- ============================================================================
-- §9. PSIProfile → PolarityType Bridge
-- ============================================================================

/-!
## Bridging the two classification systems

`Core.Lexical.PolarityItem.PolarityType` is a 5-way distributional
classification. `PSIProfile` is a 4-parameter theoretical decomposition.
The mapping should be consistent: each PSI class predicts exactly one
`PolarityType`.
-/

/-- Map a PSI profile to the expected PolarityType. -/
def PSIProfile.toPolarityType (p : PSIProfile) : PolarityType :=
  if !p.obligatoryDomainAlts then .ppi  -- no obligatory alts = plain indefinite/PPI
  else match p.grain, p.requiresProperStrengthening with
    | .max, false => .npiWeak    -- D-MAX, weak σ → pure NPI
    | .max, true  => .npiStrong  -- D-MAX, presuppositional → strong NPI (unattested)
    | .min, false => .npi_fci    -- D-MIN, weak σ → NPI/FCI (any)
    | .min, true  => .fci        -- D-MIN, presuppositional σ̃ → pure FCI (qualsiasi)

-- Verify the mapping is correct for all five named classes
theorem pureNPI_polarityType : pureNPI.toPolarityType = .npiWeak := rfl
theorem npiFCI_polarityType : npiFCI.toPolarityType = .npi_fci := rfl
theorem pureFCI_polarityType : pureFCI.toPolarityType = .fci := rfl
theorem efciNpiFci_polarityType : efciNpiFci.toPolarityType = .npi_fci := rfl
theorem efciPureFci_polarityType : efciPureFci.toPolarityType = .fci := rfl

-- Verify Fragment entries match their PSI profile's predicted PolarityType
theorem any_profile_consistent :
    any.polarityType = npiFCI.toPolarityType := rfl

theorem ever_profile_consistent :
    ever.polarityType = pureNPI.toPolarityType := rfl

theorem mai_profile_consistent :
    mai.polarityType = pureNPI.toPolarityType := rfl

theorem qualsiasi_profile_consistent :
    qualsiasi.polarityType = pureFCI.toPolarityType := rfl

theorem irgendein_profile_consistent :
    irgendein.polarityType = efciNpiFci.toPolarityType := rfl

-- ============================================================================
-- §10. σ/σ̃ Operators (Implicature Freezing)
-- ============================================================================

/-!
## σ̃: Presuppositional implicature freezing

@cite{chierchia-2006} §3.3 (definition (41)/(72)/(113)):

σ "freezes" the implicature: once σ applies, the enriched meaning becomes
part of the semantic content and can no longer be canceled. σ̃ (bold sigma)
adds a **presupposition**: the frozen meaning must be **strictly stronger**
than the plain meaning. Items selecting σ̃ (*qualsiasi*) differ from items
selecting plain σ (*any*) exactly in whether this presupposition is required.

### Why σ̃ blocks DE licensing (§5.3)

If enrichment is strengthening (enriched ⊂ plain), embedding in a DE
context **reverses** the entailment: C(plain) ⊆ C(enriched). The enriched
meaning under C is weaker, so σ̃'s presupposition fails. This is proved
as `sigma_bold_fails_in_de`.
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
  deriving DecidableEq, BEq, Repr

/-- Quantificational force of the FCI reading. -/
inductive QForce where
  | universal    -- ∀ reading
  | existential  -- ∃ reading
  | ambiguous    -- both readings available
  deriving DecidableEq, BEq, Repr

/-- FCI construction type: [qualsiasi N] vs [un N qualsiasi]. -/
inductive FCIType where
  | universal    -- [qualsiasi/qualunque N]: universal force
  | existential  -- [un N qualsiasi/qualunque]: existential force
  deriving DecidableEq, BEq, Repr

/-- Embedding context for FCI observations. -/
inductive FCIContext where
  | future              -- future tense (10a-b)
  | imperative          -- imperative mood (10c-d)
  | episodic_bare       -- bare episodic, no modifier (11a, 11c)
  | episodic_subtrigged -- episodic + relative clause (11b, 11d)
  | negation_bare       -- under negation, no modifier (12/73a)
  | negation_subtrigged -- under negation + relative clause (73b)
  deriving DecidableEq, BEq, Repr

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
  ⟨"Domani interrogherò qualsiasi studente", "(10a)",
   .universal, .future, .ambiguous, .grammatical⟩

/-- (10b): "Domani interrogherò uno studente qualsiasi" (future, existential FCI)
    — Only ∃ reading. -/
def obs_10b : FCIObservation :=
  ⟨"Domani interrogherò uno studente qualsiasi", "(10b)",
   .existential, .future, .existential, .grammatical⟩

/-- (10c): "Prendi qualunque dolce" (imperative, universal FCI)
    — Both ∀ and ∃ readings available. -/
def obs_10c : FCIObservation :=
  ⟨"Prendi qualunque dolce", "(10c)",
   .universal, .imperative, .ambiguous, .grammatical⟩

/-- (10d): "Prendi un dolce qualunque" (imperative, existential FCI)
    — Only ∃ reading. -/
def obs_10d : FCIObservation :=
  ⟨"Prendi un dolce qualunque", "(10d)",
   .existential, .imperative, .existential, .grammatical⟩

-- §2 data: subtrigging

/-- (11a): "Ieri ho parlato con un qualsiasi filosofo" (bare episodic, EFCI)
    — Marginal without modifier. -/
def obs_11a : FCIObservation :=
  ⟨"Ieri ho parlato con un qualsiasi filosofo", "(11a)",
   .existential, .episodic_bare, .existential, .marginal⟩

/-- (11b): "Ieri ho parlato con un qualsiasi filosofo che fosse interessato"
    — Marginal; the paper notes RC "if anything, makes things worse" for
    existential FCIs (p.543). Subtrigging does not rescue EFCIs. -/
def obs_11b : FCIObservation :=
  ⟨"Ieri ho parlato con un qualsiasi filosofo che fosse interessato", "(11b)",
   .existential, .episodic_subtrigged, .existential, .marginal⟩

/-- (11c): "Ieri ho parlato con qualsiasi filosofo" (bare episodic, universal FCI)
    — Marginal without modifier. -/
def obs_11c : FCIObservation :=
  ⟨"Ieri ho parlato con qualsiasi filosofo", "(11c)",
   .universal, .episodic_bare, .universal, .marginal⟩

/-- (11d): "Ieri ho parlato con qualsiasi filosofo che fosse interessato"
    — Fully grammatical: subtrigging rescues universal FCIs. -/
def obs_11d : FCIObservation :=
  ⟨"Ieri ho parlato con qualsiasi filosofo che fosse interessato", "(11d)",
   .universal, .episodic_subtrigged, .universal, .grammatical⟩

-- §5.3 / §2: negation scope

/-- (12)/(73a): "Non leggerò qualunque libro" (negation + bare universal FCI)
    — Only ¬∀ (rhetorical) reading; NOT the NPI ¬∃ reading. -/
def obs_12 : FCIObservation :=
  ⟨"Non leggerò qualunque libro", "(12)/(73a)",
   .universal, .negation_bare, .universal, .grammatical⟩

/-- (73b): "Non leggerò qualunque libro che mi consiglierà Gianni"
    — With RC under negation: ∀¬ or ¬∃ readings become available. -/
def obs_73b : FCIObservation :=
  ⟨"Non leggerò qualunque libro che mi consiglierà Gianni", "(73b)",
   .universal, .negation_subtrigged, .ambiguous, .grammatical⟩

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
    [obs_10a, obs_10c].all (·.force == .ambiguous) = true := by native_decide

/-- Existential FCIs have ∃ force only. -/
theorem existential_fci_existential_force :
    [obs_10b, obs_10d].all (·.force == .existential) = true := by native_decide

/-- Under negation, bare universal FCI yields only ¬∀ (rhetorical), not NPI ¬∃.
    This is the *qualsiasi*/*any* contrast: *qualsiasi* under negation ≠ NPI. -/
theorem negation_rhetorical_only :
    obs_12.force = .universal := rfl

end Phenomena.Polarity.Studies.Chierchia2006
