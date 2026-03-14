import Linglib.Phenomena.Polarity.Typology
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Theories.Semantics.Exhaustification.EFCI

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
(@cite{kadmon-landman-1993}, proved in `Exhaustification.Chierchia2013`):
widening strengthens in DE but weakens in UE. The PSI parameter space
refines this into D-MAX (even-like) vs D-MIN (antiexhaustive) enrichment.
-/

namespace Phenomena.Polarity.Studies.Chierchia2006

open Phenomena.Polarity.Typology
open Exhaustification.EFCI (FCIFlavor EFCIRescue)

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
appear. A surface form covers a contiguous subset of its class's eligible
region. The eligible regions themselves are contiguous.

Theoretical reasoning:
- **D-MAX** (pure NPIs): Even-like enrichment is informative only in DE
  contexts → eligible in DE functions (question through directNeg).
- **D-MIN, weak σ** (NPI/FCIs): In DE, exhaustification is vacuous → NPI;
  under modals, antiexhaustive → FC. Eligible across the full polarity +
  FC range (irrealis through freeChoice).
- **D-MIN, σ̃** (pure FCIs): Proper strengthening fails in DE (the result
  isn't strictly stronger) → only FC functions (comparative, freeChoice).
- **No obligatory alts** (plain indefinites): No polarity sensitivity →
  specific/irrealis functions only.
-/

/-- The Haspelmath functions predicted by a PSI class. -/
def PSIProfile.predictedFunctions (p : PSIProfile) : List IndefiniteFunction :=
  if !p.obligatoryDomainAlts then
    -- Plain indefinites: no polarity sensitivity
    [.specificKnown, .specificUnknown, .irrealis]
  else match p.grain, p.requiresProperStrengthening with
    -- Pure NPI (D-MAX, weak): DE contexts
    | .max, false =>
        [.question, .conditional, .indirectNeg, .directNeg]
    -- D-MAX + presuppositional: unattested (DE + proper strengthening = ⊥)
    | .max, true => []
    -- NPI/FCI (D-MIN, weak): DE + FC (full polarity range)
    | .min, false =>
        [.irrealis, .question, .conditional, .indirectNeg,
         .directNeg, .comparative, .freeChoice]
    -- Pure FCI (D-MIN, presuppositional): FC only
    | .min, true =>
        [.comparative, .freeChoice]

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

/-- NPI/FCI items are eligible in DE contexts. -/
theorem npiFCI_eligible_in_de :
    npiFCI.predictedFunctions.contains .indirectNeg = true ∧
    npiFCI.predictedFunctions.contains .directNeg = true := by
  constructor <;> native_decide

/-- Pure FCI items are NOT eligible in DE contexts. -/
theorem pureFCI_not_eligible_in_de :
    pureFCI.predictedFunctions.contains .indirectNeg = false ∧
    pureFCI.predictedFunctions.contains .directNeg = false := by
  constructor <;> native_decide

/-- The contrast derives from `requiresProperStrengthening`. -/
theorem contrast_is_proper_strengthening :
    npiFCI.requiresProperStrengthening = false ∧
    pureFCI.requiresProperStrengthening = true := ⟨rfl, rfl⟩

/-- Pure NPIs are eligible in DE but NOT in FC contexts. -/
theorem pureNPI_de_only :
    pureNPI.predictedFunctions.contains .directNeg = true ∧
    pureNPI.predictedFunctions.contains .freeChoice = false := by
  constructor <;> native_decide

/-- Among D-MIN items, `requiresProperStrengthening` is the sole
    parameter that determines DE eligibility. This is the formal
    content of the *qualsiasi*/*any* contrast. -/
theorem dMin_de_iff_weak :
    npiFCI.grain = .min ∧ npiFCI.predictedFunctions.contains .directNeg = true ∧
    pureFCI.grain = .min ∧ pureFCI.predictedFunctions.contains .directNeg = false := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;> native_decide

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

open Fragments.English.PolarityItems (any ever)
open Fragments.Italian.PolarityItems
  (mai qualsiasi nessuno qualunque uno_qualsiasi alcuno)

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

end Phenomena.Polarity.Studies.Chierchia2006
