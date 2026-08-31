import Linglib.Studies.Haspelmath1997
import Linglib.Semantics.Polarity.Item
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Fragments.German.PolarityItems
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Semantics.Exhaustification.Antiexhaustive
import Linglib.Studies.Chierchia2013
import Linglib.Data.Examples.Chierchia2006
/-!
# Chierchia 2006: domain widening and the polarity-item typology

This file formalizes the parametric decomposition of polarity-sensitive items in
[chierchia-2006]. An item's distribution follows from two things about its alternatives: how
fine-grained the domain alternatives are, and whether exhaustification over them must strictly
strengthen. Together with whether domain alternatives are obligatory and whether the item has
scalar alternatives, these fix a class — pure negative-polarity item, negative-polarity and
free-choice item, pure free-choice item, and their existential-free-choice counterparts — and each
class's eligible region turns out to be a contiguous stretch of [haspelmath-1997]'s implicational
map, which is why indefinite series cover contiguous function ranges.

The proper-strengthening parameter is what separates Italian *qualsiasi* from English *any* under
negation. Exhaustification of *any* in a downward-entailing context is vacuous, which its weak
alternative-set tolerates, so the negative-polarity reading survives; *qualsiasi* requires proper
strengthening, which a downward-entailing context cannot supply, so only the rhetorical ¬∀ reading
remains. The Italian judgments of §2 are rows in `Data/Examples/Chierchia2006.json`.

## Main definitions

* `PSIProfile`, `PSIProfile.predictedFunctions` — the parameters and the eligible region they fix
* `pureNPI`, `npiFCI`, `pureFCI`, `efciNpiFci`, `efciPureFci` — the classes
* `PSIProfile.predictedLicensor`, `PSIProfile.predictedFC`, `PSIProfile.toFCIFlavor` — what a
  profile predicts about a Fragment entry
* `sigmaBoldDefined` — the presuppositional alternative-set of the proper-strengthening items

## Main results

* `all_psi_classes_contiguous` — every class's eligible region is a contiguous Haspelmath stretch
* `dMax_presuppositional_empty` — requiring both downward-entailing contexts and proper
  strengthening is contradictory, so that cell of the typology is empty
* `sample_series_within_predicted`, `fragment_entries_match_profiles` — the sampled series and the
  Fragment entries fall inside what their classes predict
* `sigma_bold_fails_in_de`, `dMax_enrichment_vacuous_in_de`, `fci_universal_from_oMinus` — why
  proper strengthening fails in a downward-entailing context, and where the universal force of a
  free-choice item comes from
* `force_tracks_construction`, `subtrigging_rescues_universal`,
  `subtrigging_does_not_rescue_existential`, `negation_rhetorical_only` — the Italian data

## References

* [chierchia-2006]
* [haspelmath-1997]
* [kadmon-landman-1993]
* [kratzer-shimoyama-2002]
* [fox-2007]
-/

namespace Chierchia2006

open Haspelmath1997
open Indefinite
open Chierchia2013 (FCIFlavor)

-- ============================================================================
-- §1. The PSI Parameter Space
-- ============================================================================

/-- Domain alternative grain size.

    [chierchia-2006] table (76)/(94):
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
    [chierchia-2006]'s parametric PSI typology.

    The original paper used σ (weak) vs σ̃ (presuppositional) for
    implicature freezing, and O/E/O⁻ for enrichment. These specific
    operators have been superseded by IE+II ([bar-lev-fox-2020]),
    but the *parameters* they encode remain the standard way to
    classify PSIs cross-linguistically. -/
structure PSIProfile where
  /-- Domain alternative grain (MAX vs MIN) -/
  grain : DomainAltGrain
  /-- Whether domain alternatives are obligatorily active -/
  obligatoryDomainAlts : Bool
  /-- Whether exhaustification must yield proper strengthening
      (corresponds to [chierchia-2006]'s presuppositional σ̃) -/
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

Each PSI class predicts an **eligible region** on [haspelmath-1997]'s
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
    Haspelmath functions (`HaspelmathFunction.isDE`, `HaspelmathFunction.isFC`).
    Each branch filters `HaspelmathFunction.all` by the semantic property
    that the PSI class's enrichment mechanism targets. -/
def PSIProfile.predictedFunctions (p : PSIProfile) : List HaspelmathFunction :=
  HaspelmathFunction.all.filter (λ f =>
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

This is the central bridge between [chierchia-2006]'s exhaustification
theory and [haspelmath-1997]'s typological generalization. It explains
*why* indefinite pronoun series cover contiguous function ranges: each
PSI class's eligible region is contiguous, and surface forms cover
contiguous subsets of their class's region.
-/

/-- All five PSI classes have contiguous predicted function ranges. -/
theorem all_psi_classes_contiguous :
    [pureNPI, npiFCI, pureFCI, efciNpiFci, efciPureFci].all
      (λ p => HaspelmathFunction.isContiguous p.predictedFunctions) = true := by decide

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
[haspelmath-1997]'s typological data in `Typology.lean`) should be
a subset of its PSI class's predicted (eligible) region.

**All function lists are derived from `Typology.lean` profiles** — not
hardcoded — so changes to the typological data will break exactly the
theorems they should.
-/

private def functionsSubset (actual predicted : List HaspelmathFunction) : Bool :=
  actual.all (λ f => predicted.contains f)

/-- Extract Haspelmath functions for a named form from a language paradigm.
    Uses `e.functionList` (the computable list extraction) rather than
    `Finset.toList` (noncomputable). -/
private def seriesFunctions (profile : IndefiniteParadigm) (form : String)
    : List HaspelmathFunction :=
  match profile.forms.find? (·.form == form) with
  | some e => e.functionList
  | none => []

/-- The plain indefinite profile: no obligatory domain alternatives and no proper-strengthening
requirement. -/
private def plainIndefinite : PSIProfile :=
  { grain := .max, obligatoryDomainAlts := false,
    requiresProperStrengthening := false, hasScalarAlts := false }

/-- Every series in the sample covers a subset of the region its class predicts. The German
*irgend*-series is checked without `specificUnknown`, the [kratzer-shimoyama-2002] ignorance
reading, which the eligibility encoding does not generate — a gap in the encoding rather than in
the data. -/
theorem sample_series_within_predicted :
    [ (seriesFunctions italian "nessuno", pureNPI)
    , (seriesFunctions italian "qualunque/qualsiasi", pureFCI)
    , (seriesFunctions italian "qualcuno", plainIndefinite)
    , (seriesFunctions english "any- (NPI)", npiFCI)
    , (seriesFunctions english "any- (FC)", npiFCI)
    , ((seriesFunctions german "irgendwer").filter (· != .specificUnknown), efciNpiFci)
    , (seriesFunctions mandarin "shéi (谁, non-interrog.)", npiFCI) ].all
      (fun p => functionsSubset p.1 p.2.predictedFunctions) = true := by decide

-- ============================================================================
-- §6. The qualsiasi/any Contrast Under Negation
-- ============================================================================

/-!
## Deriving the core empirical contrast

[chierchia-2006]'s most striking prediction: Italian *qualsiasi*
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
    (HaspelmathFunction.all.filter (·.isDE)).all
      (npiFCI.predictedFunctions.contains ·) = true := by decide

/-- No DE Haspelmath function is in the pure FCI eligible region.
    D-MIN + σ̃: proper strengthening fails in DE (`sigma_bold_fails_in_de`). -/
theorem pureFCI_not_eligible_in_any_de :
    (HaspelmathFunction.all.filter (·.isDE)).all
      (λ f => !pureFCI.predictedFunctions.contains f) = true := by decide

/-- Every DE function is in the pure NPI eligible region.
    D-MAX + weak σ: even-like enrichment is informative in DE. -/
theorem pureNPI_eligible_in_all_de :
    (HaspelmathFunction.all.filter (·.isDE)).all
      (pureNPI.predictedFunctions.contains ·) = true := by decide

/-- No FC function is in the pure NPI eligible region.
    D-MAX items lack antiexhaustive enrichment. -/
theorem pureNPI_not_eligible_in_fc :
    (HaspelmathFunction.all.filter (·.isFC)).all
      (λ f => !pureNPI.predictedFunctions.contains f) = true := by decide

/-- The *qualsiasi*/*any* contrast: among D-MIN items, every DE function
    is included by weak σ (*any*) and excluded by σ̃ (*qualsiasi*). -/
theorem dMin_sigma_determines_de :
    (HaspelmathFunction.all.filter (·.isDE)).all
      (λ f => npiFCI.predictedFunctions.contains f &&
              !pureFCI.predictedFunctions.contains f) = true := by decide

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

-- ============================================================================
-- §8. Fragment Bridges (PSIProfile → PolarityType)
-- ============================================================================

/-!
## Bridging PSI profiles to Fragment entries

`PSIProfile` is a 4-parameter theoretical decomposition; each PSI class
predicts the item's licensing parameters (`licensor` strength and
free-choice licensing), and each Fragment entry's instantiated parameters
should match its profile's prediction.
-/

open Polarity
open English.PolarityItems (any ever)
open Italian.PolarityItems
  (mai qualsiasi nessuno qualunque uno_qualsiasi alcuno)
open German.PolarityItems (irgendein)

/-- The licensor strength a PSI profile predicts (`none` = not
    strength-licensed). -/
def PSIProfile.predictedLicensor (p : PSIProfile) :
    Option Polarity.DEStrength :=
  if !p.obligatoryDomainAlts then none
  else match p.grain, p.requiresProperStrengthening with
    | .max, false => some .weak         -- D-MAX, weak σ → pure NPI
    | .max, true  => some .antiAdditive -- D-MAX, presuppositional (unattested)
    | .min, false => some .weak         -- D-MIN, weak σ → NPI/FCI (any)
    | .min, true  => none               -- D-MIN, σ̃ → pure FCI (qualsiasi)

/-- Whether the profile predicts free-choice (mechanism) licensing. -/
def PSIProfile.predictedFC (p : PSIProfile) : Bool :=
  p.obligatoryDomainAlts && p.grain == .min

/-- Each Fragment entry's licensor and free-choice fields are what its class predicts. -/
theorem fragment_entries_match_profiles :
    [ (any, npiFCI), (ever, pureNPI), (mai, pureNPI), (alcuno, pureNPI), (nessuno, pureNPI)
    , (qualsiasi, pureFCI), (qualunque, pureFCI), (uno_qualsiasi, efciPureFci)
    , (irgendein, efciNpiFci) ].all
      (fun e => e.1.licensor == e.2.predictedLicensor && e.1.freeChoice == e.2.predictedFC)
      = true := by decide

-- ============================================================================
-- §10. Exhaustification Theory: σ̃, SI Vacuity, and O⁻
-- ============================================================================

/-!
## Exercising the Exhaustification theory layer

This section connects [chierchia-2006]'s PSI typology to the formal
results in `Exhaustification`.

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

open Exhaustification (oMinus antiexh_yields_universal)

/-- σ̃'s presupposition: the enriched meaning is **strictly stronger**
    than the plain meaning. [chierchia-2006] definition (72).

    This must hold for σ̃ to be defined (felicitous). Items selecting σ̃
    (*qualsiasi*, *qualunque*) require proper strengthening; items selecting
    plain σ (*any*, *ever*) don't. -/
def sigmaBoldDefined (plain enriched : World → Prop) : Prop :=
  (∀ w, enriched w → plain w) ∧ ¬(∀ w, plain w → enriched w)

/-- **σ̃'s presupposition fails in DE contexts.**

    [chierchia-2006] §5.3: This is the formal content of the
    *qualsiasi*/*any* contrast. If enrichment properly strengthens at the
    base level (enriched ⊂ plain), then embedding in a DE context
    *reverses* the entailment: C(plain) ⊆ C(enriched), making the
    enriched meaning under C strictly WEAKER, not stronger.

    The DE reversal gives C(plain) ⊆ C(enriched), which contradicts σ̃'s
    requirement that C(enriched) be strictly stronger than C(plain). -/
theorem sigma_bold_fails_in_de
    (C : (World → Prop) → (World → Prop))
    (hDE : ∀ (p q : World → Prop), (∀ w, p w → q w) → (∀ w, C q w → C p w))
    (plain enriched : World → Prop)
    (h_stronger : ∀ w, enriched w → plain w) :
    ¬sigmaBoldDefined (C plain) (C enriched) :=
  fun ⟨_, hnotrev⟩ => hnotrev (hDE enriched plain h_stronger)

/-- **SI vacuity in DE blocks D-MAX enrichment in UE.**

    [chierchia-2006] §4.1: D-MAX items (pure NPIs) trigger
    even-like (E) enrichment, which is an SI. SIs are vacuous in DE, so E
    enrichment is informative only in non-DE contexts — but D-MAX items
    *require* DE. This is why pure NPIs are confined to DE contexts. -/
theorem dMax_enrichment_vacuous_in_de
    (C : (World → Prop) → (World → Prop))
    (hDE : ∀ (p q : World → Prop), (∀ w, p w → q w) → (∀ w, C q w → C p w))
    (weak strong : World → Prop) (h_ent : ∀ w, strong w → weak w) :
    ∀ w, ¬(C weak w ∧ ¬C strong w) :=
  fun w ⟨hCw, hnCs⟩ => hnCs (hDE strong weak h_ent w hCw)

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

/-! ### The Italian free-choice data

The judgments of §2 are rows in `Data/Examples/Chierchia2006.json`, each tagged with the
free-choice construction it uses ([qualsiasi N] against [un N qualsiasi]), the environment it
appears in, and the quantificational force available there. Three contrasts drive the account: the
two constructions differ in force, a bare universal free-choice item is marginal in an episodic
context until a relative clause subtriggs it, and under negation the universal item yields only
the rhetorical ¬∀ reading rather than the ¬∃ reading a negative-polarity item would. -/

open Data.Examples in
/-- A row's value for one of the paper's feature keys. -/
private def feature (e : LinguisticExample) (k : String) : Option String :=
  (e.paperFeatures.find? (·.1 == k)).map Prod.snd

/-- The two constructions differ in force outside negation: the universal free-choice item admits
both readings and the existential one only the existential reading. -/
theorem force_tracks_construction :
    (∀ e ∈ Examples.all, feature e "environment" = some "future" ∨
        feature e "environment" = some "imperative" →
        feature e "fciType" = some "universal" → feature e "force" = some "ambiguous") ∧
      (∀ e ∈ Examples.all, feature e "fciType" = some "existential" →
        feature e "force" = some "existential") := by decide

/-- Subtrigging rescues a universal free-choice item in an episodic context: bare it is marginal,
with a relative clause it is acceptable. -/
theorem subtrigging_rescues_universal :
    (∀ e ∈ Examples.all, feature e "fciType" = some "universal" →
        feature e "environment" = some "episodicBare" → e.judgment = .marginal) ∧
      (∀ e ∈ Examples.all, feature e "fciType" = some "universal" →
        feature e "environment" = some "episodicSubtrigged" → e.judgment = .acceptable) := by
  decide

/-- It does nothing for an existential one, which stays marginal in an episodic context either
way — and both episodic existential rows are attested, so the claim is not vacuous. -/
theorem subtrigging_does_not_rescue_existential :
    (∀ e ∈ Examples.all, feature e "fciType" = some "existential" →
        feature e "environment" = some "episodicBare" ∨
          feature e "environment" = some "episodicSubtrigged" → e.judgment = .marginal) ∧
      (∃ e ∈ Examples.all, feature e "environment" = some "episodicBare" ∧
        feature e "fciType" = some "existential") ∧
      (∃ e ∈ Examples.all, feature e "environment" = some "episodicSubtrigged" ∧
        feature e "fciType" = some "existential") := by decide

/-- Under bare negation the universal free-choice item has only the universal (rhetorical ¬∀)
reading; adding a relative clause makes the other readings available again. This is the
*qualsiasi*/*any* contrast: *qualsiasi* under negation is not a negative-polarity item. -/
theorem negation_rhetorical_only :
    (∀ e ∈ Examples.all, feature e "environment" = some "negationBare" →
        feature e "force" = some "universal") ∧
      (∀ e ∈ Examples.all, feature e "environment" = some "negationSubtrigged" →
        feature e "force" = some "ambiguous") ∧
      (∃ e ∈ Examples.all, feature e "environment" = some "negationBare") := by decide

end Chierchia2006
