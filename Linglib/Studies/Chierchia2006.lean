import Linglib.Studies.Haspelmath1997
import Linglib.Semantics.Polarity.Item
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Fragments.German.PolarityItems
import Linglib.Data.Examples.Chierchia2006
/-!
# Chierchia (2006): Broaden your views

This file formalizes the parametric decomposition of polarity-sensitive items in
[chierchia-2006]. An item's distribution follows from two things about its alternatives: how
fine-grained the domain alternatives are, and whether exhaustification over them must strictly
strengthen. Together with whether domain alternatives are obligatory and whether the item has
scalar alternatives, these fix a class, pure negative-polarity item, negative-polarity and
free-choice item, pure free-choice item, and their existential-free-choice counterparts, and
each class's eligible region turns out to be a contiguous stretch of [haspelmath-1997]'s
implicational map, which is why indefinite series cover contiguous function ranges. The
proper-strengthening parameter separates Italian *qualsiasi* from English *any* under negation:
exhaustification of *any* in a downward-entailing context is vacuous, which its weak
alternative set tolerates, so the negative-polarity reading survives, while *qualsiasi* requires
proper strengthening, which a downward-entailing context cannot supply, so only the rhetorical
¬∀ reading remains. The Italian judgments are rows, and the theorems derive the regions, the
contrast under negation, the Fragment entries' parameters and the judgments from the profiles.

## TODO

* The German *irgend*-series is checked without `specificUnknown`, the [kratzer-shimoyama-2002]
  ignorance reading, which `PSIProfile.predictedFunctions` does not generate.

## References

* [chierchia-2006]
* [haspelmath-1997]
* [kratzer-shimoyama-2002]
-/

namespace Chierchia2006

open Haspelmath1997 Indefinite Data.Examples

/-! ### The parameters -/

/-- The grain of an item's domain alternatives: only large subdomains, which trigger the
even-like enrichment of the pure negative-polarity items *alcuno*, *mai*, *ever*, or every
subdomain down to the singletons, which trigger the antiexhaustive enrichment of the free-choice
items *any*, *qualsiasi*, *irgendein*. -/
inductive DomainAltGrain where
  | max
  | min
  deriving DecidableEq, Repr

/-- The parameters that fix a polarity-sensitive item's class: the grain of its domain
alternatives, whether they are obligatorily active, whether exhaustification over them must
properly strengthen, the presupposition of the operator σ̃, and whether scalar alternatives are
active too. -/
structure PSIProfile where
  grain : DomainAltGrain
  obligatoryDomainAlts : Bool
  requiresProperStrengthening : Bool
  hasScalarAlts : Bool
  deriving DecidableEq, Repr

/-! ### The five classes -/

/-- The pure negative-polarity items *alcuno*, *mai*, *ever*: large domain alternatives,
obligatory, weak σ, no scalar alternatives. -/
def pureNPI : PSIProfile :=
  { grain := .max
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := false
  , hasScalarAlts := false }

/-- English *any*, a negative-polarity item in downward-entailing contexts, where
exhaustification is vacuous, and a free-choice item under modals: every domain alternative,
obligatory, weak σ, no scalar alternatives. -/
def npiFCI : PSIProfile :=
  { grain := .min
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := false
  , hasScalarAlts := false }

/-- The pure free-choice items *qualsiasi* and *qualunque*: every domain alternative,
obligatory, the presuppositional σ̃, no scalar alternatives. -/
def pureFCI : PSIProfile :=
  { grain := .min
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := true
  , hasScalarAlts := false }

/-- German *irgendein*, an existential free-choice item: like *any* with scalar alternatives
active. -/
def efciNpiFci : PSIProfile :=
  { grain := .min
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := false
  , hasScalarAlts := true }

/-- Italian *uno qualsiasi*, an existential pure free-choice item: like *qualsiasi* with
scalar alternatives active. -/
def efciPureFci : PSIProfile :=
  { grain := .min
  , obligatoryDomainAlts := true
  , requiresProperStrengthening := true
  , hasScalarAlts := true }

/-! ### Eligible regions on the implicational map -/

/-- The functions of the implicational map a class is eligible for, from its parameters and
the monotonicity of the functions: a plain indefinite needs neither downward-entailing nor
free-choice licensing; even-like enrichment over large alternatives is informative only in a
downward-entailing context, and never together with proper strengthening; fine alternatives
under weak σ are vacuously exhaustified in a downward-entailing context and antiexhaustified
under a modal, irrealis included; under σ̃ only the free-choice functions remain. -/
def PSIProfile.predictedFunctions (p : PSIProfile) : List HaspelmathFunction :=
  HaspelmathFunction.all.filter λ f =>
    if !p.obligatoryDomainAlts then !f.isDE && !f.isFC
    else match p.grain, p.requiresProperStrengthening with
      | .max, false => f.isDE
      | .max, true => false
      | .min, false => f.isDE || f.isFC || f == .irrealis
      | .min, true => f.isFC

/-- The five classes. -/
def classes : List PSIProfile := [pureNPI, npiFCI, pureFCI, efciNpiFci, efciPureFci]

/-- Every class's eligible region is a contiguous stretch of the implicational map, which is
why an indefinite series covers a contiguous range of functions. -/
theorem classes_contiguous :
    ∀ p ∈ classes, HaspelmathFunction.isContiguous p.predictedFunctions = true := by
  decide

/-- Large domain alternatives with proper strengthening is an empty cell: even-like enrichment
needs a downward-entailing context, which is where strengthening fails. -/
theorem dMax_presuppositional_empty :
    (PSIProfile.mk .max true true false).predictedFunctions = [] := rfl

/-! ### The sampled series -/

/-- The functions a named form of a paradigm covers. -/
private def seriesFunctions (profile : IndefiniteParadigm) (form : String) :
    List HaspelmathFunction :=
  ((profile.forms.find? (·.form == form)).map (·.functionList)).getD []

/-- The plain indefinite profile: no obligatory domain alternatives and no proper-strengthening
requirement. -/
private def plainIndefinite : PSIProfile :=
  { grain := .max, obligatoryDomainAlts := false,
    requiresProperStrengthening := false, hasScalarAlts := false }

/-- Every series in the sample covers a subset of the region its class predicts. -/
theorem sample_series_within_predicted :
    ∀ p ∈ [(seriesFunctions italian "nessuno", pureNPI),
        (seriesFunctions italian "qualunque/qualsiasi", pureFCI),
        (seriesFunctions italian "qualcuno", plainIndefinite),
        (seriesFunctions english "any- (NPI)", npiFCI),
        (seriesFunctions english "any- (FC)", npiFCI),
        ((seriesFunctions german "irgendwer").filter (· != .specificUnknown), efciNpiFci),
        (seriesFunctions mandarin "shéi (谁, non-interrog.)", npiFCI)],
      ∀ f ∈ p.1, f ∈ p.2.predictedFunctions := by
  decide

/-! ### *qualsiasi* and *any* under negation -/

/-- A pure negative-polarity item is eligible in every downward-entailing function and in no
free-choice function: even-like enrichment is informative only under downward entailment, and
large alternatives give no antiexhaustive enrichment. -/
theorem pureNPI_region :
    ∀ f ∈ HaspelmathFunction.all,
      (f.isDE = true → f ∈ pureNPI.predictedFunctions) ∧
        (f.isFC = true → f ∉ pureNPI.predictedFunctions) := by
  decide

/-- The contrast between *any* and *qualsiasi*: with every domain alternative active, each
downward-entailing function is eligible under weak σ, where exhaustification is vacuous, and
ineligible under σ̃, whose proper strengthening the context cannot supply, leaving *qualsiasi*
under negation only the rhetorical ¬∀ reading. -/
theorem dMin_sigma_determines_de :
    ∀ f ∈ HaspelmathFunction.all, f.isDE = true →
      f ∈ npiFCI.predictedFunctions ∧ f ∉ pureFCI.predictedFunctions := by
  decide

/-! ### The Fragment entries -/

/-- The licensor strength a profile predicts: an item whose obligatory alternatives are
exhaustified under weak σ is licensed by any downward-entailing operator, since vacuous
exhaustification is tolerated there, and no other item is licensed by strength. -/
def PSIProfile.predictedLicensor (p : PSIProfile) : Option Polarity.DEStrength :=
  if p.obligatoryDomainAlts && !p.requiresProperStrengthening then some .weak else none

/-- A profile predicts free-choice licensing when its obligatory alternatives are fine. -/
def PSIProfile.PredictsFreeChoice (p : PSIProfile) : Prop :=
  p.obligatoryDomainAlts = true ∧ p.grain = .min

instance : DecidablePred PSIProfile.PredictsFreeChoice :=
  λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Each Fragment entry's licensor and free-choice fields are what its class predicts. -/
theorem fragment_entries_match_profiles :
    ∀ e ∈ [(English.PolarityItems.any, npiFCI), (English.PolarityItems.ever, pureNPI),
        (Italian.PolarityItems.mai, pureNPI), (Italian.PolarityItems.alcuno, pureNPI),
        (Italian.PolarityItems.nessuno, pureNPI), (Italian.PolarityItems.qualsiasi, pureFCI),
        (Italian.PolarityItems.qualunque, pureFCI),
        (Italian.PolarityItems.uno_qualsiasi, efciPureFci),
        (German.PolarityItems.irgendein, efciNpiFci)],
      e.1.licensor = e.2.predictedLicensor ∧ (e.1.freeChoice = true ↔ e.2.PredictsFreeChoice) := by
  decide

/-! ### Proper strengthening and downward entailment -/

section Strengthening

variable {World : Type*}

/-- The presupposition of σ̃: the enriched meaning is strictly stronger than the plain one. -/
def ProperlyStrengthens (plain enriched : World → Prop) : Prop :=
  (∀ w, enriched w → plain w) ∧ ¬ ∀ w, plain w → enriched w

/-- The presupposition fails in a downward-entailing context: an enrichment that properly
strengthens at the base is reversed there, so the enriched meaning is the weaker one. This is
what keeps *qualsiasi* out of negative-polarity positions. -/
theorem not_properlyStrengthens_of_de (C : (World → Prop) → (World → Prop))
    (hDE : ∀ p q : World → Prop, (∀ w, p w → q w) → ∀ w, C q w → C p w)
    (plain enriched : World → Prop) (h : ∀ w, enriched w → plain w) :
    ¬ ProperlyStrengthens (C plain) (C enriched) :=
  λ ⟨_, hnotrev⟩ => hnotrev (hDE enriched plain h)

/-- A scalar implicature is vacuous in a downward-entailing context: the weak alternative never
holds there while the strong one fails, which is why even-like enrichment is informative only
outside such contexts. -/
theorem dMax_enrichment_vacuous_in_de (C : (World → Prop) → (World → Prop))
    (hDE : ∀ p q : World → Prop, (∀ w, p w → q w) → ∀ w, C q w → C p w)
    (weak strong : World → Prop) (h : ∀ w, strong w → weak w) :
    ∀ w, ¬ (C weak w ∧ ¬ C strong w) :=
  λ w ⟨hCw, hnCs⟩ => hnCs (hDE strong weak h w hCw)

end Strengthening

/-! ### The Italian free-choice data -/

/-- The two constructions differ in force outside negation: the universal free-choice item admits
both readings and the existential one only the existential reading. -/
theorem force_tracks_construction :
    (∀ e ∈ Examples.all, e.feature? "environment" = some "future" ∨
        e.feature? "environment" = some "imperative" →
        e.feature? "fciType" = some "universal" → e.feature? "force" = some "ambiguous") ∧
      (∀ e ∈ Examples.all, e.feature? "fciType" = some "existential" →
        e.feature? "force" = some "existential") := by decide

/-- Subtrigging rescues a universal free-choice item in an episodic context: bare it is marginal,
with a relative clause it is acceptable. -/
theorem subtrigging_rescues_universal :
    (∀ e ∈ Examples.all, e.feature? "fciType" = some "universal" →
        e.feature? "environment" = some "episodicBare" → e.judgment = .marginal) ∧
      (∀ e ∈ Examples.all, e.feature? "fciType" = some "universal" →
        e.feature? "environment" = some "episodicSubtrigged" → e.judgment = .acceptable) := by
  decide

/-- It does nothing for an existential one, which stays marginal in an episodic context with or
without a relative clause. -/
theorem subtrigging_does_not_rescue_existential :
    (∀ e ∈ Examples.all, e.feature? "fciType" = some "existential" →
        e.feature? "environment" = some "episodicBare" ∨
          e.feature? "environment" = some "episodicSubtrigged" → e.judgment = .marginal) ∧
      (∃ e ∈ Examples.all, e.feature? "environment" = some "episodicBare" ∧
        e.feature? "fciType" = some "existential") ∧
      (∃ e ∈ Examples.all, e.feature? "environment" = some "episodicSubtrigged" ∧
        e.feature? "fciType" = some "existential") := by decide

/-- Under bare negation the universal free-choice item has only the universal (rhetorical ¬∀)
reading; adding a relative clause makes the other readings available again. This is the
*qualsiasi*/*any* contrast: *qualsiasi* under negation is not a negative-polarity item. -/
theorem negation_rhetorical_only :
    (∀ e ∈ Examples.all, e.feature? "environment" = some "negationBare" →
        e.feature? "force" = some "universal") ∧
      (∀ e ∈ Examples.all, e.feature? "environment" = some "negationSubtrigged" →
        e.feature? "force" = some "ambiguous") ∧
      (∃ e ∈ Examples.all, e.feature? "environment" = some "negationBare") := by decide

end Chierchia2006
