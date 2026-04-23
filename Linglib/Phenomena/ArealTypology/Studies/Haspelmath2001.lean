import Linglib.Theories.Diachronic.Areal
import Linglib.Datasets.WALS.Features.F37A
import Linglib.Datasets.WALS.Features.F38A
import Linglib.Datasets.WALS.Features.F47A
import Linglib.Datasets.WALS.Features.F101A
import Linglib.Datasets.WALS.Features.F107A
import Linglib.Datasets.WALS.Features.F115A
import Linglib.Datasets.WALS.Features.F121A
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Standard Average European: A Linguistic Area
@cite{haspelmath-2001}

Formalization of @cite{haspelmath-2001}'s argument that the core European
languages — the Romance, Germanic, Balkan, and Balto-Slavic families plus
the westernmost Finno-Ugric languages — form a *Sprachbund* (linguistic
area) called **Standard Average European** (SAE), defined by a dozen
shared structural features that are absent in the geographically and
genealogically adjacent languages.

This study instantiates the framework-neutral schema in
`Theories.Diachronic.Areal`: SAE is a `LinguisticArea SAELanguage SAEFeature`
whose feature set is the twelve major Europeanisms of §2 of the paper, whose
reference frame is the four samples §1 demands (area, cofamilial, adjacent,
world), and whose areality is verified feature-by-feature against
@cite{haspelmath-2001}'s Maps 107.1–107.12.

The cluster-map gradience of §4 (most notably the *Charlemagne* nucleus
formed by French and German) is recovered automatically from the discrete
feature data via `LinguisticArea.clusterScore` and `nucleus`.

## Architectural notes

* **Languages and features are local inductives**: the paper surveys a
  specific sample and committing to its boundaries is appropriate here.
  A `SAELanguage.toWALS` bridge maps each language to its WALS code where
  one exists.
* **The paper's Maps 107.1–107.12 are the primary source** for every
  isogloss. Each paper-based isogloss (e.g. `articleLgs`, `vplusNILgs`)
  is the explicit set Haspelmath plots on the corresponding map. For the
  six features with a directly comparable WALS chapter (37A, 38A, 47A,
  101A, 107A, 115A, 121A), a sibling `wals*Lgs` set is derived from
  `Datasets.WALS.F*.allData` via `walsClassifies`. The two are intentionally
  *not* unioned: where they disagree, that disagreement is a fact about
  Haspelmath's classification vs. WALS's encoding and should remain
  visible to readers and to bridge theorems.
* **Isoglosses are `Finset SAELanguage`** (the schema's `Isogloss` is a
  transparent abbreviation for `Finset L`). All filter predicates are
  decidable, so the four areality criteria reduce to `decide` against the
  computable rational `Isogloss.density`.
-/

namespace Phenomena.ArealTypology.Studies.Haspelmath2001

open Theories.Diachronic.Areal

-- ============================================================================
-- §1. The Language Sample
-- ============================================================================

/-- Languages surveyed by @cite{haspelmath-2001}, partitioned by their role
in the four reference samples (area / cofamilial / adjacent / world).

The list follows the paper's coverage but is necessarily a subset — the
maps include Sami, Mordvin, Komi, Udmurt, Mari, Tatar, Kalmyk, Lezgian,
etc. We retain enough of each subgroup to make the four samples non-empty
and to preserve the paper's headline findings (French/German nucleus,
Celtic/Basque/Turkic margin). -/
inductive SAELanguage where
  -- Romance (core SAE)
  | French | Italian | Spanish | Portuguese | Romanian | Catalan
  -- Germanic (core SAE)
  | German | Dutch | English | Swedish | Norwegian | Danish | Icelandic
  -- Slavic (core SAE)
  | Russian | Polish | Czech | Bulgarian | SerboCroatian | Ukrainian
  -- Balkan (core SAE; Romanian and Bulgarian also count above)
  | Greek | Albanian | Macedonian
  -- Baltic (core SAE)
  | Latvian | Lithuanian
  -- Finno-Ugric (marginal SAE)
  | Hungarian | Finnish | Estonian
  -- Geographically adjacent non-SAE (Celtic, Basque, Turkic, Semitic)
  | Welsh | Irish | Breton | Basque | Turkish | Maltese
  -- Cofamilial Indo-European outside SAE (rules out PIE inheritance)
  | Persian | HindiUrdu | Armenian
  -- Worldwide reference (non-IE, non-adjacent)
  | Lezgian | Georgian | Mongolian | Indonesian | Yoruba | Japanese
  | Mandarin | Swahili | Quechua
  deriving DecidableEq, Repr, Fintype

/-- WALS code for each `SAELanguage` where one exists. WALS codes are 3-letter
identifiers used by the World Atlas of Language Structures (the v2020.4 codes
in `Datasets.WALS.Features.*`). Returns `none` for languages outside the WALS
sample (currently: every `SAELanguage` constructor maps to a code, but the
return type is `Option String` to accommodate future additions to
`SAELanguage` that may not be in WALS). -/
def SAELanguage.toWALS : SAELanguage → Option String
  -- Romance
  | .French => some "fre" | .Italian => some "ita" | .Spanish => some "spa"
  | .Portuguese => some "por" | .Romanian => some "rom" | .Catalan => some "ctl"
  -- Germanic
  | .German => some "ger" | .Dutch => some "dut" | .English => some "eng"
  | .Swedish => some "swe" | .Norwegian => some "nor" | .Danish => some "dsh"
  | .Icelandic => some "ice"
  -- Slavic
  | .Russian => some "rus" | .Polish => some "pol" | .Czech => some "cze"
  | .Bulgarian => some "bul" | .SerboCroatian => some "scr"
  | .Ukrainian => some "ukr"
  -- Balkan / South Slavic
  | .Greek => some "grk" | .Albanian => some "alb" | .Macedonian => some "mcd"
  -- Baltic
  | .Latvian => some "lat" | .Lithuanian => some "lit"
  -- Finno-Ugric
  | .Hungarian => some "hun" | .Finnish => some "fin" | .Estonian => some "est"
  -- Adjacent non-SAE
  | .Welsh => some "wel" | .Irish => some "iri" | .Breton => some "bre"
  | .Basque => some "bsq" | .Turkish => some "tur" | .Maltese => some "mlt"
  -- Cofamilial IE outside SAE
  | .Persian => some "prs" | .HindiUrdu => some "hin"
  | .Armenian => some "arm"
  -- Worldwide non-IE non-adjacent
  | .Lezgian => some "lez" | .Georgian => some "geo"
  | .Mongolian => some "kha"  -- Khalkha
  | .Indonesian => some "ind" | .Yoruba => some "yor"
  | .Japanese => some "jpn" | .Mandarin => some "mnd" | .Swahili => some "swa"
  | .Quechua => some "qcu"  -- Cuzco

/-- Generic WALS classifier: language `l` has a value in WALS chapter `data`
that satisfies the boolean predicate `pred`. Returns `False` when `l` lacks
a WALS code or the chapter has no entry for it.

This is the bridging primitive for all WALS-grounded isoglosses below. Used as
`walsClassifies Datasets.WALS.F121A.allData (· == .particle)` to ask "does WALS
121A classify this language as having a particle comparative?". The result
is propositional with a derivable `Decidable` instance, so it slots directly
into `Finset.filter`. -/
def walsClassifies {V : Type} [BEq V]
    (data : List (Datasets.WALS.Datapoint V)) (pred : V → Bool)
    (l : SAELanguage) : Prop :=
  match l.toWALS with
  | none => False
  | some code => match Datasets.WALS.Datapoint.lookup data code with
    | none => False
    | some d => pred d.value = true

instance walsClassifies.instDecidable {V : Type} [BEq V]
    (data : List (Datasets.WALS.Datapoint V)) (pred : V → Bool)
    (l : SAELanguage) : Decidable (walsClassifies data pred l) := by
  unfold walsClassifies
  split
  · exact instDecidableFalse
  · split
    · exact instDecidableFalse
    · exact instDecidableEqBool _ _

-- ============================================================================
-- §2. The Twelve Major SAE Features (§2.1–§2.12)
-- ============================================================================

/-- The twelve "Europeanisms" identified in §2 of @cite{haspelmath-2001}.
Each is the subject of one of Maps 107.1–107.12. -/
inductive SAEFeature where
  /-- §2.1, Map 107.1: Both definite and indefinite articles present. -/
  | definiteIndefiniteArticles
  /-- §2.2, Map 107.2: Postnominal relative clauses introduced by an
      inflecting relative pronoun (e.g. *der/die/das*, *qui/que*). -/
  | relativeClausesWithRelPro
  /-- §2.3, Map 107.3: Transitive perfect formed by 'have' + past participle. -/
  | havePerfect
  /-- §2.4, Map 107.4: Predominant generalization of experiencer-as-nominative
      (English-style *I like it*) over inverting (*it pleases me*). -/
  | nominativeExperiencers
  /-- §2.5, Map 107.5: Canonical participial passive with copula + participle. -/
  | participialPassive
  /-- §2.6, Map 107.6: Anticausative-prominent inchoative–causative pairs. -/
  | anticausativeProminence
  /-- §2.7, Map 107.7: Dative external possessors
      (e.g. German *Die Mutter wäscht dem Kind die Haare*). -/
  | dativeExternalPossessor
  /-- §2.8, Map 107.8: Negative pronouns without obligatory verbal negation
      (V + NI type, e.g. French *personne ne vient*, German *niemand kommt*). -/
  | negativePronounsNoVerbalNeg
  /-- §2.9, Map 107.9: Particle comparatives (English *than*, Latin *quam*). -/
  | particleComparative
  /-- §2.10, Map 107.10: Equative constructions based on relative-clause
      structure (Catalan *tan Z com X*). -/
  | relativeBasedEquative
  /-- §2.11, Map 107.11: Strict subject agreement — subject affixes that
      cannot stand alone with referential force (German *ich arbeite*, not
      *arbeite*). -/
  | strictAgreement
  /-- §2.12, Map 107.12: Differentiated intensifier vs. reflexive forms
      (German *selbst* vs. *sich*, Russian *sam* vs. *sebja*). -/
  | intensifierReflexiveDifferentiation
  deriving DecidableEq, Repr, Fintype

-- ============================================================================
-- §3. Isoglosses: Languages Exhibiting Each Feature
-- ============================================================================

open SAELanguage

/-- WALS-derived: languages classified by F37A (Definite Articles) as having
a definite article (any of the three positive values). -/
def walsHasDefiniteArticle : Finset SAELanguage :=
  Finset.univ.filter (walsClassifies Datasets.WALS.F37A.allData fun v =>
    v == .definiteWordDistinctFromDemonstrative ||
    v == .demonstrativeWordUsedAsDefiniteArticle ||
    v == .definiteAffix)

/-- WALS-derived: languages classified by F38A (Indefinite Articles) as
having any indefinite article distinct from "no indefinite article" or
"indefinite-only of an unrelated kind". -/
def walsHasIndefiniteArticle : Finset SAELanguage :=
  Finset.univ.filter (walsClassifies Datasets.WALS.F38A.allData fun v =>
    v == .indefiniteWordDistinctFromOne ||
    v == .indefiniteWordSameAsOne ||
    v == .indefiniteAffix)

/-- WALS-derived intersection: languages with **both** a definite and an
indefinite article in the WALS data, matching @cite{haspelmath-2001} §2.1. -/
def walsArticleLgs : Finset SAELanguage :=
  walsHasDefiniteArticle ∩ walsHasIndefiniteArticle

/-- Languages with both definite and indefinite articles (Map 107.1).

The paper's reading: Romance, Germanic (except Icelandic), Greek, Albanian,
Macedonian, Bulgarian (the *edin* particle is treated as a budding
indefinite article), and Hungarian. Icelandic is excluded — it has a
suffixed definite article but no indefinite article. -/
def articleLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish,
   Greek, Albanian, Macedonian, Bulgarian, Hungarian}

/-- Languages with relative-pronoun relative clauses (Map 107.2). -/
def relProLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English,
   Russian, Polish, Czech, Bulgarian, SerboCroatian, Ukrainian,
   Greek, Hungarian, Georgian}

/-- Languages with the 'have'-perfect (Map 107.3).

@cite{haspelmath-2001} §2.3 restricts this isogloss to the Romance and
Germanic families plus a Balkan/peripheral fringe — Albanian, Greek,
Macedonian (an innovation: *ima* + verbal adjective), and (parts of) Czech.
Bulgarian and Serbo-Croatian retain the inherited Slavic 'be'+l-participle
perfect rather than the 'have' construction. -/
def havePerfectLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish, Icelandic,
   Czech, Albanian, Greek, Macedonian}

/-- Languages with predominant nominative-experiencer coding (Map 107.4). -/
def nomExpLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish,
   Polish, Czech, SerboCroatian, Bulgarian,
   Greek, Hungarian, Finnish, Estonian, Welsh, Irish, Breton}

/-- WALS-derived parallel: languages classified by F107A (Passive
Constructions) as having a passive present. F107A counts *any* passive
(periphrastic, morphological, etc.), so this is a strict superset of
Haspelmath's copula+participle criterion. -/
def walsPassiveLgs : Finset SAELanguage :=
  Finset.univ.filter (walsClassifies Datasets.WALS.F107A.allData (· == .present))

/-- Languages with a canonical participial passive (Map 107.5).

The Romance and Germanic copula+participle pattern, extended through Slavic
and Baltic and into Greek, Albanian, Macedonian, and Irish. -/
def particPassiveLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish, Icelandic,
   Russian, Polish, Czech, Bulgarian, SerboCroatian, Ukrainian,
   Greek, Albanian, Macedonian, Latvian, Lithuanian, Irish}

/-- Anticausative-prominent languages (Map 107.6: ≥ 70% anticausative).

@cite{haspelmath-2001} §2.6 / Map 107.6 marks only the languages whose
inchoative–causative pairs are anticausative-prominent on the Haspelmath
1993 figures. Romance is partially excluded (only French/Romanian register
as prominent; Italian/Spanish/Portuguese fall on the causative-prominent
side). The full SAE marking is German, French, Russian, Greek, Romanian,
Lithuanian, English. -/
def anticausativeLgs : Finset SAELanguage :=
  {German, French, English, Russian, Greek, Romanian, Lithuanian}

/-- Languages with dative external possessors (Map 107.7). -/
def dativeExtPossLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, Swedish, Norwegian, Danish, Icelandic,
   Russian, Polish, Czech, Bulgarian, SerboCroatian, Ukrainian,
   Greek, Albanian, Hungarian, Latvian, Lithuanian}

/-- WALS-derived parallel: languages classified by F115A (Negative
Indefinite Pronouns and Predicate Negation) as **not** requiring predicate
negation alongside the negative pronoun. Strict subset of Haspelmath's
criterion: F115A.noPredicateNegation captures only the rigid V+NI type
(predominantly Germanic), whereas Haspelmath's §2.8 also includes Romance
languages where the predicate negative is optional or weakening. -/
def walsVplusNILgs : Finset SAELanguage :=
  Finset.univ.filter
    (walsClassifies Datasets.WALS.F115A.allData (· == .noPredicateNegation))

/-- Languages with V + NI negation (no obligatory verbal negation; Map 107.8). -/
def vplusNILgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish, Icelandic,
   Albanian}

/-- WALS-derived parallel: languages classified by F121A (Comparative
Constructions) as having a particle comparative. -/
def walsParticleCompLgs : Finset SAELanguage :=
  Finset.univ.filter (walsClassifies Datasets.WALS.F121A.allData (· == .particle))

/-- Languages with particle comparatives (Map 107.9). -/
def particleCompLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish, Icelandic,
   Russian, Polish, Czech, Bulgarian, SerboCroatian, Ukrainian,
   Greek, Albanian, Macedonian, Hungarian, Finnish, Latvian, Lithuanian, Basque}

/-- Languages with relative-based equatives (Map 107.10). -/
def relEquativeLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English,
   Russian, Polish, Czech, Bulgarian, SerboCroatian, Ukrainian,
   Greek, Albanian, Hungarian, Finnish, Georgian}

/-- WALS-derived parallel: languages classified by F101A (Expression of
Pronominal Subjects) as requiring obligatory subject pronouns. -/
def walsStrictAgrLgs : Finset SAELanguage :=
  Finset.univ.filter (walsClassifies Datasets.WALS.F101A.allData
    (· == .obligatoryPronounsInSubjectPosition))

/-- Languages with strict subject agreement (Map 107.11).

A language has strict agreement when subject pronouns are obligatory even
in the presence of subject agreement on the verb (i.e., subject-agreement
affixes lack referential force on their own). Russian and the pro-drop
Romance languages (Italian, Spanish, Portuguese, Romanian) fail this
criterion. Welsh has rich agreement but allows pro-drop, so it is also
excluded. -/
def strictAgrLgs : Finset SAELanguage :=
  {French, German, Dutch, English, Swedish, Norwegian, Danish, Icelandic}

/-- WALS-derived parallel: languages classified by F47A (Intensifiers and
Reflexive Pronouns) as having differentiated forms. -/
def walsIntRefDiffLgs : Finset SAELanguage :=
  Finset.univ.filter
    (walsClassifies Datasets.WALS.F47A.allData (· == .differentiated))

/-- Languages with differentiated intensifier vs. reflexive forms (Map 107.12). -/
def intRefDiffLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish, Icelandic,
   Russian, Polish, Czech, Bulgarian, SerboCroatian, Ukrainian,
   Greek, Hungarian, Finnish, Latvian, Lithuanian}

/-- Dispatch from feature to its isogloss (as a `Finset`). -/
def isoglossFinset : SAEFeature → Finset SAELanguage
  | .definiteIndefiniteArticles            => articleLgs
  | .relativeClausesWithRelPro             => relProLgs
  | .havePerfect                           => havePerfectLgs
  | .nominativeExperiencers                => nomExpLgs
  | .participialPassive                    => particPassiveLgs
  | .anticausativeProminence               => anticausativeLgs
  | .dativeExternalPossessor               => dativeExtPossLgs
  | .negativePronounsNoVerbalNeg           => vplusNILgs
  | .particleComparative                   => particleCompLgs
  | .relativeBasedEquative                 => relEquativeLgs
  | .strictAgreement                       => strictAgrLgs
  | .intensifierReflexiveDifferentiation   => intRefDiffLgs

/-- Dispatch to the schema's `Isogloss = Finset SAELanguage` type. -/
def isoglossFor (f : SAEFeature) : Isogloss SAELanguage :=
  isoglossFinset f

-- ============================================================================
-- §4. The Reference Frame
-- ============================================================================

/-- The four reference samples for evaluating areality, per @cite{haspelmath-2001} §1.

* `area`: the core European languages (Romance, Germanic, Balkan, Balto-Slavic,
  marginal Finno-Ugric) that the paper proposes as SAE.
* `cofamilial`: other Indo-European branches (eastern IE: Iranian, Indic,
  Armenian) that lie outside the area; presence of a feature in these would
  point to PIE inheritance rather than areal contact.
* `adjacent`: geographically adjacent non-SAE languages (Celtic west, Turkic
  + Nakh-Daghestanian east, Semitic south); presence here would suggest a
  wider regional drift rather than a strictly European phenomenon.
* `world`: a small worldwide sample for the (iv) "not common worldwide"
  criterion. -/
def europeanReference : ArealReference SAELanguage where
  area :=
    {French, Italian, Spanish, Portuguese, Romanian, Catalan,
     German, Dutch, English, Swedish, Norwegian, Danish, Icelandic,
     Russian, Polish, Czech, Bulgarian, SerboCroatian, Ukrainian,
     Greek, Albanian, Macedonian, Hungarian, Finnish, Estonian, Latvian, Lithuanian}
  cofamilial := {Persian, HindiUrdu, Armenian}
  adjacent := {Welsh, Irish, Breton, Basque, Turkish, Maltese}
  world :=
    {Lezgian, Georgian, Mongolian, Indonesian, Yoruba, Japanese,
     Mandarin, Swahili, Quechua}
  area_nonempty := ⟨French, by decide⟩
  cofamilial_nonempty := ⟨Persian, by decide⟩
  adjacent_nonempty := ⟨Welsh, by decide⟩
  world_nonempty := ⟨Lezgian, by decide⟩

-- ============================================================================
-- §5. The SAE Linguistic Area
-- ============================================================================

/-- **Standard Average European** as a `LinguisticArea`: the 12 diagnostic
features of @cite{haspelmath-2001} §2 over the European/cofamilial/
adjacent/world reference frame.

`LinguisticArea` does not require every diagnostic feature to satisfy
the strict `IsAreal` predicate at any particular threshold — and
indeed, several SAE features (anticausative prominence, V+NI negation,
strict agreement) do not pass strict majority on Haspelmath's own data.
This matches the paper: @cite{haspelmath-2001}'s actual argument runs
through the cluster maps of §4, not through per-feature majority
thresholds.

Per-feature `IsArealAt` claims for the strongly-attested subset are
proved separately below; `clusterScore` and `nucleus` are computed
across all 12. -/
def sae : LinguisticArea SAELanguage SAEFeature where
  reference := europeanReference
  features := Finset.univ
  isogloss := isoglossFor

/-- Helper: discharge `IsArealAt default` for a single feature whose
isogloss meets the strict 1/2 criterion against `europeanReference`.
Each criterion bridges through `Isogloss.density_{gt,lt}_half_iff` to a
Nat-cardinal inequality that the kernel evaluates by `decide`. -/
private theorem isAreal_of_decide
    {I : Isogloss SAELanguage}
    (hArea : europeanReference.area.card < 2 * (europeanReference.area ∩ I).card)
    (hCofam : 2 * (europeanReference.cofamilial ∩ I).card < europeanReference.cofamilial.card)
    (hAdj : 2 * (europeanReference.adjacent ∩ I).card < europeanReference.adjacent.card)
    (hWorld : 2 * (europeanReference.world ∩ I).card < europeanReference.world.card) :
    IsAreal europeanReference I := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((default : ArealThresholds).inside) = 1/2 from rfl,
        Isogloss.density_gt_half_iff _ europeanReference.area_nonempty]
    exact hArea
  · rw [show ((default : ArealThresholds).outside) = 1/2 from rfl,
        Isogloss.density_lt_half_iff _ europeanReference.cofamilial_nonempty]
    exact hCofam
  · rw [show ((default : ArealThresholds).outside) = 1/2 from rfl,
        Isogloss.density_lt_half_iff _ europeanReference.adjacent_nonempty]
    exact hAdj
  · rw [show ((default : ArealThresholds).outside) = 1/2 from rfl,
        Isogloss.density_lt_half_iff _ europeanReference.world_nonempty]
    exact hWorld

/-- Definite + indefinite articles (Map 107.1) is areal at the strict 1/2
threshold: ubiquitous in the area, absent from cofamilial/adjacent/world
samples. -/
theorem articles_isAreal : IsAreal europeanReference (isoglossFor .definiteIndefiniteArticles) :=
  isAreal_of_decide (by decide) (by decide) (by decide) (by decide)

/-- The 'have'-perfect (Map 107.3) is areal at the strict 1/2 threshold. -/
theorem havePerfect_isAreal : IsAreal europeanReference (isoglossFor .havePerfect) :=
  isAreal_of_decide (by decide) (by decide) (by decide) (by decide)

/-- Particle comparatives (Map 107.9) are areal at the strict 1/2 threshold. -/
theorem particleComp_isAreal : IsAreal europeanReference (isoglossFor .particleComparative) :=
  isAreal_of_decide (by decide) (by decide) (by decide) (by decide)

/-- French sits in the SAE cluster nucleus: it exhibits all 12 diagnostic
features (the maximum cluster score). -/
theorem french_in_nucleus : French ∈ sae.nucleus := by
  unfold LinguisticArea.nucleus LinguisticArea.isopleth LinguisticArea.clusterScore
  decide

/-- German sits in the SAE cluster nucleus alongside French —
@cite{haspelmath-2001} §4's *Charlemagne Sprachbund* core. -/
theorem german_in_nucleus : German ∈ sae.nucleus := by
  unfold LinguisticArea.nucleus LinguisticArea.isopleth LinguisticArea.clusterScore
  decide

/-- The SAE feature inventory has 12 features, matching Maps 107.1–107.12
of @cite{haspelmath-2001}. -/
theorem sae_features_card : sae.features.card = 12 := by decide

end Phenomena.ArealTypology.Studies.Haspelmath2001
