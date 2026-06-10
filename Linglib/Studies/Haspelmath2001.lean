import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic
import Linglib.Data.WALS.Features.F37A
import Linglib.Data.WALS.Features.F38A
import Linglib.Data.WALS.Features.F47A
import Linglib.Data.WALS.Features.F101A
import Linglib.Data.WALS.Features.F107A
import Linglib.Data.WALS.Features.F115A
import Linglib.Data.WALS.Features.F121A
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Standard Average European: A Linguistic Area
[haspelmath-2001]

Formalization of [haspelmath-2001]'s argument that the core European
languages — the Romance, Germanic, Balkan, and Balto-Slavic families plus
the westernmost Finno-Ugric languages — form a *Sprachbund* (linguistic
area) called **Standard Average European** (SAE), defined by a dozen
shared structural features that are absent in the geographically and
genealogically adjacent languages.

The file first sets out a framework-neutral areal schema (§0:
`Isogloss`, `ArealReference`, `ArealProfile`, `IsArealAt`,
`LinguisticArea`) and then instantiates it: SAE is a
`LinguisticArea SAELanguage SAEFeature`
whose feature set is the twelve major Europeanisms of §2 of the paper, whose
reference frame is the four samples §1 demands (area, cofamilial, adjacent,
world), and whose areality is verified feature-by-feature against
[haspelmath-2001]'s Maps 107.1–107.12.

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
  `Data.WALS.F*.allData` via `walsClassifies`. The two are intentionally
  *not* unioned: where they disagree, that disagreement is a fact about
  Haspelmath's classification vs. WALS's encoding and should remain
  visible to readers and to bridge theorems.
* **Isoglosses are `Finset SAELanguage`** (the schema's `Isogloss` is a
  transparent abbreviation for `Finset L`). All filter predicates are
  decidable, so the four areality criteria reduce to `decide` against the
  computable rational `Isogloss.density`.
-/

namespace Haspelmath2001

-- ============================================================================
-- §0. The Areal Schema
-- ============================================================================

/-! A schema for typological *linguistic areas* (Sprachbünde) — groups of
geographically contiguous, often genealogically heterogeneous languages
that share structural features attributable to contact rather than
inheritance. The schema follows the methodology of [haspelmath-2001]
but is **gradient-first**, in the spirit of his §4 cluster maps: the
primary data per feature is an `ArealProfile` (a 4-tuple of densities —
in-area, in-cofamilial, in-adjacent, in-world). Binary judgments are
derived from profiles by comparison against an `ArealThresholds`
parameter, defaulting to the qualitative `1/2` cut.

Design notes. `Isogloss` is `Finset L`, not `Set L`: typology works over
finite samples, and `Finset` gives computable density without
`Classical`. Reference samples carry `Finset.Nonempty` proofs:
[haspelmath-2001] evaluates his criteria against actual evidence — there
is no "vacuous absence" in the paper — so requiring non-emptiness
eliminates the degenerate `0/0 = 0` density and lets the rational and
Nat formulations of the criteria agree on all in-use cases (cf.
`Isogloss.density_gt_iff` / `density_lt_iff`). The threshold layer is
parameterized rather than hard-coded so that stricter or paper-specific
cutoffs (Heine-Kuteva, Grambank conventions) can be instantiated without
rewriting the predicates; a future gradient treatment can replace
`Isogloss = Finset L` with `L → ℚ` strength functions and reuse
`ArealProfile` and `ArealThresholds` unchanged. -/

universe u v

/-- An **isogloss** is the set of languages exhibiting a given linguistic
feature. Following standard typological practice, isoglosses are sets of
languages, not the geometric boundaries between them.

This is a transparent abbreviation for `Finset L`; all finset operations
(`∩`, `∪`, `⊆`, `∈`, `\`, `Finset.card`) apply directly, and every
membership question is decidable. -/
abbrev Isogloss (L : Type u) := Finset L

namespace Isogloss

variable {L : Type u} [DecidableEq L]

/-- The proportion of languages in a finite reference sample `S` that lie
inside the isogloss `I`. With `Finset` operations this is a computable
rational in `[0, 1]` whenever `S` is non-empty; on `S = ∅` it returns the
ℚ-default `0/0 = 0`. -/
def density (I : Isogloss L) (S : Finset L) : ℚ :=
  (S ∩ I).card / S.card

@[simp] lemma density_empty (I : Isogloss L) :
    density I (∅ : Finset L) = 0 := by
  simp [density]

lemma density_nonneg (I : Isogloss L) (S : Finset L) : 0 ≤ density I S := by
  unfold density
  apply div_nonneg <;> exact_mod_cast Nat.zero_le _

lemma density_le_one (I : Isogloss L) (S : Finset L) : density I S ≤ 1 := by
  unfold density
  rcases Finset.eq_empty_or_nonempty S with hS | hS
  · subst hS; simp
  · have h : 0 < S.card := Finset.card_pos.mpr hS
    have hQ : (0 : ℚ) < (S.card : ℚ) := by exact_mod_cast h
    rw [div_le_one hQ]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left

/-- Bridge from the rational threshold form to a `Nat`-arithmetic form.
Requires `S` non-empty so that `density` is not the degenerate `0 / 0`.
This is the lemma proofs `rw` to reach a `decide`-amenable goal. -/
lemma density_gt_iff (I : Isogloss L) {S : Finset L} (hS : S.Nonempty) (θ : ℚ) :
    density I S > θ ↔ θ * S.card < (S ∩ I).card := by
  unfold density
  have h : 0 < S.card := Finset.card_pos.mpr hS
  have hQ : (0 : ℚ) < (S.card : ℚ) := by exact_mod_cast h
  rw [gt_iff_lt, lt_div_iff₀ hQ, mul_comm]

lemma density_lt_iff (I : Isogloss L) {S : Finset L} (hS : S.Nonempty) (θ : ℚ) :
    density I S < θ ↔ ((S ∩ I).card : ℚ) < θ * S.card := by
  unfold density
  have h : 0 < S.card := Finset.card_pos.mpr hS
  have hQ : (0 : ℚ) < (S.card : ℚ) := by exact_mod_cast h
  rw [div_lt_iff₀ hQ]

/-- Specialization of `density_gt_iff` to the `1/2` threshold. The Nat-form
RHS is fully kernel-reducible on concrete `Finset` data, so downstream
`decide` calls do not need to traverse `Rat.div`. -/
lemma density_gt_half_iff (I : Isogloss L) {S : Finset L} (hS : S.Nonempty) :
    density I S > 1 / 2 ↔ S.card < 2 * (S ∩ I).card := by
  rw [density_gt_iff I hS, div_mul_eq_mul_div, one_mul,
      div_lt_iff₀ (by norm_num : (0 : ℚ) < 2), mul_comm]
  exact_mod_cast Iff.rfl

/-- Specialization of `density_lt_iff` to the `1/2` threshold. -/
lemma density_lt_half_iff (I : Isogloss L) {S : Finset L} (hS : S.Nonempty) :
    density I S < 1 / 2 ↔ 2 * (S ∩ I).card < S.card := by
  rw [density_lt_iff I hS, div_mul_eq_mul_div, one_mul,
      lt_div_iff₀ (by norm_num : (0 : ℚ) < 2), mul_comm]
  exact_mod_cast Iff.rfl

end Isogloss

/-- The four reference samples needed to evaluate whether a feature is areal,
following [haspelmath-2001] §1's criteria (i)–(iv).

Non-emptiness is required by construction: [haspelmath-2001]'s
methodology presupposes positive evidence on each sample, and an empty
sample provides no information about the criterion it is meant to address.

For Standard Average European, the area is the core European languages,
the cofamilial sample is the eastern Indo-European branches (Iranian,
Indic, Armenian) — branches of Indo-European that lie outside the area,
used to rule out Proto-Indo-European inheritance — the adjacent sample
is the geographically neighboring non-Indo-European languages (Turkic,
Nakh-Daghestanian, Afro-Asiatic), and the world sample is a representative
global typological sample. -/
structure ArealReference (L : Type u) where
  /-- The candidate area itself (e.g. core European languages for SAE). -/
  area : Finset L
  /-- Other branches of the same families as the area's languages, used to
      rule out genealogical inheritance from a deep common ancestor.
      For SAE: eastern Indo-European (Iranian, Indic, Armenian). -/
  cofamilial : Finset L
  /-- Languages geographically adjacent to but outside the area, used to rule
      out a worldwide tendency that just happens to extend a bit further.
      For SAE: Turkic, Nakh-Daghestanian, Celtic (in some criteria), etc. -/
  adjacent : Finset L
  /-- A representative worldwide sample, used to rule out the feature being a
      cross-linguistic universal preference rather than an areal phenomenon. -/
  world : Finset L
  area_nonempty : area.Nonempty
  cofamilial_nonempty : cofamilial.Nonempty
  adjacent_nonempty : adjacent.Nonempty
  world_nonempty : world.Nonempty

/-- The **areal profile** of an isogloss against a reference: the four
densities that [haspelmath-2001]'s methodology compares. This is the
gradient datum from which both threshold-based binary judgments
(`IsArealAt`) and §4-style cluster maps are derived.

Profiles are framework-agnostic: a profile with `inArea = 0.85`,
`inCofamilial = 0.10`, `inAdjacent = 0.05`, `inWorld = 0.20` is a
canonical "areal" pattern regardless of any threshold convention. -/
structure ArealProfile where
  /-- Density of the feature in the candidate area. -/
  inArea : ℚ
  /-- Density of the feature in the cofamilial sample. -/
  inCofamilial : ℚ
  /-- Density of the feature in the geographically adjacent sample. -/
  inAdjacent : ℚ
  /-- Density of the feature in the worldwide sample. -/
  inWorld : ℚ
  deriving Repr

/-- The profile of an isogloss against a reference frame. -/
def Isogloss.profile {L : Type u} [DecidableEq L]
    (I : Isogloss L) (R : ArealReference L) : ArealProfile where
  inArea := Isogloss.density I R.area
  inCofamilial := Isogloss.density I R.cofamilial
  inAdjacent := Isogloss.density I R.adjacent
  inWorld := Isogloss.density I R.world

/-- The maximum density outside the area — the most permissive value
that the "lacks elsewhere" criteria must beat. -/
def ArealProfile.outsideMax (p : ArealProfile) : ℚ :=
  max p.inCofamilial (max p.inAdjacent p.inWorld)

/-- A natural areality score: in-area density minus the max outside
density. Range `[-1, 1]`, with higher values indicating stronger areal
patterning. This is one of several reasonable score aggregations and is
exposed for convenience; downstream studies are free to define their own. -/
def ArealProfile.contrastScore (p : ArealProfile) : ℚ :=
  p.inArea - p.outsideMax

/-- Numerical thresholds for [haspelmath-2001]'s qualitative criteria.

[haspelmath-2001] reads "the great majority" and "lack"
qualitatively; this structure exposes the cutoffs so that:

* the default `⟨1/2, 1/2⟩` is the natural first approximation,
* stricter conventions (e.g. inside = 3/4, outside = 1/4) can be
  specified per-study,
* a future probabilistic generalization can plug in here without
  disturbing the rest of the schema. -/
structure ArealThresholds where
  /-- "Majority inside" cutoff: a feature is areal-at-`T` only if the
      area's density exceeds this. -/
  inside : ℚ := 1 / 2
  /-- "Lacks outside" cutoff: cofamilial / adjacent / world densities
      must fall below this. -/
  outside : ℚ := 1 / 2

instance : Inhabited ArealThresholds := ⟨{}⟩

/-- The four-part Haspelmath criterion at a chosen `ArealThresholds`.

Each field captures one of [haspelmath-2001] §1 criteria (i)–(iv),
parameterized by the threshold `T`. With `T = default` this is the
plain "majority in / minority out" reading. -/
structure IsArealAt {L : Type u} [DecidableEq L]
    (T : ArealThresholds) (R : ArealReference L) (I : Isogloss L) : Prop where
  /-- Criterion (i): the area-internal density beats the inside threshold. -/
  area_majority : Isogloss.density I R.area > T.inside
  /-- Criterion (iii): cofamilial density falls below the outside threshold,
      ruling out common genealogical inheritance. -/
  cofamilial_lacks : Isogloss.density I R.cofamilial < T.outside
  /-- Criterion (ii): adjacent-non-area density falls below the outside
      threshold, ruling out a wider regional drift. -/
  adjacent_lacks : Isogloss.density I R.adjacent < T.outside
  /-- Criterion (iv): worldwide density falls below the outside threshold,
      ruling out a universal cross-linguistic preference. -/
  not_worldwide : Isogloss.density I R.world < T.outside

/-- Areality at the default Haspelmath threshold (`⟨1/2, 1/2⟩`). -/
abbrev IsAreal {L : Type u} [DecidableEq L]
    (R : ArealReference L) (I : Isogloss L) : Prop :=
  IsArealAt default R I

/-- A **linguistic area** (Sprachbund) parameterized by a language type `L`
and a feature index type `F`.

An area bundles the three pieces of data needed for cluster-map analysis:
a reference frame, a finite set of diagnostic features, and an isogloss
assignment. The cluster-map methodology of [haspelmath-2001] §4 is
recovered from this data via `featureProfile` (per-feature gradient),
`clusterScore` (per-language count), and `isopleth` / `nucleus` (cluster
bands and core).

`LinguisticArea` deliberately does **not** require every diagnostic
feature to satisfy `IsArealAt` at any particular threshold. Real
Sprachbund analyses (including [haspelmath-2001]'s own SAE) propose
feature inventories where strong, weak, and tendency-only features
coexist; the binary `IsArealAt` predicate is applied à la carte by
downstream proofs for whichever subset passes the threshold of
interest. -/
structure LinguisticArea (L : Type u) (F : Type v) [DecidableEq L] where
  /-- The reference frame against which areality is judged. -/
  reference : ArealReference L
  /-- The diagnostic features proposed for this Sprachbund. -/
  features : Finset F
  /-- The isogloss assigned to each feature: which languages exhibit it. -/
  isogloss : F → Isogloss L

namespace LinguisticArea

variable {L : Type u} {F : Type v} [DecidableEq L] [DecidableEq F]

/-- The areal profile of feature `f`: its four densities under the area's
reference frame. The primary gradient datum per feature. -/
def featureProfile (A : LinguisticArea L F) (f : F) : ArealProfile :=
  (A.isogloss f).profile A.reference

/-- The contrast score of feature `f`: in-area density minus the max
outside density. Range `[-1, 1]`, with `IsArealAt` features all scoring
above `T.inside - T.outside`. -/
def featureScore (A : LinguisticArea L F) (f : F) : ℚ :=
  (A.featureProfile f).contrastScore

/-- The **cluster score** of a language: how many of the area's features it
exhibits. This recovers [haspelmath-2001] §4's cluster-map gradient
membership from the discrete feature-by-feature data. -/
def clusterScore (A : LinguisticArea L F) (l : L) : ℕ :=
  (A.features.filter fun f => l ∈ A.isogloss f).card

omit [DecidableEq F] in
/-- The cluster score is bounded above by the total number of features. -/
lemma clusterScore_le_card_features (A : LinguisticArea L F) (l : L) :
    A.clusterScore l ≤ A.features.card :=
  Finset.card_filter_le _ _

/-- The **k-isopleth**: the set of languages exhibiting at least `k` of the
area's features. Used to draw cluster maps at varying tightness. -/
def isopleth (A : LinguisticArea L F) (k : ℕ) : Set L :=
  {l | k ≤ A.clusterScore l}

omit [DecidableEq F] in
/-- Isopleths are antitone in `k`: a stricter threshold yields a smaller set. -/
lemma isopleth_anti (A : LinguisticArea L F) {j k : ℕ} (h : j ≤ k) :
    A.isopleth k ⊆ A.isopleth j :=
  fun _ hl => Nat.le_trans h hl

/-- The **nucleus**: languages exhibiting all but at most one of the area's
features. For SAE, [haspelmath-2001] §4 identifies French and German
as the nuclear members — the *Charlemagne Sprachbund*.

`Nat` subtraction truncates at zero, so `features.card = 0` gives the
trivial `isopleth 0 = Set.univ`; the SAE proofs below verify the
non-degenerate case where `features.card = 12`. -/
def nucleus (A : LinguisticArea L F) : Set L :=
  A.isopleth (A.features.card - 1)

end LinguisticArea

-- ============================================================================
-- §1. The Language Sample
-- ============================================================================

/-- Languages surveyed by [haspelmath-2001], partitioned by their role
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
in `Data.WALS.Features.*`). Returns `none` for languages outside the WALS
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
`walsClassifies Data.WALS.F121A.allData (· == .particle)` to ask "does WALS
121A classify this language as having a particle comparative?". The result
is propositional with a derivable `Decidable` instance, so it slots directly
into `Finset.filter`. -/
def walsClassifies {V : Type} [BEq V]
    (data : List (Data.WALS.Datapoint V)) (pred : V → Bool)
    (l : SAELanguage) : Prop :=
  match l.toWALS with
  | none => False
  | some code => match Data.WALS.Datapoint.lookup data code with
    | none => False
    | some d => pred d.value = true

instance walsClassifies.instDecidable {V : Type} [BEq V]
    (data : List (Data.WALS.Datapoint V)) (pred : V → Bool)
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

/-- The twelve "Europeanisms" identified in §2 of [haspelmath-2001].
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
  Finset.univ.filter (walsClassifies Data.WALS.F37A.allData fun v =>
    v == .definiteWordDistinctFromDemonstrative ||
    v == .demonstrativeWordUsedAsDefiniteArticle ||
    v == .definiteAffix)

/-- WALS-derived: languages classified by F38A (Indefinite Articles) as
having any indefinite article distinct from "no indefinite article" or
"indefinite-only of an unrelated kind". -/
def walsHasIndefiniteArticle : Finset SAELanguage :=
  Finset.univ.filter (walsClassifies Data.WALS.F38A.allData fun v =>
    v == .indefiniteWordDistinctFromOne ||
    v == .indefiniteWordSameAsOne ||
    v == .indefiniteAffix)

/-- WALS-derived intersection: languages with **both** a definite and an
indefinite article in the WALS data, matching [haspelmath-2001] §2.1. -/
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

[haspelmath-2001] §2.3 restricts this isogloss to the Romance and
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
  Finset.univ.filter (walsClassifies Data.WALS.F107A.allData (· == .present))

/-- Languages with a canonical participial passive (Map 107.5).

The Romance and Germanic copula+participle pattern, extended through Slavic
and Baltic and into Greek, Albanian, Macedonian, and Irish. -/
def particPassiveLgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Romanian, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish, Icelandic,
   Russian, Polish, Czech, Bulgarian, SerboCroatian, Ukrainian,
   Greek, Albanian, Macedonian, Latvian, Lithuanian, Irish}

/-- Anticausative-prominent languages (Map 107.6: ≥ 70% anticausative).

[haspelmath-2001] §2.6 / Map 107.6 marks only the languages whose
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
    (walsClassifies Data.WALS.F115A.allData (· == .noPredicateNegation))

/-- Languages with V + NI negation (no obligatory verbal negation; Map 107.8). -/
def vplusNILgs : Finset SAELanguage :=
  {French, Italian, Spanish, Portuguese, Catalan,
   German, Dutch, English, Swedish, Norwegian, Danish, Icelandic,
   Albanian}

/-- WALS-derived parallel: languages classified by F121A (Comparative
Constructions) as having a particle comparative. -/
def walsParticleCompLgs : Finset SAELanguage :=
  Finset.univ.filter (walsClassifies Data.WALS.F121A.allData (· == .particle))

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
  Finset.univ.filter (walsClassifies Data.WALS.F101A.allData
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
    (walsClassifies Data.WALS.F47A.allData (· == .differentiated))

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

/-- The four reference samples for evaluating areality, per [haspelmath-2001] §1.

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
features of [haspelmath-2001] §2 over the European/cofamilial/
adjacent/world reference frame.

`LinguisticArea` does not require every diagnostic feature to satisfy
the strict `IsAreal` predicate at any particular threshold — and
indeed, several SAE features (anticausative prominence, V+NI negation,
strict agreement) do not pass strict majority on Haspelmath's own data.
This matches the paper: [haspelmath-2001]'s actual argument runs
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
[haspelmath-2001] §4's *Charlemagne Sprachbund* core. -/
theorem german_in_nucleus : German ∈ sae.nucleus := by
  unfold LinguisticArea.nucleus LinguisticArea.isopleth LinguisticArea.clusterScore
  decide

/-- The SAE feature inventory has 12 features, matching Maps 107.1–107.12
of [haspelmath-2001]. -/
theorem sae_features_card : sae.features.card = 12 := by decide

end Haspelmath2001
