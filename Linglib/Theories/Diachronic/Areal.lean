import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic

/-!
# Linguistic Areas (Sprachbünde)
@cite{haspelmath-2001}

A framework-neutral schema for typological *linguistic areas*
(Sprachbünde) — groups of geographically contiguous, often genealogically
heterogeneous languages that share structural features attributable to
contact rather than inheritance.

The schema follows the methodology of @cite{haspelmath-2001} but is
**gradient-first**, in the spirit of his §4 cluster maps: the primary
data per feature is an `ArealProfile` (a 4-tuple of densities — in-area,
in-cofamilial, in-adjacent, in-world). Binary judgments are derived from
profiles by comparison against an `ArealThresholds` parameter, defaulting
to the qualitative `1/2` cut.

## Layered structure

* **Profiles** (`ArealProfile`, `Isogloss.profile`): the primary
  computational concept — four densities per feature, ranging in `[0, 1]`.
  No threshold yet.
* **Thresholds** (`ArealThresholds`): a configurable cutoff parameter,
  with `default := ⟨1/2, 1/2⟩` matching @cite{haspelmath-2001}'s
  qualitative readings of "the great majority" / "lack". Stricter or
  paper-specific cutoffs (Heine-Kuteva, Grambank conventions) instantiate
  this without disturbing the schema.
* **Areality predicates** (`IsArealAt T R I`, `IsAreal := IsArealAt default`):
  the threshold-relative binary judgment, decomposed into the four
  Haspelmath criteria as named structure fields. Used à la carte: a
  study claims `IsAreal R I` for the features it can prove, with no
  expectation that *all* of an area's diagnostic features pass.
* **Linguistic areas** (`LinguisticArea L F`): bundles a reference frame,
  a feature set, and an isogloss assignment. No per-feature areality
  proof is bundled — @cite{haspelmath-2001}'s actual methodology is
  cluster-map analysis, recovered via `clusterScore` / `isopleth` /
  `nucleus`. Studies prove `IsArealAt` separately for whichever
  features pass the threshold of interest.

## Design notes

`Isogloss` is `Finset L`, not `Set L`: typology works over finite samples,
and `Finset` gives us computable density without `Classical`. Set algebra
(`∩`, `∪`, `⊆`, `\`) is inherited via mathlib's `Finset` lattice.

Reference samples carry `Finset.Nonempty` proofs. @cite{haspelmath-2001}
evaluates his criteria against actual evidence — there is no
"vacuous absence" in the paper — so requiring non-emptiness eliminates
the degenerate `0/0 = 0` density and lets the rational and Nat
formulations of the criteria agree on all in-use cases (cf.
`Isogloss.density_gt_iff` / `density_lt_iff`).

The threshold layer is parameterized rather than hard-coded: this lets
later modules (e.g. cluster-map studies, Grambank-style probabilistic
treatments) replicate paper-specific cutoffs without rewriting the
predicate.

## Relation to contemporary typology

The discrete-criterion framing is faithful to @cite{haspelmath-2001} but
is now widely seen as a first approximation. Subsequent work has
questioned whether any principled threshold separates Sprachbund from
non-Sprachbund, and large databases (Grambank, AUTOTYP) support
gradient, probabilistic treatments. The profile/threshold split here is
the bridge: a future `GradientLinguisticArea` sibling can replace
`Isogloss = Finset L` with `L → ℚ` strength functions and reuse
`ArealProfile` and `ArealThresholds` unchanged.
-/

namespace Theories.Diachronic.Areal

universe u v

-- ============================================================================
-- §1. Isoglosses
-- ============================================================================

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

-- ============================================================================
-- §2. Reference frames
-- ============================================================================

/-- The four reference samples needed to evaluate whether a feature is areal,
following @cite{haspelmath-2001} §1's criteria (i)–(iv).

Non-emptiness is required by construction: @cite{haspelmath-2001}'s
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

-- ============================================================================
-- §3. Areal profiles
-- ============================================================================

/-- The **areal profile** of an isogloss against a reference: the four
densities that @cite{haspelmath-2001}'s methodology compares. This is the
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

-- ============================================================================
-- §4. Thresholds
-- ============================================================================

/-- Numerical thresholds for @cite{haspelmath-2001}'s qualitative criteria.

@cite{haspelmath-2001} reads "the great majority" and "lack"
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

-- ============================================================================
-- §5. Areality predicates
-- ============================================================================

/-- The four-part Haspelmath criterion at a chosen `ArealThresholds`.

Each field captures one of @cite{haspelmath-2001} §1 criteria (i)–(iv),
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


-- ============================================================================
-- §6. Linguistic Areas
-- ============================================================================

/-- A **linguistic area** (Sprachbund) parameterized by a language type `L`
and a feature index type `F`.

An area bundles the three pieces of data needed for cluster-map analysis:
a reference frame, a finite set of diagnostic features, and an isogloss
assignment. The cluster-map methodology of @cite{haspelmath-2001} §4 is
recovered from this data via `featureProfile` (per-feature gradient),
`clusterScore` (per-language count), and `isopleth` / `nucleus` (cluster
bands and core).

`LinguisticArea` deliberately does **not** require every diagnostic
feature to satisfy `IsArealAt` at any particular threshold. Real
Sprachbund analyses (including @cite{haspelmath-2001}'s own SAE) propose
feature inventories where strong, weak, and tendency-only features
coexist; the binary `IsArealAt` predicate is applied à la carte by
downstream studies for whichever subset passes the threshold of
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
exhibits. This recovers @cite{haspelmath-2001} §4's cluster-map gradient
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
features. For SAE, @cite{haspelmath-2001} §4 identifies French and German
as the nuclear members — the *Charlemagne Sprachbund*.

`Nat` subtraction truncates at zero, so `features.card = 0` gives the
trivial `isopleth 0 = Set.univ`; the SAE study verifies the non-degenerate
case where `features.card = 12`. -/
def nucleus (A : LinguisticArea L F) : Set L :=
  A.isopleth (A.features.card - 1)

end LinguisticArea

end Theories.Diachronic.Areal
