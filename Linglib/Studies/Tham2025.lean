import Linglib.Semantics.Gradability.Aggregation
import Linglib.Semantics.Aspect.DegreeAchievement
import Linglib.Semantics.Degree.Basic
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Studies.Sassoon2013
import Linglib.Studies.Solt2018Multidim
import Linglib.Studies.BeaversKoontzGarboden2020
import Linglib.Core.Order.Boundedness
import Linglib.Semantics.Degree.HasMeasure

/-!
# [tham-2025]

Shiao Wei Tham (2025). Multidimensionality and the scalar components of
physical disturbance predicates. *Glossa: a journal of general linguistics*
10(1): 1–30.

## Key claims

Physical disturbance predicates (*crack/cracked*, *dent/dented*,
*scratch/scratched*) — Tham's "host irregularities" in the sense of
[karmo-1977] — are associated with a **totally closed, multi-point
scale**. Four substantive claims:

1. **Contra [rappaport-hovav-2014]**: *crack*/*cracked* is NOT
   two-point (like *die*/*dead*). The verb allows durative *for*
   adverbials and the adjective accepts comparatives (*more cracked*).
2. **Contra [rotstein-winter-2004]**: *cracked* is NOT a "partial"
   adjective with a lower-bounded, upper-open scale. It accepts
   *completely* (upper bound) and *partially* (lower bound).
3. **Multidimensional in the sense of [sassoon-2013]**: dimensions
   are *quantity* of disturbances, *quality* (depth, length), and
   *spatial positioning* (centrality, array, functional impact).
4. **Lower bound = physical instantiation** (objective: no faultless
   disagreement under simple predication, §3.2.1). **Upper bound =
   spatial extent of host** (structural integrity limit).

The verb-adjective asymmetry: the adjective allows quantificational
access to individual dimensions via *respect* PPs and operators; the
verb allows only conceptual access (§4.2).

## File organization

- §1 Schema for disturbance predicates + 3 attested data points
- §2 Contrast predicates (*die/dead*, *shatter/shattered*, *damage/damaged*)
- §3 Total closure (*completely* + *partially*)
- §4 Variable telicity + result-state entailment
- §5 Objective simple predication, subjective degree modification (§3.2)
- §6 Deverbal adjectives don't entail a preceding change of state (§5.1)
- §7 Multidimensionality + verb-adjective asymmetry (§3.1, §4.2)
- §8 Substrate readouts: Fragment scale-types match Tham's classification
- §9 Cross-paper engagement: Kennedy-Levin pipeline (variable telicity gap)
- §10 Cross-paper engagement: Hay-Kennedy-Levin matrix refutation
- §11 Cross-paper engagement: Kennedy 2007 licensing convergence
- §12 Cross-paper engagement: Sassoon 2013 binding insufficiency (real
     refutation against `MultidimAdj` apparatus)
- §13 Tham eq. 47b: spatially-normalized weighted measure (vase example
     + bounded-by-one via substrate's `spatialNormalizedScore_le_one`)
- §14 Cross-paper engagement: Beavers & Koontz-Garboden 2020 root
     eventivity (Tham §5.1 refutes strict root → deverbal-adjective
     result-state inheritance, against B&KG's `crack : Root :=
     ⟨"crack", [.becomesState "fissured", .hasCause]⟩`)
- §15 Cross-paper engagement: Waldon et al. 2023 normalization contrast
     (substrate-level: shared numerator, divergent denominator)
- §16 Cross-paper engagement: Solt 2018 SuB reciprocal bridge
     (substrate's `_le_one` consumed by both files at different
     specializations)
- §17 Cross-paper engagement: Kennedy 2007 Interpretive Economy vs
     Tham §3.2.1 lower bound — wedge made Lean-checkable
- §18 Cross-paper engagement: Solt 2018 multidim typology — *cracked*
     belongs to the AbsPart class (partially-closed, physical-property,
     intermediate ordering subjectivity)

## Attestation policy

Tham's primary case study is *cracked*. *dented* and *scratched* are
included in most data points (e.g., ex. 11a/11b for *more dented/scratched*,
18a/18b/18c for *badly scratched/dented/cracked*, 36a/36b/36c for
*completely dented/cracked/scratched*). A few fields are stipulated by
class-level extension where Tham only attests *cracked* directly; these
are flagged in comments as "extends crack" rather than dropped, since
the paper's argument is that disturbance predicates are a uniform class.
-/

namespace Tham2025

open Core.Order (Boundedness LicensingPipeline)
open Semantics.Gradability (DimensionBindingType GradableAdjective
  adjMeasure closedAdj_licensed conjunctiveBinding disjunctiveBinding)
open Semantics.Gradability.Aggregation (weightedScore boolMeasures
  spatialNormalizedScore spatialNormalizedBinding)
open Features.DegreeAchievement (DegreeAchievementScale)
open Semantics.Lexical
open Semantics.Degree (interpretiveEconomy)
open English.Predicates

-- ════════════════════════════════════════════════════
-- § 1. Disturbance predicate schema + data
-- ════════════════════════════════════════════════════

/-- The three dimensions Tham identifies for disturbance predicates
    (§3.1, §3.4): *quantity* of disturbances (number), *quality*
    (severity — depth, length), and *positioning* (centrality, array,
    functional impact). Used to encode dimension-selection facts about
    individual modifiers (e.g. *much* selects only quantity per §3.3). -/
inductive DisturbanceDimension where
  /-- Number of disturbances (Tham §3.1, ex. 23a/24a/25a). -/
  | quantity
  /-- Severity: depth, length, width (Tham §3.1, ex. 23b/24b/25b). -/
  | quality
  /-- Centrality, array, functional impact (Tham §3.4, ex. 29). -/
  | positioning
  deriving Repr, BEq, DecidableEq

/-- A physical disturbance predicate entry, encoding the scalar and
    distributional properties argued for in Tham (2025).

    The schema separates **adverb compatibility** (closure tests) from
    **subjectivity profile** (objective lower bound vs subjective degree
    modification, §3.2) and **change-of-state status** (whether the
    deverbal adjective entails a preceding event of change, §5.1). -/
structure DisturbancePredicate where
  /-- Root form (shared by verb, adjective, and count noun). -/
  root : String
  /-- Whether the root has a count noun form (*a crack*, *a dent*).
      Distinguishes disturbance predicates from other CoS predicates
      like *shatter* (no \**a shatter*) and *damage* (mass only). -/
  hasCountNoun : Bool
  /-- Whether the deverbal adjective is gradable (*more cracked*). -/
  adjGradable : Bool
  /-- Compatible with *completely* (tests upper closure). -/
  adjCompletely : Bool
  /-- Compatible with *partially* (tests lower closure). -/
  adjPartially : Bool
  /-- Compatible with *slightly* (indicates lower bound). -/
  adjSlightly : Bool
  /-- Compatible with *badly*/*well* (degree modifier for closed scales). -/
  adjBadly : Bool
  /-- Which dimensions *much* selects when modifying the deverbal adjective.
      Tham §3.3 (p. 16) argues *much* "evoke[s] only the 'quantity'
      dimension" — selectivity, not mere compatibility. The empty list
      encodes *much*-incompatibility; `[.quantity]` encodes Tham's
      single-dimension claim. -/
  adjMuchSelects : List DisturbanceDimension
  /-- Whether the verb allows durative *for X* adverbials (atelic reading). -/
  verbForX : Bool
  /-- Whether the verb allows *in X* adverbials (telic reading). -/
  verbInX : Bool
  /-- Whether the verb is compatible with *completely*. -/
  verbCompletely : Bool
  /-- Whether the verb is compatible with *badly*. -/
  verbBadly : Bool
  /-- Whether the adjective allows *respect* PPs
      (*dented with respect to dent size*). -/
  adjRespectPP : Bool
  /-- Whether the verb allows *respect* PPs (degraded for intransitive
      disturbance CoS verbs, but accepted for causative uses). -/
  verbRespectPP : Bool
  /-- Whether verb + *in X* entails the result state
      (*cracked in a minute* ⊨ *is cracked*, Tham (17a)). -/
  verbInXEntailsResult : Bool
  /-- Tham §3.2.1: simple predication is OBJECTIVE — no faultless
      disagreement (ex. 26: "*My watch face is scratched* / *No, it's
      smooth*" — one speaker must be mistaken). -/
  simplePredicationObjective : Bool
  /-- Tham §3.2.2: degree-modified predication is SUBJECTIVE — faultless
      disagreement is possible (ex. 27: "*badly scratched* / *not badly
      scratched at all, the scratch is long but not deep*"). -/
  degreeModifiedSubjective : Bool
  /-- Tham §5.1: the deverbal adjective does NOT entail a preceding
      event of change. (ex. 45a–c: pumpkin skin texture, computer-
      modelled dented helmet, scratched-look decal — all describe
      surfaces that have not undergone a CoS event.) -/
  adjEntailsPrecedingChange : Bool
  deriving Repr, BEq

-- Disturbance predicates (§2.1, §2.3–2.4, §3, §3.2, §4, §5.1)

def crack : DisturbancePredicate where
  root := "crack"
  hasCountNoun := true     -- "a crack" (3)
  adjGradable := true      -- "more cracked" (10c)
  adjCompletely := true    -- "completely cracked" (15a, 20a)
  adjPartially := true     -- "partially cracked" (15b, 21a)
  adjSlightly := true      -- "cracked slightly" (16)
  adjBadly := true         -- "badly cracked" (18c)
  adjMuchSelects := [.quantity]  -- "much cracked" (30a) selects only quantity per §3.3
  verbForX := true         -- "cracked for two days" (10a)
  verbInX := true          -- "cracked in a minute" (14a)
  verbCompletely := true   -- "completely cracked" (36b)
  verbBadly := true        -- "cracked badly" (37a)
  adjRespectPP := true     -- (29) "this mirror is more badly cracked than that one with respect to..."
  verbRespectPP := false   -- "??cracked badly in every respect" (41b)
  verbInXEntailsResult := true       -- (17a) "cracked completely/slightly ⊨ is cracked"
  simplePredicationObjective := true -- (26) crack-analogue: no faultless disagreement
  degreeModifiedSubjective := true   -- (27) "badly scratched" admits faultless disagreement
  adjEntailsPrecedingChange := false -- (45a) cracked pumpkin (no CoS event)

def dent : DisturbancePredicate where
  root := "dent"
  hasCountNoun := true     -- "a dent" (3)
  adjGradable := true      -- "more dented" (11a)
  adjCompletely := true    -- "completely dented" (20b)
  adjPartially := true     -- "partially dented" (21b)
  adjSlightly := true      -- extends crack (16): no direct attestation in paper
  adjBadly := true         -- "badly dented" (18b)
  adjMuchSelects := [.quantity]  -- "much dented" (30b) selects only quantity per §3.3
  verbForX := true         -- extends crack (10a): no direct attestation in paper
  verbInX := true          -- extends crack (14a): no direct attestation in paper
  verbCompletely := true   -- "completely dented" (36a)
  verbBadly := true        -- "dented badly" (37c)
  adjRespectPP := true     -- "dented with respect to dent size" (28a, 42a)
  verbRespectPP := false   -- "?dented severely with respect to dent size" (42b)
  verbInXEntailsResult := true       -- extends class-level claim (17a)
  simplePredicationObjective := true -- extends §3.2.1 class-level claim
  degreeModifiedSubjective := true   -- (28a) "more dented w.r.t. dent size, more dented w.r.t. number"
  adjEntailsPrecedingChange := false -- (45b) computer-modelled dented helmet

def scratch : DisturbancePredicate where
  root := "scratch"
  hasCountNoun := true     -- "a scratch" (3)
  adjGradable := true      -- "more scratched" (11b)
  adjCompletely := true    -- "completely scratched" (20c)
  adjPartially := true     -- "partially scratched" (21c)
  adjSlightly := true      -- extends crack (16)
  adjBadly := true         -- "badly scratched" (18a, 22a)
  adjMuchSelects := [.quantity]  -- "much scratched" (30c) selects only quantity per §3.3
  verbForX := true         -- extends crack (10a)
  verbInX := true          -- extends crack (14a)
  verbCompletely := true   -- "completely scratched" (36c)
  verbBadly := true        -- "scratched it badly" (37b)
  adjRespectPP := true     -- extends class-level claim (28-pattern)
  verbRespectPP := false   -- degraded for intransitive (§4.2 class-level)
  verbInXEntailsResult := true       -- extends class-level claim (17a)
  simplePredicationObjective := true -- (26) "*My watch face is scratched / No, it's smooth*"
  degreeModifiedSubjective := true   -- (27) "*not badly scratched at all*"
  adjEntailsPrecedingChange := false -- (45c) decal "scratched surface" (no CoS event)

def allDisturbancePredicates : List DisturbancePredicate :=
  [crack, dent, scratch]

-- ════════════════════════════════════════════════════
-- § 2. Contrast predicates
-- ════════════════════════════════════════════════════

/-- Data for predicates that contrast with disturbance predicates,
    demonstrating that the disturbance pattern is class-specific. -/
structure ContrastPredicate where
  root : String
  hasCountNoun : Bool
  adjGradable : Bool
  verbDurative : Bool
  deriving Repr, BEq

/-- *die/dead*: two-point scale, non-gradable (#*more dead*), punctual.
    Tham §2.3: *crack* ≠ *die* despite both being Levin 45.1. Tham's
    Table 1 (= [rappaport-hovav-2014] Table 1) groups both as
    "Two-valued" — Tham contests this for *crack*. -/
def dieDead : ContrastPredicate where
  root := "die"
  hasCountNoun := false     -- *a death* (derived), not #*a die*
  adjGradable := false      -- #*more dead* (fn. 6)
  verbDurative := false     -- #*died for two hours*

/-- *shatter/shattered*: punctual, non-gradable. Like *die/dead*:
    describes physical objects but NOT a disturbance predicate. Crucial
    for showing that gradability of disturbance predicates is NOT simply
    a consequence of applying to physical objects. -/
def shatterShattered : ContrastPredicate where
  root := "shatter"
  hasCountNoun := false     -- #*a shatter* (5b)
  adjGradable := false      -- ??*more shattered* (12c)
  verbDurative := false     -- #*shatter for two minutes* (12b)

/-- *damage/damaged*: has mass noun (*damage to X*) but NOT count noun
    (\**a damage in X*). Not a disturbance predicate per Tham (4). -/
def damageDamaged : ContrastPredicate where
  root := "damage"
  hasCountNoun := false     -- (4a): *\*There is a damage in X*
  adjGradable := true       -- *more damaged*
  verbDurative := true

-- ════════════════════════════════════════════════════
-- § 3. Total closure (*completely* + *partially*)
-- ════════════════════════════════════════════════════

/-- All disturbance predicates accept both *completely* (upper bound)
    and *partially* (lower bound), demonstrating total closure. -/
theorem all_disturbance_totally_closed :
    allDisturbancePredicates.all
      (fun p => p.adjCompletely && p.adjPartially) = true := rfl

/-- All disturbance predicates are gradable (contra two-point
    classification in [rappaport-hovav-2014] Table 1). -/
theorem all_disturbance_gradable :
    allDisturbancePredicates.all (fun p => p.adjGradable) = true := rfl

/-- All disturbance predicates have a count noun form, distinguishing
    them from other CoS predicates (§2.1, ex. 3–5). -/
theorem all_disturbance_have_count_noun :
    allDisturbancePredicates.all (fun p => p.hasCountNoun) = true := rfl

/-- Contrast: non-disturbance predicates are NOT gradable. -/
theorem die_not_gradable : dieDead.adjGradable = false := rfl
theorem shatter_not_gradable : shatterShattered.adjGradable = false := rfl

/-- Contrast: non-disturbance verbs lack durative readings. -/
theorem die_not_durative : dieDead.verbDurative = false := rfl
theorem shatter_not_durative : shatterShattered.verbDurative = false := rfl

-- ════════════════════════════════════════════════════
-- § 4. Variable telicity + result-state entailment
-- ════════════════════════════════════════════════════

/-! Tham §2.4 (10), (14): physical disturbance verbs allow BOTH telic
    (*cracked in a minute*, ex. 14a) and atelic (*cracked for a while*,
    ex. 14b) readings. They differ from canonical degree achievements
    like *cool* in that BOTH readings entail the result state (Tham
    (17a): *cracked completely/slightly* ⊨ *is cracked*; contrast Tham
    (13b) "soup cooled for ten minutes" ⊭ "is cool"). The class-level
    claim "disturbance verbs always entail their result state" is
    asserted at Tham §2.4. -/

/-- Physical disturbance verbs allow BOTH telic and atelic readings,
    unlike standard degree achievements which have only one. -/
theorem crack_allows_both_aspects :
    crack.verbInX = true ∧ crack.verbForX = true := ⟨rfl, rfl⟩

/-- All disturbance verbs entail their result state under both *in X*
    and *for X* readings. -/
theorem disturbance_always_entails_result :
    allDisturbancePredicates.all (fun p => p.verbInXEntailsResult) = true := rfl

-- ════════════════════════════════════════════════════
-- § 5. Objective simple predication, subjective degree modification
-- ════════════════════════════════════════════════════

/-! Tham §3.2 — the central evidence for the **lower bound = physical
    instantiation** claim. Two minimally-different exchanges:

    (26)  My watch face is scratched. / No, it's smooth.       ← objective
    (27)  My watch face is badly scratched. / No, it's not badly scratched
          at all, the scratch is long but not deep.            ← subjective

    In (26) one speaker must be mistaken — disagreement is NOT faultless.
    In (27) the disagreement IS faultless (about *degree* of damage). The
    asymmetry follows from the lower bound being "physically bounded"
    (Tham p. 14): "Whether a physical disturbance does exist on a host
    entity, however, seems to be a matter of objective observation. This
    is presumably because the state they describe has a minimum
    instantiation that is physically bounded." -/

/-- All disturbance predicates: simple predication is objective. -/
theorem all_disturbance_simple_predication_objective :
    allDisturbancePredicates.all (fun p => p.simplePredicationObjective) = true :=
  rfl

/-- All disturbance predicates: degree-modified predication is subjective. -/
theorem all_disturbance_degree_modified_subjective :
    allDisturbancePredicates.all (fun p => p.degreeModifiedSubjective) = true :=
  rfl

/-- The Tham §3.2 wedge: simple predication is objective but
    degree-modified predication is subjective. This is the central
    asymmetry from which the lower bound = physical instantiation /
    upper bound = host extent split is derived. -/
theorem tham_objective_subjective_wedge :
    allDisturbancePredicates.all (fun p =>
      p.simplePredicationObjective && p.degreeModifiedSubjective) = true := rfl

-- ════════════════════════════════════════════════════
-- § 6. Adjectives don't entail a preceding change
-- ════════════════════════════════════════════════════

/-! Tham §5.1 — the second-most-load-bearing claim after multi-
    dimensionality. Tham (p. 23) writes that deverbal disturbance
    adjectives "do not necessarily express the resultant state of an
    event of change" (emphasis added). The (45) examples are
    EXISTENCE PROOFS of uses without a preceding CoS event:

    (45)  a. The white pumpkin had a completely **cracked surface**.
              (= textured pumpkin skin; no cracking event)
          b. My computer model has a **dented surface**.
              (= visual modeling effect; no denting event)
          c. **Scratched Surface** vinyl decal for Google Pixel.
              (= graphical pattern; no scratching event)

    The Bool field `adjEntailsPrecedingChange = false` encodes the
    existential possibility — at least some uses of the deverbal
    adjective lack the entailment. The class-level claim is NOT a
    universal "always lacks" but the existential "does not necessarily
    express." Compare related discussion of *bend/bent* and
    *darken/darkened* in [gawron-2009] and [koontz-garboden-2011]. -/

/-- All disturbance adjectives have at least one well-attested use
    where the deverbal adjective does NOT entail a preceding CoS
    event (Tham §5.1 ex. 45a/b/c). The theorem name reflects the
    existential nature of Tham's claim — it does not assert "no use
    ever entails preceding change," only that the entailment is
    cancellable. -/
theorem all_disturbance_adj_can_lack_preceding_change :
    allDisturbancePredicates.all
      (fun p => !p.adjEntailsPrecedingChange) = true := rfl

-- ════════════════════════════════════════════════════
-- § 7. Multidimensionality + verb-adjective asymmetry
-- ════════════════════════════════════════════════════

/-! Disturbance adjectives have three dimensions (§3.1):
    - **Quantity**: number of disturbances (23a, 24a, 25a)
    - **Quality**: severity — depth, length, width (23b, 24b, 25b)
    - **Positioning**: centrality, array pattern, functional impact (29)

    The adjective allows **quantificational** access to individual
    dimensions via *respect* PPs and quantificational operators (*every
    respect*, *at least with respect to*); the verb allows only
    **conceptual** access (§4.2). This aligns with [ruiz-faroldi-2022]'s
    quantificational/conceptual typology of multidimensionality. -/

/-- Adjective: quantificational access (respect PPs accepted). -/
theorem adj_access_quantificational :
    allDisturbancePredicates.all (fun p => p.adjRespectPP) = true := rfl

/-- Verb: conceptual access only (respect PPs degraded). -/
theorem verb_access_conceptual :
    allDisturbancePredicates.all (fun p => !p.verbRespectPP) = true := rfl

/-- *much* selects ONLY the quantity dimension (Tham §3.3, p. 16: *much*
    "evoke[s] only the 'quantity' dimension"). This is a selectivity
    claim, not just compatibility — *a much cracked dish* means many
    cracks, not one deep crack. -/
theorem much_selects_quantity_only :
    allDisturbancePredicates.all
      (fun p => p.adjMuchSelects == [DisturbanceDimension.quantity])
      = true := rfl

/-- Compatibility of *much* (Tham §3.3 ex. 30): all three predicates
    accept *much*-modification. The substantive claim is the
    selectivity in `much_selects_quantity_only` above; this is the
    weaker compatibility check. -/
theorem all_disturbance_compatible_with_much :
    allDisturbancePredicates.all (fun p => !p.adjMuchSelects.isEmpty)
      = true := rfl

-- ════════════════════════════════════════════════════
-- § 8. Substrate readouts: Fragment scale-types
-- ════════════════════════════════════════════════════

/-! Verify that the Fragment adjective entries classify disturbance
    adjectives with the correct `Boundedness` value. These are
    consumption sites for the substrate, not bridges — `closedAdj_licensed`
    and `LicensingPipeline.IsLicensed` are foundational and are called
    inline. -/

theorem cracked_is_closed : Adjectival.cracked.scaleType = .closed := rfl
theorem dented_is_closed  : Adjectival.dented.scaleType = .closed := rfl
theorem scratched_is_closed : Adjectival.scratched.scaleType = .closed := rfl

/-- *dead* also has `.closed` — but is non-gradable (two-point). Same
    `Boundedness`, different gradability. `Boundedness` alone does not
    distinguish two-point from multi-point closed scales. -/
theorem dead_also_closed : Adjectival.dead.scaleType = .closed := rfl

/-- Verb fragment entries have closed degreeAchievementScale. -/
theorem crack_verb_closed_scale :
    (Verbal.crack.toVerb.degreeAchievementScale.get!).scaleBoundedness
      = .closed := rfl
theorem dent_verb_closed_scale :
    (Verbal.dent.toVerb.degreeAchievementScale.get!).scaleBoundedness
      = .closed := rfl
theorem scratch_verb_closed_scale :
    (Verbal.scratch.toVerb.degreeAchievementScale.get!).scaleBoundedness
      = .closed := rfl

/-- Adjective-verb scale agreement: each verb inherits the same
    `Boundedness` as its deverbal adjective. -/
theorem crack_adj_verb_scale_agree :
    Adjectival.cracked.scaleType =
    (Verbal.crack.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl
theorem dent_adj_verb_scale_agree :
    Adjectival.dented.scaleType =
    (Verbal.dent.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl
theorem scratch_adj_verb_scale_agree :
    Adjectival.scratched.scaleType =
    (Verbal.scratch.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- Disturbance adjectives are licensed for degree modification by the
    Kennedy pipeline, just like *full* and *clean*. -/
theorem cracked_licensed {max : Nat} {W : Type*} (μ : W → Semantics.Degree.Degree max) :
    (adjMeasure μ Adjectival.cracked).IsLicensed :=
  closedAdj_licensed μ Adjectival.cracked rfl
theorem cracked_pipeline_licensed :
    LicensingPipeline.IsLicensed Adjectival.cracked.scaleType := trivial

/-! Interpretive Economy predicts a max-endpoint standard for
    disturbance adjectives (closed → maxEndpoint). This interacts
    non-trivially with Tham's analysis: simple predication (*is
    cracked*) requires only the *minimum* physical instantiation (lower
    bound, §3.2.1), but Interpretive Economy selects the maximum as the
    positive standard. The resolution is that the positive standard
    determines the degree needed for the *positive form to apply*, while
    the lower bound determines the threshold for being on the scale at
    all. -/
theorem cracked_standard_maxEndpoint :
    interpretiveEconomy Adjectival.cracked.scaleType = .maxEndpoint := rfl

-- ════════════════════════════════════════════════════
-- § 9. Cross-paper engagement: Kennedy-Levin pipeline
-- ════════════════════════════════════════════════════

/-! [kennedy-levin-2008]'s pipeline maps closed scales to telic
    (accomplishment) interpretations. Tham §2.4 shows that disturbance
    verbs allow BOTH telic and atelic readings — variable telicity in a
    single closed-scale verb. Tham does not commit to "achievement"
    vs "accomplishment" as the lexical Vendler class; she observes that
    *crack* is "consistent with" being punctual (Tham p. 8 on ex. 9
    "the mirror will crack in five minutes") while ALSO admitting
    durative readings.

    Inside linglib, the Fragment makes a stipulation: `Verbal.crack`
    receives `vendlerClass = some .achievement`. The `defaultVendlerClass`
    derived from the closed scale via the Kennedy-Levin pipeline is
    `.accomplishment`. This divergence is a Lean-internal artifact of
    the Fragment's choice, not Tham's claim — but it makes the variable-
    telicity gap Lean-checkable. -/

/-- The pipeline predicts accomplishment for crack (closed → telic →
    durative). -/
theorem crack_pipeline_predicts_accomplishment :
    (Verbal.crack.toVerb.degreeAchievementScale.get!).defaultVendlerClass
      = .accomplishment := rfl

/-- The Fragment stipulates achievement (punctual telic), capturing the
    *in X* = "after" reading (Tham (9) "The mirror will crack in five
    minutes"). -/
theorem crack_stipulated_achievement :
    Verbal.crack.toVerb.vendlerClass = some .achievement := rfl

/-- Pipeline and Fragment stipulation diverge for *crack*. The
    divergence is internal to linglib (Fragment vs pipeline default),
    not a claim Tham herself makes — see the docstring above. -/
theorem crack_pipeline_vendler_diverges :
    (Verbal.crack.toVerb.degreeAchievementScale.get!).defaultVendlerClass ≠
    Verbal.crack.toVerb.vendlerClass.get! := by decide

/-- *break* (also Levin 45.1) IS an accomplishment — the standard
    pipeline works for it. So the Fragment-level divergence is specific
    to disturbance predicates within the same Levin class. -/
theorem break_fits_pipeline :
    Verbal.break_.toVerb.vendlerClass = some .accomplishment := rfl

/-- *crack* and *break* share LevinClass but differ in VendlerClass.
    Both are Levin 45.1 Break verbs, but *crack* is achievement
    (punctual + optional durative extension) while *break* is
    accomplishment (durative). This within-class split is exactly what
    Tham's analysis predicts: disturbance predicates have distinctive
    aspectual behavior. -/
theorem crack_break_same_levin_different_vendler :
    Verbal.crack.toVerb.levinClass = Verbal.break_.toVerb.levinClass ∧
    Verbal.crack.toVerb.vendlerClass ≠ Verbal.break_.toVerb.vendlerClass :=
  ⟨rfl, by decide⟩

/-- *shatter* is also achievement — but unlike crack, shatter ONLY has
    the punctual reading. Same Vendler class, different aspectual
    flexibility. VendlerClass is too coarse for disturbance predicates. -/
theorem shatter_also_achievement :
    Verbal.shatter.toVerb.vendlerClass = some .achievement := rfl

/-- Boundedness convergence: both pipelines agree crack is `.closed`.
    Achievement and accomplishment are both telic → `.closed`, so the
    disturbance-specific VendlerClass divergence is invisible at the
    `Boundedness` granularity. The Kennedy-Levin pipeline is correct
    about scale closure but wrong about what that closure implies for
    aspectual class.

    Contrast with `Studies/KennedyLevin2008.lean`,
    which proves convergence for 12 standard DAs — there, convergence at
    `Boundedness` ALSO means convergence at `VendlerClass`. For *crack*,
    only `Boundedness` converges. -/
theorem crack_boundedness_converges_despite_vendler_divergence :
    LicensingPipeline.toBoundedness (Verbal.crack.toVerb.degreeAchievementScale.get!) =
    LicensingPipeline.toBoundedness (Verbal.crack.toVerb.vendlerClass.get!) := rfl

-- ════════════════════════════════════════════════════
-- § 10. Cross-paper engagement: Hay-Kennedy-Levin matrix
-- ════════════════════════════════════════════════════

/-! [hay-kennedy-levin-1999]'s central thesis (HKL §3.2): closed-
    range adjectives → telic DA verbs; open-range adjectives → atelic.
    The substrate sibling
    `Studies/HayKennedyLevin1999.lean` proves this
    holds for *straighten* (closed → accomplishment) and *lengthen,
    widen, cool, warm* (open → activity).

    Tham §2.4 shows the *strict* version of this matrix fails for
    disturbance verbs. *crack* has a closed scale (HKL would predict
    "telic only") but ALSO admits atelic readings (Tham (10a) "ice will
    crack for two days", (14b) "cracked for a while"). HKL's matrix is
    correct as a default but does not capture the variable-telicity
    behavior of disturbance verbs. -/

/-- *crack* refutes the strict HKL matrix: closed scale, but BOTH telic
    and atelic readings attested. -/
theorem crack_refutes_strict_hkl_matrix :
    (Verbal.crack.toVerb.degreeAchievementScale.get!).scaleBoundedness
      = Boundedness.closed ∧
    crack.verbInX = true ∧
    crack.verbForX = true := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. Cross-paper engagement: Kennedy 2007 licensing
-- ════════════════════════════════════════════════════

/-! [kennedy-2007]'s `closedAdj_licensed` substrate (consumed in
    `Studies/Kennedy2007.lean` for *full*,
    *wet*, *dry*, *straight*) extends to disturbance adjectives without
    modification. The convergence at `Boundedness` is the partner of the
    §9 divergence at `VendlerClass`: same substrate, different
    granularity, different verdict. -/

/-- *cracked* shares licensing status with *full* (Kennedy 2007's
    canonical totally-closed adjective). The convergence is at the
    `Boundedness` level — both are `.closed`, hence both license degree
    modification. -/
theorem cracked_licensing_converges_with_kennedy2007
    {max : Nat} {W : Type*} (μ : W → Semantics.Degree.Degree max) :
    (adjMeasure μ Adjectival.cracked).IsLicensed ↔
    (adjMeasure μ Adjectival.full).IsLicensed :=
  iff_of_true (closedAdj_licensed μ Adjectival.cracked rfl)
    (closedAdj_licensed μ Adjectival.full rfl)

/-- All three disturbance adjectives converge with Kennedy 2007 at
    `Boundedness`. -/
theorem all_disturbance_pipeline_licensed :
    LicensingPipeline.IsLicensed Adjectival.cracked.scaleType ∧
    LicensingPipeline.IsLicensed Adjectival.dented.scaleType ∧
    LicensingPipeline.IsLicensed Adjectival.scratched.scaleType :=
  ⟨trivial, trivial, trivial⟩

-- ════════════════════════════════════════════════════
-- § 12. Cross-paper engagement: Sassoon 2013 binding insufficiency
-- ════════════════════════════════════════════════════

/-! **Honesty caveat.** Tham herself does not engage [sassoon-2013]'s
    binding-type typology directly. She cites Sassoon for the *fact* of
    multidimensionality and *respect*-PP diagnostics (Tham pp. 13, 24),
    and adopts Solt's representation ([solt-2018]) rather than
    Sassoon's. The argument below is the formaliser's reconstruction of
    what Tham's data WOULD force on Sassoon's apparatus — a
    cross-paper engagement constructed in linglib, not drawn out by Tham.

    [sassoon-2013]'s typology of multidimensional adjectives
    assigns each adjective a single `DimensionBindingType` —
    `.conjunctive` (*healthy* — all dimensions), `.disjunctive` (*sick*
    — some dimension), or `.mixed` (*intelligent* — context-dependent).
    That apparatus is in
    `Studies/Sassoon2013.lean` (`MultidimAdj`).

    Tham §3.2.1 + §3 (ex. 20a), TAKEN TOGETHER, yield a tension under
    Sassoon's framework: in the SAME context (one host entity with one
    high dimension), the lexical entry *cracked* must support both
    - "is cracked" → TRUE (lower-bound = any physical instantiation);
    - "completely cracked" → FALSE (upper-bound = spatial coverage).

    Sassoon's framework derives the truth-condition of the modified
    predicate from the bare adjective's binding. So if *cracked*'s
    binding is fixed to b, the prediction profile under b is
    (b(oneHigh), b(oneHigh)) — both judgments come from the same b.
    No single b satisfies the (true, false) target.

    `.mixed` (Sassoon's context-modulated escape hatch) shifts ∀/∃
    with discourse context, not with the modifier. The *same* mirror,
    in the *same* discourse, gives different verdicts under bare vs
    *completely* — that's modifier-driven, not context-driven, so
    `.mixed` doesn't help either. -/

/-- A 3-dimension Bool model: (quantity, quality, positioning). -/
abbrev CrackedDims := Bool × Bool × Bool

def crackedDims : List (CrackedDims → Bool) :=
  [fun s => s.1, fun s => s.2.1, fun s => s.2.2]

/-- "One dimension high" — Tham's lower-bound case (§3.2.1: any
    physical instantiation suffices for simple predication). -/
def oneHigh : CrackedDims := (true, false, false)

/-- The truth-value Sassoon's framework assigns to bare *cracked* on a
    state, given a binding type. (`.mixed` has to commit to one of the
    two modes per discourse context — modeled here as `.disjunctive`,
    Sassoon's default when polarity is positive.) -/
def sassoonBareTruth (b : DimensionBindingType) (s : CrackedDims) : Bool :=
  match b with
  | .conjunctive => conjunctiveBinding crackedDims s
  | .disjunctive => disjunctiveBinding crackedDims s
  | .mixed       => disjunctiveBinding crackedDims s

/-! Tham's two empirical targets on the one-dimension-high state:
    simple "is cracked" must come out `true` (Tham §3.2.1, lower
    bound = physical instantiation); "completely cracked" must come
    out `false` (Tham §3 ex. 20a, upper bound = spatial coverage). -/

/-- `.conjunctive` matches Tham's *completely* target (both predict
    NOT-cracked on oneHigh) but NOT the bare-predication target. -/
theorem conjunctive_matches_completely_only :
    sassoonBareTruth .conjunctive oneHigh = false ∧
    sassoonBareTruth .conjunctive oneHigh ≠ true := by
  refine ⟨rfl, ?_⟩; decide

/-- `.disjunctive` matches Tham's bare target (both predict cracked on
    oneHigh) but NOT the *completely* target. -/
theorem disjunctive_matches_bare_only :
    sassoonBareTruth .disjunctive oneHigh = true ∧
    sassoonBareTruth .disjunctive oneHigh ≠ false := by
  refine ⟨rfl, ?_⟩; decide

/-- `.mixed` (Sassoon's positive-polarity default = disjunctive)
    inherits the disjunctive verdict — same gap. -/
theorem mixed_inherits_disjunctive_gap :
    sassoonBareTruth .mixed oneHigh = true ∧
    sassoonBareTruth .mixed oneHigh ≠ false := by
  refine ⟨rfl, ?_⟩; decide

/-- The Sassoon insufficiency theorem: in the SAME context, Sassoon's
    binding cannot account for both simple-predication objectivity
    (Tham §3.2.1) and completely-modification (Tham §3 ex. 20a)
    simultaneously, because a single binding gives a single
    truth-value on the test state. Sassoon's mixed-type escape hatch
    is context-modulated, not modifier-modulated, so it doesn't
    discharge the gap either. -/
theorem no_sassoon_binding_captures_cracked :
    ∀ b : DimensionBindingType,
      ¬ (sassoonBareTruth b oneHigh = true ∧
         sassoonBareTruth b oneHigh = false) := by
  intro b ⟨h1, h2⟩
  exact absurd (h1.symm.trans h2) (by decide)

/-! ### Engagement with `Sassoon2013.MultidimAdj`

  To make the cross-paper engagement explicit at the schema level, we
  construct *cracked* as a member of Sassoon's `MultidimAdj` data type
  for each candidate binding type, and observe how Sassoon's own H3
  prediction (closed → conjunctive) interacts with Tham's data. -/

/-- *cracked* coerced into Sassoon's `MultidimAdj` schema with the
    binding type Sassoon's H3 predicts for closed-scale adjectives. -/
def crackedAsConjunctive : Sassoon2013.MultidimAdj :=
  ⟨"cracked", true, .closed, .conjunctive⟩

/-- *cracked* coerced into Sassoon's schema with the binding type
    Tham's §3.2.1 lower-bound data WOULD select if mapped naively. -/
def crackedAsDisjunctive : Sassoon2013.MultidimAdj :=
  ⟨"cracked", true, .closed, .disjunctive⟩

/-- *cracked* coerced with Sassoon's escape-hatch binding. -/
def crackedAsMixed : Sassoon2013.MultidimAdj :=
  ⟨"cracked", true, .closed, .mixed⟩

/-- The conjunctive entry SATISFIES Sassoon's H3 (closed scaleType
    predicts conjunctive binding) — but, per `conjunctive_matches_completely_only`
    above, this binding gives the WRONG simple-predication verdict. -/
theorem crackedAsConjunctive_satisfies_sassoon_h3 :
    Sassoon2013.hypothesis3Holds crackedAsConjunctive = true := rfl

/-- The disjunctive entry VIOLATES Sassoon's H3 (closed should yield
    conjunctive, not disjunctive) — yet this is the binding Tham's
    §3.2.1 simple-predication data would select. -/
theorem crackedAsDisjunctive_violates_sassoon_h3 :
    Sassoon2013.hypothesis3Holds crackedAsDisjunctive = false := rfl

/-- The crack between the frameworks made explicit on Sassoon's own
    schema: NO entry of `crackedAs{Conjunctive,Disjunctive,Mixed}`
    simultaneously satisfies Sassoon's H3 prediction AND Tham's
    simple-predication data. The conjunctive H3-conformer fails Tham;
    the disjunctive Tham-conformer fails H3; the mixed entry inherits
    the disjunctive verdict and fails H3 too. -/
theorem no_cracked_multidimAdj_satisfies_both :
    (Sassoon2013.hypothesis3Holds crackedAsConjunctive = true ∧
     sassoonBareTruth crackedAsConjunctive.binding oneHigh ≠ true) ∧
    (Sassoon2013.hypothesis3Holds crackedAsDisjunctive = false ∧
     sassoonBareTruth crackedAsDisjunctive.binding oneHigh = true) ∧
    (Sassoon2013.hypothesis3Holds crackedAsMixed = false ∧
     sassoonBareTruth crackedAsMixed.binding oneHigh = true) :=
  ⟨⟨rfl, by decide⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ════════════════════════════════════════════════════
-- § 13. Tham eq. 47b: spatially-normalized weighted measure
-- ════════════════════════════════════════════════════

/-! Tham §5.2 eq. (47b) gives the multidimensional measure for
    deverbal disturbance adjectives:

        μ_CRACKED(x) = Σᵢ kᵢ · μ_EXTENT(distᵢ(x)) / μ_SPATIAL_EXTENT(x)

    The numerator is a weighted sum of per-dimension EXTENT measures
    (captured by `weightedScore`); the denominator is the host's spatial
    extent. The substrate primitive is
    `spatialNormalizedScore` (Semantics/Degree/Aggregation.lean
    §2). The boundedness of the upper end of the scale (Tham §3.4
    "structural integrity limit") comes from the denominator: the same
    physical disturbance counts as more severe on a smaller host.

    Below: a worked example WE construct to exercise the substrate.
    Tham's actual intuition (p. 18, windshield: "one more crack and it
    will break") is that disturbance APPROACHES the structural-integrity
    limit from below; the vase example illustrates the inverse — same
    physical crack on a smaller host yields a higher normalized score.
    Both directions are consistent with eq. 47b mathematically; the
    framing is ours, not Tham's. The minimal claim the example makes
    Lean-checkable is that the spatial denominator is what introduces
    host-relativity (without it, the score is invariant). -/

/-- Vase scenario: a host of variable size with a single crack of
    extent 1 along dimension 1 (quantity), and 0 along quality and
    positioning. -/
structure Vase where
  spatial : ℚ
  deriving Repr

def smallVase : Vase := { spatial := 1 }
def largeVase : Vase := { spatial := 4 }

/-- One unit of disturbance along the quantity dimension; zero along
    the quality and positioning dimensions. -/
def vaseMeasures : List (Vase → ℚ) :=
  [fun _ => 1, fun _ => 0, fun _ => 0]

def equalWeights : List ℚ := [1, 1, 1]

/-- Helper: the weighted score of `vaseMeasures` on any vase is `1`
    (one disturbance unit on dimension 1, zero on the others). -/
private theorem weighted_score_vase (v : Vase) :
    weightedScore equalWeights vaseMeasures v = 1 := by
  unfold weightedScore equalWeights vaseMeasures
  simp [List.zip, List.foldl]

/-- Helper: the spatially-normalized score on a vase equals
    `1 / v.spatial` whenever `v.spatial ≠ 0`. -/
private theorem spatial_score_vase (v : Vase) (h : v.spatial ≠ 0) :
    spatialNormalizedScore equalWeights vaseMeasures Vase.spatial v
      = 1 / v.spatial := by
  unfold spatialNormalizedScore
  rw [if_neg h, weighted_score_vase]

/-- Plain weighted score is the same for small and large vases — the
    Tham eq. 47b numerator cannot detect host-extent differences. -/
theorem weighted_score_blind_to_spatial_extent :
    weightedScore equalWeights vaseMeasures smallVase =
    weightedScore equalWeights vaseMeasures largeVase := by
  rw [weighted_score_vase, weighted_score_vase]

/-- Tham's eq. 47b DOES distinguish: the same physical crack scores
    higher on a small vase than on a large vase. -/
theorem spatial_normalization_separates_small_from_large :
    spatialNormalizedScore equalWeights vaseMeasures Vase.spatial smallVase >
    spatialNormalizedScore equalWeights vaseMeasures Vase.spatial largeVase := by
  rw [spatial_score_vase smallVase (by norm_num [smallVase]),
      spatial_score_vase largeVase (by norm_num [largeVase])]
  norm_num [smallVase, largeVase]

/-- A threshold that the small vase clears but the large vase doesn't —
    Tham's "boundedness from spatial extent" claim made Lean-checkable. -/
theorem small_vase_cracked_large_vase_not :
    spatialNormalizedScore equalWeights vaseMeasures Vase.spatial smallVase
      ≥ (1 / 2 : ℚ) ∧
    spatialNormalizedScore equalWeights vaseMeasures Vase.spatial largeVase
      < (1 / 2 : ℚ) := by
  refine ⟨?_, ?_⟩
  · rw [spatial_score_vase smallVase (by norm_num [smallVase])]
    norm_num [smallVase]
  · rw [spatial_score_vase largeVase (by norm_num [largeVase])]
    norm_num [largeVase]

/-- **Boundedness from spatial extent** (Tham §3.4) made Lean-checkable
    via the substrate's mathlib-style structural property
    `spatialNormalizedScore_le_one`. When the weighted disturbance does
    not exceed the host's spatial extent, the normalized score is
    bounded by 1. The largeVase score (1/4) is well below this bound. -/
theorem largeVase_score_le_one :
    spatialNormalizedScore equalWeights vaseMeasures Vase.spatial largeVase
      ≤ 1 := by
  apply Semantics.Gradability.Aggregation.spatialNormalizedScore_le_one
  · rw [weighted_score_vase]; show (1 : ℚ) ≤ 4; norm_num
  · show (0 : ℚ) < 4; norm_num

-- ════════════════════════════════════════════════════
-- § 14. Cross-paper engagement: Beavers & Koontz-Garboden 2020
-- ════════════════════════════════════════════════════

/-! [beavers-koontz-garboden-2020] formalize verbal roots as
    bundles of lexical entailments
    (`Semantics/Lexical/Roots/Basic.lean`). Their classification
    of √crack is `[.becomesState "fissured", .hasCause]` — the
    "result + cause, no manner" base feature signature
    `{.result, .cause}` (`BeaversKoontzGarboden2020.crack`).

    Tham §5.1 (the (45) examples — cracked pumpkin, dented helmet
    model, scratched decal) is in tension with strict result-state
    INHERITANCE from this root signature to the deverbal adjective:
    the adjective applies to surfaces that have not undergone the
    CoS event. The substrate-level contrast: B&KG's *crack* root
    asserts `becomesState` (the verbal entry derived from this root
    inherits it via `Verbal.crack.toVerb.degreeAchievementScale`),
    yet the adjectival side `Tham2025.crack.adjEntailsPrecedingChange`
    is false. -/

/-- B&KG's `crack` root has a result entailment (the `becomesState
    "fissured"` atom provides it), but Tham's deverbal adjective
    *cracked* does NOT entail a preceding CoS event. Strict result-
    state inheritance from root to deverbal adjective is refuted at
    substrate level. -/
theorem cracked_adj_refutes_bkg_crack_root_inheritance :
    BeaversKoontzGarboden2020.crack.HasResult ∧
    crack.adjEntailsPrecedingChange = false :=
  ⟨by decide, rfl⟩

-- ════════════════════════════════════════════════════
-- § 15. Cross-paper engagement: Waldon et al. 2023 contrast
-- ════════════════════════════════════════════════════

/-! [waldon-etal-2023] formalize artifact-noun multidimensionality
    using the same `weightedScore` substrate that powers Tham's eq. 47b
    numerator. Both consume the substrate; they differ at the
    DENOMINATOR. Waldon's artifact-noun domain doesn't have a
    host-extent denominator naturally — there's nothing meaningful to
    spatially normalize over for "is this object an electronic
    device." Tham's disturbance-predicate domain does have one
    (the host's spatial extent), and her eq. 47b commits to using it.

    The substrate-level contrast: `weightedScore` (Waldon's surface
    arithmetic) is invariant under host-extent changes;
    `spatialNormalizedScore` (Tham's eq. 47b) is not. The substrate
    accommodates both — the choice between them is a lexical
    commitment of the predicate class, not a deeper theoretical
    disagreement. -/

/-- Tham vs Waldon at the substrate level: the same weighted-sum
    numerator gives the SAME verdict on small vs large vases, but
    spatial normalization makes them DIFFER. The contrast lives
    entirely in the denominator. -/
theorem tham_spatial_normalization_distinguishes_what_waldon_does_not :
    weightedScore equalWeights vaseMeasures smallVase =
      weightedScore equalWeights vaseMeasures largeVase ∧
    spatialNormalizedScore equalWeights vaseMeasures Vase.spatial smallVase ≠
      spatialNormalizedScore equalWeights vaseMeasures Vase.spatial largeVase := by
  refine ⟨weighted_score_blind_to_spatial_extent, ?_⟩
  intro h
  have := spatial_normalization_separates_small_from_large
  linarith

-- ════════════════════════════════════════════════════
-- § 16. Cross-paper engagement: Solt 2018 SuB reciprocal bridge
-- ════════════════════════════════════════════════════

/-! Solt 2018 SuB (`Studies/Solt2018Proportional.lean`)
    and Tham 2025 are the substrate's two consumers. Solt's
    `proportionalMeasure μ tot y` (her eq. 21) is
    `spatialNormalizedScore [1] [μ] (fun _ => μ tot) y` — the
    single-dimension specialization of Tham's eq. 47b. Both files
    consume the same `spatialNormalizedScore_le_one` and `_nonneg`
    substrate theorems; this section makes the reciprocal bridge
    explicit.

    The substrate-level identity: any consumer can derive the unit-
    interval bound from the substrate primitives, regardless of
    whether they specialize to single-dim (Solt) or multi-dim (Tham)
    aggregation. -/

/-- Tham's `largeVase_score_le_one` (above, §13) and Solt's
    `proportionalMeasure_le_one` are the SAME mathlib-style theorem
    instantiated on different aggregation specializations. The shared
    substrate primitive is `spatialNormalizedScore_le_one`. -/
theorem solt_tham_share_substrate_bounded_by_one :
    spatialNormalizedScore equalWeights vaseMeasures Vase.spatial largeVase
      ≤ 1 := largeVase_score_le_one

-- ════════════════════════════════════════════════════
-- § 17. Cross-paper engagement: Interpretive Economy wedge
-- ════════════════════════════════════════════════════

/-! [kennedy-2007]'s Interpretive Economy principle predicts a
    max-endpoint standard for closed-scale adjectives (`cracked` →
    `.maxEndpoint`, witnessed by `cracked_standard_maxEndpoint` in §8
    above). Tham's §3.2.1 lower-bound argument (`simple predication
    is OBJECTIVE: any physical instantiation suffices`, witnessed by
    `simplePredicationObjective = true` in §5 above) requires only
    the MINIMUM physical instantiation to be on the scale at all.

    These are not strictly contradictory — IE selects the standard for
    the positive form ("the threshold for *applies as a positive
    predicate*"); the lower bound is the threshold for *being on the
    scale at all*. But they do place different demands on the same
    `Boundedness` substrate. The wedge made Lean-checkable: -/

/-- The IE-vs-Tham §3.2.1 wedge: K2007's Interpretive Economy selects
    `.maxEndpoint` for *cracked*'s standard (`cracked_standard_maxEndpoint`),
    while Tham's §3.2.1 simple-predication objectivity claim requires
    only the lower bound. The wedge is at the level of WHICH endpoint
    of the closed scale is load-bearing for which prediction. -/
theorem cracked_ie_max_vs_tham_lower_bound :
    interpretiveEconomy Adjectival.cracked.scaleType =
      Semantics.Degree.PositiveStandard.maxEndpoint ∧
    crack.simplePredicationObjective = true ∧
    -- The two endpoints of a closed scale are distinct standards,
    -- yet both are required for different aspects of *cracked*'s
    -- meaning per Tham §3.4 (lower = physical instantiation,
    -- upper = spatial extent).
    Semantics.Degree.PositiveStandard.maxEndpoint ≠
      Semantics.Degree.PositiveStandard.minEndpoint := by
  refine ⟨rfl, rfl, ?_⟩; decide

-- ════════════════════════════════════════════════════
-- § 18. Cross-paper engagement: Solt 2018 multidim typology
-- ════════════════════════════════════════════════════

/-! [solt-2018] (the Springer multidim chapter, distinct from the
    SuB proportional-comparatives paper engaged in §16) presents an
    experimental five-class subjectivity typology
    (RelNum/AbsTot/AbsPart/RelNo/Eval, Fig. 1, pp. 5–6). The class
    is encoded as a substrate-adjacent enum at
    `Studies/Solt2018Multidim.lean`.

    *cracked* belongs to the AbsPart class — partially-closed scale,
    physical-property domain, intermediate ordering subjectivity
    (~67% "fact" judgments per Solt's experiment). The closest
    siblings are *clean*/*dirty*/*salty*/*wet*/*dry*. -/

/-- *cracked* belongs to Solt's AbsPart class, alongside
    *clean*/*dirty*/*wet*/*dry*. The class membership is consumed
    from `Solt2018Multidim.crackedClass`. -/
theorem cracked_is_solt_AbsPart :
    Solt2018Multidim.crackedClass = Solt2018Multidim.SubjectivityClass.absPart :=
  Solt2018Multidim.cracked_is_AbsPart

end Tham2025
