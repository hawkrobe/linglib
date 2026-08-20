import Linglib.Morphology.DistributedMorphology.Spellout
import Linglib.Morphology.Morphotactics.MirrorPrinciple

/-!
# [halle-marantz-1993]: Distributed Morphology and the Pieces of Inflection
[halle-marantz-1993]

This study file formalizes the core architecture and predictions of
Distributed Morphology as presented in [halle-marantz-1993],
Chapter 3 of *The View from Building 20* (Hale & Keyser, eds.).

## Structure

- **§1**: English Verb Inflection — the context-free Tns/Agr paradigm,
  formalized using `FeatureVI` and `subsetPrinciple`, demonstrating
  Elsewhere Condition competition
- **§2**: Conditioned Allomorphy — root-specific past tense exponents
  (`-t`, `∅`) illustrating the Paninian principle (most specific wins)
- **§3**: Tns + Agr Fusion — the MS operation that merges Tns and Agr
  into a single terminal before VI
- **§4**: Impoverishment and Syncretism — feature deletion before VI
  derives syncretism (past participle falling together with simple past)
- **§5**: Baker 1985 Bridge — English Tns/Agr features are outside
  GF-rule categories in [bybee-1985]'s relevance hierarchy,
  connecting [baker-1985], [bybee-1985], and
  [halle-marantz-1993]

## Architecture

[halle-marantz-1993] adopt a Y-model (DS → SS → {LF, MS → PF}).
Terminal nodes bear morphosyntactic features but no phonological content
until Vocabulary Insertion at MS — this is **Late Insertion**. The VI
mechanism (`subsetPrinciple`) IS Late Insertion in action: it maps
feature bundles to exponents, making DM realizational by construction.

Impoverishment and Fusion — both introduced in this paper — are
formalized as general mechanisms in
`Morphology/DistributedMorphology/Impoverishment.lean` and `Fusion.lean`.
This study file instantiates impoverishment on the English paradigm to
derive syncretism (§4) and fusion on the Tns/Agr pair (§3).
-/

namespace HalleMarantz1993

open DistributedMorphology.VI
open Morphology.MirrorPrinciple
open Morphology (MorphCategory)

-- ============================================================================
-- §1: English Verb Inflection
-- ============================================================================

/-! ### The Subset Principle and English Tns/Agr

[halle-marantz-1993] give the Vocabulary Items for English verbal
inflection. The terminal node for Tns+Agr (after fusion — see §3)
bears features drawn from {[+past], [+participle], [3sg]}. The
**Subset Principle** / **Elsewhere Condition** selects the most specific
matching VI entry: the entry whose feature specification is the largest
subset of the terminal's features.

Context-free VI entries:

| Features             | Exponent | Example           |
|----------------------|----------|-------------------|
| [+past, +participle] | `-n`     | taken, eaten      |
| [+past]              | `-d`     | walked, played    |
| [+participle]        | `-ing`   | walking, playing  |
| [3sg]                | `-z`     | walks, plays      |
| ∅ (elsewhere)        | `∅`      | walk, play        |
-/

section EnglishVerb

/-- Features on the English Tns+Agr terminal after fusion.
    [halle-marantz-1993]. -/
inductive EngInflFeature where
  | past
  | participle
  | sg3
  deriving DecidableEq, BEq, Repr

/-- Context-free VI entries for English verbal inflection.
    [halle-marantz-1993]. -/
def englishTnsVI : List (FeatureVI EngInflFeature String) :=
  [⟨[.past, .participle], "-n"⟩,
   ⟨[.past],              "-d"⟩,
   ⟨[.participle],        "-ing"⟩,
   ⟨[.sg3],               "-z"⟩,
   ⟨[],                   "∅"⟩]

/-- Past participle: [+past, +participle] → `-n`.
    `-n` beats `-d` and `-ing` because its feature set {past,
    participle} is the largest subset of the target.
    [halle-marantz-1993]. -/
theorem past_participle_gets_n :
    subsetPrinciple englishTnsVI [.past, .participle] = some "-n" := by
  decide

/-- Past finite: [+past] → `-d`.
    `-n` does not match because [+participle] ⊄ {past}.
    [halle-marantz-1993]. -/
theorem past_finite_gets_d :
    subsetPrinciple englishTnsVI [.past] = some "-d" := by
  decide

/-- Non-finite participle: [+participle] → `-ing`.
    [halle-marantz-1993]. -/
theorem nonpast_participle_gets_ing :
    subsetPrinciple englishTnsVI [.participle] = some "-ing" := by
  decide

/-- Third singular present: [3sg] → `-z`.
    [halle-marantz-1993]. -/
theorem sg3_present_gets_z :
    subsetPrinciple englishTnsVI [.sg3] = some "-z" := by
  decide

/-- Elsewhere (bare stem): [] → `∅`.
    When no features are present, the elsewhere entry wins.
    [halle-marantz-1993]. -/
theorem elsewhere_gets_null :
    subsetPrinciple englishTnsVI [] = some "∅" := by
  decide

/-- The Subset Principle resolves `-n` vs `-d` competition: for a
    [+past, +participle] target, `-n` (2 features) beats `-d`
    (1 feature). -/
theorem n_beats_d_for_past_participle :
    subsetPrinciple englishTnsVI [.past, .participle] ≠
    subsetPrinciple englishTnsVI [.past] := by
  decide

/-- The paradigm is total: every possible feature combination
    receives an exponent (thanks to the elsewhere entry). -/
theorem paradigm_total :
    (subsetPrinciple englishTnsVI [.past, .participle]).isSome = true ∧
    (subsetPrinciple englishTnsVI [.past]).isSome = true ∧
    (subsetPrinciple englishTnsVI [.participle]).isSome = true ∧
    (subsetPrinciple englishTnsVI [.sg3]).isSome = true ∧
    (subsetPrinciple englishTnsVI []).isSome = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end EnglishVerb

-- ============================================================================
-- §2: Conditioned Allomorphy
-- ============================================================================

/-! ### Root-Specific Past Tense Entries

The default past tense entry `-d` coexists with root-conditioned
variants ([halle-marantz-1993]):

- **`-t`**: dwell → dwelt, buy → bought, send → sent, ...
- **`∅`**: put → put, beat → beat, hit → hit, ...

These share the same morphosyntactic context ([+past]) but have
different root restrictions. The **Paninian principle** (= Elsewhere
Condition applied to root-conditioned entries) selects the most
specific matching entry: a root-restricted rule overrides the
unrestricted default when the root matches.

This section uses `VocabItem` (which supports root restrictions via
`rootMatch`) rather than `FeatureVI` (which is context-free). -/

section ConditionedAllomorphy

/-- Sample verb roots for demonstrating conditioned allomorphy. -/
inductive SampleVerb where
  | walk | play
  | dwell | buy | send
  | put | beat | hit
  deriving DecidableEq, BEq, Repr

/-- Root-conditioned past tense VI rules.

    All three entries share [+past] context (modeled as `Bool`);
    they differ in root restriction and specificity.
    [halle-marantz-1993]. -/
def conditionedPastVI : List (VocabItem Bool SampleVerb) :=
  [-- /-t/ for specific roots (specificity 2: context + root)
   { exponent := "-t"
     contextMatch := id
     rootMatch := some ([SampleVerb.dwell, .buy, .send].contains ·)
     specificity := 2 },
   -- /∅/ for specific roots (specificity 2: context + root)
   { exponent := "∅"
     contextMatch := id
     rootMatch := some ([SampleVerb.put, .beat, .hit].contains ·)
     specificity := 2 },
   -- /-d/ default (specificity 1: context only, no root restriction)
   { exponent := "-d"
     contextMatch := id
     rootMatch := none
     specificity := 1 }]

/-- Regular verbs get `-d`: no root-specific entry matches. -/
theorem walk_gets_d :
    vocabularyInsert conditionedPastVI true .walk = some "-d" := by
  decide

theorem play_gets_d :
    vocabularyInsert conditionedPastVI true .play = some "-d" := by
  decide

/-- Verbs in the `-t` class: root restriction overrides default. -/
theorem dwell_gets_t :
    vocabularyInsert conditionedPastVI true .dwell = some "-t" := by
  decide

theorem buy_gets_t :
    vocabularyInsert conditionedPastVI true .buy = some "-t" := by
  decide

/-- Verbs in the `∅` class: no overt past tense marking. -/
theorem put_gets_null :
    vocabularyInsert conditionedPastVI true .put = some "∅" := by
  decide

theorem beat_gets_null :
    vocabularyInsert conditionedPastVI true .beat = some "∅" := by
  decide

/-- The Paninian principle: root-restricted entries override the
    default for matching roots. -/
theorem root_restriction_overrides_default :
    vocabularyInsert conditionedPastVI true .dwell ≠
    vocabularyInsert conditionedPastVI true .walk := by
  decide

/-- Non-past context: no entry matches (all require [+past]). -/
theorem nonpast_no_match :
    vocabularyInsert conditionedPastVI false .walk = none := by
  decide

end ConditionedAllomorphy

-- ============================================================================
-- §3: Tns + Agr Fusion
-- ============================================================================

/-! ### Fusion of Tns and Agr at MS

[halle-marantz-1993] argue that English Tns and Agr are separate
syntactic heads. At MS, they undergo **Fusion**: the two adjacent
terminals merge into a single terminal bearing the union of both
feature bundles. A single VI entry then spells out the fused node.

This explains why English has a single affix (not two stacked
affixes) for Tns+Agr: *walk-s* realizes both non-past Tns and 3sg
Agr in one exponent, because Fusion merges the two terminals before
VI applies.

We model fusion with `DistributedMorphology.FusionRule` and show that the
fused features feed directly into the VI paradigm from §1. -/

section TnsAgrFusion

/-- The two inflectional heads that fuse in English. -/
inductive InflHead where
  /-- Tns head: bears tense/aspect features. -/
  | tns (past : Bool) (participle : Bool)
  /-- Agr head: bears agreement features. -/
  | agr (sg3 : Bool)
  deriving DecidableEq, Repr

/-- Extract inflectional features from each head type. -/
def InflHead.features : InflHead → List EngInflFeature
  | .tns true true   => [.past, .participle]
  | .tns true false  => [.past]
  | .tns false true  => [.participle]
  | .tns false false => []
  | .agr true        => [.sg3]
  | .agr false       => []

/-- Tns+Agr fusion ([halle-marantz-1993]): the two heads are adjacent
    sisters after head movement, so the structural condition is trivially
    met here and the fused bundle is feature-list union. -/
def tnsAgrFusion : DistributedMorphology.FusionRule (List EngInflFeature) Unit where
  contextOk _ := True
  decContext _ := inferInstanceAs (Decidable True)
  bundlesOk _ _ := True
  decBundles _ _ := inferInstanceAs (Decidable True)
  fuse := (· ++ ·)

/-- The conditioned application always succeeds for adjacent Tns/Agr. -/
theorem tnsAgrFusion_apply (p q : List EngInflFeature) :
    tnsAgrFusion.apply p q () = some (p ++ q) :=
  DistributedMorphology.FusionRule.apply_pos trivial trivial

/-- The fused feature bundle for a Tns+Agr combination. -/
def fusedFeatures (tPast tPart : Bool) (aSg3 : Bool) : List EngInflFeature :=
  tnsAgrFusion.fuse (InflHead.tns tPast tPart).features (InflHead.agr aSg3).features

/-- 3sg present: Tns[−past,−part] fused with Agr[3sg] → [sg3] → `-z`.
    One exponent realizes both heads. -/
theorem fusion_3sg_present :
    subsetPrinciple englishTnsVI (fusedFeatures false false true) = some "-z" := by
  decide

/-- Past finite: Tns[+past] fused with Agr[−3sg] → [past] → `-d`. -/
theorem fusion_past :
    subsetPrinciple englishTnsVI (fusedFeatures true false false) = some "-d" := by
  decide

/-- Past participle: Tns[+past,+part] fused with Agr[−3sg]
    → [past, participle] → `-n`. -/
theorem fusion_past_participle :
    subsetPrinciple englishTnsVI (fusedFeatures true true false) = some "-n" := by
  decide

/-- Present participle: Tns[−past,+part] fused with Agr[−3sg]
    → [participle] → `-ing`. -/
theorem fusion_present_participle :
    subsetPrinciple englishTnsVI (fusedFeatures false true false) = some "-ing" := by
  decide

/-- Elsewhere: Tns[−past,−part] fused with Agr[−3sg] → [] → `∅`. -/
theorem fusion_elsewhere :
    subsetPrinciple englishTnsVI (fusedFeatures false false false) = some "∅" := by
  decide

/-- Every Tns+Agr fusion produces a feature bundle that the VI
    paradigm can spell out — the paradigm is complete. -/
theorem fusion_always_spellable (tPast tPart aSg3 : Bool) :
    (subsetPrinciple englishTnsVI (fusedFeatures tPast tPart aSg3)).isSome = true := by
  cases tPast <;> cases tPart <;> cases aSg3 <;> decide

/-- The Tns+Agr pipeline over a spell-out domain: the fusion module,
    then pointwise insertion by the Subset Principle. -/
def tnsAgrSpellout :
    DistributedMorphology.Spellout (List EngInflFeature) String where
  modules := [tnsAgrFusion.applyFirstAdjacent ()]
  insert := subsetPrinciple englishTnsVI

/-- *walk-s*: the domain [Tns[−past,−part], Agr[3sg]] spells out as the
    single exponent `-z`. -/
theorem walks_pf :
    tnsAgrSpellout.pf
        [(InflHead.tns false false).features, (InflHead.agr true).features]
      = [some "-z"] := by decide

/-- Two syntactic terminals enter, one exponent slot leaves — the
    terminal/exponent misalignment is carried entirely by the fusion
    module. -/
theorem walks_terminal_exponent_misalignment :
    [(InflHead.tns false false).features,
      (InflHead.agr true).features].length = 2 ∧
    (tnsAgrSpellout.pf
        [(InflHead.tns false false).features,
          (InflHead.agr true).features]).length = 1 := by
  exact ⟨rfl, by rw [walks_pf]; rfl⟩

end TnsAgrFusion

-- ============================================================================
-- §4: Impoverishment and Syncretism
-- ============================================================================

/-! ### Impoverishment Derives Syncretism

[halle-marantz-1993] introduce **Impoverishment**: deletion of
features from a terminal node before Vocabulary Insertion. When a
distinguishing feature is deleted, two formerly distinct contexts
fall together at VI, producing **syncretism** — distinct morphosyntactic
specifications receiving the same exponent.

The general Impoverishment mechanism is formalized in
`Morphology/DistributedMorphology/Impoverishment.lean`. Here we instantiate it
on the English Tns/Agr paradigm to demonstrate the derivation of
syncretism: deleting [+participle] from [+past, +participle] causes
the past participle to receive the same exponent as simple past.

This models the fact that regular English verbs have identical simple
past and past participle forms (*walked* does both): the [+participle]
feature is not visible at VI, leaving only [+past] to trigger `-d`. -/

section ImpoverishmentSyncretism

/-- Delete occurrences of a feature from a bundle.

    This mirrors `deleteFeature` in `Morphology/DistributedMorphology/Impoverishment.lean`,
    instantiated for `EngInflFeature`. The structural parallel is
    exact: both filter a list, removing elements that match the target. -/
def deleteFeature (bundle : List EngInflFeature) (target : EngInflFeature) :
    List EngInflFeature :=
  bundle.filter (· != target)

/-- Impoverishment is idempotent: deleting a feature twice is the
    same as deleting it once.

    This mirrors `deleteFeature_idempotent` in `Impoverishment.lean`
    — filter is idempotent when the predicate is stable. -/
theorem deleteFeature_idempotent (bundle : List EngInflFeature)
    (target : EngInflFeature) :
    deleteFeature (deleteFeature bundle target) target =
    deleteFeature bundle target := by
  simp only [deleteFeature, List.filter_filter]
  congr 1; ext f; simp only [Bool.and_self]

/-- Impoverishing [+participle] from [+past, +participle] produces
    syncretism: the impoverished bundle receives the same exponent
    as simple [+past]. -/
theorem impoverish_produces_syncretism :
    subsetPrinciple englishTnsVI
      (deleteFeature [.past, .participle] .participle) =
    subsetPrinciple englishTnsVI [.past] := by
  decide

/-- Without impoverishment, [+past, +participle] gets `-n`
    (*taken*, *eaten*). -/
theorem without_impoverishment_gets_n :
    subsetPrinciple englishTnsVI [.past, .participle] = some "-n" := by
  decide

/-- With impoverishment of [+participle], the same context gets `-d`
    (*walked* as both simple past and past participle). -/
theorem with_impoverishment_gets_d :
    subsetPrinciple englishTnsVI
      (deleteFeature [.past, .participle] .participle) = some "-d" := by
  decide

/-- Full DM pipeline: Fusion → Impoverishment → VI.

    Past participle with impoverishment of [+participle]:
    1. Fusion: Tns[+past,+part] + Agr[−3sg] → [past, participle]
    2. Impoverishment: delete [+participle] → [past]
    3. VI: [past] → `-d`

    Without impoverishment, step 3 would give `-n` (via
    `fusion_past_participle`). This full pipeline connects
    §1 (VI), §3 (fusion), and §4 (impoverishment). -/
theorem pipeline_fusion_impoverishment_vi :
    subsetPrinciple englishTnsVI
      (deleteFeature (fusedFeatures true true false) .participle) = some "-d" := by
  decide

end ImpoverishmentSyncretism

-- ============================================================================
-- §5: Baker 1985 Bridge
-- ============================================================================

/-! ### Connecting to the Mirror Principle and Bybee's Hierarchy

[halle-marantz-1993] discuss how DM's post-syntactic architecture
derives [baker-1985]'s Mirror Principle: GF-rules (passive,
causative, applicative, reflexive/reciprocal) are syntactic head
movements, and Morphological Structure preserves the derivation order.
Affix layering necessarily mirrors syntactic structure because MS is
derived from syntax.

We formalize two connections:

1. English verb inflection is concatenative, placing it within
   [baker-1985]'s scope.

2. All English Tns/Agr features map to [bybee-1985] categories
   that are OUTSIDE GF-rule categories in the relevance hierarchy.
   This is consistent with DM's clause structure: Tns and Agr sit
   structurally above GF-rule projections, so their exponents are
   outermost after head movement. -/

section BakerBridge

/-- Map English inflectional features to [bybee-1985]'s
    morphological categories. -/
def EngInflFeature.toMorphCategory : EngInflFeature → MorphCategory
  | .past => .tense
  | .participle => .aspect
  | .sg3 => .agreement .subj

/-- All English Tns/Agr features map to categories that are OUTSIDE
    GF-rule categories in [bybee-1985]'s relevance hierarchy.

    GF-rules (passive → voice rank 3, causative/applicative/reciprocal
    → valence rank 2) are always closer to the stem than English
    Tns/Agr features (aspect rank 4, tense rank 5, agreement rank 8).

    This is consistent with DM's clause structure: Tns and Agr are
    structurally above GF-rule projections (PassP, CausP, ApplP),
    so after head movement and fusion, the Tns+Agr exponent sits
    outermost. The relevance hierarchy and the syntactic hierarchy
    converge — connecting [baker-1985], [bybee-1985],
    and [halle-marantz-1993]. -/
theorem tnsAgr_outside_gfRules (f : EngInflFeature) (r : GFRuleType) :
    r.toMorphCategory.RelevanceLT f.toMorphCategory := by
  cases f <;> cases r <;> decide

/-- English verb inflection is concatenative: affixes are linearly
    concatenated to the stem. This places it within the scope of
    [baker-1985]'s Mirror Principle ([baker-1985] restricts
    the principle to concatenative morphology, excluding clitics and
    nonconcatenative processes). -/
theorem english_inflection_in_scope :
    MorphDomain.concatenative.InScope := rfl

end BakerBridge

end HalleMarantz1993
