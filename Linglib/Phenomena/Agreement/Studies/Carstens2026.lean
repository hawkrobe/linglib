import Linglib.Fragments.Bantu.Params
import Linglib.Fragments.Xhosa.Basic
import Linglib.Fragments.Shona.Basic
import Linglib.Fragments.Swahili.Basic
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Phenomena.Gender.Studies.Kramer2020
import Linglib.Theories.Syntax.Minimalism.Agreement.GenderResolution
import Linglib.Theories.Syntax.Minimalism.Agreement.CoordinateResolution
import Linglib.Phenomena.Agreement.Studies.AdamsonAnagnostopoulou2025

/-!
# Carstens 2026: The Grammar of Gender

@cite{carstens-2026}

Carstens, Vicki. 2026. "The grammar of gender: Insights from Bantu
asymmetries of AGR with conjoined subjects." *Natural Language &
Linguistic Theory* 44:20.

## Core claims

1. **nP stacking**: Bantu nominals have stacked nP structure where visible
   gender (class prefix) wraps around a semantic i-gender core. The internal
   structure is [nP₁ n1 [nP₂ n2+root]]; n2 is always the bearer of the
   semantic gender.

2. **Three semantic cores in Xhosa**: genders A (1/2), D (7/8), E (9/10) have
   interpretable i[entity] flavors — [human], [inanimate], [animal]
   respectively. Genders B (3/4) and C (5/6) are uninterpretable.

3. **Resolution via percolation + intersection**: Following
   @cite{adamson-anagnostopoulou-2025}, agreement with conjoined singulars
   works by percolating conjuncts' i-features to &P and intersecting them.
   u-features are excluded. Non-empty intersection → gender-matching plural
   agreement; empty intersection → default agreement.

4. **Diagnostic**: Gender-matching plural agreement with uniform conjoined
   singulars succeeds iff the gender is interpretable (has i[entity] flavor).

5. **Shona confirmation**: In Shona (8 genders), only 2 are interpretable
   ([human] 1/2 and [non-human] 7/8). The 6:2 ratio of uninterpretable to
   interpretable confirms that matching agreement is the exception, not
   the rule.

## Formalization

Resolution uses `GenderResolution.resolve` — the single compositional
endpoint — via `statusToBundle` which bridges Bantu `GenderStatus` to
`FeatureBundle SemanticCore`. Study-level theorems verify the mechanism's
predictions against @cite{carstens-2026}'s empirical data.
-/

namespace Phenomena.Agreement.Studies.Carstens2026

open Fragments.Bantu
open Theories.Syntax.Minimalism.Agreement.GenderResolution

-- ============================================================================
-- Preamble: Fragment → Theory Bridge
-- ============================================================================

/-- A single interpretable nP layer bearing `SemanticCore` c. -/
def nP (c : SemanticCore) : FeatureBundle SemanticCore := [⟨c, true⟩]

/-- An uninterpretable nP layer (no features to percolate). -/
def nP_u : FeatureBundle SemanticCore := []

/-- Stack an outer gender layer on an inner core (outer ++ inner). -/
def nPStack (outer inner : FeatureBundle SemanticCore) := outer ++ inner

/-- Convert `GenderStatus` to a feature bundle for `resolve`.
    Interpretable genders produce a singleton i-feature bundle;
    uninterpretable genders produce an empty bundle. -/
def statusToBundle (s : GenderStatus) : FeatureBundle SemanticCore :=
  match s with
  | .interpretable c => nP c
  | .uninterpretable => nP_u

-- ============================================================================
-- § 1: Resolution Mechanism — Core Properties
-- ============================================================================

/-- Interpretable genders yield non-empty intersection with themselves. -/
theorem interpretable_self_nonempty (c : SemanticCore) :
    resolve (statusToBundle (.interpretable c)) (statusToBundle (.interpretable c))
    = some [c] := by
  cases c <;> native_decide

/-- Uninterpretable genders yield empty intersection with themselves. -/
theorem uninterpretable_self_empty :
    resolve (statusToBundle .uninterpretable) (statusToBundle .uninterpretable)
    = none := rfl

/-- Uninterpretable + interpretable yields empty intersection. -/
theorem uninterpretable_interpretable_empty (c : SemanticCore) :
    resolve (statusToBundle .uninterpretable) (statusToBundle (.interpretable c))
    = none := rfl

/-- Mismatched interpretable cores yield empty intersection. -/
theorem mismatched_cores_empty (c1 c2 : SemanticCore) (h : c1 ≠ c2) :
    resolve (statusToBundle (.interpretable c1)) (statusToBundle (.interpretable c2))
    = none := by
  cases c1 <;> cases c2 <;> simp_all (config := { decide := true })

/-- **The central claim** (@cite{carstens-2026}): for ANY Bantu gender,
    matching agreement with uniform conjoined singulars succeeds iff
    the gender is interpretable. This holds at the parameter type level,
    not just for specific Xhosa/Shona inventories.

    The language-specific `xhosa_matching_iff_interpretable` and
    `shona_matching_iff_interpretable` are corollaries of this theorem. -/
theorem bantu_matching_iff_interpretable (s : GenderStatus) :
    (resolve (statusToBundle s) (statusToBundle s)).isSome = s.isInterpretable := by
  cases s with
  | interpretable c => cases c <;> native_decide
  | uninterpretable => rfl

-- ============================================================================
-- § 2: Xhosa Predictions — Uniform Conjoined Singulars
-- ============================================================================

/-! ### Matching agreement available (interpretable genders) -/

/-- [1&1] human conjuncts: intersection = [human] → matching cl 2 available.
    @cite{carstens-2026} Table 13: 100% ba- (matching = default for [human]). -/
theorem xhosa_1and1_matching :
    resolve (statusToBundle (Fragments.Xhosa.Gender.genderA).status)
           (statusToBundle (Fragments.Xhosa.Gender.genderA).status)
    = some [.human] := by native_decide

/-- [7&7] inanimate conjuncts: intersection = [inanimate] → matching cl 8.
    @cite{carstens-2026} Table 13: 100% zi- for non-human [7&7]. -/
theorem xhosa_7and7_matching :
    resolve (statusToBundle (Fragments.Xhosa.Gender.genderD).status)
           (statusToBundle (Fragments.Xhosa.Gender.genderD).status)
    = some [.inanimate] := by native_decide

/-- [9&9] animal conjuncts: intersection = [animal] → matching cl 10.
    @cite{carstens-2026} Table 13: 50% zi- matching + 40% ba- default
    for human [9&9]; 100% zi- for non-human [9&9]. -/
theorem xhosa_9and9_matching :
    resolve (statusToBundle (Fragments.Xhosa.Gender.genderE).status)
           (statusToBundle (Fragments.Xhosa.Gender.genderE).status)
    = some [.animal] := by native_decide

/-! ### Matching agreement unavailable (uninterpretable genders) -/

/-- [3&3] conjuncts: intersection = ∅ → default agreement only.
    @cite{carstens-2026} Table 13: 0% matching for human (100% ba-);
    2.2% matching for non-human (73.3% zi- default). -/
theorem xhosa_3and3_no_matching :
    resolve (statusToBundle (Fragments.Xhosa.Gender.genderB).status)
           (statusToBundle (Fragments.Xhosa.Gender.genderB).status)
    = none := rfl

/-- [5&5] conjuncts: intersection = ∅ → default agreement only.
    @cite{carstens-2026} Table 13: 0% matching; 63.33% ba- for human,
    73.33% zi- for non-human. -/
theorem xhosa_5and5_no_matching :
    resolve (statusToBundle (Fragments.Xhosa.Gender.genderC).status)
           (statusToBundle (Fragments.Xhosa.Gender.genderC).status)
    = none := rfl

/-! ### The core prediction: matching ↔ interpretability -/

/-- Every Xhosa gender: matching agreement is available iff interpretable. -/
theorem xhosa_matching_iff_interpretable (g : Fragments.Xhosa.Gender) :
    (resolve (statusToBundle g.status) (statusToBundle g.status)).isSome
    = g.status.isInterpretable := by
  cases g <;> native_decide

-- ============================================================================
-- § 3: Xhosa Predictions — Mismatched Conjoined Singulars
-- ============================================================================

/-- Mismatched [human] conjuncts (e.g. [3&5] gangster + policeman):
    both have [human] core from stacking → intersection = [human].
    @cite{carstens-2026} (85)a, (86)a: class 2 ba- agreement. -/
theorem xhosa_mismatched_human :
    resolve (statusToBundle (.interpretable .human))
           (statusToBundle (.interpretable .human))
    = some [.human] := by native_decide

/-- Mismatched [inanimate] conjuncts (e.g. [3&5] carrot + egg):
    both have [inanimate] core from stacking → intersection = [inanimate].
    @cite{carstens-2026} (85)b, (86)b: class 8 zi- agreement. -/
theorem xhosa_mismatched_inanimate :
    resolve (statusToBundle (.interpretable .inanimate))
           (statusToBundle (.interpretable .inanimate))
    = some [.inanimate] := by native_decide

/-- Human + inanimate (e.g. [9&1a] girl + train):
    [human] ∩ [inanimate] = ∅ → ineffable.
    @cite{carstens-2026} (91)–(92): agreement with conjoined humans
    and inanimates is generally ineffable. -/
theorem xhosa_human_inanimate_ineffable :
    resolve (statusToBundle (.interpretable .human))
           (statusToBundle (.interpretable .inanimate))
    = none := by native_decide

-- ============================================================================
-- § 4: Default Agreement Classes
-- ============================================================================

/-- Default for [human]: class 2 ba- (@cite{carstens-2026} (52c)). -/
theorem default_human_is_class2 :
    SemanticCore.defaultPluralClass .human = 2 := rfl

/-- Default for [inanimate]: class 8 zi- (@cite{carstens-2026} (52c)). -/
theorem default_inanimate_is_class8 :
    SemanticCore.defaultPluralClass .inanimate = 8 := rfl

/-- Default for [animal]: class 8 zi- (class 10 = syncretic with 8 for
    default purposes; @cite{carstens-2026} §3.4). -/
theorem default_animal_is_class8 :
    SemanticCore.defaultPluralClass .animal = 8 := rfl

-- ============================================================================
-- § 5: Shona Predictions
-- ============================================================================

/-- Shona [1&1]: class 2 va- (human matching/default).
    @cite{carstens-2026} (58): va- for conjoined [1&1] (consistent across speakers). -/
theorem shona_1and1_matching :
    resolve (statusToBundle (Fragments.Shona.Gender.genderA).status)
           (statusToBundle (Fragments.Shona.Gender.genderA).status)
    = some [.human] := by native_decide

/-- Shona [7&7]: class 8 zvi- (non-human matching/default).
    @cite{carstens-2026} (62): zvi- for non-human [7&7] (consistent across speakers). -/
theorem shona_7and7_matching :
    resolve (statusToBundle (Fragments.Shona.Gender.genderD).status)
           (statusToBundle (Fragments.Shona.Gender.genderD).status)
    = some [.nonhuman] := by native_decide

/-- Shona [3&3]: no matching → default only.
    @cite{carstens-2026} (59): zvi- (class 8 default) for non-human. -/
theorem shona_3and3_no_matching :
    resolve (statusToBundle (Fragments.Shona.Gender.genderB).status)
           (statusToBundle (Fragments.Shona.Gender.genderB).status)
    = none := rfl

/-- Shona [5&5]: no matching → default only.
    @cite{carstens-2026} (60)–(61). -/
theorem shona_5and5_no_matching :
    resolve (statusToBundle (Fragments.Shona.Gender.genderC).status)
           (statusToBundle (Fragments.Shona.Gender.genderC).status)
    = none := rfl

/-- Shona [9&9]: no matching → default only.
    Unlike Xhosa [9&9], Shona's [animal] core has bleached from 9/10.
    @cite{carstens-2026} §5.2, (64)b–d: va- for human, zvi- for non-human. -/
theorem shona_9and9_no_matching :
    resolve (statusToBundle (Fragments.Shona.Gender.genderE).status)
           (statusToBundle (Fragments.Shona.Gender.genderE).status)
    = none := rfl

/-- Shona [11&11]: no matching → default only.
    @cite{carstens-2026} (65): zvi- (class 8 default). -/
theorem shona_11and11_no_matching :
    resolve (statusToBundle (Fragments.Shona.Gender.genderF).status)
           (statusToBundle (Fragments.Shona.Gender.genderF).status)
    = none := rfl

/-- Shona [14&14]: no matching → default only (abstract nouns).
    @cite{carstens-2026}: genderG (14/6) is uninterpretable. -/
theorem shona_14and14_no_matching :
    resolve (statusToBundle (Fragments.Shona.Gender.genderG).status)
           (statusToBundle (Fragments.Shona.Gender.genderG).status)
    = none := rfl

/-- Shona [12&12]: no matching → default only (diminutives).
    @cite{carstens-2026}: conjoined diminutives take class 8 zvi-. -/
theorem shona_12and12_no_matching :
    resolve (statusToBundle (Fragments.Shona.Gender.genderH).status)
           (statusToBundle (Fragments.Shona.Gender.genderH).status)
    = none := rfl

/-- Every Shona gender: matching ↔ interpretable. -/
theorem shona_matching_iff_interpretable (g : Fragments.Shona.Gender) :
    (resolve (statusToBundle g.status) (statusToBundle g.status)).isSome
    = g.status.isInterpretable := by
  cases g <;> native_decide

-- ============================================================================
-- § 6: Cross-linguistic Comparison
-- ============================================================================

/-- Xhosa has 3 interpretable genders out of 5 (60%). -/
theorem xhosa_interpretable_count :
    ([Fragments.Xhosa.Gender.genderA, .genderB, .genderC, .genderD, .genderE].filter
      (λ g => g.status.isInterpretable)).length = 3 := rfl

/-- Shona has 2 interpretable genders out of 8 (25%). -/
theorem shona_interpretable_count :
    ([Fragments.Shona.Gender.genderA, .genderB, .genderC, .genderD,
     .genderE, .genderF, .genderG, .genderH].filter
      (λ g => g.status.isInterpretable)).length = 2 := rfl

/-- Core insight (@cite{carstens-2026} §3.5, §5.2): in Shona, genders in which
    matching agreement succeeds are outnumbered by those where it fails by 6:2,
    confirming that matching is the exception. -/
theorem shona_matching_is_minority :
    ([Fragments.Shona.Gender.genderA, .genderB, .genderC, .genderD,
     .genderE, .genderF, .genderG, .genderH].filter
      (λ g => !(resolve (statusToBundle g.status) (statusToBundle g.status)).isSome)).length = 6 := by
  native_decide

-- ============================================================================
-- § 7: nP Stacking Verification
-- ============================================================================

/-- Canonical [human] nouns: visible = core (no stacking). -/
theorem human_canonical_no_stacking :
    Fragments.Xhosa.humanCanonical.isCanonical = true := rfl

/-- [Human] nouns in class 3: stacked (visible ≠ core). -/
theorem human_class3_stacked :
    Fragments.Xhosa.humanInClass3.isCanonical = false := rfl

/-- [Human] nouns in class 5: stacked (visible ≠ core). -/
theorem human_class5_stacked :
    Fragments.Xhosa.humanInClass5.isCanonical = false := rfl

/-- Stacked nouns retain the core gender despite different visible class. -/
theorem stacking_preserves_core :
    Fragments.Xhosa.humanInClass3.status = .interpretable .human ∧
    Fragments.Xhosa.humanInClass5.status = .interpretable .human ∧
    Fragments.Xhosa.animalInClass1.status = .interpretable .animal :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Bridge to DM Categorizer (@cite{kramer-2015})
-- ============================================================================

/-- Bantu `SemanticCore` → DM `Interpretability` bridge.
    Interpretable genders bear `Interpretability.i` (natural gender);
    uninterpretable genders bear `Interpretability.u` (arbitrary gender).
    @cite{carstens-2026} directly extends @cite{kramer-2015}'s i/u distinction. -/
def toDMInterpretability : GenderStatus → Morphology.DM.Interpretability
  | .interpretable _ => .i
  | .uninterpretable => .u

/-- The bridge preserves the interpretability predicate. -/
theorem dm_bridge_faithful (s : GenderStatus) :
    (toDMInterpretability s == .i) = s.isInterpretable := by
  cases s <;> rfl

/-- Bantu `SemanticCore` → typological `SemanticBasis` bridge.
    @cite{carstens-2026}'s cores map to @cite{kramer-2020}'s
    core semantic bases. All are `isCore = true`.

    The [non-human] core (Shona 7/8) maps to `.humanness` because
    Shona's system is organized around the human/non-human distinction.
    Xhosa's finer [animal] and [inanimate] cores map to `.animacy`. -/
def toSemanticBasis : SemanticCore → Phenomena.Gender.Typology.SemanticBasis
  | .human     => .humanness
  | .animal    => .animacy
  | .inanimate => .animacy
  | .nonhuman  => .humanness

/-- All Bantu semantic cores map to Kramer's semantic core bases. -/
theorem bantu_cores_are_kramer_cores (c : SemanticCore) :
    (toSemanticBasis c).isCore = true := by
  cases c <;> rfl

-- ============================================================================
-- § 9: Bridge to Gender Typology (WALS)
-- ============================================================================

/-- Xhosa gender profile: 5+ genders, non-sex-based, semantic+formal assignment.
    @cite{carstens-2026} §2.2: semantic cores for some genders, formal (class prefix)
    assignment for others. -/
def xhosaGenderProfile : Phenomena.Gender.Typology.GenderProfile where
  name := "Xhosa"
  iso639 := "xho"
  genderCount := .fivePlus
  rawGenderCount := 5
  basis := .nonSexBased
  assignment := .semanticAndFormal
  semanticBases := [.humanness, .animacy]
  agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun, .verbTarget]

/-- Shona gender profile: 8 genders (5+), non-sex-based. -/
def shonaGenderProfile : Phenomena.Gender.Typology.GenderProfile where
  name := "Shona"
  iso639 := "sna"
  genderCount := .fivePlus
  rawGenderCount := 8
  basis := .nonSexBased
  assignment := .semanticAndFormal
  semanticBases := [.humanness]
  agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun, .verbTarget]

/-- Both profiles satisfy the Semantic Core Generalization
    (@cite{kramer-2020} ex. 2/28). -/
theorem xhosa_satisfies_semantic_core :
    xhosaGenderProfile.satisfiesSemanticCore = true := rfl

theorem shona_satisfies_semantic_core :
    shonaGenderProfile.satisfiesSemanticCore = true := rfl

-- ============================================================================
-- § 10: Resolution of Mismatched Conjuncts via nP Stack Cores
-- ============================================================================

/-- Resolution with nP stacking: agreement is determined by the stack's
    semantic core, not the visible class. Two nouns in different visible
    classes but the same core gender resolve to that core.
    @cite{carstens-2026} (85)–(88): mismatched [3&5] humans → ba-,
    mismatched [3&5] inanimates → zi-. -/
def resolveStacks (s1 s2 : NPStack) : Option (List SemanticCore) :=
  resolve (statusToBundle s1.status) (statusToBundle s2.status)

/-- Criminal (cl3) + policeman (cl5): both [human] core → class 2 ba-.
    @cite{carstens-2026} (85)a, (86)a. -/
theorem mismatched_3and5_human :
    resolveStacks
      ⟨3, 1, .interpretable .human⟩
      ⟨5, 1, .interpretable .human⟩
    = some [.human] := by native_decide

/-- Carrot (cl3) + egg (cl5): both [inanimate] core → class 8 zi-.
    @cite{carstens-2026} (85)b, (86)b. -/
theorem mismatched_3and5_inanimate :
    resolveStacks
      ⟨3, 7, .interpretable .inanimate⟩
      ⟨5, 7, .interpretable .inanimate⟩
    = some [.inanimate] := by native_decide

/-- Medium (cl7, human) + girl (cl9, human): both have [human] core
    from nP stacking → [human] ∩ [human] = {[human]} → class 2 ba-.
    Visible genders differ (7 vs 9) but cores agree.
    @cite{carstens-2026} (87)a, (88)a. -/
theorem mismatched_7and9_both_human :
    resolveStacks
      ⟨7, 1, .interpretable .human⟩
      ⟨9, 1, .interpretable .human⟩
    = some [.human] := by native_decide

/-- Backpack (cl1a, inanimate) + book (cl9, inanimate): both have
    [inanimate] core → [inanimate] ∩ [inanimate] = {[inanimate]} → class 8 zi-.
    @cite{carstens-2026} (87)b, (88)b. -/
theorem mismatched_1aand9_both_inanimate :
    resolveStacks
      ⟨1, 7, .interpretable .inanimate⟩
      ⟨9, 7, .interpretable .inanimate⟩
    = some [.inanimate] := by native_decide

-- ============================================================================
-- § 11: Swahili General Animate Concords Connection
-- ============================================================================

/-- Swahili's 5 genders also instantiate the Bantu semantic core system.
    @cite{carstens-2026} §8 discusses Swahili's GAC (General Animate Concords)
    as evidence for a [+animate] feature. -/
theorem swahili_genderA_interpretable :
    Fragments.Swahili.Gender.genderA.status.isInterpretable = true := rfl

theorem swahili_genderE_interpretable :
    Fragments.Swahili.Gender.genderE.status.isInterpretable = true := rfl

/-- Three Bantu languages, shared diagnostic: A (1/2) = [human] in all. -/
theorem three_languages_agree_on_human :
    Fragments.Xhosa.Gender.genderA.status = .interpretable .human ∧
    Fragments.Shona.Gender.genderA.status = .interpretable .human ∧
    Fragments.Swahili.Gender.genderA.status = .interpretable .human :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 12: End-to-End Derivation Chain
-- ============================================================================

/-! The "deepest derivation" from the paper connects nP stacking to
    agreement outcome through the full chain:

    1. **nP stacking**: assign feature bundles from layered nP structure
    2. **Percolation**: exclude u-features
    3. **Intersection**: find shared i-features
    4. **Agreement**: matching (non-empty) or default (empty)

    Each theorem below traces this chain for a concrete example from
    @cite{carstens-2026} §5. -/

/-- Feature bundle: citizen (class 1, canonical human — no stacking).
    Structure: [n₁/₂ √CITIZEN].
    @cite{carstens-2026} (6)a, (72)a. -/
def citizenBundle := nP .human

/-- Feature bundle: gangster (class 3, human core via stacking).
    Structure: [n₃/₄ [n₁/₂ √GULUKUDU]].
    Outer n₃/₄ is u → excluded. Inner n₁/₂ is i[human] → percolates.
    @cite{carstens-2026} (28)d, (85)a, (86)a; structure type per (72)b. -/
def gangsterBundle := nPStack nP_u (nP .human)

/-- Feature bundle: policeman (class 5, human core via stacking).
    Structure: [n₅/₆ [n₁/₂ √POLISA]].
    @cite{carstens-2026} (85)a; structure type per (72)c. -/
def policemanBundle := nPStack nP_u (nP .human)

/-- Feature bundle: hat (class 3, no stacking — arbitrary inanimate in u-gender).
    Structure: [n₃/₄ √HAT]. No inner layer.
    @cite{carstens-2026} (38)a, (77)a. -/
def hatBundle := nP_u

/-- Feature bundle: carrot (class 3, inanimate core via stacking).
    Structure: [n₃/₄ [n₇/₈ √CARROT]].
    @cite{carstens-2026} (86)b. -/
def carrotBundle := nPStack nP_u (nP .inanimate)

/-- Feature bundle: egg (class 5, inanimate core via stacking).
    Structure: [n₅/₆ [n₇/₈ √EGG]].
    @cite{carstens-2026} (86)b. -/
def eggBundle := nPStack nP_u (nP .inanimate)

/-- Feature bundle: elephant (class 9, canonical animal — no stacking).
    Structure: [n₉/₁₀ √ELEPHANT].
    @cite{carstens-2026} (49)b, (73)a. -/
def elephantBundle := nP .animal

/-- End-to-end derivation: citizen.1 & president.1 → matching [human].
    @cite{carstens-2026} (6)a: class 2 ba- agreement.

    Chain: canonical class 1 → i[human] percolates → {human} ∩ {human}
    = {human} → matching → class 2 ba-. -/
theorem derivation_1and1_human :
    resolve citizenBundle citizenBundle = some [.human] := by native_decide

/-- End-to-end derivation: gangster.3 & policeman.5 → matching [human].
    @cite{carstens-2026} (86)a: class 2 ba- agreement.

    Chain: nP stacking gives u-outer + i[human]-inner →
    u excluded, {human} percolates from each →
    {human} ∩ {human} = {human} → matching → class 2 ba-. -/
theorem derivation_3and5_human :
    resolve gangsterBundle policemanBundle = some [.human] := by native_decide

/-- End-to-end derivation: carrot.3 & egg.5 → matching [inanimate].
    @cite{carstens-2026} (86)b: class 8 zi- agreement.

    Chain: u-outer + i[inanimate]-inner →
    {inanimate} ∩ {inanimate} = {inanimate} → matching → class 8 zi-. -/
theorem derivation_3and5_inanimate :
    resolve carrotBundle eggBundle = some [.inanimate] := by native_decide

/-- End-to-end derivation: hat.3 & gun.3 → default.
    @cite{carstens-2026} (77)a, (38)a: class 8 zi- (default for non-human).

    Chain: u-gender, no stacking → no i-features to percolate →
    {} ∩ {} = {} → default → class 8 zi-. -/
theorem derivation_3and3_default :
    resolve hatBundle hatBundle = none := rfl

/-- End-to-end derivation: elephant.9 & leopard.9 → matching [animal].
    @cite{carstens-2026} (49)b, (82)a: class 10 zi- agreement.

    Chain: canonical class 9 → i[animal] percolates →
    {animal} ∩ {animal} = {animal} → matching → class 10 zi-. -/
theorem derivation_9and9_animal :
    resolve elephantBundle elephantBundle = some [.animal] := by native_decide

/-- End-to-end derivation: human + inanimate → default (generally ineffable).
    @cite{carstens-2026} (91)–(92): *girl.9 & train.1a → no agreement.

    Chain: i[human] vs i[inanimate] →
    {human} ∩ {inanimate} = {} → default.
    But no default class satisfies both cores → ineffable. -/
theorem derivation_human_inanimate_default :
    resolve citizenBundle (nP .inanimate)
    = none := by native_decide

-- ============================================================================
-- § 13: Two Grammars — Highest Wins vs Best Semantic Match
-- ============================================================================

/-! @cite{carstens-2026} §5.1, (78)–(81): when arbitrary members of
    interpretable genders stack in non-canonical classes, both the outer
    (arbitrary) and inner (core) i-features percolate to &P. The intersection
    then contains multiple features, and two grammars determine which one
    selects the agreement class.

    We use a structured feature type that carries both the class number
    (determining agreement morphology) and a core/arbitrary flag
    (determining BSM specificity). -/

/-- Feature with core/arbitrary distinction for the two-grammars analysis.
    @cite{carstens-2026} (71): n₁ = i[entity] i[core]; n₂ = i[entity]
    (for arbitrary members). Core features are more specific. -/
structure TwoGrammarFeature where
  classNum : Nat
  isCore : Bool
  deriving DecidableEq, BEq, Repr

/-- BSM specificity: core flavors outrank arbitrary i[entity]. -/
def TwoGrammarFeature.specificity (f : TwoGrammarFeature) : Nat :=
  if f.isCore then 2 else 1

/-- Feature bundle for train.1a: [n₁ₐ(arbitrary) [n₇(core inanimate) √TRAIN]].
    Outer: class 1, arbitrary i[entity] from gender A.
    Inner: class 7, core i[inanimate] from gender D.
    @cite{carstens-2026} (78)a, (79)a, (80)a. -/
def trainFeatures : FeatureBundle TwoGrammarFeature :=
  [⟨⟨1, false⟩, true⟩, ⟨⟨7, true⟩, true⟩]

/-- Feature bundle for diviner.7: [n₇(arbitrary) [n₁(core human) √DIVINER]].
    Outer: class 7, arbitrary i[entity] from gender D.
    Inner: class 1, core i[human] from gender A.
    @cite{carstens-2026} (78)b, (79)b, (80)b. -/
def divinerFeatures : FeatureBundle TwoGrammarFeature :=
  [⟨⟨7, false⟩, true⟩, ⟨⟨1, true⟩, true⟩]

/-- Intersection for train.1a & machine.1a: both layers survive.
    @cite{carstens-2026} (79)a: &P {1, {7}} ∩ {1, {7}} = {1, {7}}. -/
theorem train_intersection :
    resolve trainFeatures trainFeatures
    = some [⟨1, false⟩, ⟨7, true⟩] := by native_decide

/-- Intersection for diviner.7 & scholar.7: both layers survive.
    @cite{carstens-2026} (79)b: &P {7, {1}} ∩ {7, {1}} = {7, {1}}. -/
theorem diviner_intersection :
    resolve divinerFeatures divinerFeatures
    = some [⟨7, false⟩, ⟨1, true⟩] := by native_decide

/-- Highest Wins for train.1a & machine.1a: outermost = class 1 → cl 2 ba-.
    @cite{carstens-2026} (79)a. -/
theorem train_highest_wins :
    selectFeature .highestWins
      TwoGrammarFeature.specificity
      [⟨1, false⟩, ⟨7, true⟩]
    = some ⟨1, false⟩ := rfl

/-- BSM for train.1a & machine.1a: core class 7 (inanimate) → cl 8 zi-.
    @cite{carstens-2026} (80)a. -/
theorem train_best_semantic_match :
    selectFeature .bestSemanticMatch
      TwoGrammarFeature.specificity
      [⟨1, false⟩, ⟨7, true⟩]
    = some ⟨7, true⟩ := rfl

/-- Highest Wins for diviner.7 & scholar.7: outermost = class 7 → cl 8 zi-.
    @cite{carstens-2026} (79)b. -/
theorem diviner_highest_wins :
    selectFeature .highestWins
      TwoGrammarFeature.specificity
      [⟨7, false⟩, ⟨1, true⟩]
    = some ⟨7, false⟩ := rfl

/-- BSM for diviner.7 & scholar.7: core class 1 (human) → cl 2 ba-.
    @cite{carstens-2026} (80)b: 'The fool and the scholar are studying'
    with ba- agreement. -/
theorem diviner_best_semantic_match :
    selectFeature .bestSemanticMatch
      TwoGrammarFeature.specificity
      [⟨7, false⟩, ⟨1, true⟩]
    = some ⟨1, true⟩ := rfl

/-- The two grammars give DIFFERENT predictions for stacked nPs:
    for train.1a & machine.1a, HW picks class 1 (ba-) while BSM
    picks class 7 (zi-). Both are attested by Xhosa speakers.
    @cite{carstens-2026} (81)a: zi- for [L & M] = BSM;
    (45)a: ba- for [L & M] = HW. -/
theorem two_grammars_differ_train :
    selectFeature .highestWins TwoGrammarFeature.specificity
      [⟨1, false⟩, ⟨7, true⟩] ≠
    selectFeature .bestSemanticMatch TwoGrammarFeature.specificity
      [⟨1, false⟩, ⟨7, true⟩] := by
  decide

/-- And they also differ for diviner.7 & scholar.7:
    HW → class 7 (zi-), BSM → class 1 (ba-). -/
theorem two_grammars_differ_diviner :
    selectFeature .highestWins TwoGrammarFeature.specificity
      [⟨7, false⟩, ⟨1, true⟩] ≠
    selectFeature .bestSemanticMatch TwoGrammarFeature.specificity
      [⟨7, false⟩, ⟨1, true⟩] := by
  decide

-- ============================================================================
-- § 14: Bridge to Unified Coordinate Resolution
-- ============================================================================

open Theories.Syntax.Minimalism.Agreement.CoordinateResolution

/-! ### Bantu–CoordinateResolution bridge

    The unified `CoordinateResolution` framework resolves all three
    phi-dimensions (person, number, gender) independently. Here we
    show that the gender dimension, instantiated with `SemanticCore`
    via `statusToBundle`, gives the expected outcomes for conjoined
    Bantu singular DPs. -/

/-- A Bantu singular DP's phi-bundle: 3rd person (all full DPs are 3rd),
    singular number, gender from the noun's gender status. -/
def bantuDP (s : GenderStatus) : PhiBundle SemanticCore :=
  { person := ⟨.third, true⟩
    number := ⟨.singular, true⟩
    gender := statusToBundle s }

/-- Conjoined Bantu singulars → plural number (summation). -/
theorem bantu_coordinate_number (s₁ s₂ : GenderStatus) :
    (resolveCoordinate (bantuDP s₁) (bantuDP s₂)).number = some .plural := by
  cases s₁ with
  | interpretable c₁ => cases s₂ with
    | interpretable c₂ => cases c₁ <;> cases c₂ <;> rfl
    | uninterpretable => cases c₁ <;> rfl
  | uninterpretable => cases s₂ with
    | interpretable c₂ => cases c₂ <;> rfl
    | uninterpretable => rfl

/-- Conjoined Bantu singulars → 3rd person (full DPs are always 3rd). -/
theorem bantu_coordinate_person (s₁ s₂ : GenderStatus) :
    (resolveCoordinate (bantuDP s₁) (bantuDP s₂)).person = some .third := by
  cases s₁ with
  | interpretable c₁ => cases s₂ with
    | interpretable c₂ => cases c₁ <;> cases c₂ <;> rfl
    | uninterpretable => cases c₁ <;> rfl
  | uninterpretable => cases s₂ with
    | interpretable c₂ => cases c₂ <;> rfl
    | uninterpretable => rfl

/-- Gender dimension of composed resolution matches direct `resolve`. -/
theorem bantu_coordinate_gender (s₁ s₂ : GenderStatus) :
    (resolveCoordinate (bantuDP s₁) (bantuDP s₂)).gender
    = resolve (statusToBundle s₁) (statusToBundle s₂) := by
  rfl

/-- End-to-end: conjoined [human] Xhosa singulars via unified resolution.
    Person: 3rd + 3rd → 3rd. Number: sg + sg → pl. Gender: [human] ∩ [human]
    = some [human]. All three succeed. -/
theorem xhosa_human_coordinate :
    resolveCoordinate (bantuDP (.interpretable .human))
                      (bantuDP (.interpretable .human))
    = ⟨some .third, some .plural, some [.human]⟩ := rfl

/-- End-to-end: conjoined uninterpretable Xhosa singulars.
    Person and number resolve; gender fails → default. -/
theorem xhosa_uninterpretable_coordinate :
    resolveCoordinate (bantuDP .uninterpretable) (bantuDP .uninterpretable)
    = ⟨some .third, some .plural, none⟩ := rfl

-- ============================================================================
-- § 15: Cross-Study Bridge — A&A 2025 ↔ Carstens 2026
-- ============================================================================

/-! ### Shared mechanism

    @cite{carstens-2026} explicitly adopts @cite{adamson-anagnostopoulou-2025}'s
    percolation-and-intersection mechanism. Both studies use the same
    `GenderResolution.resolve` function, instantiated with different
    feature types:
    - A&A: `GenderNode` (privative geometry nodes — CLASS, MASC, FEM, etc.)
    - Carstens: `SemanticCore` (entity flavors — human, animal, inanimate)

    The bridge below proves this is not just a narrative claim but a
    structural fact: both resolution functions are projections of the same
    parameterized mechanism. -/

open Phenomena.Agreement.Studies.AdamsonAnagnostopoulou2025

/-- Both studies agree on the self-matching property for interpretable
    features: Bantu interpretable cores self-match via `statusToBundle`,
    and A&A singleton i-features self-match — both through `resolve`. -/
theorem bantu_aa_self_matching_consistent :
    -- Bantu: interpretable cores self-match
    (∀ c : SemanticCore,
      (resolve (statusToBundle (.interpretable c)) (statusToBundle (.interpretable c))).isSome
      = true) ∧
    -- A&A: singleton i-features self-match
    (∀ f : GenderNode,
      (resolve [⟨f, true⟩] [⟨f, true⟩]).isSome = true) := by
  constructor
  · intro c; cases c <;> native_decide
  · intro f; cases f <;> native_decide

-- ============================================================================
-- § 16: Mismatch Resolution Hypothesis — Bantu
-- ============================================================================

/-! ### MRH failure in Bantu

    Unlike Greek/Icelandic (@cite{adamson-anagnostopoulou-2025}), Bantu
    does NOT satisfy MRH: uninterpretable genders produce empty
    intersections, requiring default agreement. This is the structural
    reason why default agreement is needed in Bantu but not in Greek. -/

/-- Bantu does not satisfy MRH: the full inventory includes
    uninterpretable genders that yield empty intersections. -/
theorem bantu_fails_mrh :
    satisfiesMRH [statusToBundle (.interpretable .human),
                  statusToBundle (.interpretable .inanimate),
                  statusToBundle (.interpretable .animal),
                  statusToBundle .uninterpretable]
    = false := by native_decide

/-- Restricted to interpretable-only, MRH still fails:
    mismatched cores (human ≠ inanimate) yield empty intersection. -/
theorem bantu_interpretable_fails_mrh :
    satisfiesMRH [statusToBundle (.interpretable .human),
                  statusToBundle (.interpretable .inanimate),
                  statusToBundle (.interpretable .animal)]
    = false := by native_decide

/-- But uniform cores satisfy MRH trivially (self-matching). -/
theorem bantu_uniform_satisfies_mrh (c : SemanticCore) :
    satisfiesMRH [statusToBundle (.interpretable c),
                  statusToBundle (.interpretable c)]
    = true := by
  cases c <;> native_decide

-- ============================================================================
-- § 17: N-ary Bantu Resolution
-- ============================================================================

/-! ### Three or more conjuncts

    `resolveN` extends the mechanism to n-ary coordination.
    Bantu predictions generalize cleanly: matching agreement requires
    ALL conjuncts to share the same interpretable core. -/

/-- Three [human] conjuncts → matching [human]. -/
theorem nary_three_humans :
    resolveN [statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .human)]
    = some [.human] := by native_decide

/-- Three [inanimate] conjuncts → matching [inanimate]. -/
theorem nary_three_inanimates :
    resolveN [statusToBundle (.interpretable .inanimate),
              statusToBundle (.interpretable .inanimate),
              statusToBundle (.interpretable .inanimate)]
    = some [.inanimate] := by native_decide

/-- Three uninterpretable conjuncts → default (none). -/
theorem nary_three_uninterpretable :
    resolveN [statusToBundle .uninterpretable,
              statusToBundle .uninterpretable,
              statusToBundle .uninterpretable]
    = none := rfl

/-- Mixed: two [human] + one [inanimate] → default (none).
    A single mismatched conjunct blocks matching agreement. -/
theorem nary_mixed_fails :
    resolveN [statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .inanimate)]
    = none := by native_decide

/-- Mixed: two [human] + one uninterpretable → default (none).
    Uninterpretable conjuncts block matching even with uniform cores. -/
theorem nary_human_plus_unintrp_fails :
    resolveN [statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .human),
              statusToBundle .uninterpretable]
    = none := rfl

/-- N-ary subsumes binary for Bantu. -/
theorem nary_subsumes_binary_bantu (s₁ s₂ : GenderStatus) :
    resolveN [statusToBundle s₁, statusToBundle s₂]
    = resolve (statusToBundle s₁) (statusToBundle s₂) := by
  exact resolveN_binary (statusToBundle s₁) (statusToBundle s₂)

end Phenomena.Agreement.Studies.Carstens2026
