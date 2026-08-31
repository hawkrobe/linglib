import Linglib.Fragments.Bantu.Params
import Linglib.Fragments.Xhosa.Basic
import Linglib.Fragments.Shona.Basic
import Linglib.Fragments.Swahili.Basic
import Linglib.Morphology.DistributedMorphology.Categorizer.Gender
import Linglib.Studies.Kramer2020
import Linglib.Features.Number.Resolve
import Linglib.Features.Person.Resolve
import Linglib.Studies.AdamsonAnagnostopoulou2025
import Linglib.Studies.TaraldsenEtAl2018

/-!
# Carstens 2026: the grammar of gender

This file formalizes the account of Bantu gender agreement with conjoined subjects in
[carstens-2026]. Two singular conjuncts of the same visible gender sometimes take gender-matching
plural agreement and sometimes only semantic agreement from the default classes, and the split is
not arbitrary: matching succeeds exactly with the genders whose `n` carries an interpretable
semantic flavor. Agreement is computed as in [adamson-anagnostopoulou-2025], by percolating each
conjunct's interpretable features to `&P` and intersecting them, with uninterpretable features
excluded — so a gender with no flavor contributes nothing and the intersection is empty.

Bantu nominals stack: the visible gender is an outer `nP` wrapping a semantic core, the way
[kramer-2015] has Somali gender stack, so a noun's class prefix and the gender it agrees by can
differ. Two nouns of different visible genders that share a core therefore resolve as if they
shared a gender. Xhosa's genders A (1/2), D (7/8) and E (9/10) carry i[human], i[inanimate] and
i[animal]; B (3/4) and C (5/6) carry none. Shona, with eight gender pairs, carries flavors in only
1/2 and 7/8, which is what makes matching agreement the exception there.

## Main definitions

* `nP`, `nP_u`, `nPStack`, `statusToBundle` — nP layers as feature bundles
* `resolveStacks`, `resolveCoordinate` — resolution through a stack and over a φ-bundle
* `TwoGrammarFeature` — the two-grammar treatment of arbitrary members (§5.1)

## Main results

* `bantu_matching_iff_interpretable` — matching agreement succeeds iff the gender is interpretable
* `xhosa_matching_iff_interpretable`, `shona_matching_iff_interpretable` — the two inventories
* `stacked_core_resolve` — a stacked u-gender leaves the core's features to percolate
* `bantu_fails_mrh` — Bantu refutes the Mismatch Resolution Hypothesis
* `xhosa_matching_iff_sharesClassifierN` — the semantic diagnostic and
  [taraldsen-et-al-2018]'s structural one coincide on the Xhosa lexicon

## References

* [carstens-2026]
* [adamson-anagnostopoulou-2025]
* [kramer-2015]
* [kramer-2020]
* [taraldsen-et-al-2018]
-/

namespace Carstens2026

open Bantu
open Minimalist.Coordination (Annotated Bundle percolate conversion resolve resolveN
  resolveN_binary MismatchResolutionOn)
open _root_.Minimalist (Interpretability)

/-- When multiple i-features survive (stacked nPs), the language selects which one
    determines the agreement class (§5.1). -/
inductive SelectionGrammar where
  /-- The outermost (highest) nP layer wins — the first surviving feature. -/
  | highestWins
  /-- The most specific semantic match wins. -/
  | bestSemanticMatch
  deriving DecidableEq, Repr

/-- Select the determining feature from a non-empty intersection; `specificity` ranks
    features (higher = more specific). -/
def selectFeature {F : Type}
    (grammar : SelectionGrammar) (specificity : F → Nat)
    (features : List F) : Option F :=
  match grammar with
  | .highestWins => features.head?
  | .bestSemanticMatch =>
    features.foldl (init := none) fun acc f =>
      match acc with
      | none => some f
      | some best =>
        match Nat.blt (specificity best) (specificity f) with
        | true => some f
        | false => some best

/-! ### Feature bundles for nP layers -/

/-- A single interpretable nP layer bearing `SemanticCore` c. -/
def nP (c : SemanticCore) : Bundle SemanticCore := [⟨c, .interpretable⟩]

/-- An uninterpretable nP layer (no features to percolate). -/
def nP_u : Bundle SemanticCore := []

/-- Stack an outer gender layer on an inner core (outer ++ inner). -/
def nPStack (outer inner : Bundle SemanticCore) := outer ++ inner

/-- Convert `GenderStatus` to a feature bundle for `resolve`.
    Interpretable genders produce a singleton i-feature bundle;
    uninterpretable genders produce an empty bundle. -/
def statusToBundle (s : GenderStatus) : Bundle SemanticCore :=
  match s with
  | .interpretable c => nP c
  | .uninterpretable => nP_u

/-! ### The resolution mechanism -/

/-- Interpretable genders yield non-empty intersection with themselves. -/
theorem interpretable_self_nonempty (c : SemanticCore) :
    resolve (statusToBundle (.interpretable c)) (statusToBundle (.interpretable c))
    = some [c] := by
  cases c <;> decide

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

/-- **The central claim** ([carstens-2026]): for ANY Bantu gender,
    matching agreement with uniform conjoined singulars succeeds iff
    the gender is interpretable. This holds at the parameter type level,
    not just for specific Xhosa/Shona inventories.

    The language-specific `xhosa_matching_iff_interpretable` and
    `shona_matching_iff_interpretable` are corollaries of this theorem. -/
theorem bantu_matching_iff_interpretable (s : GenderStatus) :
    (resolve (statusToBundle s) (statusToBundle s)).isSome = s.isInterpretable := by
  cases s with
  | interpretable c => cases c <;> decide
  | uninterpretable => rfl

/-! ### Xhosa

Genders A (1/2), D (7/8) and E (9/10) carry the flavors i[human], i[inanimate] and i[animal];
B (3/4) and C (5/6) carry none, so they pair only with semantic agreement from classes 2, 8 or 10
(§4). The paper's Table 13 finds matching agreement at 100% for [1&1] human, 100% for non-human
[7&7] and [9&9], and 50% for human [9&9] against 40% default, while [3&3] and [5&5] reach 2.2%
matching at most.
-/

/-- Matching agreement is available for a Xhosa gender exactly when that gender is
interpretable. -/
theorem xhosa_matching_iff_interpretable (g : Xhosa.Gender) :
    (resolve (statusToBundle g.status) (statusToBundle g.status)).isSome
    = g.status.isInterpretable :=
  bantu_matching_iff_interpretable g.status

/-! ### Mismatched conjuncts -/

/-- Mismatched [human] conjuncts (e.g. [3&5] gangster + policeman):
    both have [human] core from stacking → intersection = [human].
    [carstens-2026] (85)a, (86)a: class 2 ba- agreement. -/
theorem xhosa_mismatched_human :
    resolve (statusToBundle (.interpretable .human))
           (statusToBundle (.interpretable .human))
    = some [.human] := by decide

/-- Mismatched [inanimate] conjuncts (e.g. [3&5] carrot + egg):
    both have [inanimate] core from stacking → intersection = [inanimate].
    [carstens-2026] (85)b, (86)b: class 8 zi- agreement. -/
theorem xhosa_mismatched_inanimate :
    resolve (statusToBundle (.interpretable .inanimate))
           (statusToBundle (.interpretable .inanimate))
    = some [.inanimate] := by decide

/-- Human + inanimate (e.g. [9&1a] girl + train):
    [human] ∩ [inanimate] = ∅ → ineffable.
    [carstens-2026] (91)–(92): agreement with conjoined humans
    and inanimates is generally ineffable. -/
theorem xhosa_human_inanimate_ineffable :
    resolve (statusToBundle (.interpretable .human))
           (statusToBundle (.interpretable .inanimate))
    = none := by decide

/-! ### Default agreement classes -/

/-- Default for [human]: class 2 ba- ([carstens-2026] (52c)). -/
theorem default_human_is_class2 :
    SemanticCore.defaultPluralClass .human = 2 := rfl

/-- Default for [inanimate]: class 8 zi- ([carstens-2026] (52c)). -/
theorem default_inanimate_is_class8 :
    SemanticCore.defaultPluralClass .inanimate = 8 := rfl

/-- Default for [animal]: class 8 zi- (class 10 = syncretic with 8 for
    default purposes; [carstens-2026] §3.4). -/
theorem default_animal_is_class8 :
    SemanticCore.defaultPluralClass .animal = 8 := rfl

/-! ### Shona -/

/-! Only 1/2 (i[human]) and 7/8 (i[non-human]) carry flavors among Shona's eight gender pairs;
3/4, 5/6, 9/10, 11/10, 14/6 and 12/13 carry none, so [3&3], [5&5], [9&9], [11&11], [14&14] and
[12&12] all take default agreement ((59)–(65)). Shona 9/10 differs from its Xhosa counterpart in
having lost the [animal] flavor (§5.2). -/

/-- The same for Shona, whose eight genders leave matching agreement available in two. -/
theorem shona_matching_iff_interpretable (g : Shona.Gender) :
    (resolve (statusToBundle g.status) (statusToBundle g.status)).isSome
    = g.status.isInterpretable :=
  bantu_matching_iff_interpretable g.status

/-! ### Stacked nouns -/

/-- Stacked nouns retain the core gender despite different visible class. -/
theorem stacking_preserves_core :
    Xhosa.humanInClass3.status = .interpretable .human ∧
    Xhosa.humanInClass5.status = .interpretable .human ∧
    Xhosa.animalInClass1.status = .interpretable .animal :=
  ⟨rfl, rfl, rfl⟩

/-! ### Interpretability in Distributed Morphology -/

/-- Bantu `SemanticCore` → DM `Interpretability` bridge.
    Interpretable genders bear `Interpretability.i` (natural gender);
    uninterpretable genders bear `Interpretability.u` (arbitrary gender).
    [carstens-2026] directly extends [kramer-2015]'s i/u distinction. -/
def toDMInterpretability : GenderStatus → DistributedMorphology.Interpretability
  | .interpretable _ => .i
  | .uninterpretable => .u

/-- The bridge preserves the interpretability predicate. -/
theorem dm_bridge_faithful (s : GenderStatus) :
    (toDMInterpretability s == .i) = s.isInterpretable := by
  cases s <;> rfl

/-- Bantu `SemanticCore` → typological `SemanticBasis` bridge.
    [carstens-2026]'s cores map to [kramer-2020]'s
    core semantic bases. All are `isCore = true`.

    The [non-human] core (Shona 7/8) maps to `.humanness` because
    Shona's system is organized around the human/non-human distinction.
    Xhosa's finer [animal] and [inanimate] cores map to `.animacy`. -/
def toSemanticBasis : SemanticCore → Corbett1991.SemanticBasis
  | .human     => .humanness
  | .animal    => .animacy
  | .inanimate => .animacy
  | .nonhuman  => .humanness

/-- All Bantu semantic cores map to Kramer's semantic core bases. -/
theorem bantu_cores_are_kramer_cores (c : SemanticCore) :
    Kramer2020.IsCore (toSemanticBasis c) := by
  cases c <;> trivial

/-! ### Resolution through the stack -/

/-- Resolution with nP stacking: agreement is determined by the stack's
    semantic core, not the visible class. Two nouns in different visible
    classes but the same core gender resolve to that core.
    [carstens-2026] (85)–(88): mismatched [3&5] humans → ba-,
    mismatched [3&5] inanimates → zi-. -/
def resolveStacks (s1 s2 : NPStack) : Option (List SemanticCore) :=
  resolve (statusToBundle s1.status) (statusToBundle s2.status)

/-- Criminal (cl3) + policeman (cl5): both [human] core → class 2 ba-.
    [carstens-2026] (85)a, (86)a. -/
theorem mismatched_3and5_human :
    resolveStacks
      ⟨3, 1, .interpretable .human⟩
      ⟨5, 1, .interpretable .human⟩
    = some [.human] := by decide

/-- Carrot (cl3) + egg (cl5): both [inanimate] core → class 8 zi-.
    [carstens-2026] (85)b, (86)b. -/
theorem mismatched_3and5_inanimate :
    resolveStacks
      ⟨3, 7, .interpretable .inanimate⟩
      ⟨5, 7, .interpretable .inanimate⟩
    = some [.inanimate] := by decide

/-- Medium (cl7, human) + girl (cl9, human): both have [human] core
    from nP stacking → [human] ∩ [human] = {[human]} → class 2 ba-.
    Visible genders differ (7 vs 9) but cores agree.
    [carstens-2026] (87)a, (88)a. -/
theorem mismatched_7and9_both_human :
    resolveStacks
      ⟨7, 1, .interpretable .human⟩
      ⟨9, 1, .interpretable .human⟩
    = some [.human] := by decide

/-- Backpack (cl1a, inanimate) + book (cl9, inanimate): both have
    [inanimate] core → [inanimate] ∩ [inanimate] = {[inanimate]} → class 8 zi-.
    [carstens-2026] (87)b, (88)b. -/
theorem mismatched_1aand9_both_inanimate :
    resolveStacks
      ⟨1, 7, .interpretable .inanimate⟩
      ⟨9, 7, .interpretable .inanimate⟩
    = some [.inanimate] := by decide

/-! ### Swahili -/

/-- Swahili's 5 genders also instantiate the Bantu semantic core system.
    [carstens-2026] §8 discusses Swahili's GAC (General Animate Concords)
    as evidence for a [+animate] feature. -/
theorem swahili_genderA_interpretable :
    Swahili.Gender.genderA.status.isInterpretable = true := rfl

theorem swahili_genderE_interpretable :
    Swahili.Gender.genderE.status.isInterpretable = true := rfl

/-- Three Bantu languages, shared diagnostic: A (1/2) = [human] in all. -/
theorem three_languages_agree_on_human :
    Xhosa.Gender.genderA.status = .interpretable .human ∧
    Shona.Gender.genderA.status = .interpretable .human ∧
    Swahili.Gender.genderA.status = .interpretable .human :=
  ⟨rfl, rfl, rfl⟩

/-! ### Stacking and the derivation

A noun's visible gender is the outer nP; the core it agrees by is the inner one. Stacking a
u-gender above an i-gender core leaves the percolated features untouched, so *gangster* (class 3)
and *policeman* (class 5), both `[n₃/₄ [n₁/₂ √]]` and `[n₅/₆ [n₁/₂ √]]`, resolve exactly as a pair
of canonical class-1 nouns does — class 2 agreement ((85a), (86a)) — and *carrot* and *egg*
likewise take class 8 ((86b)). A class-3 noun with no inner layer, like *hat*, has nothing to
percolate and falls to default agreement ((38a), (77a)). -/

/-- A u-gender stacked above an i-gender core percolates the core, so two nouns of different
visible genders that share a core resolve as if they shared a gender. -/
theorem stacked_core_resolve (c : SemanticCore) :
    resolve (nPStack nP_u (nP c)) (nPStack nP_u (nP c)) = some [c] := by
  cases c <;> decide

/-- A visible u-gender with no inner layer has nothing to percolate. -/
theorem unstacked_uninterpretable_resolve : resolve nP_u nP_u = none := rfl

/-! [carstens-2026] §5.1, (78)–(81): when arbitrary members of
    interpretable genders stack in non-canonical classes, both the outer
    (arbitrary) and inner (core) i-features percolate to &P. The intersection
    then contains multiple features, and two grammars determine which one
    selects the agreement class.

    We use a structured feature type that carries both the class number
    (determining agreement morphology) and a core/arbitrary flag
    (determining BSM specificity). -/

/-- Feature with core/arbitrary distinction for the two-grammars analysis.
    [carstens-2026] (71): n₁ = i[entity] i[core]; n₂ = i[entity]
    (for arbitrary members). Core features are more specific. -/
structure TwoGrammarFeature where
  classNum : Nat
  isCore : Bool
  deriving DecidableEq, Repr

/-- BSM specificity: core flavors outrank arbitrary i[entity]. -/
def TwoGrammarFeature.specificity (f : TwoGrammarFeature) : Nat :=
  if f.isCore then 2 else 1

/-- Feature bundle for train.1a: [n₁ₐ(arbitrary) [n₇(core inanimate) √TRAIN]].
    Outer: class 1, arbitrary i[entity] from gender A.
    Inner: class 7, core i[inanimate] from gender D.
    [carstens-2026] (78)a, (79)a, (80)a. -/
def trainFeatures : Bundle TwoGrammarFeature :=
  [⟨⟨1, false⟩, .interpretable⟩, ⟨⟨7, true⟩, .interpretable⟩]

/-- Feature bundle for diviner.7: [n₇(arbitrary) [n₁(core human) √DIVINER]].
    Outer: class 7, arbitrary i[entity] from gender D.
    Inner: class 1, core i[human] from gender A.
    [carstens-2026] (78)b, (79)b, (80)b. -/
def divinerFeatures : Bundle TwoGrammarFeature :=
  [⟨⟨7, false⟩, .interpretable⟩, ⟨⟨1, true⟩, .interpretable⟩]

/-- Intersection for train.1a & machine.1a: both layers survive.
    [carstens-2026] (79)a: &P {1, {7}} ∩ {1, {7}} = {1, {7}}. -/
theorem train_intersection :
    resolve trainFeatures trainFeatures
    = some [⟨1, false⟩, ⟨7, true⟩] := by decide

/-- Intersection for diviner.7 & scholar.7: both layers survive.
    [carstens-2026] (79)b: &P {7, {1}} ∩ {7, {1}} = {7, {1}}. -/
theorem diviner_intersection :
    resolve divinerFeatures divinerFeatures
    = some [⟨7, false⟩, ⟨1, true⟩] := by decide

/-- Highest Wins for train.1a & machine.1a: outermost = class 1 → cl 2 ba-.
    [carstens-2026] (79)a. -/
theorem train_highest_wins :
    selectFeature .highestWins
      TwoGrammarFeature.specificity
      [⟨1, false⟩, ⟨7, true⟩]
    = some ⟨1, false⟩ := rfl

/-- BSM for train.1a & machine.1a: core class 7 (inanimate) → cl 8 zi-.
    [carstens-2026] (80)a. -/
theorem train_best_semantic_match :
    selectFeature .bestSemanticMatch
      TwoGrammarFeature.specificity
      [⟨1, false⟩, ⟨7, true⟩]
    = some ⟨7, true⟩ := rfl

/-- Highest Wins for diviner.7 & scholar.7: outermost = class 7 → cl 8 zi-.
    [carstens-2026] (79)b. -/
theorem diviner_highest_wins :
    selectFeature .highestWins
      TwoGrammarFeature.specificity
      [⟨7, false⟩, ⟨1, true⟩]
    = some ⟨7, false⟩ := rfl

/-- BSM for diviner.7 & scholar.7: core class 1 (human) → cl 2 ba-.
    [carstens-2026] (80)b: 'The fool and the scholar are studying'
    with ba- agreement. -/
theorem diviner_best_semantic_match :
    selectFeature .bestSemanticMatch
      TwoGrammarFeature.specificity
      [⟨7, false⟩, ⟨1, true⟩]
    = some ⟨1, true⟩ := rfl

/-- The two grammars give DIFFERENT predictions for stacked nPs:
    for train.1a & machine.1a, HW picks class 1 (ba-) while BSM
    picks class 7 (zi-). Both are attested by Xhosa speakers.
    [carstens-2026] (81)a: zi- for [L & M] = BSM;
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

/-! ### Coordinate φ-resolution

The three φ-dimensions of a conjoined DP compose independently: number by lattice join
(`Number.resolveIn`, [link-1983], [harbour-2014]), person by hierarchy (`Person.resolve`,
[noyer-1997]), gender by percolation and intersection. Number and person always succeed;
only gender can fail, and then agreement is default. -/

/-- A conjunct DP's φ-bundle. -/
structure PhiBundle (G : Type) where
  person : Annotated Person
  number : Annotated Number
  gender : Bundle G

/-- Resolved φ-features for a conjoined DP (`&P`). -/
structure PhiResolved (G : Type) where
  person : Option Person
  number : Option Number
  gender : Option (List G)

/-- Percolate an annotated feature: its value iff interpretable. -/
private def percolate {F : Type} (a : Annotated F) : Option F :=
  if a.interp == .interpretable then some a.value else none

/-- Resolve two annotated features under a dimension operation `op`; both must be
    interpretable to proceed. -/
private def resolveAnnotated {F : Type} (op : F → F → Option F)
    (a b : Annotated F) : Option F :=
  match percolate a, percolate b with
  | some x, some y => op x y
  | _, _ => none

/-- Resolve all φ-features for two conjoined DPs, each dimension independently:
    number by `Number.resolveIn` (coarsened to `system`), person by `Person.resolve`,
    gender by percolation+intersection (`resolve`). -/
def resolveCoordinate {G : Type} [DecidableEq G]
    (system : List Number) (dp1 dp2 : PhiBundle G) : PhiResolved G :=
  { person := resolveAnnotated (fun p q => some (Person.resolve p q).coarsen)
                dp1.person dp2.person
    number := resolveAnnotated (fun a b => some (Number.resolveIn system a b))
                dp1.number dp2.number
    gender := resolve dp1.gender dp2.gender }

/-! ### Bantu coordinate-resolution outcomes

    The gender dimension, instantiated with `SemanticCore` via `statusToBundle`, gives
    the expected outcomes for conjoined Bantu singular DPs. -/

/-- A Bantu singular DP's phi-bundle: 3rd person (all full DPs are 3rd),
    singular number, gender from the noun's gender status. -/
def bantuDP (s : GenderStatus) : PhiBundle SemanticCore :=
  { person := ⟨.third, .interpretable⟩
    number := ⟨.singular, .interpretable⟩
    gender := statusToBundle s }

/-- Conjoined Bantu singulars → plural number (summation).
    Bantu languages have a {sg, pl} number system. -/
theorem bantu_coordinate_number (s₁ s₂ : GenderStatus) :
    (resolveCoordinate [.singular, .plural] (bantuDP s₁) (bantuDP s₂)).number = some .plural := by
  cases s₁ with
  | interpretable c₁ => cases s₂ with
    | interpretable c₂ => cases c₁ <;> cases c₂ <;> rfl
    | uninterpretable => cases c₁ <;> rfl
  | uninterpretable => cases s₂ with
    | interpretable c₂ => cases c₂ <;> rfl
    | uninterpretable => rfl

/-- Conjoined Bantu singulars → 3rd person (full DPs are always 3rd). -/
theorem bantu_coordinate_person (s₁ s₂ : GenderStatus) :
    (resolveCoordinate [.singular, .plural] (bantuDP s₁) (bantuDP s₂)).person = some .third := by
  cases s₁ with
  | interpretable c₁ => cases s₂ with
    | interpretable c₂ => cases c₁ <;> cases c₂ <;> rfl
    | uninterpretable => cases c₁ <;> rfl
  | uninterpretable => cases s₂ with
    | interpretable c₂ => cases c₂ <;> rfl
    | uninterpretable => rfl

/-- Gender dimension of composed resolution matches direct `resolve`. -/
theorem bantu_coordinate_gender (s₁ s₂ : GenderStatus) :
    (resolveCoordinate [.singular, .plural] (bantuDP s₁) (bantuDP s₂)).gender
    = resolve (statusToBundle s₁) (statusToBundle s₂) := by
  rfl

/-- End-to-end: conjoined [human] Xhosa singulars via unified resolution.
    Person: 3rd + 3rd → 3rd. Number: sg + sg → pl. Gender: [human] ∩ [human]
    = some [human]. All three succeed. -/
theorem xhosa_human_coordinate :
    resolveCoordinate [.singular, .plural]
                      (bantuDP (.interpretable .human))
                      (bantuDP (.interpretable .human))
    = ⟨some .third, some .plural, some [.human]⟩ := rfl

/-- End-to-end: conjoined uninterpretable Xhosa singulars.
    Person and number resolve; gender fails → default. -/
theorem xhosa_uninterpretable_coordinate :
    resolveCoordinate [.singular, .plural]
                      (bantuDP .uninterpretable) (bantuDP .uninterpretable)
    = ⟨some .third, some .plural, none⟩ := rfl

/-! ### The shared mechanism -/

/-! ### Shared mechanism

    [carstens-2026] explicitly adopts [adamson-anagnostopoulou-2025]'s
    percolation-and-intersection mechanism. Both studies use the same
    `resolve` function, instantiated with different
    feature types:
    - A&A: `Node` (privative geometry nodes — CLASS, MASC, FEM, etc.)
    - Carstens: `SemanticCore` (entity flavors — human, animal, inanimate)

    The bridge below proves this is not just a narrative claim but a
    structural fact: both resolution functions are projections of the same
    parameterized mechanism. -/

open AdamsonAnagnostopoulou2025

/-- Both studies agree on the self-matching property for interpretable
    features: Bantu interpretable cores self-match via `statusToBundle`,
    and A&A singleton i-features self-match — both through `resolve`. -/
theorem bantu_aa_self_matching_consistent :
    -- Bantu: interpretable cores self-match
    (∀ c : SemanticCore,
      (resolve (statusToBundle (.interpretable c)) (statusToBundle (.interpretable c))).isSome
      = true) ∧
    -- A&A: singleton i-features self-match
    (∀ f : Node,
      (resolve [⟨f, .interpretable⟩] [⟨f, .interpretable⟩]).isSome = true) := by
  constructor
  · intro c; cases c <;> decide
  · intro f; cases f <;> decide

/-! ### The Mismatch Resolution Hypothesis -/

/-! ### MRH failure in Bantu

    Unlike Greek/Icelandic ([adamson-anagnostopoulou-2025]), Bantu
    does NOT satisfy MRH: uninterpretable genders produce empty
    intersections, requiring default agreement. This is the structural
    reason why default agreement is needed in Bantu but not in Greek. -/

/-- Bantu does not satisfy MRH: the full inventory includes
    uninterpretable genders that yield empty intersections. -/
theorem bantu_fails_mrh :
    ¬ MismatchResolutionOn [statusToBundle (.interpretable .human),
                  statusToBundle (.interpretable .inanimate),
                  statusToBundle (.interpretable .animal),
                  statusToBundle .uninterpretable] := by decide

/-- Restricted to interpretable-only, MRH still fails:
    mismatched cores (human ≠ inanimate) yield empty intersection. -/
theorem bantu_interpretable_fails_mrh :
    ¬ MismatchResolutionOn [statusToBundle (.interpretable .human),
                  statusToBundle (.interpretable .inanimate),
                  statusToBundle (.interpretable .animal)] := by decide

/-- But uniform cores satisfy MRH trivially (self-matching). -/
theorem bantu_uniform_satisfies_mrh (c : SemanticCore) :
    MismatchResolutionOn [statusToBundle (.interpretable c),
                  statusToBundle (.interpretable c)] := by
  cases c <;> decide

/-! ### Three or more conjuncts

    `resolveN` extends the mechanism to n-ary coordination.
    Bantu predictions generalize cleanly: matching agreement requires
    ALL conjuncts to share the same interpretable core. -/

/-- Three [human] conjuncts → matching [human]. -/
theorem nary_three_humans :
    resolveN [statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .human)]
    = some [.human] := by decide

/-- Mixed: two [human] + one [inanimate] → default (none).
    A single mismatched conjunct blocks matching agreement. -/
theorem nary_mixed_fails :
    resolveN [statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .human),
              statusToBundle (.interpretable .inanimate)]
    = none := by decide

/-- N-ary subsumes binary for Bantu. -/
theorem nary_subsumes_binary_bantu (s₁ s₂ : GenderStatus) :
    resolveN [statusToBundle s₁, statusToBundle s₂]
    = resolve (statusToBundle s₁) (statusToBundle s₂) := by
  exact resolveN_binary (statusToBundle s₁) (statusToBundle s₂)

/-! ### Bridge to [taraldsen-et-al-2018]: shared classifier N ↔ matching agreement

[taraldsen-et-al-2018] §2 reads the same conjoined-singular agreement data
structurally: matching plural agreement succeeds iff the gender's singular and
plural prefixes contain the same classifier N. [carstens-2026]'s diagnostic is
semantic: matching succeeds iff the gender has an interpretable core. On the
Xhosa lexicon the two classifications coincide — the shared-N pairs (1/2, 7/8,
9/10) are exactly the interpretable genders (A, D, E). -/

/-- Per Xhosa gender, [carstens-2026]'s matching-agreement diagnostic agrees
    with [taraldsen-et-al-2018]'s shared-classifier-N diagnostic. -/
theorem xhosa_matching_iff_sharesClassifierN (g : Xhosa.Gender) :
    (resolve (statusToBundle g.status) (statusToBundle g.status)).isSome = true ↔
    TaraldsenEtAl2018.SharesClassifierN (TaraldsenEtAl2018.xhosaSg g)
      (TaraldsenEtAl2018.xhosaPl g) := by
  cases g <;> decide

end Carstens2026
