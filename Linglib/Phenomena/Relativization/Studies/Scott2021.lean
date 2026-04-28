import Linglib.Core.Relativization.Basic
import Linglib.Core.Tree
import Linglib.Fragments.Swahili.Relativization
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Theories.Syntax.Minimalist.Features

/-!
# Scott 2021: Two Types of Resumptive Pronouns in Swahili
@cite{scott-2021}

Two Types of Resumptive Pronouns in Swahili. *Linguistic Inquiry*
52(4): 812–833.

## Core Claims

Swahili distinguishes two types of resumptive pronouns:

1. **Movement copies** (personless: *-ye*, *-o*): lower copies of Ā-movement
   chains, reduced by chain reduction at PF. Diagnosed by parasitic gap
   constructions — the "true gap" position must license movement, and
   the "parasitic gap" position shows personless resumptives.

2. **Base-generated bound pronouns** (person-matching: *-mi*, *-we*, *-si*, *-nyi*):
   not copies — syntactically bound by the head of the RC. Diagnosed by
   adjunct islands — movement is blocked, so only binding is available,
   and bound resumptives obligatorily match person.

## Analysis: Chain Reduction + MaxElide

Following @cite{landau-2006} and @cite{van-urk-2018}:

- Movement leaves full copies of the pronoun (including PersP)
- Chain reduction at PF deletes copies except the highest
- Where a phonological requirement (bimoraic Minimality on monosyllabic
  prepositions) prevents full deletion, MaxElide deletes the largest
  deletable constituent — PersP
- After PersP deletion, the remaining features [GEN: ANIM, NUM: SG/PL]
  trigger insertion of the less specific (personless) VI *-ye* or *-o*

## DP Structure (Tree-Based)

Pronouns: [DP D [NumP Num [nP n_anim [PersP Pers:x]]]]
Lexical DPs: [DP D [NumP Num [nP n/n_anim [√P √]]]]

Modeled using `Core.Tree DPCat String` with Minimalism-grounded
categories (D, Num, n, Pers).

## Vocabulary Insertion (FeatureBundle-Based)

Uses `Minimalist.FeatureBundle` and `Morphology.DM.VI.vocabularyInsertSimple`
from the DM theory module. The Elsewhere Condition is structural: person-
specified rules (specificity 3) beat personless defaults (specificity 2).
Chain reduction removes person features from the bundle, so only the
default matches.
-/

namespace Phenomena.Relativization.Studies.Scott2021

open Core Fragments.Swahili
open Minimalist (FeatureBundle FeatureVal PhiFeature)
open Features.Prominence (PersonLevel)

-- ============================================================================
-- § 1: DP-Internal Categories
-- ============================================================================

/-- Categories for DP-internal structure. Grounded in Minimalism
    categories but restricted to the four projections relevant to
    Bantu pronoun structure (@cite{scott-2021}). -/
inductive DPCat where
  | D     -- determiner (outermost; null in Swahili)
  | Num   -- number (hosts sg/pl; portmanteau with n)
  | n     -- categorizer (hosts gender/animacy; @cite{kramer-2015})
  | Pers  -- person (innermost; only in pronouns, not lexical DPs)
  deriving DecidableEq, Repr

instance : Inhabited DPCat := ⟨.D⟩

-- ============================================================================
-- § 2: Tree-Based DP Structure
-- ============================================================================

open Core.Tree (Tree)

/-- 1SG pronoun *mi*: [DP D [NumP Num:sg [nP n_anim [PersP 1]]]]
    @cite{scott-2021}. -/
def pronTree1sg : Tree DPCat String :=
  .node .D [
    .terminal .D "",
    .node .Num [
      .terminal .Num "sg",
      .node .n [
        .terminal .n "anim",
        .node .Pers [.terminal .Pers "1"]]]]

/-- 2SG pronoun *we*: [DP D [NumP Num:sg [nP n_anim [PersP 2]]]] -/
def pronTree2sg : Tree DPCat String :=
  .node .D [
    .terminal .D "",
    .node .Num [
      .terminal .Num "sg",
      .node .n [
        .terminal .n "anim",
        .node .Pers [.terminal .Pers "2"]]]]

/-- Noun class 1 pronoun *ye* (no person): [DP D [NumP Num:sg [nP n_anim]]]
    @cite{scott-2021}. This is also the structure AFTER chain reduction
    deletes PersP from a 1SG/2SG pronoun. -/
def pronTreeCl1 : Tree DPCat String :=
  .node .D [
    .terminal .D "",
    .node .Num [
      .terminal .Num "sg",
      .node .n [.terminal .n "anim"]]]

/-- Plural counterparts. -/
def pronTree1pl : Tree DPCat String :=
  .node .D [
    .terminal .D "",
    .node .Num [
      .terminal .Num "pl",
      .node .n [
        .terminal .n "anim",
        .node .Pers [.terminal .Pers "1"]]]]

def pronTreeCl2 : Tree DPCat String :=
  .node .D [
    .terminal .D "",
    .node .Num [
      .terminal .Num "pl",
      .node .n [.terminal .n "anim"]]]

-- ============================================================================
-- § 3: MaxElide as Structural Deletion
-- ============================================================================

mutual
/-- Delete the PersP subtree from a pronoun tree. This is what MaxElide
    does to movement copies: it removes the biggest deletable constituent,
    which is PersP (nP cannot be deleted because Num and n form a
    portmanteau — no VI exists for Num alone).

    Uses mutual recursion with list helpers so that tree operations
    reduce definitionally on concrete trees. -/
def deletePersP : Tree DPCat String → Tree DPCat String
  | .node .n children => .node .n (filterPers children)
  | .node c children => .node c (mapDeletePersP children)
  | other => other

private def mapDeletePersP : List (Tree DPCat String) → List (Tree DPCat String)
  | [] => []
  | t :: ts => deletePersP t :: mapDeletePersP ts

private def filterPers : List (Tree DPCat String) → List (Tree DPCat String)
  | [] => []
  | t :: ts => if t.cat == .Pers then filterPers ts else t :: filterPers ts
end

/-- Deleting PersP from a 1SG pronoun yields a class 1 pronoun. -/
theorem delete_persP_1sg : deletePersP pronTree1sg = pronTreeCl1 := rfl

/-- Deleting PersP from a 2SG pronoun yields the same class 1 pronoun. -/
theorem delete_persP_2sg : deletePersP pronTree2sg = pronTreeCl1 := rfl

/-- Deleting PersP from a 1PL pronoun yields a class 2 pronoun. -/
theorem delete_persP_1pl : deletePersP pronTree1pl = pronTreeCl2 := rfl

/-- Class 1 pronoun has no PersP — deletion is idempotent. -/
theorem delete_persP_idempotent : deletePersP pronTreeCl1 = pronTreeCl1 := rfl

-- ============================================================================
-- § 4: Feature Extraction from Trees
-- ============================================================================

/-- Extract the feature bundle from a pronoun tree's terminals.
    Each terminal maps to a `FeatureVal`:
    - Pers "1" → phi (person .first)
    - Pers "2" → phi (person .second)
    - Num "sg" → phi (number .Sing)
    - Num "pl" → phi (number .Plur)
    - n "anim" → phi (gender 1)   (encoding animacy as gender 1) -/
def terminalToFeature : DPCat → String → Option FeatureVal
  | .Pers, "1" => some (.phi (.person .first))
  | .Pers, "2" => some (.phi (.person .second))
  | .Num, "sg" => some (.phi (.number .Sing))
  | .Num, "pl" => some (.phi (.number .Plur))
  | .n, "anim" => some (.phi (.gender 1))
  | _, _ => none

mutual
/-- Collect all features from a tree's terminals.
    Uses mutual recursion for definitional reduction. -/
def extractFeatures : Tree DPCat String → FeatureBundle
  | .terminal c w => match terminalToFeature c w with
    | some fv => [.valued fv]
    | none => []
  | .node _ children => extractFeaturesList children
  | .trace _ _ => []
  | .bind _ _ body => extractFeatures body

private def extractFeaturesList : List (Tree DPCat String) → FeatureBundle
  | [] => []
  | t :: ts => extractFeatures t ++ extractFeaturesList ts
end

/-- 1SG pronoun has features: [number:sg, gender:anim, person:1].
    (Order follows depth-first tree traversal.) -/
theorem features_1sg :
    extractFeatures pronTree1sg =
    [.valued (.phi (.number .Sing)),
     .valued (.phi (.gender 1)),
     .valued (.phi (.person .first))] := by decide

/-- After PersP deletion, features are: [number:sg, gender:anim] — no person. -/
theorem features_after_deletion :
    extractFeatures (deletePersP pronTree1sg) =
    [.valued (.phi (.number .Sing)),
     .valued (.phi (.gender 1))] := by decide

-- ============================================================================
-- § 5: Vocabulary Insertion via DM Elsewhere Condition
-- ============================================================================

/-- Helper: does a feature bundle contain a person feature? -/
def hasPerson (fb : FeatureBundle) : Bool :=
  fb.any fun f => match f with
    | .valued (.phi (.person _)) => true
    | _ => false

/-- Helper: extract the person level if present. -/
def getPerson (fb : FeatureBundle) : Option PersonLevel :=
  fb.findSome? fun f => match f with
    | .valued (.phi (.person p)) => some p
    | _ => none

/-- Helper: is the number singular? -/
def isSg (fb : FeatureBundle) : Bool :=
  fb.any fun f => match f with
    | .valued (.phi (.number .Sing)) => true
    | _ => false

/-- Helper: does the bundle contain animacy? -/
def isAnim (fb : FeatureBundle) : Bool :=
  fb.any fun f => match f with
    | .valued (.phi (.gender 1)) => true
    | _ => false

/-- Swahili resumptive VI rules using the DM `VocabItem` type.
    @cite{scott-2021}. Person-specified rules have specificity 3
    (checking 3 features); personless defaults have specificity 2.
    The Elsewhere Condition in `vocabularyInsertSimple` picks the most
    specific matching rule. -/
def resumptiveVIRules : List (Morphology.DM.VI.VocabItem FeatureBundle Unit) :=
  [ -- [PERS: 1, GEN: ANIM, NUM: SG] ↔ -mi
    { exponent := "-mi"
    , contextMatch := fun fb => getPerson fb == some .first && isAnim fb && isSg fb
    , specificity := 3 }
  , -- [PERS: 1, GEN: ANIM, NUM: PL] ↔ -si
    { exponent := "-si"
    , contextMatch := fun fb => getPerson fb == some .first && isAnim fb && !isSg fb
    , specificity := 3 }
  , -- [PERS: 2, GEN: ANIM, NUM: SG] ↔ -we
    { exponent := "-we"
    , contextMatch := fun fb => getPerson fb == some .second && isAnim fb && isSg fb
    , specificity := 3 }
  , -- [PERS: 2, GEN: ANIM, NUM: PL] ↔ -nyi
    { exponent := "-nyi"
    , contextMatch := fun fb => getPerson fb == some .second && isAnim fb && !isSg fb
    , specificity := 3 }
  , -- [GEN: ANIM, NUM: SG] ↔ -ye (default animate sg)
    { exponent := "-ye"
    , contextMatch := fun fb => isAnim fb && isSg fb
    , specificity := 2 }
  , -- [GEN: ANIM, NUM: PL] ↔ -o (default animate pl)
    { exponent := "-o"
    , contextMatch := fun fb => isAnim fb && !isSg fb
    , specificity := 2 }
  ]

/-- Insert the correct resumptive exponent for a feature bundle
    using the DM Elsewhere Condition. -/
def insertResumptive (fb : FeatureBundle) : String :=
  (Morphology.DM.VI.vocabularyInsertSimple resumptiveVIRules fb).getD "-ye"

-- ============================================================================
-- § 6: Chain Reduction Pipeline
-- ============================================================================

/-- Whether a pronoun occurrence is a movement copy (part of an
    Ā-movement chain). Only copies undergo chain reduction. -/
inductive PronOrigin where
  | bound
  | movementCopy
  deriving DecidableEq, Repr

/-- Full pipeline: tree → (optional) MaxElide → feature extraction → VI.

    - Bound pronouns: tree is unchanged → full features → person-matching VI
    - Movement copies: MaxElide deletes PersP → reduced features → personless VI -/
def realize (tree : Tree DPCat String) (origin : PronOrigin) : String :=
  let pfTree := match origin with
    | .bound => tree
    | .movementCopy => deletePersP tree
  insertResumptive (extractFeatures pfTree)

-- ============================================================================
-- § 7: Core Predictions — Bound Resumptives
-- ============================================================================

-- TODO: `decide` chokes on String equality through `Morphology.DM.VI`;
-- restructure as compositional lemmas (extractFeatures + insertResumptive).

/-- Bound 1SG in adjunct island → person-matching *-mi*. -/
theorem island_bound_1sg : realize pronTree1sg .bound = "-mi" := by native_decide

/-- Bound 2SG in adjunct island → person-matching *-we*. -/
theorem island_bound_2sg : realize pronTree2sg .bound = "-we" := by native_decide

/-- Bound 1PL in adjunct island → person-matching *-si*. -/
theorem island_bound_1pl : realize pronTree1pl .bound = "-si" := by native_decide

-- ============================================================================
-- § 8: Core Predictions — Movement Resumptives
-- ============================================================================

/-- Movement copy 1SG in parasitic gap → personless *-ye*. -/
theorem parasitic_movement_1sg : realize pronTree1sg .movementCopy = "-ye" := by
  native_decide

/-- Movement copy 2SG in parasitic gap → also *-ye*. Person is irrelevant
    because chain reduction deletes PersP regardless. -/
theorem parasitic_movement_2sg : realize pronTree2sg .movementCopy = "-ye" := by
  native_decide

/-- Movement copy 1PL in parasitic gap → personless *-o*. -/
theorem parasitic_movement_1pl : realize pronTree1pl .movementCopy = "-o" := by
  native_decide

/-- Both 1SG and 2SG movement copies produce the same form — chain
    reduction erases the person distinction. -/
theorem movement_erases_person_distinction :
    realize pronTree1sg .movementCopy = realize pronTree2sg .movementCopy := by
  native_decide

-- ============================================================================
-- § 9: End-to-End Argumentation Chain
-- ============================================================================

/-- The complete derivation in one theorem:
    1. Start with 1SG pronoun tree (with PersP:1)
    2. MaxElide deletes PersP → tree matches class 1 structure
    3. Feature extraction yields [number:sg, gender:anim] — no person
    4. VI inserts *-ye* (specificity 2 default beats nothing more specific)
    5. The same tree, unreduced (bound), yields *-mi* (specificity 3 wins) -/
theorem end_to_end :
    -- Step 2: MaxElide produces class 1 structure
    deletePersP pronTree1sg = pronTreeCl1 ∧
    -- Step 3: no person features remain
    hasPerson (extractFeatures (deletePersP pronTree1sg)) = false ∧
    -- Step 4: VI produces -ye
    realize pronTree1sg .movementCopy = "-ye" ∧
    -- Step 5: unreduced VI produces -mi
    realize pronTree1sg .bound = "-mi" := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 10: Parasitic Gap Interspeaker Variation (Table 4)
-- ============================================================================

/-- Parasitic gap judgments per speaker. Each field encodes whether the
    combination (true-gap-form ... parasitic-gap-form) is accepted.
    @cite{scott-2021} Table 4. -/
structure ParasiticGapJudgments where
  moveMove : Bool       -- Row 1: ye_t ... ye_p
  pronounMove : Bool    -- Row 2: mi_t ... ye_p
  pronounPronoun : Bool -- Row 3: mi_t ... mi_p
  movePronoun : Bool    -- Row 4: ye_t ... mi_p
  deriving DecidableEq, Repr

def speaker1 : ParasiticGapJudgments :=
  { moveMove := true, pronounMove := false, pronounPronoun := false, movePronoun := false }

def speaker2 : ParasiticGapJudgments :=
  { moveMove := true, pronounMove := false, pronounPronoun := true, movePronoun := false }

def speaker3 : ParasiticGapJudgments :=
  { moveMove := true, pronounMove := false, pronounPronoun := true, movePronoun := false }

/-- All speakers accept ye...ye (Row 1); no speaker accepts mi...ye
    (Row 2) or ye...mi (Row 4). The parasitic gap requires the true gap
    to also be movement, and a movement true gap cannot license a bound
    parasitic pronoun. -/
theorem parasitic_gap_generalization :
    -- Row 1: ye_t ... ye_p is universally accepted
    (speaker1.moveMove && speaker2.moveMove && speaker3.moveMove) = true ∧
    -- Row 2: mi_t ... ye_p is universally rejected
    (speaker1.pronounMove || speaker2.pronounMove || speaker3.pronounMove) = false ∧
    -- Row 4: ye_t ... mi_p is universally rejected
    (speaker1.movePronoun || speaker2.movePronoun || speaker3.movePronoun) = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 11: Islands Are Syntactic, Not Phonological
-- ============================================================================

/-- Both island constructions have overt resumptive pronouns — the
    difference is syntactic (movement vs. binding), not phonological
    (overt vs. gap). If islands were phonological, both *-mi* and *-ye*
    should be equally acceptable inside islands. -/
theorem islands_are_syntactic :
    realize pronTree1sg .bound = "-mi" ∧
    realize pronTree1sg .movementCopy = "-ye" ∧
    realize pronTree1sg .bound ≠ realize pronTree1sg .movementCopy := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 12: MaxElide Targets PersP
-- ============================================================================

/-- Whether a DP layer can be deleted by MaxElide. Deletable iff the
    remaining material can be spelled out (a VI exists for the residue).
    - PersP: deletable (VI [sg + n_anim] ↔ *-ye* exists)
    - nP: NOT deletable (Num and n portmanteau; no VI for Num alone)
    - NumP/DP: never deleted (highest copy is pronounced) -/
def DPCat.isDeletable : DPCat → Bool
  | .Pers => true
  | .n    => false
  | .Num  => false
  | .D    => false

/-- MaxElide: "Elide the biggest deletable constituent." Trying from
    biggest (D) to smallest (Pers), PersP is the only deletable layer. -/
def maxElideTarget : Option DPCat :=
  [DPCat.D, .Num, .n, .Pers].find? DPCat.isDeletable

theorem maxElide_targets_persP : maxElideTarget = some .Pers := by decide

-- ============================================================================
-- § 13: Structural Properties
-- ============================================================================

/-- Chain reduction (PersP deletion) preserves number features. -/
theorem reduction_preserves_number :
    isSg (extractFeatures (deletePersP pronTree1sg)) =
    isSg (extractFeatures pronTree1sg) := by decide

/-- Chain reduction preserves animacy features. -/
theorem reduction_preserves_animacy :
    isAnim (extractFeatures (deletePersP pronTree1sg)) =
    isAnim (extractFeatures pronTree1sg) := by decide

/-- Chain reduction removes person features. -/
theorem reduction_removes_person :
    hasPerson (extractFeatures pronTree1sg) = true ∧
    hasPerson (extractFeatures (deletePersP pronTree1sg)) = false :=
  ⟨by decide, by decide⟩

/-- Bound pronouns retain person features (no PersP deletion). -/
theorem bound_retains_person :
    hasPerson (extractFeatures pronTree1sg) = true := by decide

-- ============================================================================
-- § 14: Cross-Linguistic Prediction
-- ============================================================================

/-- If a language has both types with morphological distinction,
    the movement resumptive is featurally a proper subset of the
    bound resumptive (chain reduction only deletes). -/
theorem movement_is_subset :
    let fullFeats := extractFeatures pronTree1sg
    let reducedFeats := extractFeatures (deletePersP pronTree1sg)
    reducedFeats.length < fullFeats.length ∧
    reducedFeats.all (· ∈ fullFeats) := by
  constructor <;> decide

/-- Full pronoun alternation: bound *-mi* can alternate with full
    *mimi*, but movement *-ye* cannot alternate with *yeye*.
    Movement copies exist only to satisfy bimoraic minimality. -/
def canAlternateWithFull (origin : PronOrigin) : Bool :=
  match origin with
  | .bound => true
  | .movementCopy => false

theorem bound_alternates : canAlternateWithFull .bound = true := rfl
theorem movement_no_alternate : canAlternateWithFull .movementCopy = false := rfl

-- ============================================================================
-- § 15: Bridge — Fragment Consistency
-- ============================================================================

/-- The theory-neutral observation in the Fragment (`resumptivePronounIsPersonMatching`)
    is consistent with the theoretical pipeline in this study (`realize`).
    Person-matching (bound) ↔ Fragment says true; personless (movement) ↔ false. -/
theorem fragment_consistency_1sg :
    resumptivePronounIsPersonMatching .first .sg = true ∧
    realize pronTree1sg .bound = resumptivePronoun .first .sg ∧
    realize pronTree1sg .movementCopy = resumptivePronoun .third .sg := by
  refine ⟨rfl, ?_, ?_⟩ <;> native_decide

/-- The movement marker in the Fragment is correctly classified. -/
theorem marker_classification :
    ambaMovement.npRel.isMovementCopy = some true ∧
    ambaBound.npRel.isMovementCopy = some false ∧
    ambaGap.npRel.isMovementCopy = none := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 16: Cross-Linguistic Prediction — Person Entails Number
-- ============================================================================

/-- "If the copied pronouns match in person, they also match in number"
    (@cite{scott-2021} §6). This follows from the DP structure: Num
    dominates PersP, so deleting PersP cannot affect Num. Conversely,
    if person survives (not deleted), then Num — being structurally
    higher — necessarily also survived. -/
theorem person_entails_number :
    -- If person features are present, number features must be present too
    hasPerson (extractFeatures pronTree1sg) = true →
    isSg (extractFeatures pronTree1sg) = true := by
  intro; decide

/-- The converse does NOT hold: number can be present without person
    (as in noun class pronouns / movement copies). -/
theorem number_without_person :
    isSg (extractFeatures pronTreeCl1) = true ∧
    hasPerson (extractFeatures pronTreeCl1) = false := by
  constructor <;> decide

end Phenomena.Relativization.Studies.Scott2021
