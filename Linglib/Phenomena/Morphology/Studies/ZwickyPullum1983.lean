import Linglib.Core.Morphology.MorphRule
import Linglib.Fragments.English.Auxiliaries
import Linglib.Core.IntensionalLogic.RestrictedModality
import Mathlib.Data.Fin.Basic

-- ============================================================================
-- §0: Six-Criteria Diagnostic Substrate
--     (was Theories/Morphology/Core/CliticVsAffix.lean, relocated 0.230.455 —
--     ZP 1983 is the originating paper, anchor lives here)
-- ============================================================================

/-! Six criteria for distinguishing clitics from inflectional affixes,
formalized as a diagnostic profile. The classification (clitic vs. affix)
is *derived* from the profile, not stipulated. ZP's surprising result:
English *-n't* scores affix-like on all six.

| Criterion | Clitic-like | Affix-like |
|-----------|-------------|------------|
| A. Selection | low (any category) | high (specific stems) |
| B. Paradigm gaps | none | present |
| C. Morphophonological idiosyncrasies | none | present |
| D. Semantic idiosyncrasies | none | present |
| E. Syntactic rules affect combination | no | yes |
| F. Attaches to cliticized material | yes | no | -/

namespace Morphology.Diagnostics

open Core.Morphology (MorphStatus SelectionDegree)

structure CliticAffixProfile where
  morpheme : String
  selection : SelectionDegree
  hasArbitraryGaps : Bool
  hasMorphophonIdiosyncrasies : Bool
  hasSemanticIdiosyncrasies : Bool
  syntacticRulesApply : Bool
  attachesToCliticizedMaterial : Bool
  deriving Repr, BEq

def CliticAffixProfile.affixLikeSelection (p : CliticAffixProfile) : Bool :=
  decide p.selection.IsHighSelection

def CliticAffixProfile.affixScore (p : CliticAffixProfile) : Nat :=
  let scores : List Bool := [
    p.affixLikeSelection,
    p.hasArbitraryGaps,
    p.hasMorphophonIdiosyncrasies,
    p.hasSemanticIdiosyncrasies,
    p.syntacticRulesApply,
    !p.attachesToCliticizedMaterial
  ]
  scores.filter id |>.length

def CliticAffixProfile.cliticScore (p : CliticAffixProfile) : Nat :=
  6 - p.affixScore

def CliticAffixProfile.classify (p : CliticAffixProfile) : MorphStatus :=
  if p.affixScore == 6 then .inflAffix
  else if p.cliticScore == 6 then .simpleClitic
  else .specialClitic

def CliticAffixProfile.isUnambiguousAffix (p : CliticAffixProfile) : Bool :=
  p.affixScore == 6

def CliticAffixProfile.isUnambiguousClitic (p : CliticAffixProfile) : Bool :=
  p.cliticScore == 6

theorem classify_all_affix (p : CliticAffixProfile)
    (h : p.affixScore = 6) :
    p.classify = .inflAffix := by
  simp [CliticAffixProfile.classify, h]

theorem classify_all_clitic (p : CliticAffixProfile)
    (h : p.affixScore = 0) :
    p.classify = .simpleClitic := by
  simp [CliticAffixProfile.classify, h, CliticAffixProfile.cliticScore]

theorem classify_total (p : CliticAffixProfile) :
    p.classify = .inflAffix ∨ p.classify = .simpleClitic
    ∨ p.classify = .specialClitic := by
  unfold CliticAffixProfile.classify
  split
  · left; rfl
  · split
    · right; left; rfl
    · right; right; rfl

end Morphology.Diagnostics

/-!
# @cite{zwicky-pullum-1983}: Cliticization vs. Inflection
@cite{zwicky-pullum-1983}

Empirical data and classification theorems for the argument that
English contracted negator *-n't* is an inflectional affix, not a
simple clitic.

## Core argument

Six diagnostics (A–F) separate clitics from inflectional affixes.
English simple clitics (*'s*, *'ve*, *'d*) score clitic-like on all six.
English inflectional affixes (*-ed*, *-s*, *-est*) score affix-like on all six.
The contracted negator *-n't* scores **affix-like on all six** — a surprising
result given the near-universal prior assumption that it is a clitic.

## Semantic scope bridge (criterion D)

The scope irregularity of negation with modals provides a bridge to
`Semantics.Modality`: *can't* means NOT(CAN(P)) but *mustn't*
means MUST(NOT(P)). This non-compositional scope behavior is characteristic
of inflectional affixes, not clitics.

-/

namespace Phenomena.Morphology.ZwickyPullum1983

open Morphology.Diagnostics
open Core.Morphology (MorphStatus SelectionDegree)
open Fragments.English.Auxiliaries (AuxEntry)

-- ============================================================================
-- §1: Diagnostic Profiles
-- ============================================================================

/-! ### Simple clitics: *'s* (has/is), *'ve*, *'d*

Z&P §2 (criteria A–D) and §3 (criteria E–F):
- A. Low selection: attach to prepositions, verbs, adjectives, adverbs
- B. No arbitrary gaps: combine with any phonologically suitable host
- C. No morphophonological idiosyncrasies: regular reduction
- D. No semantic idiosyncrasies: meaning identical to full form
- E. No syntactic rules affect the combination (no SAI on clitic groups)
- F. Can attach to material already containing clitics (*I'd've*) -/

def cliticS : CliticAffixProfile where
  morpheme := "'s (has/is)"
  selection := .low
  hasArbitraryGaps := false
  hasMorphophonIdiosyncrasies := false
  hasSemanticIdiosyncrasies := false
  syntacticRulesApply := false
  attachesToCliticizedMaterial := true

def cliticVe : CliticAffixProfile where
  morpheme := "'ve (have)"
  selection := .low
  hasArbitraryGaps := false
  hasMorphophonIdiosyncrasies := false
  hasSemanticIdiosyncrasies := false
  syntacticRulesApply := false
  attachesToCliticizedMaterial := true

def cliticD : CliticAffixProfile where
  morpheme := "'d (had/would)"
  selection := .low
  hasArbitraryGaps := false
  hasMorphophonIdiosyncrasies := false
  hasSemanticIdiosyncrasies := false
  syntacticRulesApply := false
  attachesToCliticizedMaterial := true

/-! ### Inflectional affixes: *-ed* (past), *-s* (plural), *-est* (superlative)

Z&P §2 (criteria A–D) and §3 (criteria E–F):
- A. High selection: each attaches to a single major category
- B. Arbitrary gaps: *strided, *goed
- C. Morphophonological idiosyncrasies: *slept*, *went*, *best*
- D. Semantic idiosyncrasies: *last* (superlative of *late*, but not
     "most recent" — rather "final")
- E. Syntactic rules affect affixed words (inflected nouns, verbs,
     adjectives are regular syntactic units)
- F. Cannot attach to cliticized material -/

def affixEd : CliticAffixProfile where
  morpheme := "-ed (past tense)"
  selection := .singleCategory
  hasArbitraryGaps := true
  hasMorphophonIdiosyncrasies := true
  hasSemanticIdiosyncrasies := true
  syntacticRulesApply := true
  attachesToCliticizedMaterial := false

def affixPluralS : CliticAffixProfile where
  morpheme := "-s (noun plural)"
  selection := .singleCategory
  hasArbitraryGaps := true      -- *oxes, *sheeps
  hasMorphophonIdiosyncrasies := true  -- oxen, dice, feet
  hasSemanticIdiosyncrasies := true     -- "last words" is idiomatic
  syntacticRulesApply := true
  attachesToCliticizedMaterial := false

def affixEst : CliticAffixProfile where
  morpheme := "-est (superlative)"
  selection := .singleCategory
  hasArbitraryGaps := true      -- *beautifulest
  hasMorphophonIdiosyncrasies := true  -- best, worst
  hasSemanticIdiosyncrasies := true     -- last, most
  syntacticRulesApply := true
  attachesToCliticizedMaterial := false

/-! ### The contracted negator *-n't*

Z&P §4 (the core of the paper):
- A. High selection (closedClass): attaches only to finite auxiliaries
     (not to main verbs, prepositions, adjectives, adverbs)
- B. Arbitrary gaps: *mayn't, *amn't (Table 1)
- C. Morphophonological idiosyncrasies: *won't* [wont] ← *will*,
     *can't* [kænt] ← *can*, *don't* [dont] ← *do*, *shan't* ← *shall*
- D. Semantic idiosyncrasies: *mustn't* = MUST(NOT(P)), not NOT(MUST(P));
     *can't* = NOT(CAN(P)), not CAN(NOT(P)). Scope of negation varies.
- E. SAI applies to *-n't* forms: *Isn't he?*, *Can't you?*, *Haven't
     they?*. Contracted negator moves with auxiliary under T-to-C.
- F. Cannot attach to cliticized material: **I'd'ven't* (cf. *I'd've*) -/

def negNt : CliticAffixProfile where
  morpheme := "-n't (contracted negator)"
  selection := .closedClass
  hasArbitraryGaps := true
  hasMorphophonIdiosyncrasies := true
  hasSemanticIdiosyncrasies := true
  syntacticRulesApply := true
  attachesToCliticizedMaterial := false

-- ============================================================================
-- §2: Classification Theorems
-- ============================================================================

/-! The simple clitics classify as `simpleClitic`. -/

theorem cliticS_is_clitic : cliticS.classify = .simpleClitic := by native_decide
theorem cliticVe_is_clitic : cliticVe.classify = .simpleClitic := by native_decide
theorem cliticD_is_clitic : cliticD.classify = .simpleClitic := by native_decide

/-! The inflectional affixes classify as `inflAffix`. -/

theorem affixEd_is_affix : affixEd.classify = .inflAffix := by native_decide
theorem affixPluralS_is_affix : affixPluralS.classify = .inflAffix := by native_decide
theorem affixEst_is_affix : affixEst.classify = .inflAffix := by native_decide

/-! **The main result**: *-n't* classifies as `inflAffix`, not `simpleClitic`. -/

theorem nt_is_affix : negNt.classify = .inflAffix := by native_decide

/-! *-n't* scores 6/6 affix-like — unambiguous. -/

theorem nt_unambiguous : negNt.isUnambiguousAffix = true := by native_decide

/-! The simple clitics score 0/6 affix-like — unambiguous. -/

theorem clitics_unambiguous :
    cliticS.isUnambiguousClitic = true ∧
    cliticVe.isUnambiguousClitic = true ∧
    cliticD.isUnambiguousClitic = true := by
  constructor <;> [native_decide; constructor <;> native_decide]

-- ============================================================================
-- §3: Paradigm Gap Verification (Criterion B)
-- ============================================================================

/-! Verify that the paradigm gaps in Table 1 are encoded in the Fragment data. -/

open Fragments.English.Auxiliaries in
/-- *may* has no contracted negative form (*mayn't is a paradigm gap). -/
theorem may_gap : may.negForm = none := rfl

open Fragments.English.Auxiliaries in
/-- *am* has no contracted negative form (*amn't is a paradigm gap). -/
theorem am_gap : am.negForm = none := rfl

-- ============================================================================
-- §4: Morphophonological Irregularity Verification (Criterion C)
-- ============================================================================

/-! Verify that the phonologically irregular forms are flagged in Fragment data. -/

open Fragments.English.Auxiliaries in
/-- *won't* is phonologically irregular (not *willn't*). -/
theorem wont_irregular : will.negIrregular = true := rfl

open Fragments.English.Auxiliaries in
/-- *can't* is phonologically irregular. -/
theorem cant_irregular : can.negIrregular = true := rfl

open Fragments.English.Auxiliaries in
/-- *don't* is phonologically irregular (not *don't* [dunt]). -/
theorem dont_irregular : do_.negIrregular = true := rfl

open Fragments.English.Auxiliaries in
/-- *shan't* is phonologically irregular (not *shalln't*). -/
theorem shant_irregular : shall.negIrregular = true := rfl

open Fragments.English.Auxiliaries in
/-- *mustn't* shows [t]-deletion: [mʌsnt] not *[mʌstnt]. -/
theorem mustnt_irregular : must.negIrregular = true := rfl

open Fragments.English.Auxiliaries in
/-- Regular forms: *couldn't*, *wouldn't*, *shouldn't* show no irregularity. -/
theorem regular_negatives :
    could.negIrregular = false ∧
    would.negIrregular = false ∧
    should.negIrregular = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §5: Semantic Scope Bridge (Criterion D)
-- ============================================================================

/-! ### Scope of negation with contracted modals

Z&P observe that *can't* and *mustn't* show opposite scope relations:

- *You can't go home* = NOT(CAN(P)): negation scopes over possibility
- *You mustn't go home* = MUST(NOT(P)): necessity scopes over negation

This is an irregularity in the connection between the contracted form
and its uncontracted paraphrase. For *can*, *You cannot go home* = *You
can not go home* = NOT(CAN(P)). But for *must*, *You must not go home* is
ambiguous — it can mean MUST(NOT(P)) (the reading that *mustn't*
unambiguously selects).

This scope irregularity is predicted by the inflectional-affix analysis:
if *-n't* is an affix, it forms a lexical unit with the auxiliary, and
lexical items can have idiosyncratic scope properties. If *-n't* were
a clitic (a reduced form of *not*), its scope should always match *not*.

We formalize this using `boxR`/`diamondR` from
`Core.IntensionalLogic`: a Kripke countermodel exhibits
an accessibility relation under which the two scope readings diverge. -/

section ScopeBridge

open Core.Modality (ModalForce)
open Core.IntensionalLogic (AccessRel boxR diamondR)

abbrev World := Fin 4

/-- Scope of negation relative to a modal operator. -/
inductive NegModalScope where
  /-- Negation scopes over the modal: NOT(MODAL(P)).
      *You can't go* = it's not the case that you can go. -/
  | negOverModal
  /-- Modal scopes over negation: MODAL(NOT(P)).
      *You mustn't go* = you must not go. -/
  | modalOverNeg
  deriving DecidableEq, Repr

/-- The scope pattern for a contracted negative auxiliary.

*can't*: NOT(CAN(P)) — `negOverModal` with possibility
*mustn't*: MUST(NOT(P)) — `modalOverNeg` with necessity

That these differ is the semantic idiosyncrasy. If *-n't* were simply
a reduced form of *not*, both should have the same scope relation. -/
structure ContractedNegScope where
  /-- The base auxiliary form. -/
  auxiliary : String
  /-- The modal force of the auxiliary. -/
  force : ModalForce
  /-- Which scope reading the contracted form selects. -/
  scope : NegModalScope
  deriving Repr, BEq

/-- *can't* selects NOT(CAN(P)): negation over possibility. -/
def cantScope : ContractedNegScope where
  auxiliary := "can"
  force := .possibility
  scope := .negOverModal

/-- *mustn't* selects MUST(NOT(P)): necessity over negation. -/
def mustntScope : ContractedNegScope where
  auxiliary := "must"
  force := .necessity
  scope := .modalOverNeg

/-- The scope patterns differ — this is the semantic idiosyncrasy. -/
theorem scope_idiosyncrasy : cantScope.scope ≠ mustntScope.scope := by
  decide

/-- Kripke accessibility with non-trivial structure: w0 sees {w1, w2};
every other world sees only itself.

This suffices to separate ¬◇P from ◇¬P and ¬□P from □¬P at w0:
when P holds at w1 and fails at w2, both accessible worlds disagree,
so ◇P and ◇¬P are both true while ¬◇P is false. -/
private def kripkeR : AccessRel World := fun w v =>
  match w with
  | 0 => v = (1 : World) ∨ v = (2 : World)
  | 1 => v = (1 : World)
  | 2 => v = (2 : World)
  | 3 => v = (3 : World)

private instance : DecidableRel kripkeR := fun w v => by
  unfold kripkeR
  match w with
  | 0 => infer_instance
  | 1 => infer_instance
  | 2 => infer_instance
  | 3 => infer_instance

/-- Witness proposition: true at w0/w1, false at w2/w3. -/
private def witnessP : World → Prop := fun w =>
  match w with | 0 | 1 => True | 2 | 3 => False

private instance : DecidablePred witnessP := fun w => by
  unfold witnessP
  match w with
  | 0 => infer_instance
  | 1 => infer_instance
  | 2 => infer_instance
  | 3 => infer_instance

/-- NOT(CAN(P)) and CAN(NOT(P)) are not equivalent in general.

There exists a Kripke accessibility relation where ¬◇P ≠ ◇¬P: when w0
accesses worlds where P differs, ◇P and ◇¬P are both true, so
¬◇P = false but ◇¬P = true. -/
theorem neg_over_poss_ne_poss_over_neg :
    ∃ (R : AccessRel World),
    ¬(∀ (p : World → Prop) (w : World),
      ¬ diamondR R p w ↔ diamondR R (fun w' => ¬ p w') w) := by
  refine ⟨kripkeR, ?_⟩
  intro h
  have := h witnessP (0 : World)
  simp [diamondR, kripkeR, witnessP] at this

/-- NOT(MUST(P)) and MUST(NOT(P)) are not equivalent in general.

There exists a Kripke accessibility relation where ¬□P ≠ □¬P: failing
to be necessary (¬□P = true when P fails at w2) is weaker than being
necessarily false (□¬P = false when P holds at w1). -/
theorem neg_over_nec_ne_nec_over_neg :
    ∃ (R : AccessRel World),
    ¬(∀ (p : World → Prop) (w : World),
      ¬ boxR R p w ↔ boxR R (fun w' => ¬ p w') w) := by
  refine ⟨kripkeR, ?_⟩
  intro h
  have := h witnessP (0 : World)
  simp [boxR, kripkeR, witnessP] at this

end ScopeBridge

-- ============================================================================
-- §6: Selection Restriction Verification (Criterion A)
-- ============================================================================

/-! *-n't* attaches only to finite auxiliaries. Verify that the host set
matches the auxiliary inventory from `Fragments/English/FunctionWords`. -/

open Fragments.English.Auxiliaries in
/-- Every auxiliary in the inventory is either a modal, do-support, be, or have. -/
theorem aux_hosts_are_closed_class :
    allAuxiliaries.all (λ a => a.auxType == .modal
      || a.auxType == .doSupport
      || a.auxType == .be
      || a.auxType == .have) = true := by native_decide

open Fragments.English.Auxiliaries in
/-- The number of auxiliaries with contracted negative forms
    (= the productive range of *-n't*). -/
def ntHostCount : Nat :=
  allAuxiliaries.filter (λ a => a.negForm.isSome) |>.length

open Fragments.English.Auxiliaries in
/-- The number of paradigm gaps (auxiliaries without *-n't*). -/
def ntGapCount : Nat :=
  allAuxiliaries.filter (λ a => a.negForm.isNone) |>.length

open Fragments.English.Auxiliaries in
/-- Most auxiliaries have a contracted negative form, but there are gaps. -/
theorem nt_has_gaps : ntGapCount > 0 := by native_decide

open Fragments.English.Auxiliaries in
/-- At least five auxiliaries show phonological irregularity in their
contracted negative form (Z&P criterion C). -/
theorem nt_has_irregulars :
    (allAuxiliaries.filter (λ a => a.negIrregular)).length ≥ 5 := by native_decide

end Phenomena.Morphology.ZwickyPullum1983
