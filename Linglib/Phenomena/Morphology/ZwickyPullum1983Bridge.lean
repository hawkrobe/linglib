import Linglib.Theories.Morphology.Diagnostics.CliticVsAffix
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Semantics.Modality.Basic

/-!
# Zwicky & Pullum 1983: Cliticization vs. Inflection

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

## References

- Zwicky, A. M. & Pullum, G. K. (1983). Cliticization vs. Inflection:
  English N'T. *Language* 59(3), 502–513.
-/

namespace Phenomena.Morphology.ZwickyPullum1983

open Morphology.Diagnostics
open Core.Morphology (MorphStatus SelectionDegree)
open Fragments.English.FunctionWords (AuxEntry)

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

open Fragments.English.FunctionWords in
/-- *may* has no contracted negative form (*mayn't is a paradigm gap). -/
theorem may_gap : may.negForm = none := rfl

open Fragments.English.FunctionWords in
/-- *am* has no contracted negative form (*amn't is a paradigm gap). -/
theorem am_gap : am.negForm = none := rfl

-- ============================================================================
-- §4: Morphophonological Irregularity Verification (Criterion C)
-- ============================================================================

/-! Verify that the phonologically irregular forms are flagged in Fragment data. -/

open Fragments.English.FunctionWords in
/-- *won't* is phonologically irregular (not *willn't*). -/
theorem wont_irregular : will.negIrregular = true := rfl

open Fragments.English.FunctionWords in
/-- *can't* is phonologically irregular. -/
theorem cant_irregular : can.negIrregular = true := rfl

open Fragments.English.FunctionWords in
/-- *don't* is phonologically irregular (not *don't* [dunt]). -/
theorem dont_irregular : do_.negIrregular = true := rfl

open Fragments.English.FunctionWords in
/-- *shan't* is phonologically irregular (not *shalln't*). -/
theorem shant_irregular : shall.negIrregular = true := rfl

open Fragments.English.FunctionWords in
/-- *mustn't* shows [t]-deletion: [mʌsnt] not *[mʌstnt]. -/
theorem mustnt_irregular : must.negIrregular = true := rfl

open Fragments.English.FunctionWords in
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

We formalize this using `Semantics.Modality.ModalTheory`. -/

section ScopeBridge

open Semantics.Modality
open Semantics.Attitudes.Intensional (World allWorlds)

/-- Scope of negation relative to a modal operator. -/
inductive NegModalScope where
  /-- Negation scopes over the modal: NOT(MODAL(P)).
      *You can't go* = it's not the case that you can go. -/
  | negOverModal
  /-- Modal scopes over negation: MODAL(NOT(P)).
      *You mustn't go* = you must not go. -/
  | modalOverNeg
  deriving DecidableEq, Repr, BEq

/-- Evaluate NOT(MODAL(P)) at world w. -/
def evalNegOverModal (T : ModalTheory) (force : ModalForce) (p : Proposition) (w : World) : Bool :=
  !(T.eval force p w)

/-- Evaluate MODAL(NOT(P)) at world w. -/
def evalModalOverNeg (T : ModalTheory) (force : ModalForce) (p : Proposition) (w : World) : Bool :=
  let notP : Proposition := λ w' => !p w'
  T.eval force notP w

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

/-- NOT(CAN(P)) and CAN(NOT(P)) are not equivalent in general.

There exist models where something is not possible, but the negation
of the proposition is not necessary — i.e., ¬◇P ≠ ◇¬P. -/
theorem neg_over_poss_ne_poss_over_neg (T : ModalTheory)
    (h : T.isNormal) :
    ¬(∀ (p : Proposition) (w : World),
      evalNegOverModal T .possibility p w =
      evalModalOverNeg T .possibility p w) := by
  sorry  -- TODO: construct a countermodel; requires finding
         -- a ModalTheory instance where ¬◇p ≠ ◇¬p at some world

/-- NOT(MUST(P)) and MUST(NOT(P)) are not equivalent in general.

¬□P ≠ □¬P: failing to be necessary is weaker than being necessarily false. -/
theorem neg_over_nec_ne_nec_over_neg (T : ModalTheory)
    (h : T.isNormal) :
    ¬(∀ (p : Proposition) (w : World),
      evalNegOverModal T .necessity p w =
      evalModalOverNeg T .necessity p w) := by
  sorry  -- TODO: construct a countermodel; requires finding
         -- a ModalTheory instance where ¬□p ≠ □¬p at some world

end ScopeBridge

-- ============================================================================
-- §6: Selection Restriction Verification (Criterion A)
-- ============================================================================

/-! *-n't* attaches only to finite auxiliaries. Verify that the host set
matches the auxiliary inventory from `Fragments/English/FunctionWords`. -/

open Fragments.English.FunctionWords in
/-- Every auxiliary in the inventory is either a modal, do-support, be, or have. -/
theorem aux_hosts_are_closed_class :
    allAuxiliaries.all (λ a => a.auxType == .modal
      || a.auxType == .doSupport
      || a.auxType == .be
      || a.auxType == .have) = true := by native_decide

open Fragments.English.FunctionWords in
/-- The number of auxiliaries with contracted negative forms
    (= the productive range of *-n't*). -/
def ntHostCount : Nat :=
  allAuxiliaries.filter (λ a => a.negForm.isSome) |>.length

open Fragments.English.FunctionWords in
/-- The number of paradigm gaps (auxiliaries without *-n't*). -/
def ntGapCount : Nat :=
  allAuxiliaries.filter (λ a => a.negForm.isNone) |>.length

open Fragments.English.FunctionWords in
/-- Most auxiliaries have a contracted negative form, but there are gaps. -/
theorem nt_has_gaps : ntGapCount > 0 := by native_decide

open Fragments.English.FunctionWords in
/-- At least five auxiliaries show phonological irregularity in their
contracted negative form (Z&P criterion C). -/
theorem nt_has_irregulars :
    (allAuxiliaries.filter (λ a => a.negIrregular)).length ≥ 5 := by native_decide

end Phenomena.Morphology.ZwickyPullum1983
