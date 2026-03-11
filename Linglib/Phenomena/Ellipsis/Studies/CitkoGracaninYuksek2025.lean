import Linglib.Theories.Syntax.Minimalism.Core.Economy
import Linglib.Theories.Syntax.Minimalism.Core.Multidominance
import Linglib.Phenomena.Ellipsis.Sluicing
/-!
# Economy in PF Reduction
@cite{citko-gracanin-yuksek-2025}

Coordinated wh-questions (CWHs) and coordinated sluices (CSs) are two
PF-reduced constructions with wh-phrase remnants. Despite superficial
similarity, they differ in structure, derivational cost, and empirical
properties. Economy governs the choice between ellipsis and
multidominance as the PF reduction mechanism.

## Key Claims

1. CWHs use **non-bulk-sharing MD**: each conjunct CP contains one
   wh-phrase; functional heads (C, T) are multiply dominated.
   No ellipsis is involved.

2. CSs use **bulk-sharing MD + ellipsis**: the entire C' is shared
   between conjuncts; both wh-phrases originate inside the shared vP.
   The E-feature on C triggers TP deletion (cf. `FeatureVal.ellipsis`
   in `Core/Features.lean`, which models this E-feature).

3. **Economy selects the structure**: MD is preferred over ellipsis
   (fewer operations, fewer lexical items). Bulk-sharing MD is more
   economical than non-bulk-sharing, but is blocked for CWHs by the
   MWF parameter. CSs can't have the CWH structure because of
   Pronunciation Economy.

## Empirical Contrasts

- CWHs ban coordination of obligatory wh-arguments;
  CSs allow it.
- CWHs ban wh-object + wh-adjunct with obligatorily transitive verbs;
  CSs allow it.
- CWHs only allow nonpaired readings;
  CSs allow paired readings (with obligatorily transitive verbs)
  and nonpaired readings (with optionally transitive verbs).

## Integration

- CSs are coordinated sluices — each conjunct of a CS is a sluice.
  Bridge theorems connect CS data to `Sluicing.lean` data structures.
- The MWF parameter connects to `Questions/MultipleWh.lean`:
  non-MWF languages (English) ban multiple wh-fronting in questions.
- RNR (§6.2) demonstrates that economy can force BOTH ellipsis and MD
  in a single derivation.
-/

namespace Phenomena.Ellipsis.Studies.CitkoGracaninYuksek2025

open Minimalism

-- ============================================================================
-- § 1: Construction Types and Empirical Data
-- ============================================================================

/-- The two PF-reduced wh-coordination constructions. -/
inductive WHCoordType where
  /-- Coordinated wh-question: "What and when did John teach?" -/
  | CWH
  /-- Coordinated sluice: "I forgot what and when." -/
  | CS
  deriving Repr, DecidableEq

/-- An empirical datum contrasting CWHs and CSs. -/
structure WHCoordDatum where
  sentence : String
  construction : WHCoordType
  whPhrases : List String
  grammatical : Bool
  notes : String := ""
  deriving Repr

-- CWH examples

def cwh_basic : WHCoordDatum :=
  { sentence := "What and when did John teach?"
  , construction := .CWH
  , whPhrases := ["what", "when"]
  , grammatical := true }

/-- CWHs ban coordination of obligatory wh-arguments (ex 5a). -/
def cwh_obligatory_args_banned : WHCoordDatum :=
  { sentence := "*What and to whom did John give?"
  , construction := .CWH
  , whPhrases := ["what", "to whom"]
  , grammatical := false
  , notes := "Both are obligatory arguments of 'give'; banned in CWHs" }

/-- CWHs ban wh-object + wh-adjunct with obligatorily transitive verbs (ex 6a).
    Distinct from (5a): here only one wh-phrase is an obligatory argument;
    the other is an adjunct. The ban persists because the verb ('buy')
    is obligatorily transitive. -/
def cwh_obj_adjunct_banned : WHCoordDatum :=
  { sentence := "*What and when did John buy?"
  , construction := .CWH
  , whPhrases := ["what", "when"]
  , grammatical := false
  , notes := "Wh-object + wh-adjunct; 'buy' is obligatorily transitive" }

-- CS examples

def cs_basic : WHCoordDatum :=
  { sentence := "John taught something, but I forgot what and when."
  , construction := .CS
  , whPhrases := ["what", "when"]
  , grammatical := true }

/-- CSs allow coordination of obligatory wh-arguments (ex 5b). -/
def cs_obligatory_args_allowed : WHCoordDatum :=
  { sentence := "I heard that John gave something to someone, but I forgot what and to whom."
  , construction := .CS
  , whPhrases := ["what", "to whom"]
  , grammatical := true
  , notes := "Both are obligatory arguments of 'give'; allowed in CSs" }

/-- CSs allow wh-object + wh-adjunct coordination (ex 6b). -/
def cs_obj_adjunct_allowed : WHCoordDatum :=
  { sentence := "I heard that John bought something sometime last week, but I forgot what and when."
  , construction := .CS
  , whPhrases := ["what", "when"]
  , grammatical := true
  , notes := "Wh-object + wh-adjunct with obligatorily transitive 'buy'; allowed in CSs" }

-- Paired vs nonpaired readings

/-- Reading type for wh-coordination. -/
inductive ReadingType where
  /-- Each wh-phrase interpreted in its own conjunct only. -/
  | nonpaired
  /-- The trace of the first wh-phrase is interpreted as an E-type
      pronoun in the second conjunct (pairing). -/
  | paired
  deriving Repr, DecidableEq

/-- Reading availability datum. -/
structure ReadingDatum where
  sentence : String
  construction : WHCoordType
  reading : ReadingType
  available : Bool
  paraphrase : String := ""
  deriving Repr

/-- CWHs: only nonpaired reading available (ex 8a). -/
def cwh_nonpaired : ReadingDatum :=
  { sentence := "I know John ate candy because he was stressed out, but I don't know what candy and why."
  , construction := .CWH
  , reading := .nonpaired
  , available := true
  , paraphrase := "what candy he ate; why he was stressed out" }

/-- CWHs: paired reading unavailable (ex 8a). -/
def cwh_no_paired : ReadingDatum :=
  { sentence := "I know John ate candy because he was stressed out, but I don't know what candy and why."
  , construction := .CWH
  , reading := .paired
  , available := false
  , paraphrase := "*what candy he ate and why he ate it" }

/-- CSs: paired reading available with obligatorily transitive verbs (ex 8b).
    The paired reading arises because in the bulk-sharing structure,
    both wh-phrases originate inside the shared vP — the lower copy of
    the first wh-phrase is interpreted as an E-type pronoun in the
    second conjunct. -/
def cs_paired : ReadingDatum :=
  { sentence := "I know John ate candy because he was stressed out, but I don't know what candy and why."
  , construction := .CS
  , reading := .paired
  , available := true
  , paraphrase := "what candy he ate and why he ate it (= that candy)" }

/-- CSs: nonpaired reading available with optionally transitive verbs (§6.1, ex 43).
    With verbs like 'teach' (optionally transitive), each wh-phrase can
    start in its own clause, yielding a nonpaired reading. This requires
    a different structure: non-bulk-sharing with two independent Cs,
    only one bearing the E-feature. -/
def cs_nonpaired : ReadingDatum :=
  { sentence := "I know John taught something, but I forgot what and where."
  , construction := .CS
  , reading := .nonpaired
  , available := true
  , paraphrase := "what he taught; where he taught" }

-- Verification: CWH and CS differ on all three properties
theorem cwh_bans_obligatory_args : cwh_obligatory_args_banned.grammatical = false := rfl
theorem cs_allows_obligatory_args : cs_obligatory_args_allowed.grammatical = true := rfl
theorem cwh_bans_obj_adjunct : cwh_obj_adjunct_banned.grammatical = false := rfl
theorem cs_allows_obj_adjunct : cs_obj_adjunct_allowed.grammatical = true := rfl
theorem cwh_bans_paired_reading : cwh_no_paired.available = false := rfl
theorem cs_allows_paired_reading : cs_paired.available = true := rfl
theorem cs_allows_nonpaired_reading : cs_nonpaired.available = true := rfl

-- ============================================================================
-- § 1b: CSs as Coordinated Sluices — Bridge to Sluicing.lean
-- ============================================================================

/-! Each conjunct of a CS is itself a sluice: the wh-phrase is the remnant
and the TP is the elided material. We show this by decomposing CS examples
into `SluicingDatum` instances from `Phenomena.Ellipsis.Sluicing`. -/

open Phenomena.Ellipsis.Sluicing

/-- The "what" conjunct of `cs_basic` as a standalone sluice:
    "John taught something, but I forgot what [John taught _]" -/
def cs_basic_sluice_what : SluicingDatum :=
  { sentence := "John taught something, but I forgot what"
  , antecedent := "John taught something"
  , innerAntecedent := "something"
  , whPhrase := "what"
  , elided := "John taught"
  , notes := "First conjunct of cs_basic decomposed as sluice" }

/-- The "when" conjunct of `cs_basic` as a standalone sluice:
    "John taught something, but I forgot when [John taught something]" -/
def cs_basic_sluice_when : SluicingDatum :=
  { sentence := "John taught something, but I forgot when"
  , antecedent := "John taught something"
  , innerAntecedent := "something"
  , whPhrase := "when"
  , elided := "John taught something"
  , notes := "Second conjunct of cs_basic decomposed as sluice (sprouting-like: temporal adjunct)" }

/-- Each CS decomposes into sluices: the wh-phrases in a CS are
    exactly the remnants of the component sluices. -/
theorem cs_basic_decomposes_into_sluices :
    cs_basic.whPhrases = [cs_basic_sluice_what.whPhrase, cs_basic_sluice_when.whPhrase] := rfl

/-- Both component sluices are grammatical. -/
theorem cs_components_grammatical :
    cs_basic_sluice_what.grammatical = true ∧ cs_basic_sluice_when.grammatical = true :=
  ⟨rfl, rfl⟩

/-- The "what" and "to whom" conjuncts of `cs_obligatory_args_allowed`. -/
def cs_oblig_sluice_what : SluicingDatum :=
  { sentence := "I heard that John gave something to someone, but I forgot what"
  , antecedent := "John gave something to someone"
  , innerAntecedent := "something"
  , whPhrase := "what"
  , elided := "John gave _ to someone" }

def cs_oblig_sluice_toWhom : SluicingDatum :=
  { sentence := "I heard that John gave something to someone, but I forgot to whom"
  , antecedent := "John gave something to someone"
  , innerAntecedent := "to someone"
  , whPhrase := "to whom"
  , elided := "John gave something _" }

/-- Obligatory-argument CS also decomposes into sluices. -/
theorem cs_obligatory_decomposes :
    cs_obligatory_args_allowed.whPhrases =
      [cs_oblig_sluice_what.whPhrase, cs_oblig_sluice_toWhom.whPhrase] := rfl

-- ============================================================================
-- § 2: English MWF Parameter
-- ============================================================================

/-- English is a non-MWF language: multiple wh-fronting is banned.
    *"Who what saw?" is ungrammatical (ex 28). -/
def english : MWFParameter := ⟨false⟩

/-- English bans multiple wh-specifiers at a phase edge. -/
theorem english_bans_multiple_wh : mwfViolation english 2 = true := by decide

/-- A single wh-specifier is fine in English. -/
theorem english_allows_single_wh : mwfViolation english 1 = false := by decide

-- ============================================================================
-- § 2b: MWF Cross-Linguistic Typology
-- ============================================================================

/-! The MWF parameter varies cross-linguistically. We define language
classifications that connect to the multiple wh-question data in
`Phenomena/Questions/MultipleWh.lean`. -/

/-- MWF language classification. -/
structure MWFLanguageDatum where
  language : String
  mwfParam : MWFParameter
  /-- Example multiple wh-question -/
  example_ : String
  /-- Is the example grammatical? -/
  grammatical : Bool
  /-- Does this language allow multiple sluicing? -/
  allowsMultipleSluicing : Bool
  notes : String := ""
  deriving Repr

/-- Bulgarian: MWF language. -/
def bulgarian : MWFLanguageDatum :=
  { language := "Bulgarian"
  , mwfParam := ⟨true⟩
  , example_ := "Koj kakvo e kupil?"
  , grammatical := true
  , allowsMultipleSluicing := true
  , notes := "All wh-phrases front; MWF language" }

/-- German: non-MWF language, but allows multiple sluicing. -/
def german_mwf : MWFLanguageDatum :=
  { language := "German"
  , mwfParam := ⟨false⟩
  , example_ := "*Wer was hat gesehen?"
  , grammatical := false
  , allowsMultipleSluicing := true
  , notes := "Non-MWF; bans multiple wh-fronting in questions but allows multiple sluicing (ex 31a)" }

/-- Greek: non-MWF language, but allows multiple sluicing. -/
def greek_mwf : MWFLanguageDatum :=
  { language := "Greek"
  , mwfParam := ⟨false⟩
  , example_ := "*Pços ti efere?"
  , grammatical := false
  , allowsMultipleSluicing := true
  , notes := "Non-MWF; bans multiple wh-fronting in questions but allows multiple sluicing (ex 31b)" }

/-- English variety A: non-MWF, bans multiple sluicing. -/
def english_varietyA : MWFLanguageDatum :=
  { language := "English (variety A)"
  , mwfParam := ⟨false⟩
  , example_ := "*Who what saw?"
  , grammatical := false
  , allowsMultipleSluicing := false
  , notes := "MWF violation at BOTH vP and CP edges; no ellipsis repair possible" }

/-- English variety B: non-MWF, allows multiple sluicing. -/
def english_varietyB : MWFLanguageDatum :=
  { language := "English (variety B)"
  , mwfParam := ⟨false⟩
  , example_ := "*Who what saw?"
  , grammatical := false
  , allowsMultipleSluicing := true
  , notes := "MWF violation only at vP edge; sluicing repairs by deleting vP" }

/-- MWF languages never have MWF violations in questions. -/
theorem mwf_language_questions_ok :
    mwfViolation bulgarian.mwfParam 2 = false := by decide

/-- Non-MWF languages DO have violations with 2+ wh-specifiers. -/
theorem non_mwf_language_questions_bad :
    mwfViolation german_mwf.mwfParam 2 = true := by decide

/-- German and Greek: non-MWF but allow multiple sluicing — the
    offending vP edge is deleted by ellipsis (same mechanism as CSs). -/
theorem german_greek_sluicing_repair :
    german_mwf.allowsMultipleSluicing = true ∧
    greek_mwf.allowsMultipleSluicing = true ∧
    ellipsisRepairsMWF german_mwf.mwfParam 2 (edgeDeleted := true) = true := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Derivation Cost Functions
-- ============================================================================

/-! The derivation cost of a PF-reduced coordination depends on whether
the shared material is built once (MD) or twice (ellipsis). We provide
two levels of parameterization:

**Coarse** (MD vs ellipsis): parameterized by total shared/non-shared cost.
Used for Theorems 1–2.

- `sm`/`sl`: Merge/lexical cost of shared material (built once with MD, twice with ellipsis)
- `nsm`/`nsl`: cost of non-shared parts (wh-movement, coordination)

**Fine** (non-bulk vs bulk sharing): decomposes shared material into
heads vs phrasal structure. Used for Theorem 3.

- `hm`/`hl`: cost of shared heads (C, T — built once either way)
- `pm`/`pl`: cost of per-conjunct phrasal structure (C', TP, vP assembly)
- `wm`/`wl`: cost of wh-phrases + coordination (non-shared)
-/

/-- Cost of CWH via non-bulk-sharing MD (adopted structure, paper's (10b)).
    Shared material built once; no ellipsis. -/
def cwhMDCost (sm sl nsm nsl : Nat) : DerivationCost where
  mergeOps := sm + nsm
  lexicalItems := sl + nsl
  agreeOps := 0
  ellipsisOps := 0

/-- Cost of CWH via ellipsis (biclausal alternative, paper's (11b)).
    Shared material duplicated; one E-feature deletion. -/
def cwhEllipsisCost (sm sl nsm nsl : Nat) : DerivationCost where
  mergeOps := 2 * sm + nsm
  lexicalItems := 2 * sl + nsl
  agreeOps := 0
  ellipsisOps := 1

/-- Cost of CWH via non-bulk-sharing MD — fine-grained (paper's (10b)).
    Individual heads (C, T) shared; per-conjunct phrasal structure
    (assembling C', TP, vP around shared heads) built in each conjunct. -/
def cwhNonBulkCost (hm hl pm pl wm wl : Nat) : DerivationCost where
  mergeOps := hm + 2 * pm + wm
  lexicalItems := hl + 2 * pl + wl
  agreeOps := 0
  ellipsisOps := 0

/-- Cost of CWH via bulk-sharing MD (excluded, paper's (12b)).
    Entire C' shared — phrasal structure built only once.
    More economical than non-bulk-sharing, but blocked by MWF. -/
def cwhBulkMDCost (hm hl pm pl wm wl : Nat) : DerivationCost where
  mergeOps := hm + pm + wm
  lexicalItems := hl + pl + wl
  agreeOps := 0
  ellipsisOps := 0

/-- Cost of CS via bulk-sharing MD + single ellipsis (adopted, paper's (20b)).
    C' shared; E-feature on C deletes TP once. -/
def csBulkCost (sm sl nsm nsl : Nat) : DerivationCost where
  mergeOps := sm + nsm
  lexicalItems := sl + nsl
  agreeOps := 0
  ellipsisOps := 1

/-- Cost of CS via double ellipsis, no MD (excluded, paper's (19b)).
    Both conjuncts built in full; E-feature in each. -/
def csDoubleEllipsisCost (sm sl nsm nsl : Nat) : DerivationCost where
  mergeOps := 2 * sm + nsm
  lexicalItems := 2 * sl + nsl
  agreeOps := 0
  ellipsisOps := 2

-- ============================================================================
-- § 4: Economy Theorems
-- ============================================================================

/-- **Theorem 1**: For CWHs, the MD derivation is strictly more economical
    than the ellipsis alternative (paper's (10b) vs (11b)).

    The MD derivation saves `sm` Merge operations (shared material built
    once instead of twice) and avoids the ellipsis operation entirely.
    This holds for ANY amount of shared material — even if `sm = 0`,
    the ellipsis operation alone makes the alternative costlier. -/
theorem cwh_md_beats_ellipsis (sm sl nsm nsl : Nat) :
    strictlyMoreEconomical (cwhMDCost sm sl nsm nsl) (cwhEllipsisCost sm sl nsm nsl) := by
  simp only [strictlyMoreEconomical, atLeastAsEconomical, DerivationCost.totalOps,
    cwhMDCost, cwhEllipsisCost]
  omega

/-- **Theorem 2**: For CSs, the bulk-sharing derivation is strictly more
    economical than the double-ellipsis alternative (paper's (20b) vs (19b)).

    The bulk-sharing derivation saves `sm` Merge operations and `sl`
    lexical items, and uses one fewer ellipsis operation. -/
theorem cs_bulk_beats_double_ellipsis (sm sl nsm nsl : Nat) :
    strictlyMoreEconomical (csBulkCost sm sl nsm nsl) (csDoubleEllipsisCost sm sl nsm nsl) := by
  simp only [strictlyMoreEconomical, atLeastAsEconomical, DerivationCost.totalOps,
    csBulkCost, csDoubleEllipsisCost]
  omega

/-- **Theorem 3**: Bulk-sharing is strictly more economical than
    non-bulk-sharing for CWHs (paper's (12b) vs (10b)).

    This is the paper's crucial insight: the MOST economical derivation
    for CWHs (bulk-sharing, which builds C' once) is blocked by an
    independent constraint (MWF), forcing the LESS economical
    non-bulk-sharing structure. The precondition `0 < pm ∨ 0 < pl`
    ensures there is at least some phrasal structure to share —
    which holds for any non-trivial clause. -/
theorem cwh_bulk_beats_nonbulk (hm hl pm pl wm wl : Nat) (h : 0 < pm ∨ 0 < pl) :
    strictlyMoreEconomical
      (cwhBulkMDCost hm hl pm pl wm wl)
      (cwhNonBulkCost hm hl pm pl wm wl) := by
  simp only [strictlyMoreEconomical, atLeastAsEconomical, DerivationCost.totalOps,
    cwhBulkMDCost, cwhNonBulkCost]
  omega

-- ============================================================================
-- § 5: Why CWHs Cannot Have the CS Structure
-- ============================================================================

/-! The CS (bulk-sharing) structure places both wh-phrases inside a single
vP. Both must pass through the vP phase edge, creating a phase node
with multiple wh-specifiers (paper's (36b)/(37b)).

In a non-MWF language like English, this configuration receives an
asterisk at PF, crashing the derivation.

Unlike CSs, CWHs do NOT involve ellipsis — the vP edge survives to PF,
so the asterisk is not deleted and the crash is unavoidable.

CSs survive because the E-feature on C triggers TP deletion (including
the offending vP edge), removing the asterisk before PF interprets it. -/

/-- The bulk-sharing structure for CWHs crashes in English:
    2 wh-specifiers at vP edge in a non-MWF language. -/
theorem cwh_bulk_crashes_in_english :
    mwfViolation english 2 = true := by decide

/-- CWHs have no ellipsis to repair the MWF violation —
    the vP edge survives to PF, and the asterisk crashes. -/
theorem cwh_no_ellipsis_repair :
    ellipsisRepairsMWF english 2 (edgeDeleted := false) = false := by decide

/-- CSs survive the same MWF configuration because ellipsis deletes
    the vP edge containing the multiple wh-specifiers. -/
theorem cs_ellipsis_repairs_mwf :
    ellipsisRepairsMWF english 2 (edgeDeleted := true) = true := by decide

-- ============================================================================
-- § 6: Why CSs Cannot Have the CWH Structure
-- ============================================================================

/-- If CSs had the non-bulk-sharing (CWH) structure (paper's (38d)),
    with a shared C bearing the E-feature, the C would have two TP
    complements (one per conjunct). The E-feature triggers deletion
    of both TPs:

    1. Deleting TP₁ removes the TP-internal string from PF.
    2. Deleting TP₂ would remove the same string — but it was already
       removed by step 1.
    3. The second deletion is vacuous → violates Pronunciation Economy.

    This reasoning crucially relies on C being shared (economy forces
    sharing unless independent Cs are needed, as in (16) where each
    C hosts different phonological material). -/
theorem cs_nonbulk_violates_pronunciation_economy :
    let pfAfterFirstDeletion := ["what", "and", "when"]
    let pfAfterBothDeletions := ["what", "and", "when"]
    vacuousEllipsis pfAfterFirstDeletion pfAfterBothDeletions := rfl

/-- The Pronunciation Economy principle is violated: the second ellipsis
    does not change the PF output. -/
theorem cs_nonbulk_fails_pronEcon :
    let pfAfterFirstDeletion := ["what", "and", "when"]
    let pfAfterBothDeletions := ["what", "and", "when"]
    ¬pronunciationEconomy pfAfterFirstDeletion pfAfterBothDeletions := by
  simp [pronunciationEconomy]

-- ============================================================================
-- § 7: Structural Summary — with populated sharedNodes
-- ============================================================================

/-- The adopted CWH structure: non-bulk-sharing MD, no ellipsis (paper's (10b)).
    Shared nodes: C and T are individually multiply dominated. -/
def cwhStructure : PFReducedCoordination where
  conjunct1 := mkLeaf .C [] 0
  conjunct2 := mkLeaf .C [] 1
  mechanisms := [.multidominance]
  sharing := some .nonBulk
  sharedNodes :=
    [ { node := mkLeaf .C [] 10, category := some .C, pronounced := true }
    , { node := mkLeaf .T [] 11, category := some .T, pronounced := false } ]
  pfOutput := ["what", "and", "when", "should", "you", "teach"]

/-- The adopted CS structure: bulk-sharing MD + ellipsis (paper's (20b)).
    The E-feature on C (cf. `FeatureVal.ellipsis` in `Core/Features.lean`)
    triggers TP deletion, repairing the MWF violation at the vP edge.
    Shared nodes: entire C' is shared (includes C, TP, vP, VP). -/
def csStructure : PFReducedCoordination where
  conjunct1 := mkLeaf .C [] 0
  conjunct2 := mkLeaf .C [] 1
  mechanisms := [.multidominance, .ellipsis]
  sharing := some .bulk
  sharedNodes :=
    [ { node := mkLeaf .C [] 10, category := some .C, pronounced := true }
    , { node := mkLeaf .T [] 11, category := some .T, pronounced := false }
    , { node := mkLeaf .v [] 12, category := some .v, pronounced := false } ]
  pfOutput := ["what", "and", "when"]

/-- CWHs use only MD. -/
theorem cwh_uses_md_only :
    cwhStructure.usesMD = true ∧ cwhStructure.usesEllipsis = false := by decide

/-- CSs use both MD and ellipsis. -/
theorem cs_uses_both :
    csStructure.usesBoth = true := by decide

/-- CWHs share individual heads (C, T); CSs share an entire constituent. -/
theorem cwh_shares_heads_cs_shares_constituent :
    cwhStructure.sharedNodes.length = 2 ∧ csStructure.sharedNodes.length = 3 := by decide

/-- All CWH shared nodes have explicit categories. -/
theorem cwh_shared_categories :
    cwhStructure.sharedNodes.all (·.category.isSome) = true := by decide

/-- All CS shared nodes have explicit categories. -/
theorem cs_shared_categories :
    csStructure.sharedNodes.all (·.category.isSome) = true := by decide

-- ============================================================================
-- § 8: End-to-End Argumentation Chains
-- ============================================================================

/-! The paper's central contribution is explaining WHY CWHs and CSs
must have different structures — and therefore different empirical
properties — despite their superficial similarity.

**For CWHs** (§4.1):
1. Bulk-sharing MD is most economical (`cwh_bulk_beats_nonbulk`)
2. But bulk-sharing creates MWF violation at vP (`cwh_bulk_crashes_in_english`)
3. CWHs have no ellipsis to repair MWF (`cwh_no_ellipsis_repair`)
4. So non-bulk-sharing MD is selected (`cwh_md_beats_ellipsis` over ellipsis)

**For CSs** (§4.2):
1. Bulk-sharing MD + ellipsis is most economical (`cs_bulk_beats_double_ellipsis`)
2. Bulk-sharing creates MWF at vP, but ellipsis repairs it (`cs_ellipsis_repairs_mwf`)
3. Non-bulk-sharing (CWH structure) violates Pronunciation Economy (`cs_nonbulk_fails_pronEcon`)
4. So bulk-sharing MD + ellipsis is selected

**Different structures → different properties**:
- Non-bulk-sharing (CWH): each conjunct has one wh-phrase → bans
  obligatory arg coordination, bans obj+adjunct coordination with
  obligatorily transitive verbs, only nonpaired readings
- Bulk-sharing (CS): both wh-phrases in shared vP → allows all of the above
-/

/-- The two constructions use different PF reduction mechanisms,
    explaining why they have different empirical properties. -/
theorem different_mechanisms :
    cwhStructure.mechanisms ≠ csStructure.mechanisms := by decide

/-- The two constructions use different sharing types. -/
theorem different_sharing :
    cwhStructure.sharing ≠ csStructure.sharing := by decide

/-- End-to-end: CWHs cannot use bulk-sharing (most economical)
    because the MWF violation at vP cannot be repaired without ellipsis.
    Combines Theorems 3, `cwh_bulk_crashes_in_english`, and
    `cwh_no_ellipsis_repair`. -/
theorem cwh_forced_to_nonbulk (hm hl pm pl wm wl : Nat) (h : 0 < pm ∨ 0 < pl) :
    -- Bulk-sharing IS more economical...
    strictlyMoreEconomical (cwhBulkMDCost hm hl pm pl wm wl) (cwhNonBulkCost hm hl pm pl wm wl)
    -- ...but it crashes in English (MWF at vP)...
    ∧ mwfViolation english 2 = true
    -- ...and CWHs can't repair the crash (no ellipsis).
    ∧ ellipsisRepairsMWF english 2 (edgeDeleted := false) = false := by
  exact ⟨cwh_bulk_beats_nonbulk hm hl pm pl wm wl h, rfl, rfl⟩

/-- End-to-end: CSs use bulk-sharing because it is most economical
    AND the MWF violation is repaired by ellipsis; the CWH structure
    is excluded by Pronunciation Economy. -/
theorem cs_forced_to_bulk (sm sl nsm nsl : Nat) :
    -- Bulk-sharing beats double-ellipsis...
    strictlyMoreEconomical (csBulkCost sm sl nsm nsl) (csDoubleEllipsisCost sm sl nsm nsl)
    -- ...ellipsis repairs the MWF violation at vP...
    ∧ ellipsisRepairsMWF english 2 (edgeDeleted := true) = true
    -- ...and the CWH (non-bulk) structure violates Pronunciation Economy.
    ∧ ¬pronunciationEconomy ["what", "and", "when"] ["what", "and", "when"] := by
  refine ⟨cs_bulk_beats_double_ellipsis sm sl nsm nsl, rfl, ?_⟩
  simp [pronunciationEconomy]

-- ============================================================================
-- § 9: Right Node Raising — Ellipsis + MD Interaction
-- ============================================================================

/-! Section 6.2 of the paper extends the economy analysis to Right Node
Raising (RNR). RNR is a key test case because it can involve BOTH
ellipsis and MD simultaneously — the "mix and match" analysis of
@cite{belk-neeleman-philip-2023}.

The core claim: economy favors MD over ellipsis when both yield the same
string and interpretation. In RNR, the shared pivot (rightmost material)
is multiply dominated. When the pivot and antecedent are not morphologically
identical (vehicle change), ellipsis is additionally required for the
non-shared material in the first conjunct.

Examples:
- Pure MD: "Alice must, and Iris should, work on different topics" (ex 55)
  → No morphological mismatch, so MD alone suffices.
- Ellipsis + MD: "Alice must ⟨work on different topics⟩, and Iris ought
  to be, working on different topics" (ex 52/53)
  → Morphological mismatch forces ellipsis for verb form; MD for PP pivot.

The analysis predicts prosodic break placement: the break should occur
at the onset of the MD-shared material. -/

/-- RNR pivot type: what is shared at the right edge. -/
inductive RNRPivotType where
  /-- Only the rightmost constituent (e.g., PP) is shared. -/
  | minimal
  /-- A larger constituent (e.g., VP) is shared. -/
  | extended
  deriving Repr, DecidableEq

/-- An RNR datum captures the structural analysis. -/
structure RNRDatum where
  sentence : String
  /-- The shared pivot string -/
  pivot : String
  /-- Does the pivot exhibit morphological identity with the antecedent? -/
  morphologicalIdentity : Bool
  /-- Does the pivot exhibit properties of MD? (e.g., cumulative agreement,
      internal reading of relational adjective) -/
  mdProperties : Bool
  /-- Does the construction involve ellipsis in addition to MD? -/
  involvesEllipsis : Bool
  pivotType : RNRPivotType
  notes : String := ""
  deriving Repr

/-- Pure MD: identical verbs, no mismatch → economy selects MD only (ex 55). -/
def rnr_pureMD : RNRDatum :=
  { sentence := "Alice must, and Iris should, work on different topics."
  , pivot := "work on different topics"
  , morphologicalIdentity := true
  , mdProperties := true
  , involvesEllipsis := false
  , pivotType := .extended
  , notes := "No morphological mismatch; MD alone is most economical" }

/-- Ellipsis + MD: verb morphology mismatch forces ellipsis for VP,
    but PP pivot is still shared via MD (ex 52/53). -/
def rnr_ellipsisPlusMD : RNRDatum :=
  { sentence := "Alice must work on different topics, and Iris ought to be working on different topics."
  , pivot := "on different topics"
  , morphologicalIdentity := false
  , mdProperties := true
  , involvesEllipsis := true
  , pivotType := .minimal
  , notes := "Morphological mismatch (work vs working); PP shared via MD, VP ellipsis in first conjunct" }

/-- Morphological mismatch signals ellipsis, not MD. -/
def rnr_ellipsisOnly : RNRDatum :=
  { sentence := "I usually don't wake up early every day, but Alice wakes up early every day."
  , pivot := "wake up early every day"
  , morphologicalIdentity := false
  , mdProperties := false
  , involvesEllipsis := true
  , pivotType := .extended
  , notes := "Vehicle change effect: 'wake' vs 'wakes'; ellipsis signature" }

/-- Relational adjective with internal reading signals MD. -/
def rnr_internalReading : RNRDatum :=
  { sentence := "Alice composed, and Beatrix performed, different songs."
  , pivot := "different songs"
  , morphologicalIdentity := true
  , mdProperties := true
  , involvesEllipsis := false
  , pivotType := .minimal
  , notes := "Internal reading of 'different' requires c-command from both subjects → MD" }

/-- Economy prediction for RNR: when morphology matches and no
    independent constraint forces ellipsis, pure MD is selected. -/
theorem rnr_economy_prefers_md :
    rnr_pureMD.involvesEllipsis = false ∧
    rnr_pureMD.morphologicalIdentity = true ∧
    rnr_pureMD.mdProperties = true := ⟨rfl, rfl, rfl⟩

/-- When morphology mismatches, ellipsis is ADDITIONALLY needed. -/
theorem rnr_mismatch_forces_ellipsis :
    rnr_ellipsisPlusMD.morphologicalIdentity = false ∧
    rnr_ellipsisPlusMD.involvesEllipsis = true ∧
    rnr_ellipsisPlusMD.mdProperties = true := ⟨rfl, rfl, rfl⟩

/-- RNR pivot cost: MD derivation for the shared pivot.
    The pivot is built once (MD) rather than twice (ellipsis). -/
def rnrMDPivotCost (pivotMerge pivotLex nonsharedMerge nonsharedLex : Nat) :
    DerivationCost where
  mergeOps := pivotMerge + nonsharedMerge
  lexicalItems := pivotLex + nonsharedLex
  agreeOps := 0
  ellipsisOps := 0

/-- RNR cost with full ellipsis (no MD): pivot duplicated. -/
def rnrEllipsisCost (pivotMerge pivotLex nonsharedMerge nonsharedLex : Nat) :
    DerivationCost where
  mergeOps := 2 * pivotMerge + nonsharedMerge
  lexicalItems := 2 * pivotLex + nonsharedLex
  agreeOps := 0
  ellipsisOps := 1

/-- **Theorem 4**: For RNR, MD is strictly more economical than
    ellipsis when both yield the same string. Same reasoning as
    Theorem 1 (CWHs). -/
theorem rnr_md_beats_ellipsis (pm pl nm nl : Nat) :
    strictlyMoreEconomical (rnrMDPivotCost pm pl nm nl) (rnrEllipsisCost pm pl nm nl) := by
  simp only [strictlyMoreEconomical, atLeastAsEconomical, DerivationCost.totalOps,
    rnrMDPivotCost, rnrEllipsisCost]
  omega

end Phenomena.Ellipsis.Studies.CitkoGracaninYuksek2025
