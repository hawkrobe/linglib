import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.Economy
import Linglib.Syntax.Question
/-!
# Economy in PF Reduction
[citko-gracanin-yuksek-2025]

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

## Substrate engagement

- MD primitives (`PFReductionMechanism`, `MDSharing`, `SharedNode`,
  `PFReducedCoordination`) are imported from
  `Syntax/Minimalist/Multidominance.lean` (anchored on Citko
  2014). They were briefly inlined here while the substrate file was
  absent; restored to substrate for cross-paper reuse.
- MWF parameter substrate (`MWFParameter`, `PhaseEdge`, `EdgeAsterisk`,
  `MWFViolation`, `EllipsisRepairsMWF`) lives in
  `Typology/Question.lean`. Cross-linguistic data (Bulgarian, German,
  Greek) and the intra-English variety A/B split — paper-specific to
  [citko-gracanin-yuksek-2025] — live in §2 over that substrate.
- Pronunciation Economy is the **per-operation** primitive
  `pronunciationEconomy : List PFOperation → Prop` from
  `Syntax/Minimalist/Economy.lean`. Paper p. 32 ex (45c) needs
  per-op vacuity (a derivation with one real deletion + one vacuous
  deletion violates), which a whole-derivation `pfBefore ≠ pfAfter`
  check could not express.

## Integration

- CSs are coordinated sluices — each conjunct of a CS is a sluice.
  §1b decomposes CS examples into standalone component sluices.
- The MWF parameter (`Typology/Question.lean`) classifies languages:
  non-MWF languages (English) ban multiple wh-fronting in questions.
- RNR (§9) demonstrates that economy can force BOTH ellipsis and MD
  in a single derivation ([belk-neeleman-philip-2023],
  [barros-vicente-2011]).
-/

namespace CitkoGracaninYuksek2025

open Minimalist
open Syntax.Question

/-! ### Multidominance (relocated from Minimalist/Multidominance.lean)

A multidominance (MD) structure is a syntactic object built once that is
structurally accessible from two (or more) dominating nodes. At PF, it
linearizes once. MD is one of the two main mechanisms for producing
PF-reduced representations (representations where some material is
interpreted but not pronounced); the other is ellipsis. [citko-2014] [wilder-2008]

The MD primitives any MD-using analysis needs:

- `PFReductionMechanism` — the two PF-reduction mechanisms (ellipsis vs
  multidominance);
- `MDSharing` — bulk vs non-bulk sharing in coordination;
- `SharedNode` — a multiply-dominated node + its category + whether it
  is pronounced;
- `PFReducedCoordination` — a coordinate &P with PF reduction.

Anchored on [citko-2014] (textbook treatment of parallel-Merge MD)
and [wilder-2008] (constituent-sharing flavor).

## Convention notes

- This does **not** commit to a particular MD flavor (parallel-Merge
  vs constituent-sharing vs 3-D phrase structure). `SharedNode` records
  the multiply-dominated node abstractly; specific MD theories
  instantiate the dominance/sharing relation via their own apparatus.
- `MDSharing` was renamed from `SharingType` at 0.230.575 to avoid a
  bare-name collision with
  `Syntax/DependencyGrammar/Formal/CoordinationParallelism.lean`'s
  `SharingType` (which classifies *extraction symmetry*, not constituent
  sharing).
- `UsesMD` / `UsesEllipsis` / `UsesBoth` are `Prop` with decidability
  instances (per `feedback_no_intrinsic_bool` discipline); decide-checked
  consumers continue to work.
-/

/-- The two mechanisms of PF reduction.

    Both produce representations where material is interpreted but not
    pronounced. Economy (`Syntax/Minimalist/Economy.lean`)
    governs the choice between them. -/
inductive PFReductionMechanism where
  /-- E-feature on a functional head triggers deletion of its complement
      at PF. The deleted material is built in full during the derivation. -/
  | ellipsis
  /-- A syntactic object is built once and shared between two dominating
      nodes. Pronounced at one position only. -/
  | multidominance
  deriving Repr, DecidableEq

/-- How material is shared between conjuncts in an MD coordination.

    The empirical motivation is [citko-gracanin-yuksek-2025]:
    coordinated wh-questions use non-bulk-sharing (individual heads
    shared), while coordinated sluices use bulk-sharing (entire C'
    shared). The two sharing modes derive different syntactic and
    interpretive properties.

    NB: name distinguished from
    `Syntax/DependencyGrammar/Formal/CoordinationParallelism.SharingType`
    (extraction symmetry, not constituent sharing). -/
inductive MDSharing where
  /-- Individual functional heads shared between conjuncts. Each conjunct
      remains a separate full phrase; only specific heads (e.g., C, T)
      are multiply dominated. -/
  | nonBulk
  /-- An entire constituent is shared between conjuncts. Both conjuncts
      dominate the same subtree, so they share all material inside it
      (C, TP, vP, VP, ...). -/
  | bulk
  deriving Repr, DecidableEq

/-- A node shared between two conjuncts in a coordination structure.

    The shared node is built once but is structurally accessible from
    both `parent1` and `parent2`. At PF, it is linearized once. -/
structure SharedNode where
  /-- The multiply dominated node. -/
  node : SyntacticObject
  /-- Category of the shared node, when labelled. -/
  category : Option Cat
  /-- The shared node has PF content (vs. is silent). -/
  pronounced : Bool
  deriving Repr, DecidableEq

/-- A coordination structure with PF reduction.

    Models a coordinate &P where material is either multiply dominated
    (shared between conjuncts) or elided by an E-feature.

    **Substrate note (post-MCB Phase 1.0).** The `conjunct1` / `conjunct2`
    field names are **stipulated planar labels** at the coord-structure
    *meta*-level, NOT inherited from the SyntacticObject substrate (which is nonplanar
    via FreeCommMagma — see `Minimalist.merge_comm`). The first-vs-second
    conjunct distinction tracked by these fields is a *coordination-
    specific stipulation* about which conjunct hosts the shared / deleted
    material, parallel to `BrueningAlKhalaf2020.mergeCoordSymmetry`.
    Phase 2+: harmonize with [citko-2011]'s symmetric-merge
    multidominance framework, where conjunct ordering is genuinely
    a multiset operation. -/
structure PFReducedCoordination where
  /-- First conjunct. Planar label is stipulated at coord-structure level
      (not inherited from substrate). -/
  conjunct1 : SyntacticObject
  /-- Second conjunct. -/
  conjunct2 : SyntacticObject
  /-- PF reduction mechanism(s) used. -/
  mechanisms : List PFReductionMechanism
  /-- Mode of sharing (for MD structures). -/
  sharing : Option MDSharing
  /-- Nodes that are shared or deleted. -/
  sharedNodes : List SharedNode
  /-- PF output after reduction. -/
  pfOutput : List String
  deriving Repr, DecidableEq

namespace PFReducedCoordination

/-- Does this coordination use multidominance? -/
def UsesMD (c : PFReducedCoordination) : Prop :=
  PFReductionMechanism.multidominance ∈ c.mechanisms

instance (c : PFReducedCoordination) : Decidable c.UsesMD := by
  unfold UsesMD; infer_instance

/-- Does this coordination use ellipsis? -/
def UsesEllipsis (c : PFReducedCoordination) : Prop :=
  PFReductionMechanism.ellipsis ∈ c.mechanisms

instance (c : PFReducedCoordination) : Decidable c.UsesEllipsis := by
  unfold UsesEllipsis; infer_instance

/-- Does this coordination use both MD and ellipsis? -/
def UsesBoth (c : PFReducedCoordination) : Prop :=
  c.UsesMD ∧ c.UsesEllipsis

instance (c : PFReducedCoordination) : Decidable c.UsesBoth := by
  unfold UsesBoth; infer_instance

end PFReducedCoordination

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
  { sentence := "John gave something to someone, but I forgot what and to whom."
  , construction := .CS
  , whPhrases := ["what", "to whom"]
  , grammatical := true
  , notes := "Both obligatory args; allowed in CSs" }

/-- CSs allow wh-object + wh-adjunct coordination (ex 6b). -/
def cs_obj_adjunct_allowed : WHCoordDatum :=
  { sentence := "John bought something at some point, but I forgot what and when."
  , construction := .CS
  , whPhrases := ["what", "when"]
  , grammatical := true
  , notes := "Wh-object + wh-adjunct; allowed in CSs even with 'buy'" }

/-- All CWH/CS empirical contrasts as a single drift-sentry table. Replaces
    seven trivial `rfl` readouts (`cwh_bans_obligatory_args` etc.) with one
    decide-checked aggregate that catches drift in any row. -/
def whCoordContrastTable : List (WHCoordDatum × Bool) :=
  [ (cwh_basic, true)
  , (cwh_obligatory_args_banned, false)
  , (cwh_obj_adjunct_banned, false)
  , (cs_basic, true)
  , (cs_obligatory_args_allowed, true)
  , (cs_obj_adjunct_allowed, true) ]

theorem whCoordContrastTable_consistent :
    whCoordContrastTable.all (fun ⟨d, expected⟩ => d.grammatical == expected) = true := by
  decide

-- ============================================================================
-- § 1a: Reading Typology
-- ============================================================================

/-- Reading type for wh-coordination. -/
inductive ReadingType where
  /-- Each wh-phrase ranges over a single value (n-tuple as the answer). -/
  | paired
  /-- Each wh-phrase ranges over multiple values (cross-product answer). -/
  | nonpaired
  deriving Repr, DecidableEq

/-- Reading availability datum. -/
structure ReadingDatum where
  construction : WHCoordType
  reading : ReadingType
  available : Bool
  notes : String := ""
  deriving Repr

/-- CWHs: only nonpaired reading available (ex 8a). -/
def cwh_nonpaired : ReadingDatum :=
  { construction := .CWH
  , reading := .nonpaired
  , available := true
  , notes := "Each wh-phrase ranges over multiple values" }

/-- CWHs: paired reading unavailable (ex 8a). -/
def cwh_no_paired : ReadingDatum :=
  { construction := .CWH
  , reading := .paired
  , available := false
  , notes := "Single-pair reading is unavailable for CWHs" }

/-- CSs: paired reading available with obligatorily transitive verbs (ex 8b).
    The bulk-sharing CS structure puts both wh-phrases inside a single vP. -/
def cs_paired : ReadingDatum :=
  { construction := .CS
  , reading := .paired
  , available := true
  , notes := "Both wh-phrases share scope inside the bulk-shared vP" }

/-- CSs: nonpaired reading available with optionally transitive verbs (§6.1, ex 43).
    With optionally transitive verbs, the CWH-style structure becomes
    available, yielding a nonpaired reading. -/
def cs_nonpaired : ReadingDatum :=
  { construction := .CS
  , reading := .nonpaired
  , available := true
  , notes := "Available with optionally transitive verbs (CWH-style structure)" }

/-- Reading availability drift sentry. Replaces three rfl-readouts. -/
def readingTable : List ReadingDatum :=
  [cwh_nonpaired, cwh_no_paired, cs_paired, cs_nonpaired]

/-- Drift sentry: the four reading datums encode the paper's central
    paired/nonpaired contrast — CWH bans paired, CS allows both. -/
theorem readingTable_consistent :
    cwh_nonpaired.available = true ∧
    cwh_no_paired.available = false ∧
    cs_paired.available = true ∧
    cs_nonpaired.available = true := by decide

-- ============================================================================
-- § 1b: Sluicing Decomposition (CSs ≈ coordinated sluices)
-- ============================================================================

/-- One conjunct of a coordinated sluice, recast as a standalone sluice. -/
structure ComponentSluice where
  sentence : String
  whPhrase : String
  grammatical : Bool := true
  deriving Repr, DecidableEq

/-- The "what" conjunct of `cs_basic` as a standalone sluice
    (antecedent "John taught something", correlate "something",
    elided "John taught"). -/
def cs_basic_sluice_what : ComponentSluice :=
  { sentence := "John taught something, but I forgot what."
  , whPhrase := "what" }

/-- The "when" conjunct of `cs_basic` as a standalone sluice
    (antecedent "John taught (then)", correlate "(then)",
    elided "John taught"). -/
def cs_basic_sluice_when : ComponentSluice :=
  { sentence := "John taught (then), but I forgot when."
  , whPhrase := "when" }

/-- Each CS decomposes into sluices: the wh-phrases in a CS are
    each sluice remnants. -/
theorem cs_basic_decomposes_into_sluices :
    cs_basic.whPhrases =
      [cs_basic_sluice_what.whPhrase, cs_basic_sluice_when.whPhrase] := rfl

/-- Both component sluices are grammatical. -/
theorem cs_components_grammatical :
    cs_basic_sluice_what.grammatical = true ∧
    cs_basic_sluice_when.grammatical = true := ⟨rfl, rfl⟩

/-- The "what" conjunct of `cs_obligatory_args_allowed` (correlate
    "something", elided "John gave (to someone)"). -/
def cs_oblig_sluice_what : ComponentSluice :=
  { sentence := "John gave something to someone, but I forgot what."
  , whPhrase := "what" }

/-- The "to whom" conjunct of `cs_obligatory_args_allowed` (correlate
    "to someone", elided "John gave (something)"). -/
def cs_oblig_sluice_toWhom : ComponentSluice :=
  { sentence := "John gave something to someone, but I forgot to whom."
  , whPhrase := "to whom" }

/-- Obligatory-argument CS also decomposes into sluices. -/
theorem cs_obligatory_decomposes :
    cs_obligatory_args_allowed.whPhrases =
      [cs_oblig_sluice_what.whPhrase, cs_oblig_sluice_toWhom.whPhrase] := rfl

-- ============================================================================
-- § 2: Cross-linguistic MWF data and the English variety A/B split
-- ============================================================================

/-! Languages vary in whether multiple wh-specifiers at a phase edge are
tolerable at PF ([rudin-1988], [citko-gracanin-yuksek-2025]). The
substrate primitives (`MWFParameter`, `PhaseEdge`, `EdgeAsterisk`,
`MWFViolation`, `EllipsisRepairsMWF`) are in `Typology/Question.lean`;
this section holds the per-language data and theorems consuming them.

The intra-English variety A/B split is paper-specific to
[citko-gracanin-yuksek-2025] (p. 19): both varieties are non-MWF in
matrix questions, but they diverge on multiple sluicing — variety A bans
it, variety B allows it. The paper *derives* this asymmetry from where
the PF asterisk lands (vP only vs both vP and CP edges), not as a free
parameter: variety B is `.nonFrontsVPOnly`, variety A is
`.nonFrontsBothEdges`. -/

/-- Cross-linguistic MWF datum. Records the parameter setting and an
    example question. `AllowsMultipleSluicing` is **derived** from the
    parameter via `EllipsisRepairsMWF`. -/
structure MWFLanguageDatum where
  language : String
  mwfParam : MWFParameter
  /-- Example multiple wh-question. -/
  exampleQuestion : String
  /-- Is the bare multiple-wh question grammatical? -/
  grammatical : Bool
  notes : String := ""
  deriving Repr, DecidableEq

/-- Multiple sluicing is licensed iff vP-edge ellipsis repairs the MWF
    violation for `n = 2` wh-specifiers. **Derived, not stipulated.** -/
def MWFLanguageDatum.AllowsMultipleSluicing (d : MWFLanguageDatum) : Prop :=
  EllipsisRepairsMWF d.mwfParam 2 (vpEdgeDeleted := true)

instance (d : MWFLanguageDatum) : Decidable d.AllowsMultipleSluicing := by
  unfold MWFLanguageDatum.AllowsMultipleSluicing; infer_instance

/-- Bulgarian: MWF language ([rudin-1988] canonical case). -/
def bulgarian : MWFLanguageDatum :=
  { language := "Bulgarian"
  , mwfParam := .fronts
  , exampleQuestion := "Koj kakvo e kupil?"
  , grammatical := true
  , notes := "All wh-phrases front; [rudin-1988] canonical MWF language" }

/-- German: non-MWF; vP-only asterisk; multiple sluicing repairs.
    [citko-gracanin-yuksek-2025] ex 31a. -/
def german : MWFLanguageDatum :=
  { language := "German"
  , mwfParam := .nonFrontsVPOnly
  , exampleQuestion := "*Wer was hat gesehen?"
  , grammatical := false
  , notes := "Non-MWF; bans multiple wh-fronting in questions; "
           ++ "allows multiple sluicing ([citko-gracanin-yuksek-2025] ex 31a)" }

/-- Greek: non-MWF; vP-only asterisk; multiple sluicing repairs.
    [citko-gracanin-yuksek-2025] ex 31b. -/
def greek : MWFLanguageDatum :=
  { language := "Greek"
  , mwfParam := .nonFrontsVPOnly
  , exampleQuestion := "*Pços ti efere?"
  , grammatical := false
  , notes := "Non-MWF; bans multiple wh-fronting in questions; "
           ++ "allows multiple sluicing ([citko-gracanin-yuksek-2025] ex 31b)" }

/-- Cross-linguistic MWF table (textbook-consensus subset). -/
def mwfLanguageTable : List MWFLanguageDatum := [bulgarian, german, greek]

/-- Bulgarian: MWF language → no violations on bare multiple wh. -/
theorem bulgarian_no_violation : ¬ MWFViolation bulgarian.mwfParam 2 := by decide

/-- German question with two wh-phrases is starred. -/
theorem german_violates_in_questions : MWFViolation german.mwfParam 2 := by decide

/-- Sluicing repairs in German and Greek (vP-only asterisk eliminated). -/
theorem german_greek_sluicing_repairs :
    german.AllowsMultipleSluicing ∧ greek.AllowsMultipleSluicing := by decide

/-- English (default): variety A — both vP and CP asterisks; no sluicing
    repair. -/
def english : MWFParameter := .nonFrontsBothEdges

/-- English bans multiple wh-specifiers at a phase edge. -/
theorem english_bans_multiple_wh : MWFViolation english 2 := by decide

/-- A single wh-specifier is fine in English. -/
theorem english_allows_single_wh : ¬ MWFViolation english 1 := by decide

/-- English variety A: non-MWF, bans multiple sluicing. The CP-edge
    asterisk survives ellipsis (vP-edge deletion is not enough). -/
def english_varietyA : MWFLanguageDatum :=
  { language := "English (variety A)"
  , mwfParam := .nonFrontsBothEdges
  , exampleQuestion := "*Who what saw?"
  , grammatical := false
  , notes := "MWF asterisks at BOTH vP and CP edges; ellipsis cannot repair" }

/-- English variety B: non-MWF, allows multiple sluicing. Only the vP
    edge has the asterisk; vP-edge deletion repairs it. -/
def english_varietyB : MWFLanguageDatum :=
  { language := "English (variety B)"
  , mwfParam := .nonFrontsVPOnly
  , exampleQuestion := "*Who what saw?"
  , grammatical := false
  , notes := "MWF asterisk only at vP edge; sluicing repairs by deleting vP" }

/-- Variety A bans multiple sluicing, variety B allows it. **Derived** from
    the parameter via `EllipsisRepairsMWF`, not stipulated as an
    independent Bool. -/
theorem english_variety_split :
    ¬ english_varietyA.AllowsMultipleSluicing ∧
    english_varietyB.AllowsMultipleSluicing := by decide

-- ============================================================================
-- § 3: Derivation Cost Functions
-- ============================================================================

/-! Cost defs unchanged in shape from earlier revisions. The 4-Nat
parameterization (sm/sl/nsm/nsl coarse, hm/hl/pm/pl/wm/wl fine) is
ergonomically cryptic but matches the paper's argument granularity:

**Coarse** (MD vs ellipsis): parameterized by total shared/non-shared cost.
Used for Theorems 1–2.

- `sm`/`sl`: Merge/lexical cost of shared material (built once with MD,
  twice with ellipsis)
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

    The MD derivation saves `sm` Merge ops and `sl` lexical items, and
    avoids the ellipsis op entirely. This holds for ANY shared material —
    even `sm = sl = 0`, the ellipsis op alone makes the alternative
    costlier. -/
theorem cwh_md_beats_ellipsis (sm sl nsm nsl : Nat) :
    strictlyMoreEconomical (cwhMDCost sm sl nsm nsl) (cwhEllipsisCost sm sl nsm nsl) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp only [cwhMDCost, cwhEllipsisCost]
  all_goals omega

/-- **Theorem 2**: For CSs, the bulk-sharing derivation is strictly more
    economical than the double-ellipsis alternative (paper's (20b) vs (19b)).

    The bulk-sharing derivation saves `sm` Merge operations and `sl`
    lexical items, and uses one fewer ellipsis operation. -/
theorem cs_bulk_beats_double_ellipsis (sm sl nsm nsl : Nat) :
    strictlyMoreEconomical (csBulkCost sm sl nsm nsl) (csDoubleEllipsisCost sm sl nsm nsl) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp only [csBulkCost, csDoubleEllipsisCost]
  all_goals omega

/-- **Theorem 3**: Bulk-sharing is strictly more economical than
    non-bulk-sharing for CWHs (paper's (12b) vs (10b)).

    The paper's crucial insight: the MOST economical derivation for CWHs
    (bulk-sharing, which builds C' once) is blocked by an independent
    constraint (MWF), forcing the LESS economical non-bulk-sharing
    structure. The precondition `0 < pm ∨ 0 < pl` ensures there is at
    least some phrasal structure to share — which holds for any
    non-trivial clause. -/
theorem cwh_bulk_beats_nonbulk (hm hl pm pl wm wl : Nat) (h : 0 < pm ∨ 0 < pl) :
    strictlyMoreEconomical
      (cwhBulkMDCost hm hl pm pl wm wl)
      (cwhNonBulkCost hm hl pm pl wm wl) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp only [cwhBulkMDCost, cwhNonBulkCost]
  all_goals omega

/-! ### Identifying economy winners

The Theorems 1-3 above establish *strict-domination* facts; combining
each with `Minimalist.economy_winner_of_pair` (which discharges the
existence guarantee from `economy_admits_winner` for the binary case)
identifies the actual economy winner of the relevant 2-candidate
reference set. These are the load-bearing wirings: C&G-Y's selection
arguments need both "X dominates Y" AND "the reference set has a
winner" to deliver "X is THE winner". -/

/-- **CWH economy winner**: of the reference set `{cwhMDCost, cwhEllipsisCost}`,
    `cwhMDCost` is an economy winner — no element of the set is
    strictly more economical than it. Wires `cwh_md_beats_ellipsis`
    through `Minimalist.economy_winner_of_pair`. -/
theorem cwh_md_is_economy_winner (sm sl nsm nsl : Nat) :
    ∀ alt ∈ ({cwhMDCost sm sl nsm nsl, cwhEllipsisCost sm sl nsm nsl} : Set _),
      ¬ strictlyMoreEconomical alt (cwhMDCost sm sl nsm nsl) :=
  Minimalist.economy_winner_of_pair (cwh_md_beats_ellipsis sm sl nsm nsl)

/-- **CS economy winner**: of the reference set `{csBulkCost, csDoubleEllipsisCost}`,
    `csBulkCost` is an economy winner. Wires `cs_bulk_beats_double_ellipsis`
    through `Minimalist.economy_winner_of_pair`. -/
theorem cs_bulk_is_economy_winner (sm sl nsm nsl : Nat) :
    ∀ alt ∈ ({csBulkCost sm sl nsm nsl, csDoubleEllipsisCost sm sl nsm nsl} : Set _),
      ¬ strictlyMoreEconomical alt (csBulkCost sm sl nsm nsl) :=
  Minimalist.economy_winner_of_pair (cs_bulk_beats_double_ellipsis sm sl nsm nsl)

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
    MWFViolation english 2 := by decide

/-- CWHs have no ellipsis to repair the MWF violation —
    the vP edge survives to PF, and the asterisk crashes. -/
theorem cwh_no_ellipsis_repair :
    ¬ EllipsisRepairsMWF english 2 (vpEdgeDeleted := false) := by decide

/-- In English variety B (vP-only asterisk), CSs survive the same MWF
    configuration because ellipsis deletes the vP edge. Variety A
    (both-edges asterisk) is **not** repairable — CP-edge survives. -/
theorem cs_ellipsis_repairs_mwf_varietyB :
    EllipsisRepairsMWF english_varietyB.mwfParam 2 (vpEdgeDeleted := true) := by decide

-- ============================================================================
-- § 6: Why CSs Cannot Have the CWH Structure (per-op Pronunciation Economy)
-- ============================================================================

/-! Paper p. 32 (re. ex (45c)): "If both Cs had the E feature, …
Pronunciation Economy would be violated since the TP would be elided
twice (once by the E feature on each C)."

The argument depends on the CS structure where a **shared TP** has two
Cs each bearing the E-feature. Both Cs fire the E-feature on the same
TP — but only the first deletion has any PF effect; the second targets
material the first already removed. This is the per-operation vacuity
that requires the new `pronunciationEconomy : List PFOperation → Prop`
shape: a whole-derivation `pfBefore ≠ pfAfter` check would let this
through (the first deletion ensures the whole derivation's PF differs).
-/

/-- Initial PF state of the shared TP: contains "John taught". -/
def cs_twoEFeature_initialPF : List String := ["John", "taught"]

/-- The first C's E-feature deletion: removes "John taught" from the
    shared TP. Non-vacuous. -/
def cs_twoEFeature_firstDeletion : PFOperation :=
  { pfBefore := cs_twoEFeature_initialPF, pfAfter := [] }

/-- The second C's E-feature deletion: tries to delete the same shared
    TP, but it is already empty after the first deletion. Vacuous. -/
def cs_twoEFeature_secondDeletion : PFOperation :=
  { pfBefore := [], pfAfter := [] }

/-- The full deletion sequence under a hypothetical two-E-feature CS
    structure (paper's (45c) configuration). -/
def cs_twoEFeature_deletions : List PFOperation :=
  [cs_twoEFeature_firstDeletion, cs_twoEFeature_secondDeletion]

/-- The second deletion is vacuous (its PF before/after coincide). -/
theorem cs_twoEFeature_secondDeletion_vacuous :
    cs_twoEFeature_secondDeletion.isVacuous := rfl

/-- The two-E-feature CS structure violates Pronunciation Economy at
    the second deletion. This is the paper's (45c) ban — the per-op
    vacuity is what rules it out, even though the full derivation's
    pfBefore (`["John", "taught"]`) ≠ pfAfter (`[]`) is satisfied.

    A whole-derivation PF≠ check would pass this configuration
    incorrectly; the per-op `pronunciationEconomy` correctly fails it. -/
theorem cs_twoEFeature_violates_pronunciation_economy :
    ¬ pronunciationEconomy cs_twoEFeature_deletions :=
  pronunciationEconomy_violated_of_vacuous
    (op := cs_twoEFeature_secondDeletion)
    (by simp [cs_twoEFeature_deletions])
    cs_twoEFeature_secondDeletion_vacuous

/-- Whole-derivation PF differs (initial ["John","taught"] → final [])
    even though the second op is vacuous. This is exactly what makes a
    whole-derivation PF≠ check inadequate for the paper's argument. -/
theorem cs_twoEFeature_wholeDeriv_pf_differs :
    cs_twoEFeature_initialPF ≠ ([] : List String) := by decide

-- ============================================================================
-- § 7: Structural Summary — with populated sharedNodes
-- ============================================================================

/-- The adopted CWH structure: non-bulk-sharing MD, no ellipsis (paper's (10b)).
    Shared nodes: C and T are individually multiply dominated. -/
def cwhStructure : PFReducedCoordination where
  conjunct1 := SyntacticObject.mkLeaf .C [] 0
  conjunct2 := SyntacticObject.mkLeaf .C [] 1
  mechanisms := [.multidominance]
  sharing := some .nonBulk
  sharedNodes :=
    [ { node := SyntacticObject.mkLeaf .C [] 10, category := some .C, pronounced := true }
    , { node := SyntacticObject.mkLeaf .T [] 11, category := some .T, pronounced := false } ]
  pfOutput := ["what", "and", "when", "should", "you", "teach"]

/-- The adopted CS structure: bulk-sharing MD + ellipsis (paper's (20b)).
    The E-feature on C (cf. `FeatureVal.ellipsis` in `Core/Features.lean`)
    triggers TP deletion, repairing the MWF violation at the vP edge.
    Shared nodes: entire C' is shared (includes C, TP, vP, VP). -/
def csStructure : PFReducedCoordination where
  conjunct1 := SyntacticObject.mkLeaf .C [] 0
  conjunct2 := SyntacticObject.mkLeaf .C [] 1
  mechanisms := [.multidominance, .ellipsis]
  sharing := some .bulk
  sharedNodes :=
    [ { node := SyntacticObject.mkLeaf .C [] 10, category := some .C, pronounced := true }
    , { node := SyntacticObject.mkLeaf .T [] 11, category := some .T, pronounced := false }
    , { node := SyntacticObject.mkLeaf .v [] 12, category := some .v, pronounced := false } ]
  pfOutput := ["what", "and", "when"]

/-- Structural drift sentry over the four key properties of cwhStructure
    and csStructure. Replaces five individual rfl theorems
    (`cwh_uses_md_only`, `cs_uses_both`, `cwh_shares_heads_cs_shares_constituent`,
    `cwh_shared_categories`, `cs_shared_categories`). -/
theorem cwhStructure_csStructure_drift_sentry :
    cwhStructure.UsesMD ∧ ¬ cwhStructure.UsesEllipsis ∧
    csStructure.UsesBoth ∧
    cwhStructure.sharedNodes.length = 2 ∧ csStructure.sharedNodes.length = 3 ∧
    cwhStructure.sharedNodes.all (·.category.isSome) = true ∧
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
2. Bulk-sharing creates MWF at vP, but ellipsis repairs it
   (`cs_ellipsis_repairs_mwf_varietyB`, in vP-only varieties)
3. Non-bulk-sharing (CWH structure) violates Pronunciation Economy
   (`cs_twoEFeature_violates_pronunciation_economy`)
4. So bulk-sharing MD + ellipsis is selected
-/

/-- The two constructions differ in which mechanisms they use. -/
theorem different_mechanisms :
    cwhStructure.mechanisms ≠ csStructure.mechanisms := by decide

/-- The two constructions differ in sharing type. -/
theorem different_sharing :
    cwhStructure.sharing ≠ csStructure.sharing := by decide

/-- End-to-end: CWHs cannot use bulk-sharing (most economical)
    because the MWF violation at vP cannot be repaired without ellipsis.
    Combines Theorem 3, `cwh_bulk_crashes_in_english`, and
    `cwh_no_ellipsis_repair`. -/
theorem cwh_forced_to_nonbulk (hm hl pm pl wm wl : Nat) (h : 0 < pm ∨ 0 < pl) :
    -- Bulk-sharing IS more economical...
    strictlyMoreEconomical (cwhBulkMDCost hm hl pm pl wm wl) (cwhNonBulkCost hm hl pm pl wm wl)
    -- ...but it crashes in English (MWF at vP)...
    ∧ MWFViolation english 2
    -- ...and CWHs can't repair the crash (no ellipsis).
    ∧ ¬ EllipsisRepairsMWF english 2 (vpEdgeDeleted := false) :=
  ⟨cwh_bulk_beats_nonbulk hm hl pm pl wm wl h, by decide, by decide⟩

/-- End-to-end: CSs use bulk-sharing because it is most economical AND the
    MWF violation is repaired by ellipsis (in vP-only varieties); the CWH
    (two-E-feature) structure is excluded by per-op Pronunciation Economy. -/
theorem cs_forced_to_bulk (sm sl nsm nsl : Nat) :
    -- Bulk-sharing beats double-ellipsis...
    strictlyMoreEconomical (csBulkCost sm sl nsm nsl) (csDoubleEllipsisCost sm sl nsm nsl)
    -- ...ellipsis repairs the MWF violation at vP (variety B / German / Greek)...
    ∧ EllipsisRepairsMWF english_varietyB.mwfParam 2 (vpEdgeDeleted := true)
    -- ...and the two-E-feature CWH-style CS violates Pronunciation Economy.
    ∧ ¬ pronunciationEconomy cs_twoEFeature_deletions :=
  ⟨cs_bulk_beats_double_ellipsis sm sl nsm nsl, by decide,
   cs_twoEFeature_violates_pronunciation_economy⟩

-- ============================================================================
-- § 9: Right Node Raising — Ellipsis + MD Interaction
-- ============================================================================

/-! Section 6.2 of the paper extends the economy analysis to Right Node
Raising (RNR). RNR is a key test case because it can involve BOTH
ellipsis and MD simultaneously — the "mix and match" analysis of
[belk-neeleman-philip-2023] (and earlier [barros-vicente-2011]).

The core claim: economy favors MD over ellipsis when both yield the same
string and interpretation. In RNR, the shared pivot (rightmost material)
is multiply dominated. When the pivot and antecedent are not morphologically
identical (vehicle change), ellipsis is additionally required for the
non-shared material in the first conjunct. -/

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
  /-- The shared pivot string (right-edge material). -/
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
  { sentence :=
    "Alice must work on different topics, and Iris ought to be working on different topics."
  , pivot := "on different topics"
  , morphologicalIdentity := false
  , mdProperties := true
  , involvesEllipsis := true
  , pivotType := .minimal
  , notes :=
    "Morphological mismatch (work vs working); PP shared via MD, VP ellipsis in first conjunct" }

/-- Vehicle-change diagnostic from [barros-vicente-2011] ex (47):
    morphological mismatch signals ellipsis (not MD).

    The angled brackets mark the **first** conjunct's predicate as
    PF-reduced under identity with the **second** conjunct's overt
    predicate — backwards elision, not forwards RNR with a right-edge
    pivot. The morphological mismatch (`wake` vs `wakes`) confirms
    ellipsis (which tolerates vehicle change) over MD (which requires
    morphological identity for a single multiply-dominated node). -/
def rnr_ellipsisOnly : RNRDatum :=
  { sentence := "I usually don't ⟨wake up early every day⟩, but Alice wakes up early every day."
  , pivot := "wake up early every day"  -- the elided string in 1st conjunct
  , morphologicalIdentity := false
  , mdProperties := false
  , involvesEllipsis := true
  , pivotType := .extended
  , notes := "[barros-vicente-2011] ex (47): backwards elision pattern; "
           ++ "1st conjunct predicate PF-reduced under identity with 2nd; "
           ++ "morphological mismatch ('wake' vs 'wakes') signals ellipsis not MD" }

/-- Relational adjective with internal reading signals MD. -/
def rnr_internalReading : RNRDatum :=
  { sentence := "Alice composed, and Beatrix performed, different songs."
  , pivot := "different songs"
  , morphologicalIdentity := true
  , mdProperties := true
  , involvesEllipsis := false
  , pivotType := .minimal
  , notes := "Internal reading of 'different' requires c-command from both subjects → MD" }

/-- RNR datum drift sentry: morphological-identity / MD-properties /
    ellipsis-involvement consistent with the paper's typology. Replaces
    `rnr_economy_prefers_md` and `rnr_mismatch_forces_ellipsis`. -/
theorem rnr_typology_drift_sentry :
    -- pureMD: morph match, MD, no ellipsis
    rnr_pureMD.morphologicalIdentity = true ∧
    rnr_pureMD.mdProperties = true ∧
    rnr_pureMD.involvesEllipsis = false ∧
    -- ellipsisPlusMD: morph mismatch, MD, ellipsis
    rnr_ellipsisPlusMD.morphologicalIdentity = false ∧
    rnr_ellipsisPlusMD.mdProperties = true ∧
    rnr_ellipsisPlusMD.involvesEllipsis = true ∧
    -- internalReading: morph match, MD (internal-reading diagnostic)
    rnr_internalReading.mdProperties = true ∧
    rnr_internalReading.involvesEllipsis = false := by decide

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
    ellipsis when both yield the same string. Same shape as Theorem 1. -/
theorem rnr_md_beats_ellipsis (pm pl nm nl : Nat) :
    strictlyMoreEconomical (rnrMDPivotCost pm pl nm nl) (rnrEllipsisCost pm pl nm nl) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp only [rnrMDPivotCost, rnrEllipsisCost]
  all_goals omega

/-- **RNR economy winner**: of the reference set `{rnrMDPivotCost, rnrEllipsisCost}`,
    `rnrMDPivotCost` is an economy winner. Wires `rnr_md_beats_ellipsis`
    through `Minimalist.economy_winner_of_pair`. -/
theorem rnr_md_is_economy_winner (pm pl nm nl : Nat) :
    ∀ alt ∈ ({rnrMDPivotCost pm pl nm nl, rnrEllipsisCost pm pl nm nl} : Set _),
      ¬ strictlyMoreEconomical alt (rnrMDPivotCost pm pl nm nl) :=
  Minimalist.economy_winner_of_pair (rnr_md_beats_ellipsis pm pl nm nl)

end CitkoGracaninYuksek2025
