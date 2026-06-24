import Linglib.Syntax.Minimalist.VerbMovementParameter
import Linglib.Syntax.Minimalist.Agree
import Linglib.Syntax.Minimalist.Amalgamation
import Linglib.Data.Examples.ArregiPietraszko2021

/-!
# GenHM and Do-Support
[arregi-pietraszko-2021]

Connects the GenHM formalization to A&P's do-support paradigm
(`Data/Examples/ArregiPietraszko2021.json`).

## Structure

**§1** English GenHM chain configurations for A&P's four do-support contexts
**§2** The bridge table: each contextual datum paired with its GenHM prediction
**§3** The parallelism theorem: do-support uniformity across all four contexts
**§4** Deriving VMovementParam from GenHM

## Central Result

The parallelism of do-support across A&P's three core contexts (negation,
SAI, verum focus) plus VPE is a DERIVED consequence of GenHM chain
structure, not a stipulation about the V-movement parameter. The four
contexts involve two structurally distinct reasons for chain-splitting —
intervention by a [+P] specifier (negation, SAI, verum) and post-syntactic
[-P] on V* (VPE) — yet all produce the same do-support outcome because
spell-out depends only on WHETHER the chain is split.

A&P unify the three intervention contexts under a single specifier-intervention
rule (footnote 30). SAI is intervention by the subject in Spec,TP, NOT
"probe displacement"; verum focus is intervention by a covert specifier in
Spec,ΣP, NOT a "weak Foc head".

## Out of scope

Tag questions (e.g. *She likes him, doesn't she?*) are not in A&P's paper;
their analysis belongs in a future Sailor 2018 study file. A substantive
`TenseSupportContext → GenHMChain` bridge that would connect this file's
predictions to `Pollock1989.lean`'s `needsDoSupport` is deferred to a
cross-framework wiring follow-up. Orphan Assignment (the actual do-insertion
derivation) and the strong V parameter (A&P's cross-linguistic prediction)
are deferred to follow-up substrate work; `needsDoSupportGenHM` here is a
Boolean proxy.

-/

namespace ArregiPietraszko2021

open Data.Examples
open Minimalist

/-! ### Generalized Head Movement (relocated from Minimalist/GenHM.lean)

Formalization of Generalized Head Movement following [arregi-pietraszko-2021].

## Central Claim

Head displacement (subject-auxiliary inversion, T-lowering, do-support) is
not syntactic movement but a single Agree-based operation — **GenHM** — that
shares morphological features (M-values) between terminal nodes. The
*direction* of displacement (upward vs downward) is determined postsyntactically
at PF, based on which terminal in the chain spells out the shared M-value.

## Mechanism

1. **GenHM** relates two terminals X and Y in a local syntactic configuration,
   sharing an M-value (tense/phi features) between them → chain ⟨X, Y⟩.
2. **PF Chain Resolution**: The M-value is pronounced on exactly one terminal.
   - Default: the M-value lowers to the goal (V) — affix hopping.
   - When the chain is *split*, the M-value is stranded on the probe (T) —
     looks like "raising".
3. **Chain-splitting** occurs for exactly two reasons (A&P unify intervention
   contexts under a single [+P]-specifier rule; cf. footnote 30):
   - **Split-by-Intervention**: a [+P] specifier intervenes between the top
     of the chain and V*. This subsumes overt negation (Spec,ΣP), verum
     focus (covert specifier in Spec,ΣP), and SAI (subject in Spec,TP).
   - **Split-by-Deletion**: V* is marked [-P] post-syntactically, e.g.
     inside an elided VP.
4. **Do-support**: When the M-value is stranded on a probe (T) that has no
   independent lexical content, a dummy verb *do* is inserted at PF.

## Key Result

The parallelism of do-support across A&P's three core contexts (negation,
SAI, verum focus) plus VPE is DERIVED from GenHM chain structure: all four
share the same structural property, namely a split chain stranding the
M-value on a contentless T. The specific *reason* for the split is
irrelevant to the do-support prediction.

## Out of scope (deferred)

- **Orphan Assignment** (the actual *do*-insertion mechanism: [O] feature
  on stranded V_m, defective Vocabulary Insertion). `needsDoSupportGenHM`
  here is a Boolean proxy for the do-insertion decision, not the derivation.
- **Strong V parameter** (A&P's cross-linguistic prediction for Monnese
  and Mainland Scandinavian: strength of V/T/C heads governs whether
  chain-splitting feeds defective spell-out). The Boolean `isSplit`
  here corresponds only to the English/strong-V case.
- **Tag questions** (e.g. *She likes him, doesn't she?*) are NOT in A&P's
  paper; they have their own literature (Sailor 2018, Bjorkman 2011).
  A future tag-question study file is the right home for them.
-/

-- ============================================================================
-- § GenHM.1  M-Values (Morphological Feature Bundles)
-- ============================================================================

/-- An M-value is a bundle of morphological features (tense, agreement)
    shared between terminal nodes via GenHM.

    We reuse `FeatureBundle` since M-values are grammatical features. -/
abbrev MValue := FeatureBundle

-- ============================================================================
-- § GenHM.2  GenHM Relation
-- ============================================================================

/-- The Generalized Head Movement relation.

    GenHM relates two terminal nodes X (probe) and Y (goal) in a local
    syntactic configuration, sharing an M-value between them. This is an
    instance of Agree specialized for head displacement. -/
structure GenHMRelation where
  /-- The higher terminal (e.g., T or C) — the probe -/
  probe : SyntacticObject
  /-- The lower terminal (e.g., V or Aux) — the goal -/
  goal : SyntacticObject
  /-- The shared morphological features -/
  mValue : MValue
  /-- The feature type being shared (tense, phi, etc.) -/
  feature : FeatureVal
  /-- The containing tree -/
  root : SyntacticObject
  /-- Structural condition: probe c-commands goal -/
  probe_commands_goal : cCommandsIn root probe goal
  /-- The goal bears valued M-features -/
  goal_has_mvalue : hasValuedFeature mValue feature = true
  /-- The probe bears unvalued M-features -/
  probe_needs_mvalue : hasUnvaluedFeature mValue feature = true

/-- GenHM is an instance of Agree: it relates a probe with unvalued features
    to a goal with valued features under c-command. -/
def genHM_to_agree (g : GenHMRelation) : AgreeRelation :=
  { probe := g.probe
    goal := g.goal
    feature := g.feature
    probeFeatures := g.mValue
    goalFeatures := g.mValue }

/-- A valid GenHM relation satisfies the conditions for valid Agree. -/
theorem genHM_is_agree (g : GenHMRelation) :
    validAgree (genHM_to_agree g) g.root := by
  refine ⟨?_, ?_, ?_⟩
  · exact g.probe_commands_goal
  · exact g.probe_needs_mvalue
  · exact g.goal_has_mvalue

-- ============================================================================
-- § GenHM.3  Chain-Splitting and Chain Structure
-- ============================================================================

/-- Identification of the [+P] specifier that triggers Split-by-Intervention.

    Per [arregi-pietraszko-2021] footnote 30, A&P unify the three
    intervention contexts under a single specifier-intervention rule.
    This field is therefore diagnostic only — A&P's chain-splitting rule
    itself does not branch on which specifier intervened. -/
inductive InterveningSpecifier where
  /-- Subject in Spec,TP. The configuration A&P invoke for SAI: GenHM
      relates V, T, and C across the subject specifier. -/
  | subjectInSpecTP
  /-- Overt negation in Spec,ΣP (sentential negation, e.g. *Sue does not
      eat fish*). -/
  | negSpecifier
  /-- Covert specifier in Spec,ΣP triggering verum focus (e.g. *Sue DOES
      eat fish*). -/
  | verumCovertSpecifier
  deriving DecidableEq, Repr

/-- The reason a GenHM chain is split, preventing M-value lowering.

    [arregi-pietraszko-2021] recognize exactly two chain-splitting
    mechanisms:

    1. **Split-by-Intervention**: a [+P] specifier intervenes between the
       top of the chain and V*. Subsumes overt negation, verum focus, and
       SAI under one rule.
    2. **Split-by-Deletion**: V* is marked [-P] post-syntactically (e.g.
       inside an elided VP), blocking Vocabulary Insertion of the lowered
       M-value.

    Both produce the same PF effect: the M-value cannot lower and is
    stranded on the probe. -/
inductive ChainSplitReason where
  /-- A [+P] specifier intervenes; field identifies which one. -/
  | intervention (specifier : InterveningSpecifier)
  /-- V* is post-syntactically marked [-P], e.g. inside an elided VP. -/
  | deletion
  deriving DecidableEq, Repr

/-- A GenHM chain between a probe and a goal, possibly split.

    The chain captures the structural configuration relevant for PF
    spell-out: whether the M-value can lower from probe to goal, or
    is stranded on the probe. The `splitReason` field tracks both
    whether the chain is split and why. -/
structure GenHMChain where
  /-- Category of the probe (T or C) -/
  probeCat : Cat
  /-- Category of the goal (V) -/
  goalCat : Cat
  /-- Why the chain is split, if at all. `none` = clear chain. -/
  splitReason : Option ChainSplitReason

/-- Is the chain split? A split chain strands the M-value on the probe. -/
def GenHMChain.isSplit (chain : GenHMChain) : Bool :=
  chain.splitReason.isSome

-- ============================================================================
-- § GenHM.4  PF Spell-Out Rule
-- ============================================================================

/-- Where the M-value is pronounced at PF.

    - `.onGoal`: M-value lowers to the goal (= affix hopping / T-lowering)
    - `.onProbe`: M-value stays on the probe (= "raising" / stranding) -/
inductive SpellOutTarget where
  | onGoal
  | onProbe
  deriving DecidableEq, Repr

/-- Determine where the M-value is spelled out.

    The M-value surfaces on the goal (lower terminal) unless the chain
    is split, in which case it is stranded on the probe (higher terminal).
    The reason for the split is irrelevant — only whether it is split. -/
def spellOutTarget (chain : GenHMChain) : SpellOutTarget :=
  if chain.isSplit then .onProbe else .onGoal

-- ============================================================================
-- § GenHM.5  Do-Support
-- ============================================================================

/-- The do-support condition.

    Do-support is triggered when:
    1. The M-value is stranded on the probe (chain is split), AND
    2. The probe has no independent lexical content (is a contentless T head)

    This is a PF repair strategy: the grammar inserts *do* to host
    tense features that cannot lower to V and have no other host.

    NOTE: this is a Boolean proxy. A&P's actual derivation routes through
    Orphan Assignment ([O] feature on the stranded V_m, then defective
    Vocabulary Insertion as *do*). Modeling that machinery is deferred. -/
def needsDoSupportGenHM (chain : GenHMChain) (probeHasContent : Bool) : Bool :=
  match spellOutTarget chain with
  | .onProbe => !probeHasContent
  | .onGoal => false

/-- Do-support is a last resort: it is only used when the M-value cannot
    reach the goal AND the probe cannot host it independently. -/
theorem doSupport_is_lastResort (chain : GenHMChain) (probeHasContent : Bool) :
    needsDoSupportGenHM chain probeHasContent = true →
    spellOutTarget chain = .onProbe ∧ probeHasContent = false := by
  simp only [needsDoSupportGenHM]
  split
  · intro h; exact ⟨‹_›, by simpa using h⟩
  · intro h; simp at h

-- ============================================================================
-- § GenHM.6  Key Theorems
-- ============================================================================

/-- **Theorem 1: Lowering when chain is clear.**

    When the chain is not split, the M-value surfaces on the goal
    (= T-lowering / affix hopping). -/
theorem lowering_when_not_split (chain : GenHMChain)
    (h : chain.isSplit = false) :
    spellOutTarget chain = .onGoal := by
  simp [spellOutTarget, h]

/-- **Theorem 2: Raising when chain is split.**

    When the chain is split (by intervention or deletion), the M-value
    surfaces on the probe (= "raising" / stranding). -/
theorem raising_when_split (chain : GenHMChain)
    (h : chain.isSplit = true) :
    spellOutTarget chain = .onProbe := by
  simp [spellOutTarget, h]

/-- **Theorem 3: Do-support iff split and contentless.**

    Do-support is triggered iff (a) the chain is split AND
    (b) the probe has no lexical content. -/
theorem doSupport_iff_split_and_empty (chain : GenHMChain) (probeContent : Bool) :
    needsDoSupportGenHM chain probeContent = true ↔
    (chain.isSplit = true ∧ probeContent = false) := by
  constructor
  · intro h
    have ⟨hTarget, hContent⟩ := doSupport_is_lastResort chain probeContent h
    refine ⟨?_, hContent⟩
    unfold spellOutTarget at hTarget
    split at hTarget
    · assumption
    · exact absurd hTarget (by simp)
  · intro ⟨hSplit, hContent⟩
    simp [needsDoSupportGenHM, spellOutTarget, hSplit, hContent]

/-- **Theorem 4: Do-support is uniform across contexts.**

    For ANY GenHM chain with the same split status and probe content,
    do-support is triggered or not uniformly. The specific reason for
    the split (intervention or deletion) is irrelevant.
    This is the parallelism theorem. -/
theorem doSupport_uniform_across_contexts
    (chain₁ chain₂ : GenHMChain) (content₁ content₂ : Bool)
    (h_same_split : chain₁.isSplit = chain₂.isSplit)
    (h_same_content : content₁ = content₂) :
    needsDoSupportGenHM chain₁ content₁ = needsDoSupportGenHM chain₂ content₂ := by
  simp only [needsDoSupportGenHM, spellOutTarget, h_same_split, h_same_content]

/-- **Theorem 5: Auxiliaries don't need do-support.**

    When the probe IS the auxiliary (T = Aux with lexical content), do-support
    is never needed, regardless of chain structure. -/
theorem auxiliaries_dont_need_doSupport (chain : GenHMChain) :
    needsDoSupportGenHM chain true = false := by
  simp [needsDoSupportGenHM]
  split <;> rfl

/-- **Corollary: Lexical verbs need do-support when chain is split.** -/
theorem lexical_verb_needs_doSupport_when_split (chain : GenHMChain)
    (h : chain.isSplit = true) :
    needsDoSupportGenHM chain false = true := by
  simp [needsDoSupportGenHM, spellOutTarget, h]

-- ============================================================================
-- § GenHM.7  Unification with Existing Infrastructure
-- ============================================================================

/-- Extended head displacement classification.

    Adds GenHM as a third option alongside syntactic movement (= MCB
    Internal Merge, encoded as `Step.im` in `Derivation.lean`) and
    postsyntactic amalgamation. The `syntactic` constructor is now a
    pure tag — the analyst supplies the actual `Step.im` evidence via
    a separate `Derivation` when the diagnostic predicates are needed.
    Refactored at 0.230.788 when the legacy `Movement` record was
    deleted in favor of MCB-aligned `Step.im` / `Derivation.movedItems`. -/
inductive HeadDisplacementExt where
  | syntactic : HeadDisplacementExt
  | amalgam : Amalgamation → HeadDisplacementExt
  | genHM : GenHMRelation → HeadDisplacementExt

/-- GenHM subsumes both "raising" and "lowering" as surface realizations
    of a single operation. -/
theorem genHM_subsumes_raising_lowering (chain : GenHMChain) :
    spellOutTarget chain = .onGoal ∨ spellOutTarget chain = .onProbe := by
  simp only [spellOutTarget]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- GenHM chain structure determines the surface pattern captured by
    `VMovementParam`. -/
def genHM_to_vMovementParam (chain : GenHMChain) : VMovementParam :=
  match spellOutTarget chain with
  | .onGoal => .raises
  | .onProbe => .inSitu

/-- When the chain is clear, the surface pattern is V-raising. -/
theorem genHM_clear_chain_is_raises (chain : GenHMChain)
    (h : chain.isSplit = false) :
    genHM_to_vMovementParam chain = .raises := by
  simp [genHM_to_vMovementParam, spellOutTarget, h]

/-- When the chain is split, the surface pattern is V-in-situ. -/
theorem genHM_split_chain_is_inSitu (chain : GenHMChain)
    (h : chain.isSplit = true) :
    genHM_to_vMovementParam chain = .inSitu := by
  simp [genHM_to_vMovementParam, spellOutTarget, h]

-- ============================================================================
-- § 1  English GenHM Chain Configurations
-- ============================================================================

/-! A&P's four do-support contexts as GenHM chains. The four chains involve
two distinct split mechanisms:

- **Split-by-Intervention** (a [+P] specifier intervenes between top of
  chain and V*): negation, SAI, verum focus.
- **Split-by-Deletion** (V* marked [-P] post-syntactically): VPE. -/

/-- **Negation chain**: T ... [Spec,ΣP: *not*] ... V

    "Sue does not eat fish" — overt *not* in Spec,ΣP intervenes.
    Split-by-Intervention. -/
def negationChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := some (.intervention .negSpecifier)

/-- **Verum focus chain**: T ... [Spec,ΣP: covert verum specifier] ... V

    "Sue DOES eat fish" — covert specifier in Spec,ΣP intervenes
    (cf. A&P fn. 30 — same intervention mechanism as negation).
    Split-by-Intervention. -/
def verumChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := some (.intervention .verumCovertSpecifier)

/-- **Question chain (SAI)**: C ← T ... [Spec,TP: subject] ... V

    "Where does Sue eat fish?" — the subject in Spec,TP intervenes
    between T (chained to C) and V*. Crucially this is intervention,
    NOT "probe displacement" — see A&P, where GenHM is taken to relate
    V, T, and C across the subject specifier.
    Split-by-Intervention. -/
def questionChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := some (.intervention .subjectInSpecTP)

/-- **VP ellipsis chain**: T ... V (with V* marked [-P] post-syntactically)

    "She runs faster than he does" — V is present and chained to T;
    VPE marks V* with [-P], blocking lowered Vocabulary Insertion.
    Split-by-Deletion (NOT goal-absence — A&P's analysis crucially has
    GenHM still applying). -/
def vpEllipsisChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := some .deletion

/-- A declarative chain with no split: T ... V

    "Sue eats fish" — clear chain, M-value lowers to V (affix hopping). -/
def declarativeChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := none

/-- Behavioral fact about declaratives: M-value lowers (affix hopping). -/
@[simp] theorem declarative_lowers : spellOutTarget declarativeChain = .onGoal := rfl

/-- Behavioral fact about declaratives with lexical V: no do-support. -/
@[simp] theorem declarative_no_doSupport :
    needsDoSupportGenHM declarativeChain false = false := rfl

-- ============================================================================
-- § 2  Bridge Table: Empirical Data Meets GenHM Predictions
-- ============================================================================

/-- Value of a `paperFeatures` key, if present. -/
def featureOf (row : LinguisticExample) (key : String) : Option String :=
  (row.paperFeatures.find? (·.1 == key)).map (·.2)

/-- Does the sentence use do-support? (`do_support` feature). -/
def usesDoSupport (row : LinguisticExample) : Option Bool :=
  (featureOf row "do_support").map (· == "true")

/-- Does the probe carry lexical content? (auxiliary = true, lexical
    V = false; `verb_type` feature). -/
def probeHasContent (row : LinguisticExample) : Option Bool :=
  (featureOf row "verb_type").map (· == "auxiliary")

/-- A&P's do-support paradigm as a bridge table: each generated row
    paired with the GenHM chain configuration assigned in §1.

    Coverage: A&P's three core contexts (negation, SAI, verum focus)
    each tested with lexical V, auxiliary, and the starred do-support
    misuse; VPE tested with lexical V only (the auxiliary case is not a
    do-support trigger and not in A&P's discussion of VPE). -/
def doSupportTable : List (LinguisticExample × GenHMChain) :=
  [ (Examples.ex32, negationChain)    -- "Sue does not eat fish"
  , (Examples.ex33, negationChain)    -- *"Sue not eats fish"
  , (Examples.ex34, negationChain)    -- "Sue is not eating fish"
  , (Examples.ex35, negationChain)    -- *"Sue does not be eating fish"
  , (Examples.ex27, questionChain)    -- "Where does Sue eat fish?"
  , (Examples.ex30, questionChain)    -- "Where is Sue eating fish?"
  , (Examples.ex31, questionChain)    -- *"Where does Sue be eating fish?"
  , (Examples.ex39, verumChain)       -- "Sue DOES eat fish"
  , (Examples.ex40, verumChain)       -- "She IS eating fish"
  , (Examples.ex41, verumChain)       -- *"She DOES be eating fish"
  , (Examples.ex38, vpEllipsisChain)  -- "She runs faster than he does"
  ]

/-- **Transfer equation**: a row in the bridge table is acceptable iff
    its use (or omission) of do-support matches the GenHM prediction for
    its chain and probe content. The starred rows (`ex31`, `ex33`,
    `ex35`, `ex41`) are exactly those whose do-support usage contradicts
    the prediction — A&P's parallelism claim is precisely that this
    holds uniformly across all four contexts. -/
theorem all_bridges_hold :
    ∀ p ∈ doSupportTable,
      p.1.judgment = .acceptable ↔
        usesDoSupport p.1 = (probeHasContent p.1).map (needsDoSupportGenHM p.2) := by
  decide

-- ============================================================================
-- § 3  The Parallelism Theorem
-- ============================================================================

/-- **Parallelism for lexical verbs**: any split chain triggers do-support
    when the probe is contentless. Concrete consequence of the substrate
    theorem `lexical_verb_needs_doSupport_when_split`. -/
theorem doSupport_parallel_lexical
    (chain : GenHMChain) (h : chain.isSplit = true) :
    needsDoSupportGenHM chain false = true :=
  lexical_verb_needs_doSupport_when_split chain h

/-- **Parallelism for auxiliaries**: no chain triggers do-support when the
    probe carries lexical content. Concrete consequence of
    `auxiliaries_dont_need_doSupport`. -/
theorem doSupport_parallel_aux (chain : GenHMChain) :
    needsDoSupportGenHM chain true = false :=
  auxiliaries_dont_need_doSupport chain

/-- **Context-irrelevance**: any two chains with the same split status give
    the same do-support decision. The reason for the split (intervention
    vs deletion) is irrelevant. -/
theorem doSupport_context_irrelevant
    (chain₁ chain₂ : GenHMChain) (content : Bool)
    (h : chain₁.isSplit = chain₂.isSplit) :
    needsDoSupportGenHM chain₁ content = needsDoSupportGenHM chain₂ content :=
  doSupport_uniform_across_contexts chain₁ chain₂ content content h rfl

-- ============================================================================
-- § 4  Deriving VMovementParam from GenHM
-- ============================================================================

/-- A clear chain (no split) yields the `.raises` surface pattern. -/
theorem genHM_derives_raises :
    genHM_to_vMovementParam declarativeChain = .raises := rfl

/-- A split chain yields the `.inSitu` surface pattern. -/
theorem genHM_derives_inSitu :
    genHM_to_vMovementParam negationChain = .inSitu := rfl

/-! TODO: a substantive `chainOf : TenseSupportContext → GenHMChain` map
would let us state `needsDoSupport p ctx = needsDoSupportGenHM (chainOf ctx)
(contentOf p)` — converting Pollock1989's flat parameter into a derived
view of GenHM's chain structure. Deferred to a cross-framework wiring
follow-up that also touches `Pollock1989.lean`. -/

end ArregiPietraszko2021
