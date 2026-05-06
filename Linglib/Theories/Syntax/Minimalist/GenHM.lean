import Linglib.Theories.Syntax.Minimalist.VerbMovementParameter
import Linglib.Theories.Syntax.Minimalist.Agree
import Linglib.Theories.Syntax.Minimalist.Amalgamation

/-!
# Generalized Head Movement (GenHM)
@cite{arregi-pietraszko-2021}

Formalization of Generalized Head Movement following @cite{arregi-pietraszko-2021}.

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

namespace Minimalist

-- ============================================================================
-- § 1  M-Values (Morphological Feature Bundles)
-- ============================================================================

/-- An M-value is a bundle of morphological features (tense, agreement)
    shared between terminal nodes via GenHM.

    We reuse `FeatureBundle` since M-values are grammatical features. -/
abbrev MValue := FeatureBundle

-- ============================================================================
-- § 2  GenHM Relation
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
-- § 3  Chain-Splitting and Chain Structure
-- ============================================================================

/-- Identification of the [+P] specifier that triggers Split-by-Intervention.

    Per @cite{arregi-pietraszko-2021} footnote 30, A&P unify the three
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

    @cite{arregi-pietraszko-2021} recognize exactly two chain-splitting
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
-- § 4  PF Spell-Out Rule
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
-- § 5  Do-Support
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
-- § 6  Key Theorems
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
-- § 7  Unification with Existing Infrastructure
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

end Minimalist
