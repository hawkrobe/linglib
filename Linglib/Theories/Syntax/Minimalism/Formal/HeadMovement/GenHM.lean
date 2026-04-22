/-
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
3. **Chain-splitting** occurs for three structurally distinct reasons:
   - A weak terminal (Neg, Foc) intervenes (Split-by-Intervention)
   - The probe is displaced away from the goal (Split-by-Displacement, e.g., SAI)
   - The goal is absent or deleted (Split-by-Deletion, e.g., VP ellipsis, tags)
4. **Do-support**: When the M-value is stranded on a probe (T) that has no
   independent lexical content, a dummy verb *do* is inserted at PF.

## Key Result

The parallelism of do-support across five contexts (negation, SAI, verum
focus, tag questions, VP ellipsis) is DERIVED from GenHM chain structure,
not stipulated. All five contexts share the same structural property:
a split chain stranding the M-value on a contentless T. The specific
*reason* for the split is irrelevant to the do-support prediction.

-/

import Linglib.Theories.Syntax.Minimalism.Formal.HeadMovement.VerbMovement
import Linglib.Theories.Syntax.Minimalism.Agree
import Linglib.Theories.Syntax.Minimalism.Formal.Constraints.HMC

namespace Minimalism

-- ============================================================================
-- § 1  M-Values (Morphological Feature Bundles)
-- ============================================================================

/-- An M-value is a bundle of morphological features (tense, agreement)
    shared between terminal nodes via GenHM.

    We reuse `FeatureBundle` since M-values are grammatical features. -/
abbrev MValue := FeatureBundle

-- ============================================================================
-- § 2  Terminal Strength
-- ============================================================================

/-- Terminal strength determines whether a head can host M-value pronunciation.

    Strong terminals can bear inflectional morphology. Weak terminals (Neg, Foc)
    cannot host inflection and act as chain-splitters when they intervene. -/
inductive TerminalStrength where
  | strong
  | weak
  deriving DecidableEq, Repr

/-- A language-specific assignment of strength to syntactic categories. -/
def TerminalStrengthAssignment := Cat → TerminalStrength

/-- Default strength assignment for English.

    - V, T, C: strong (can host inflection)
    - Neg, Foc: weak (cannot host inflection; split GenHM chains)
    - All other categories: strong by default -/
def defaultStrength : TerminalStrengthAssignment
  | .Neg => .weak
  | .Foc => .weak
  | _    => .strong

-- ============================================================================
-- § 3  GenHM Relation
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
-- § 4  Chain-Splitting and Chain Structure
-- ============================================================================

/-- The reason a GenHM chain is split, preventing M-value lowering.

    @cite{arregi-pietraszko-2021} identify three structurally distinct
    configurations that split a chain (§4.1):

    1. **Split-by-Intervention**: A weak terminal (Neg, Foc) between probe
       and goal blocks M-value transmission.
    2. **Split-by-Displacement**: The probe is displaced (e.g., T to C in SAI),
       breaking the structural adjacency needed for lowering.
    3. **Split-by-Deletion**: The goal is absent — deleted at PF (VP ellipsis)
       or anaphoric (tag questions) — so lowering has no target.

    All three produce the same PF effect: the M-value cannot lower and is
    stranded on the probe. -/
inductive ChainSplitReason where
  /-- A weak terminal intervenes between probe and goal (e.g., Neg in
      "Sue does not eat fish", Foc in "Sue DOES eat fish") -/
  | weakIntervener (cat : Cat)
  /-- The probe is displaced away from the goal (e.g., T displaced to C
      in SAI: "Where does Sue eat fish?") -/
  | probeDisplaced
  /-- The goal is absent — deleted (VP ellipsis: "She runs faster than he does")
      or anaphoric (tag questions: "She likes him, doesn't she?") -/
  | goalAbsent
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
  /-- The strength assignment for this language -/
  strength : TerminalStrengthAssignment

/-- Is the chain split? A split chain strands the M-value on the probe. -/
def GenHMChain.isSplit (chain : GenHMChain) : Bool :=
  chain.splitReason.isSome

/-- A chain is well-formed when split-by-intervention involves a genuinely
    weak head in the given strength assignment. -/
def GenHMChain.wellFormed (chain : GenHMChain) : Bool :=
  match chain.splitReason with
  | some (.weakIntervener cat) => chain.strength cat == .weak
  | _ => true

-- ============================================================================
-- § 5  PF Spell-Out Rule
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
-- § 6  Do-Support
-- ============================================================================

/-- The do-support condition.

    Do-support is triggered when:
    1. The M-value is stranded on the probe (chain is split), AND
    2. The probe has no independent lexical content (is a contentless T head)

    This is a PF repair strategy: the grammar inserts *do* to host
    tense features that cannot lower to V and have no other host. -/
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
-- § 7  Key Theorems
-- ============================================================================

/-- **Theorem 1: Lowering when chain is clear.**

    When the chain is not split, the M-value surfaces on the goal
    (= T-lowering / affix hopping). -/
theorem lowering_when_not_split (chain : GenHMChain)
    (h : chain.isSplit = false) :
    spellOutTarget chain = .onGoal := by
  simp [spellOutTarget, h]

/-- **Theorem 2: Raising when chain is split.**

    When the chain is split (by intervention, displacement, or deletion),
    the M-value surfaces on the probe (= "raising" / stranding). -/
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
    the split (intervention, displacement, deletion) is irrelevant.
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
-- § 8  Unification with Existing Infrastructure
-- ============================================================================

/-- Extended head displacement classification.

    Adds GenHM as a third option alongside syntactic movement and
    amalgamation. -/
inductive HeadDisplacementExt where
  | syntactic : Movement → HeadDisplacementExt
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

end Minimalism
