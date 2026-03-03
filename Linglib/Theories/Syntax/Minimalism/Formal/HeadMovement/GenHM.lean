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
   - When an intervening head *splits* the chain, the M-value is stranded
     on the probe (T) — looks like "raising".
3. **Do-support**: When the M-value is stranded on a probe (T) that has no
   independent lexical content, a dummy verb *do* is inserted at PF.

## Key Result

The parallelism of do-support across five contexts (negation, SAI, verum
focus, tag questions, VP ellipsis) is DERIVED from GenHM chain structure,
not stipulated. All five contexts share the same structural property:
a split chain stranding the M-value on a contentless T.

-/

import Linglib.Theories.Syntax.Minimalism.Formal.HeadMovement.VerbMovement
import Linglib.Theories.Syntax.Minimalism.Core.Agree
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
  deriving DecidableEq, Repr, BEq

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
  /-- The containing tree -/
  root : SyntacticObject
  /-- Structural condition: probe c-commands goal -/
  probe_commands_goal : cCommandsIn root probe goal
  /-- The goal bears valued M-features -/
  goal_has_mvalue : hasValuedFeature mValue (.tense true) = true
  /-- The probe bears unvalued M-features -/
  probe_needs_mvalue : hasUnvaluedFeature mValue (.tense true) = true

/-- GenHM is an instance of Agree: it relates a probe with unvalued features
    to a goal with valued features under c-command. -/
def genHM_to_agree (g : GenHMRelation) : AgreeRelation :=
  { probe := g.probe
    goal := g.goal
    feature := .tense true
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
-- § 4  Intervention and Chain Structure
-- ============================================================================

/-- A GenHM chain: the ordered sequence of terminals between probe and goal.

    The chain may be split by intervening heads. The key property of each
    intervener is its strength: weak interveners (Neg, Foc) split the chain,
    preventing the M-value from reaching the goal. -/
structure GenHMChain where
  /-- The higher terminal (probe) -/
  probe : SyntacticObject
  /-- The lower terminal (goal) -/
  goal : SyntacticObject
  /-- Intervening terminals between probe and goal -/
  interveners : List SyntacticObject
  /-- Category of the probe (for strength lookup) -/
  probeCat : Cat
  /-- Category of the goal (for strength lookup) -/
  goalCat : Cat
  /-- Categories of interveners (parallel to `interveners` list) -/
  intervenerCats : List Cat
  /-- Length consistency -/
  cats_match : interveners.length = intervenerCats.length
  /-- The strength assignment for this language -/
  strength : TerminalStrengthAssignment

/-- Does the chain have a weak intervener?

    A weak intervener (e.g., Neg, Foc) splits the GenHM chain,
    stranding the M-value on the probe. -/
def GenHMChain.hasWeakIntervener (chain : GenHMChain) : Bool :=
  chain.intervenerCats.any (chain.strength · == .weak)

/-- Are all interveners weak? -/
def GenHMChain.allIntervenersWeak (chain : GenHMChain) : Bool :=
  chain.intervenerCats.all (chain.strength · == .weak)

/-- Does the chain have no interveners? -/
def GenHMChain.noInterveners (chain : GenHMChain) : Bool :=
  chain.interveners.isEmpty

-- ============================================================================
-- § 5  PF Spell-Out Rule
-- ============================================================================

/-- Where the M-value is pronounced at PF.

    - `.onGoal`: M-value lowers to the goal (= affix hopping / T-lowering)
    - `.onProbe`: M-value stays on the probe (= "raising" / stranding) -/
inductive SpellOutTarget where
  | onGoal
  | onProbe
  deriving DecidableEq, Repr, BEq

/-- Determine where the M-value is spelled out.

    The M-value surfaces on the goal (lower terminal) unless the chain
    is split by a weak intervener, in which case it is stranded on the
    probe (higher terminal). -/
def spellOutTarget (chain : GenHMChain) : SpellOutTarget :=
  if chain.hasWeakIntervener then .onProbe else .onGoal

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

/-- **Theorem 1: Lowering when no intervener.**

    When no weak terminal intervenes between T and V, the M-value surfaces
    on V (= T-lowering / affix hopping). -/
theorem lowering_when_no_intervener (chain : GenHMChain)
    (h : chain.hasWeakIntervener = false) :
    spellOutTarget chain = .onGoal := by
  simp [spellOutTarget, h]

/-- **Theorem 2: Raising when weak intervener.**

    When a weak terminal (Neg, Foc) intervenes, the M-value surfaces on T
    (= raising / stranding). -/
theorem raising_when_weak_intervener (chain : GenHMChain)
    (h : chain.hasWeakIntervener = true) :
    spellOutTarget chain = .onProbe := by
  simp [spellOutTarget, h]

/-- **Theorem 3: Do-support iff blocked and empty.**

    Do-support is triggered iff (a) a weak intervener blocks lowering AND
    (b) the probe has no lexical content. -/
theorem doSupport_iff_blocked_and_empty (chain : GenHMChain) (probeContent : Bool) :
    needsDoSupportGenHM chain probeContent = true ↔
    (chain.hasWeakIntervener = true ∧ probeContent = false) := by
  constructor
  · intro h
    have ⟨hTarget, hContent⟩ := doSupport_is_lastResort chain probeContent h
    refine ⟨?_, hContent⟩
    unfold spellOutTarget at hTarget
    split at hTarget
    · assumption
    · exact absurd hTarget (by simp)
  · intro ⟨hWeak, hContent⟩
    simp [needsDoSupportGenHM, spellOutTarget, hWeak, hContent]

/-- **Theorem 4: Do-support is uniform across contexts.**

    For ANY GenHM chain with the same structural properties (same intervener
    configuration, same probe content), do-support is triggered or not
    uniformly. The parallelism theorem. -/
theorem doSupport_uniform_across_contexts
    (chain₁ chain₂ : GenHMChain) (content₁ content₂ : Bool)
    (h_same_split : chain₁.hasWeakIntervener = chain₂.hasWeakIntervener)
    (h_same_content : content₁ = content₂) :
    needsDoSupportGenHM chain₁ content₁ = needsDoSupportGenHM chain₂ content₂ := by
  simp only [needsDoSupportGenHM, spellOutTarget, h_same_split, h_same_content]

/-- **Theorem 5: Auxiliaries don't need do-support.**

    When the probe IS the auxiliary (T = Aux with lexical content), do-support
    is never needed, even with interveners. -/
theorem auxiliaries_dont_need_doSupport (chain : GenHMChain) :
    needsDoSupportGenHM chain true = false := by
  simp [needsDoSupportGenHM]
  split <;> rfl

/-- **Corollary: Lexical verbs need do-support when chain is split.** -/
theorem lexical_verb_needs_doSupport_when_split (chain : GenHMChain)
    (h : chain.hasWeakIntervener = true) :
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
    (h : chain.hasWeakIntervener = false) :
    genHM_to_vMovementParam chain = .raises := by
  simp [genHM_to_vMovementParam, spellOutTarget, h]

/-- When the chain is split, the surface pattern is V-in-situ. -/
theorem genHM_split_chain_is_inSitu (chain : GenHMChain)
    (h : chain.hasWeakIntervener = true) :
    genHM_to_vMovementParam chain = .inSitu := by
  simp [genHM_to_vMovementParam, spellOutTarget, h]

end Minimalism
