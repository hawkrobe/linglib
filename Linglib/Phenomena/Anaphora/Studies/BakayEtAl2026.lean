import Linglib.Theories.Processing.CueBasedRetrieval.Basic
import Linglib.Fragments.Turkish.Anaphors
import Linglib.Phenomena.Anaphora.Compare

/-!
# Bakay, Akkuş & Dillon (2026)
@cite{bakay-etal-2026}

Hierarchical relations guide memory retrieval in sentence comprehension:
Evidence from a local anaphor in Turkish. *Journal of Memory and Language*
148, 104747.

## Summary

Three visual-world experiments show that **c-command relations between NPs
within a single clause** guide antecedent retrieval for the Turkish
reciprocal *birbirleri* from the earliest moments of processing — above
and beyond clause-mateness, case marking, subjecthood, and linear
order/recency.

## Design Innovation

Prior studies confounded c-command with clause membership and/or case
marking (Figure 1 Venn diagram: 45 experiments from 28 studies). Bakay
et al. isolate c-command by placing target and distractor in the **same**
clause with the **same** case marking, varying only whether the NP
c-commands the anaphor.

## Formalization

We derive the retrieval predictions from three independently formalized
components:

1. **Fragment** (`Fragments.Turkish.Anaphors`): *birbirleri* is a
   reciprocal requiring a plural antecedent
2. **Theory** (Principle A): reciprocals require a local c-commanding
   clause-mate antecedent
3. **Processing** (`Processing.CueBasedRetrieval`): retrieval cues
   from (1) + (2) feed a weighted activation model; structural cues
   (c-command, clause-mate) predict the target advantage

C-command is verified computationally on tree addresses using the
binary-branching `cCommand` from `Phenomena.Anaphora.Compare`.

-/

set_option autoImplicit false

namespace BakayEtAl2026

open Processing.CueBasedRetrieval
open Phenomena.Anaphora.Compare (cCommand Dir Address dominates)

-- ============================================================================
-- §1: Feature Inventory
-- ============================================================================

/-- Features relevant to antecedent retrieval for *birbirleri*.
    Divided into structural (relational) and item-level (intrinsic). -/
inductive Feature where
  /-- Structural: c-commands the anaphor -/
  | cCommanding
  /-- Structural: in the same local clause as the anaphor -/
  | clauseMate
  /-- Item-level: plural number -/
  | plural
  /-- Item-level: singular number -/
  | singular
  /-- Item-level: genitive case -(n)In -/
  | genCase
  /-- Item-level: dative case -(y)A -/
  | datCase
  deriving DecidableEq, Repr

-- ============================================================================
-- §2: Retrieval Cues from Fragment + Theory
-- ============================================================================

/-! The retrieval cues that processing *birbirleri* generates are
    **derived** from two independent sources:

    1. **Principle A** (syntactic theory): reciprocals must be bound by
       a c-commanding clause-mate → structural cues
    2. **Fragment property** (`requiresPluralAntecedent`): reciprocals
       need a plural antecedent → item-level cue -/

/-- birbirleri is a reciprocal (from the fragment) -/
theorem birbirleri_is_reciprocal :
    Fragments.Turkish.Anaphors.birbirleriAcc.anaphorType =
    .reciprocal := rfl

/-- Reciprocals require plural antecedents (from the fragment) -/
theorem reciprocal_requires_plural :
    Fragments.Turkish.Anaphors.AnaphorType.reciprocal.requiresPluralAntecedent =
    true := rfl

/-- Retrieval cues generated when processing *birbirleri*.

    - Structural cues from Principle A (c-command + clause-mate)
    - Item-level cue from the fragment's plurality requirement -/
def birbirleriCues : List (Cue Feature) :=
  [ ⟨.structural, .cCommanding⟩   -- Principle A: c-command
  , ⟨.structural, .clauseMate⟩    -- Principle A: locality
  , ⟨.itemLevel, .plural⟩         -- Fragment: plural antecedent
  ]

-- ============================================================================
-- §3: Experiment 1 — C-command and Subjecthood
-- ============================================================================

/-! ### Experiment 1: Subject vs. possessor

    Target = embedded subject (c-commanding, clause-mate, GEN, plural).
    Distractor = possessor within the subject NP (clause-mate, GEN, plural,
    but does NOT c-command the anaphor).

    Both NPs are in the same clause, have the same case (GEN), and can be
    plural — the **only** distinguishing feature is c-command.

    Simplified tree for the embedded clause:
    ```
            CP_emb
           /      \
       NP_subj     VP_emb
       /    \       /   \
    NP_poss  N'   anaph   V
    (dist)  (head)
    ```
-/

section Experiment1

/-- Target (embedded subject): address [L] in the embedded clause tree -/
private def exp1Target : Address := [Dir.L]
/-- Distractor (possessor within subject NP): address [L, L] -/
private def exp1Distractor : Address := [Dir.L, Dir.L]
/-- Anaphor *birbirleri* (direct object): address [R, L] -/
private def exp1Anaphor : Address := [Dir.R, Dir.L]

/-- The target subject c-commands the anaphor. -/
theorem exp1_target_ccommands :
    cCommand exp1Target exp1Anaphor = true := by native_decide

/-- The distractor possessor does NOT c-command the anaphor. -/
theorem exp1_distractor_no_ccommand :
    cCommand exp1Distractor exp1Anaphor = false := by native_decide

/-- Target item: embedded subject (cameramen).
    Features: c-commanding, clause-mate, plural, genitive case. -/
def exp1TargetItem : Item Feature :=
  { label := "cameramen (target subject)"
  , features := [.cCommanding, .clauseMate, .plural, .genCase] }

/-- Distractor item: possessor NP (director(s)), Match condition.
    Features: clause-mate, plural, genitive case — but NOT c-commanding.
    Same clause, same case, same number as target. -/
def exp1DistractorMatch : Item Feature :=
  { label := "director(s) (distractor possessor, match)"
  , features := [.clauseMate, .plural, .genCase] }

/-- Distractor item: possessor NP (director), Mismatch condition.
    Singular distractor — does not match the reciprocal's number. -/
def exp1DistractorMismatch : Item Feature :=
  { label := "director (distractor possessor, mismatch)"
  , features := [.clauseMate, .singular, .genCase] }

-- Structural match counts
theorem exp1_target_structural :
    matchCount exp1TargetItem birbirleriCues .structural = 2 := by native_decide

theorem exp1_distractor_structural :
    matchCount exp1DistractorMatch birbirleriCues .structural = 1 := by native_decide

-- Item-level match counts are equal in the Match condition
theorem exp1_itemLevel_equal :
    matchCount exp1TargetItem birbirleriCues .itemLevel =
    matchCount exp1DistractorMatch birbirleriCues .itemLevel := by native_decide

-- No positional cues
theorem exp1_positional_equal :
    matchCount exp1TargetItem birbirleriCues .positional =
    matchCount exp1DistractorMatch birbirleriCues .positional := by native_decide

/-- **Experiment 1 prediction**: target is retrieved over distractor in the
    Match condition — the hardest case, where item-level cues don't
    distinguish target from distractor. Holds for any positive structural
    weight. -/
theorem exp1_target_retrieved (ws wi wp : Nat) (h : 0 < ws) :
    weightedActivation ws wi wp exp1DistractorMatch birbirleriCues <
    weightedActivation ws wi wp exp1TargetItem birbirleriCues :=
  structural_advantage ws wi wp h
    exp1TargetItem exp1DistractorMatch birbirleriCues
    (by native_decide) (by native_decide) (by native_decide)

/-- Target also wins in the Mismatch condition. The distractor is
    singular, so it matches **fewer** cues on both the structural and
    item-level dimensions — a fortiori advantage for the target. -/
theorem exp1_target_retrieved_mismatch (ws wi wp : Nat) (h : 0 < ws) :
    weightedActivation ws wi wp exp1DistractorMismatch birbirleriCues <
    weightedActivation ws wi wp exp1TargetItem birbirleriCues := by
  have h1 : matchCount exp1TargetItem birbirleriCues .structural = 2 := by native_decide
  have h2 : matchCount exp1DistractorMismatch birbirleriCues .structural = 1 := by native_decide
  have h3 : matchCount exp1TargetItem birbirleriCues .itemLevel = 1 := by native_decide
  have h4 : matchCount exp1DistractorMismatch birbirleriCues .itemLevel = 0 := by native_decide
  have h5 : matchCount exp1TargetItem birbirleriCues .positional = 0 := by native_decide
  have h6 : matchCount exp1DistractorMismatch birbirleriCues .positional = 0 := by native_decide
  simp only [weightedActivation, h1, h2, h3, h4, h5, h6]
  omega

end Experiment1

-- ============================================================================
-- §4: Experiment 2 — C-command and Indirect Objects
-- ============================================================================

/-! ### Experiment 2: IO vs. adjunct distractor

    Target = c-commanding indirect object (IO) with DAT case.
    Distractor = non-c-commanding adjunct NP with DAT case.

    The IO is an argument sister to V', so it c-commands the anaphor.
    The distractor is inside a PP adjunct, so it does not.

    IO condition:                   Distractor condition:
    ```
        CP_emb                          CP_emb
       /      \                        /      \
   NP_subj     VP                  NP_subj     VP
               /  \                            /  \
           NP_IO   V'                       PP_adj  V'
                  /  \                     /    \  /  \
              anaph   V               NP_dist  P anaph V
    ```
-/

section Experiment2

private def exp2IO : Address := [Dir.R, Dir.L]
private def exp2AnaphorIO : Address := [Dir.R, Dir.R, Dir.L]
private def exp2Distractor : Address := [Dir.R, Dir.L, Dir.L]
private def exp2AnaphorDist : Address := [Dir.R, Dir.R, Dir.L]

/-- The IO c-commands the anaphor. -/
theorem exp2_io_ccommands :
    cCommand exp2IO exp2AnaphorIO = true := by native_decide

/-- The adjunct distractor does NOT c-command the anaphor. -/
theorem exp2_distractor_no_ccommand :
    cCommand exp2Distractor exp2AnaphorDist = false := by native_decide

def exp2IOItem : Item Feature :=
  { label := "IO (target, c-commanding)"
  , features := [.cCommanding, .clauseMate, .plural, .datCase] }

def exp2DistractorItem : Item Feature :=
  { label := "adjunct NP (distractor, non-c-commanding)"
  , features := [.clauseMate, .plural, .datCase] }

/-- **Experiment 2 prediction**: the IO is retrieved over the adjunct
    distractor, extending the structural advantage to non-subject
    c-commanding positions. -/
theorem exp2_io_retrieved (ws wi wp : Nat) (h : 0 < ws) :
    weightedActivation ws wi wp exp2DistractorItem birbirleriCues <
    weightedActivation ws wi wp exp2IOItem birbirleriCues :=
  structural_advantage ws wi wp h
    exp2IOItem exp2DistractorItem birbirleriCues
    (by native_decide) (by native_decide) (by native_decide)

end Experiment2

-- ============================================================================
-- §5: Cross-Experiment Generalization
-- ============================================================================

/-! ### Key finding

    The structural advantage holds across all experiments:
    - Exp 1: subjects over non-c-commanding possessors (GEN case)
    - Exp 2: IOs over non-c-commanding adjuncts (DAT case)
    - Exp 3: pre-registered replication combining Exp 1–2 conditions

    In all cases, target and distractor share clause, case marking, and
    (in the Match condition) number. The **only** distinguishing feature
    is c-command — and the target is immediately retrieved.

    This is captured by the structural advantage theorem: under *any*
    retrieval model where structural cues carry positive weight, the
    c-commanding item has higher activation. -/

/-- The structural advantage is independent of the specific weight
    assignment: it holds for **any** positive structural weight,
    regardless of item-level and positional weights.

    This formalizes the paper's claim that "hierarchical relational
    information guides antecedent retrieval above and beyond other
    sources of structural information and linear order." -/
theorem structural_advantage_robust :
    ∀ (ws wi wp : Nat), 0 < ws →
    weightedActivation ws wi wp exp1DistractorMatch birbirleriCues <
    weightedActivation ws wi wp exp1TargetItem birbirleriCues :=
  fun ws wi wp h => exp1_target_retrieved ws wi wp h

/-- Both the weighted activation model and the privileged-access model
    predict the target advantage: the target is privileged (matches all
    structural cues), while the distractor is not. -/
theorem exp1_target_privileged :
    isPrivileged exp1TargetItem birbirleriCues = true := by native_decide

theorem exp1_distractor_not_privileged :
    isPrivileged exp1DistractorMatch birbirleriCues = false := by native_decide

/-- Under the privileged-access model, target and distractor have
    different accessibility status: the target is directly accessible,
    the distractor requires search. -/
theorem exp1_privileged_advantage :
    isPrivileged exp1TargetItem birbirleriCues ≠
    isPrivileged exp1DistractorMatch birbirleriCues := by native_decide

end BakayEtAl2026
