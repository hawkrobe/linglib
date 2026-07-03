import Linglib.Fragments.Turkish.Anaphors
import Linglib.Studies.BarkerPullum1990
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.DeriveFintype

/-!
# Bakay, Akkuş & Dillon (2026)
[bakay-etal-2026]

Hierarchical relations guide memory retrieval in sentence comprehension:
Evidence from a local anaphor in Turkish. *Journal of Memory and Language*
148, 104747.

Three visual-world experiments show that **c-command between NPs within a
single clause** guides antecedent retrieval for the Turkish reciprocal
*birbirleri* from the earliest moments of processing. The design deconfounds
c-command from clause-mateness, case marking, subjecthood, and linear
order/recency: the paper's review (45 experiments from 28 studies) finds no
prior study isolating c-command from cues that are "plausibly construed as
item-level features".

## Formalization

Retrieval predictions are derived from three independently formalized
components:

1. **Fragment** (`Turkish.Anaphors`): *birbirleri* is a reciprocal whose
   plurality requirement generates the item-level number cue.
2. **Theory** (Principle A): reciprocals need a local c-commanding
   clause-mate antecedent; c-command is computed on tree addresses via the
   binary-branching `cCommand` of `BarkerPullum1990`.
3. **Retrieval model**: a cue-based model in the [lewis-vasishth-2005]
   tradition reduced to its ordinal core — activation as a weighted count of
   cue matches. Base-level decay, fan, mismatch penalty, and noise are not
   modeled; only activation *orderings* are derived.

Cue sources follow the paper: **relational** (c-command per se — a
configuration between retrieval site and candidate), **item-level** (features
stored with the item: number, case, and clause-mateness, which the paper
argues is plausibly an item-level feature such as a clause index), and
**positional** (linear order/recency). In a content-addressable memory only
item features are visible, so the relational cue is realized as a dynamically
assigned feature approximating c-command — the strategy the paper attributes
to [kush-2013] (`LOCAL:1/0` rewritten at clause boundaries, in the paper's
summary; the dissertation's own device is a clause index plus a spine-mate
feature).

## Two accounts

The paper's General Discussion distinguishes **differentially weighted cues**
(hierarchical cues weighted above item-level ones — favored by its
limited-interference data) from a **privileged representation** (c-commanding
items temporarily occupy a *region of direct access*, [mcelree-2006];
[oberauer-2002]; structure-gated retrieval in [dillon-etal-2013] — access by
representational position, not cue matching). Both predict the target
advantage: the former via `dominance`, the latter via `privileged` on the
tree configuration. They diverge on early interference from feature-matching
distractors, which needs the unmodeled fan/mismatch machinery; the paper
reports limited, inconsistent number-based interference and leaves the
distinction open.

The paper also leaves open whether the operative relation is c-command or
coargumenthood ([pollard-sag-1994]). Linglib's `Binding` engine states
Principle A over an abstract command relation and would host that divergence,
but its `SimpleClause` (subject/object positions only) cannot yet represent
the possessor and indirect-object configurations used here. The looks-based
findings connect to `Processing.VisualWorld` observables through a monotone
linking hypothesis (more activation → more looks), not yet formalized.
-/

namespace BakayEtAl2026

open BarkerPullum1990 (cCommand Dir Address)

/-! ### Cue-based retrieval: ordinal core -/

/-- Source of a retrieval cue, following the paper's deconfound: `relational`
    information holds between the retrieval site and the candidate (c-command);
    `itemLevel` features are stored with the candidate (number, case, clause
    index); `positional` cues track linear order/recency. -/
inductive CueSource where
  | relational
  | itemLevel
  | positional
  deriving DecidableEq, Fintype, Repr

/-- A retrieval cue: a required feature tagged with its source. -/
structure Cue (F : Type*) where
  source : CueSource
  feature : F
  deriving Repr

variable {F : Type*} [DecidableEq F]

/-- Number of cues from source `s` that a memory item's feature bundle matches. -/
def matchCount (feats : List F) (cues : List (Cue F)) (s : CueSource) : ℕ :=
  cues.countP fun c => decide (c.source = s ∧ c.feature ∈ feats)

/-- Activation of an item as a weighted count of cue matches, the ordinal core
    of [lewis-vasishth-2005]-style spreading activation. -/
def weightedActivation (w : CueSource → ℕ) (feats : List F) (cues : List (Cue F)) : ℕ :=
  ∑ s, w s * matchCount feats cues s

/-- **Dominance.** If `a`'s cue-match vector pointwise dominates `b`'s, strictly
    at some source carrying positive weight, then `a` out-activates `b` under
    every such weighting: Pareto dominance transfers to all positive linear
    readings of the cue weights. -/
theorem dominance {w : CueSource → ℕ} {a b : List F} {cues : List (Cue F)}
    (hle : ∀ s, matchCount b cues s ≤ matchCount a cues s)
    (hlt : ∃ s, 0 < w s ∧ matchCount b cues s < matchCount a cues s) :
    weightedActivation w b cues < weightedActivation w a cues :=
  have ⟨s, hw, hs⟩ := hlt
  Finset.sum_lt_sum (fun i _ => Nat.mul_le_mul_left _ (hle i))
    ⟨s, Finset.mem_univ s, Nat.mul_lt_mul_of_pos_left hs hw⟩

/-! ### Retrieval cues for *birbirleri* -/

/-- Features relevant to antecedent retrieval for *birbirleri*. `cCommanding`
    is the dynamically assigned feature realizing the relational cue. -/
inductive Feature where
  | cCommanding
  | clauseMate
  | plural
  | singular
  | genCase
  | datCase
  deriving DecidableEq, Repr

/-- Item-level number cue, generated exactly when the fragment's anaphor type
    imposes a plurality requirement on its antecedent. -/
def numberCues : List (Cue Feature) :=
  if Turkish.Anaphors.birbirleriAcc.anaphorType.requiresPluralAntecedent then
    [⟨.itemLevel, .plural⟩]
  else []

/-- Retrieval cues generated on encountering *birbirleri*: Principle A supplies
    the relational c-command cue and the clause-mate cue; the fragment's
    plurality requirement supplies the number cue. -/
def birbirleriCues : List (Cue Feature) :=
  ⟨.relational, .cCommanding⟩ :: ⟨.itemLevel, .clauseMate⟩ :: numberCues

/-! ### Experiment 1: subject targets vs. possessor distractors

Target = embedded subject (c-commanding clause-mate, GEN, plural). Distractor =
possessor inside the subject NP (clause-mate, GEN, plural or singular, not
c-commanding). Same clause, same case, and — in the Match condition — same
number: only c-command distinguishes them.

```
        CP_emb
       /      \
   NP_subj     VP_emb
   /    \       /   \
NP_poss  N'  anaph   V
```
-/

def exp1TargetAddr : Address := [Dir.L]
def exp1DistractorAddr : Address := [Dir.L, Dir.L]
def exp1AnaphorAddr : Address := [Dir.R, Dir.L]

/-- The embedded subject c-commands the anaphor. -/
theorem exp1_target_ccommands :
    cCommand exp1TargetAddr exp1AnaphorAddr = true := by decide

/-- The possessor does not c-command the anaphor. -/
theorem exp1_distractor_no_ccommand :
    cCommand exp1DistractorAddr exp1AnaphorAddr = false := by decide

/-- Target subject (*kameramanlar* 'cameramen'). -/
def exp1Target : List Feature := [.cCommanding, .clauseMate, .plural, .genCase]

/-- Possessor distractor, Match condition (plural *yönetmenler* 'directors'). -/
def exp1DistractorMatch : List Feature := [.clauseMate, .plural, .genCase]

/-- Possessor distractor, Mismatch condition (singular *yönetmen* 'director'). -/
def exp1DistractorMismatch : List Feature := [.clauseMate, .singular, .genCase]

/-- In the Match condition only the relational cue distinguishes target from
    distractor: item-level (and positional) match counts tie. -/
theorem exp1_relational_distinguishes :
    matchCount exp1Target birbirleriCues .relational = 1 ∧
    matchCount exp1DistractorMatch birbirleriCues .relational = 0 ∧
    ∀ s, s ≠ .relational →
      matchCount exp1Target birbirleriCues s =
      matchCount exp1DistractorMatch birbirleriCues s := by decide

/-- **Experiment 1 prediction**: the target out-activates the Match distractor —
    the hardest case, where item-level cues do not distinguish them — for any
    weighting with positive relational weight. -/
theorem exp1_target_retrieved (w : CueSource → ℕ) (hw : 0 < w .relational) :
    weightedActivation w exp1DistractorMatch birbirleriCues <
    weightedActivation w exp1Target birbirleriCues :=
  dominance (by decide) ⟨.relational, hw, by decide⟩

/-- In the Mismatch condition the distractor also loses the number cue, so the
    target advantage holds a fortiori. -/
theorem exp1_target_retrieved_mismatch (w : CueSource → ℕ) (hw : 0 < w .relational) :
    weightedActivation w exp1DistractorMismatch birbirleriCues <
    weightedActivation w exp1Target birbirleriCues :=
  dominance (by decide) ⟨.relational, hw, by decide⟩

/-! ### Experiment 2: indirect-object targets vs. adjunct distractors

Target = c-commanding indirect object (DAT). Distractor = NP inside a
postpositional adjunct (DAT, e.g. *göre* 'according to'), not c-commanding.
Extends the advantage to non-subject c-commanders, ruling out a composite
subject-of-the-current-clause item-level cue.

```
    IO condition:              Distractor condition:
        CP_emb                     CP_emb
       /      \                   /      \
   NP_subj     VP             NP_subj     VP
               /  \                       /  \
           NP_IO   V'                 PP_adj   V'
                  /  \                /    \  /  \
              anaph   V          NP_dist  P anaph V
```
-/

def exp2IOAddr : Address := [Dir.R, Dir.L]
def exp2DistractorAddr : Address := [Dir.R, Dir.L, Dir.L]
def exp2AnaphorAddr : Address := [Dir.R, Dir.R, Dir.L]

/-- The indirect object c-commands the anaphor. -/
theorem exp2_io_ccommands :
    cCommand exp2IOAddr exp2AnaphorAddr = true := by decide

/-- The adjunct-internal distractor does not c-command the anaphor. -/
theorem exp2_distractor_no_ccommand :
    cCommand exp2DistractorAddr exp2AnaphorAddr = false := by decide

/-- Indirect-object target: c-commanding clause-mate, plural, DAT. -/
def exp2IO : List Feature := [.cCommanding, .clauseMate, .plural, .datCase]

/-- Adjunct-internal distractor: clause-mate, plural, DAT, not c-commanding. -/
def exp2Distractor : List Feature := [.clauseMate, .plural, .datCase]

/-- **Experiment 2 prediction**: the indirect object out-activates the adjunct
    distractor for any weighting with positive relational weight. Experiment 3
    is the paper's pre-registered, high-powered replication of the Experiment
    1–2 contrasts; it introduces no new configuration. -/
theorem exp2_io_retrieved (w : CueSource → ℕ) (hw : 0 < w .relational) :
    weightedActivation w exp2Distractor birbirleriCues <
    weightedActivation w exp2IO birbirleriCues :=
  dominance (by decide) ⟨.relational, hw, by decide⟩

/-! ### Privileged representation

The representational account grants c-commanding items a temporary association
with a privileged store — access by structural position, not cue matching — so
privilege is defined on the tree configuration, not on `matchCount`. -/

/-- An NP position is privileged at a retrieval site iff it c-commands it: the
    region of direct access holds the current c-commanders. -/
def privileged (np anaphor : Address) : Prop :=
  cCommand np anaphor = true

/-- The Experiment 1 target is in the region of direct access. -/
theorem exp1_target_privileged : privileged exp1TargetAddr exp1AnaphorAddr :=
  exp1_target_ccommands

/-- The Experiment 1 distractor is not, whatever its feature match. -/
theorem exp1_distractor_not_privileged :
    ¬ privileged exp1DistractorAddr exp1AnaphorAddr := by
  simp [privileged, exp1_distractor_no_ccommand]

end BakayEtAl2026
