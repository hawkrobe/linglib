import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Theories.Syntax.Minimalism.Derivation
import Linglib.Theories.Interfaces.SyntaxSemantics.Linking

/-!
# Larson (1988): On the Double Object Construction
@cite{larson-1988} @cite{barss-lasnik-1986}

*Linguistic Inquiry* 19(3): 335–391.

## Core Claims

1. **VP shells**: Ditransitive verbs project binary-branching VP structures
   with an outer VP shell whose head is initially empty. V raises from
   the inner VP to the outer V position (V Raising).

2. **Dative Shift = PASSIVE**: The double object construction (DOC) is
   derived from the oblique dative by Internal Merge — the same operation
   as Passive — applied within the VP domain rather than the IP domain.
   Both operations are `Step.im` in the `Derivation` infrastructure.

3. **@cite{barss-lasnik-1986} asymmetries**: In the derived DOC, the
   indirect object (NP1) asymmetrically c-commands the direct object
   (NP2), deriving six asymmetries: anaphor binding, quantifier-pronoun
   binding, weak crossover, superiority, *each...the other*, NPI licensing.

4. **Recoverability** (§5.2): Dative Shift requires that *to*'s semantic
   content be recoverable from V's θ-role assignment. V and *to* both
   independently assign θ-roles to the indirect object. When V's role
   **subsumes** *to*'s role (both assign Goal), *to*'s contribution reduces
   to Case marking and can be absorbed by PASSIVE. When V assigns only
   Beneficiary and not Goal, *to*'s contribution is non-redundant — its
   suppression would cause irrecoverable loss of thematic information,
   blocking Dative Shift.

## Simplification

The paper's VP shell has V raising from the inner V position to an
initially empty outer V position (head-to-head movement, §2.1, trees
13–14). This formalization uses `Step.im` (phrasal Internal Merge)
for Dative Shift and Passive, which correctly captures the NP Movement
component. Head movement (V Raising) is not modeled — the
`Derivation` infrastructure does not currently support head movement.
This omission does not affect the c-command predictions, which depend
on the positions of DP arguments, not the position of V.

## Cross-references

- `Minimalism.Derivation`: `Step.im` = Internal Merge
- `Studies/Pylkkanen2008.lean`: Modern Voice/Appl decomposition with
  tree-based c-command verification; bridge theorem proving convergence
- `ColeHermon2008`: English passive derivation
  using the same `Derivation` infrastructure
-/

namespace Larson1988

open Minimalism

-- ============================================================================
-- § 1: Lexical Items
-- ============================================================================

def V_send    := mkLeafPhon .V [.D]    "send"    300
def P_to      := mkLeafPhon .P [.D]   "to"       301
def DP_john   := mkLeafPhon .D []     "John"      302
def DP_mary   := mkLeafPhon .D []     "Mary"      303
def DP_letter := mkLeafPhon .D []     "a letter"  304

def V_kick    := mkLeafPhon .V [.D]   "kicked"    310
def DP_ball   := mkLeafPhon .D []     "the ball"  311

-- ============================================================================
-- § 2: Oblique Dative Derivation
-- ============================================================================

/-! The oblique dative "John sent a letter to Mary" is built bottom-up:

    1. EM-R the PP complement `[PP to Mary]`
    2. EM-L the direct object `a letter` (inner VP-subject)
    3. EM-L the agent `John` (outer VP-subject / Spec-VP)

    The direct object (a letter) c-commands the goal (Mary), but not
    vice versa — Mary is buried inside PP. -/

def obliqueDative : Derivation :=
  { initial := V_send
    steps := [
      .emR (merge P_to DP_mary),   -- [V' send [PP to Mary]]
      .emL DP_letter,               -- [VP a_letter [V' send [PP to Mary]]]
      .emL DP_john                  -- [VP John [VP a_letter [V' send [PP to Mary]]]]
    ] }

-- Oblique dative c-command predictions

theorem oblique_do_ccommands_goal :
    cCommandsIn obliqueDative.final DP_letter DP_mary := by native_decide

theorem oblique_goal_not_ccommands_do :
    ¬ cCommandsIn obliqueDative.final DP_mary DP_letter := by native_decide

theorem oblique_agent_ccommands_both :
    cCommandsIn obliqueDative.final DP_john DP_letter ∧
    cCommandsIn obliqueDative.final DP_john DP_mary := by
  constructor <;> native_decide

-- ============================================================================
-- § 3: DOC Derivation — Dative Shift as Step.im
-- ============================================================================

/-! The DOC "John sent Mary a letter" extends the oblique dative with
one additional step: **Internal Merge of the indirect object** (`Step.im`).

This is Larson's central insight: Dative Shift = PASSIVE within VP.
The `Step.im` constructor is the same one used for standard Passive
(cf. `ColeHermon2008.lean`'s `englishPassive` derivation). The only
difference is *which* argument moves and *when* in the derivation.

Derivation steps:
1. EM-R the PP complement `[PP to Mary]`
2. EM-L the direct object `a letter`
3. **IM the IO `Mary`** — Dative Shift. Mary is extracted from inside
   `[PP to Mary]`, leaving a trace, and re-merged at the left edge.
   This promotes Mary above the direct object.
4. EM-L the agent `John` -/

def docDativeShift : Derivation :=
  { initial := V_send
    steps := [
      .emR (merge P_to DP_mary),   -- [V' send [PP to Mary]]
      .emL DP_letter,               -- [VP a_letter [V' send [PP to Mary]]]
      .im DP_mary 0,               -- DATIVE SHIFT: Mary moves to Spec
      .emL DP_john                  -- [VP John [VP Mary_i [VP a_letter ...]]]
    ] }

-- DOC c-command predictions: the asymmetries are REVERSED

/-- In the DOC, the indirect object (Mary) c-commands the direct object
    (a letter). Mary has been promoted above the DO by Internal Merge.
    This derives all six @cite{barss-lasnik-1986} asymmetries (§3.2):
    - Anaphor binding: "I showed Mary herself" vs *"I showed herself Mary"
    - Quantifier binding: "I gave every worker his paycheck"
    - Weak crossover, superiority, *each...the other*, NPI licensing -/
theorem doc_io_ccommands_do :
    cCommandsIn docDativeShift.final DP_mary DP_letter := by native_decide

/-- The direct object does NOT c-command the indirect object in the DOC. -/
theorem doc_do_not_ccommands_io :
    ¬ cCommandsIn docDativeShift.final DP_letter DP_mary := by native_decide

theorem doc_agent_ccommands_both :
    cCommandsIn docDativeShift.final DP_john DP_mary ∧
    cCommandsIn docDativeShift.final DP_john DP_letter := by
  constructor <;> native_decide

-- ============================================================================
-- § 4: PASSIVE — Same Step.im, Different Domain
-- ============================================================================

/-! Standard Passive ("The ball was kicked by John") is also `Step.im`:
the object moves to subject position. By using the same `Step.im`
constructor, the type system enforces Larson's thesis that Passive
and Dative Shift share the same structural operation. -/

def standardPassive : Derivation :=
  { initial := V_kick
    steps := [
      .emR DP_ball,                 -- [V' kicked [DP the ball]]
      .emL DP_john,                 -- [VP John [V' kicked [DP the ball]]]
      .im DP_ball 0                 -- PASSIVE: ball promoted to Spec
    ] }

-- Passive c-command: promoted object c-commands demoted subject

theorem passive_object_ccommands_subject :
    cCommandsIn standardPassive.final DP_ball DP_john := by native_decide

theorem passive_subject_not_ccommands_object :
    ¬ cCommandsIn standardPassive.final DP_john DP_ball := by native_decide

-- ============================================================================
-- § 5: Structural Parallel — Passive and Dative Shift
-- ============================================================================

/-! Both Passive and Dative Shift use `Step.im`. We can extract the
movement steps and verify they share the same structure. -/

/-- Dative Shift involves exactly one Internal Merge (of the IO). -/
theorem dativeShift_has_one_im :
    docDativeShift.movedItems = [DP_mary] := by native_decide

/-- Standard Passive involves exactly one Internal Merge (of the object). -/
theorem passive_has_one_im :
    standardPassive.movedItems = [DP_ball] := by native_decide

/-- Both operations promote an argument by Internal Merge, reversing
    the c-command relation between the two internal arguments.

    Oblique dative:  DO > IO  (letter c-commands Mary)
    DOC:             IO > DO  (Mary c-commands letter)  [reversed by Step.im]
    Active:          Subj > Obj (John c-commands ball)
    Passive:         Obj > Subj (ball c-commands John)  [reversed by Step.im] -/
theorem passive_dativeShift_parallel :
    -- Both reverse c-command via the same Step.im mechanism
    cCommandsIn obliqueDative.final DP_letter DP_mary ∧
    cCommandsIn docDativeShift.final DP_mary DP_letter ∧
    cCommandsIn standardPassive.final DP_ball DP_john := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 6: Barss & Lasnik (1986) Asymmetries — Structured Data
-- ============================================================================

/-! @cite{barss-lasnik-1986} identify six asymmetries in DOC sentences
of the form V–NP1–NP2, all pointing to the same conclusion: NP1
c-commands NP2 but not vice versa. These are the empirical facts
that Larson's Dative Shift analysis derives structurally. -/

/-- A single Barss & Lasnik asymmetry datum. -/
structure BLAsymmetry where
  name : String
  grammatical : String
  ungrammatical : String
  deriving Repr, BEq

def bl_anaphor : BLAsymmetry :=
  { name := "anaphor binding"
    grammatical := "I showed Mary herself."
    ungrammatical := "*I showed herself Mary." }

def bl_quantifier : BLAsymmetry :=
  { name := "quantifier-pronoun binding"
    grammatical := "I gave every worker his paycheck."
    ungrammatical := "*I gave its owner every paycheck." }

def bl_wco : BLAsymmetry :=
  { name := "weak crossover"
    grammatical := "Which man did you send his paycheck?"
    ungrammatical := "*Whose pay did you send his mother?" }

def bl_superiority : BLAsymmetry :=
  { name := "superiority"
    grammatical := "Who did you give which paycheck?"
    ungrammatical := "*Which paycheck did you give who?" }

def bl_each_other : BLAsymmetry :=
  { name := "each...the other"
    grammatical := "I showed each man the other's socks."
    ungrammatical := "*I showed the other's friend each man." }

def bl_npi : BLAsymmetry :=
  { name := "NPI licensing"
    grammatical := "I showed no one anything."
    ungrammatical := "*I showed anyone nothing." }

def blAsymmetries : List BLAsymmetry :=
  [bl_anaphor, bl_quantifier, bl_wco, bl_superiority, bl_each_other, bl_npi]

/-- There are exactly six @cite{barss-lasnik-1986} asymmetries. -/
theorem bl_six_asymmetries : blAsymmetries.length = 6 := rfl

/-- All six asymmetries are derived from a single structural fact:
    in the DOC, NP1 (IO) asymmetrically c-commands NP2 (DO). -/
theorem bl_asymmetries_from_ccommand :
    cCommandsIn docDativeShift.final DP_mary DP_letter ∧
    ¬ cCommandsIn docDativeShift.final DP_letter DP_mary := by
  constructor <;> native_decide

-- ============================================================================
-- § 7: Recoverability Condition (§5 of the paper)
-- ============================================================================

/-! Dative Shift is possible only when *to*'s semantic content is
recoverable from V's θ-role assignment (§5.2).

Both V and *to* independently assign θ-roles to the indirect object:
- *to* always assigns **Goal** (goal of motion along some path)
- V assigns its own role to the IO: **Beneficiary + Goal** for *give/send*,
  but only **Beneficiary** for *donate/distribute/contribute*

When V's role subsumes *to*'s (V assigns Goal among its roles), *to*'s
contribution is redundant — it reduces to Case marking and can be
absorbed by PASSIVE. When V does NOT assign Goal (only Beneficiary),
*to*'s Goal contribution is non-redundant — its suppression causes
irrecoverable loss, blocking Dative Shift. -/

/-- A dative verb entry with its θ-role assignment to the IO.

    `ioRoles` lists the θ-roles V assigns to its indirect object.
    Recoverability is DERIVED: Dative Shift is possible iff V's roles
    include `.goal`, making *to*'s contribution redundant. -/
structure DativeVerbEntry where
  verb : String
  /-- θ-roles V independently assigns to the indirect object -/
  ioRoles : List ThetaRole
  deriving Repr, BEq

/-- *to* always assigns Goal — this is its semantic contribution. -/
def toRole : ThetaRole := .goal

/-- Recoverability: V's IO roles subsume *to*'s contribution iff
    V independently assigns a Goal role. -/
def recoverable (e : DativeVerbEntry) : Bool :=
  e.ioRoles.contains toRole

/-- *give*: V assigns Beneficiary + Goal → subsumes *to* → DS ✓ -/
def give_entry : DativeVerbEntry :=
  { verb := "give", ioRoles := [.goal] }

/-- *send*: V assigns Goal → subsumes *to* → DS ✓ -/
def send_entry : DativeVerbEntry :=
  { verb := "send", ioRoles := [.goal] }

/-- *promise*: V assigns Goal → subsumes *to* → DS ✓ -/
def promise_entry : DativeVerbEntry :=
  { verb := "promise", ioRoles := [.goal] }

/-- *donate*: V assigns only Beneficiary → does NOT subsume *to* → DS ✗
    Example (§5.2): "I donated money to charity." / *"I donated charity money." -/
def donate_entry : DativeVerbEntry :=
  { verb := "donate", ioRoles := [] }

/-- *distribute*: V assigns only Beneficiary → DS ✗
    Example (§5.2): "I distributed apples to the children." /
    *"I distributed the children apples." -/
def distribute_entry : DativeVerbEntry :=
  { verb := "distribute", ioRoles := [] }

/-- *contribute*: V assigns only Beneficiary → DS ✗
    Example (§5.2): "I contributed my time to the auction." /
    *"I contributed the auction my time." -/
def contribute_entry : DativeVerbEntry :=
  { verb := "contribute", ioRoles := [] }

def allDativeVerbs : List DativeVerbEntry :=
  [give_entry, send_entry, promise_entry, donate_entry, distribute_entry, contribute_entry]

/-- Recoverability correctly predicts Dative Shift for all six verbs:
    give/send/promise alternate (V assigns Goal); donate/distribute/contribute
    do not (V assigns only Beneficiary, *to*'s Goal is non-redundant). -/
theorem recoverability_predicts_dative_shift :
    (allDativeVerbs.filter recoverable).map (·.verb) = ["give", "send", "promise"] ∧
    (allDativeVerbs.filter (! recoverable ·)).map (·.verb) = ["donate", "distribute", "contribute"] := by
  constructor <;> native_decide

-- ============================================================================
-- § 8: Scope Freezing in the DOC
-- ============================================================================

/-! In the derived DOC, the IO (NP1) asymmetrically c-commands the DO
(NP2). This structural asymmetry predicts scope freezing: QR of DO
over IO would violate locality/superiority, so only surface scope is
available. The data are recorded in `Phenomena.Quantification.Data`
(examples `dative_double_object` and `dative_variant`). -/

/-- Scope freezing follows from asymmetric c-command: in the DOC,
    IO c-commands DO but not vice versa. QR of the lower quantifier
    (DO) over the higher one (IO) is blocked, yielding surface-only scope.

    This connects to `Phenomena.Quantification.Data.dative_double_object`
    which records "Someone gave every student a book" as `surfaceOnly`. -/
theorem doc_scope_freezing_structural_basis :
    -- IO > DO (IO c-commands DO): surface scope available
    cCommandsIn docDativeShift.final DP_mary DP_letter ∧
    -- DO ≯ IO (DO does not c-command IO): inverse scope blocked
    ¬ cCommandsIn docDativeShift.final DP_letter DP_mary := by
  constructor <;> native_decide

-- ============================================================================
-- § 9: Indirect Passive (§4 of the paper)
-- ============================================================================

/-! @cite{larson-1988} §4: "Mary was sent a letter" is an **indirect
passive** — the IO is promoted directly to subject. Under the standard
two-step analysis, this requires Dative Shift (oblique → DOC) followed
by Passive (DOC → indirect passive). Larson proposes an alternative
"3→1 advancement" where PASSIVE applies directly to the oblique
dative, promoting the IO without an intermediate DOC stage.

Both routes use the same operations (NP Movement = `Step.im`). We
formalize the two-step route, which produces the same surface
c-command relations. -/

def V_sent     := mkLeafPhon .V [.D]  "was-sent"   320
def DP_mary2   := mkLeafPhon .D []    "Mary"        321
def DP_letter2 := mkLeafPhon .D []    "a letter"    322
def P_to2      := mkLeafPhon .P [.D]  "to"          323

/-- Indirect passive: "Mary was sent a letter"

    Two-step derivation:
    1. Build oblique dative base: [VP a_letter [V' send [PP to Mary]]]
    2. Dative Shift (IM Mary): Mary promotes to inner Spec
    3. Passive (IM Mary again): Mary promotes to outer Spec (subject) -/
def indirectPassive : Derivation :=
  { initial := V_sent
    steps := [
      .emR (merge P_to2 DP_mary2),   -- [V' sent [PP to Mary]]
      .emL DP_letter2,                -- [VP a_letter [V' sent [PP to Mary]]]
      .im DP_mary2 0,                -- DATIVE SHIFT: Mary to inner Spec
      .im DP_mary2 1                 -- PASSIVE: Mary to outer Spec (subject)
    ] }

/-- In the indirect passive, the promoted IO (Mary) c-commands the
    stranded DO (a letter). -/
theorem indirect_passive_io_ccommands_do :
    cCommandsIn indirectPassive.final DP_mary2 DP_letter2 := by native_decide

/-- The indirect passive uses two Internal Merge steps:
    Dative Shift + Passive — both are `Step.im`. -/
theorem indirect_passive_two_im :
    indirectPassive.movedItems.length = 2 := by native_decide

end Larson1988
