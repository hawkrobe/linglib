import Linglib.Studies.GoldbergJackendoff2004
import Linglib.Syntax.Minimalist.Basic
import Linglib.Syntax.DependencyGrammar.Basic

/-!
# Cross-Theory Comparison: Resultative Argument Licensing

Three syntactic theories predict the same argument frames for resultatives
but differ on *how* arguments are licensed: Minimalism via the Theta
Criterion, CxG via Full Argument Realization plus Semantic Coherence
(the substrate predicates `ConstructionGrammar.Resultatives.farSatisfied`
and `rolesCoherent`), and DG via valency saturation.

All three converge on canonical resultatives ("She hammered the metal
flat") and diverge on fake reflexives ("She laughed herself silly"),
where CxG licenses the extra argument constructionally while the verb's
theta grid cannot.
-/

namespace TheoryComparison

open ConstructionGrammar
open ConstructionGrammar.Resultatives
open GoldbergJackendoff2004
open DepGrammar

/-! ## §1. Three theories of argument licensing -/

/-- A predicted argument frame: ordered list of theta roles (the canonical
`ThetaRole` vocabulary from the linking interface). -/
abbrev ArgFrame := List ThetaRole

/-! ### Minimalist argument licensing

In Minimalism, theta roles drive External Merge. Each theta role must be
assigned to exactly one argument (Theta Criterion). -/

/-- What triggers Merge? In Minimalism, uninterpretable features drive
    operations. Used here as a descriptive enum for the comparison
    study; not part of the M-C-B substrate (M-C-B's Merge action is
    feature-driven via the coproduct, not via discrete triggers). -/
inductive MergeTrigger where
  | selection : Minimalist.Cat → MergeTrigger  -- selectional [uF]
  | epp : MergeTrigger                          -- EPP triggers specifier
  | theta : MergeTrigger                        -- theta-role assignment
  deriving Repr, DecidableEq

/-- Minimalist licensing: each theta role in the frame triggers External Merge
    via `MergeTrigger.theta`. -/
def minimalistFrame (roles : ArgFrame) : List MergeTrigger :=
  roles.map (λ _ => .theta)

/-- The theta criterion requires 1-to-1 mapping between roles and arguments.
    This is satisfied iff no duplicate roles appear. -/
def thetaCriterionSatisfied (frame : ArgFrame) : Bool :=
  frame.dedup.length == frame.length

/-! ### CxG argument licensing

In CxG, both the verb and the construction contribute argument roles;
shared roles fuse. The substrate types this directly:
`Resultatives.ArgSource` records each surface argument's source(s), FAR
(`farSatisfied`) demands every argument have one, and Semantic Coherence
(`rolesCoherent`/`semanticCoherenceSatisfied`) constrains fusion. -/

/-- The roles a frame's verb contributes. -/
def verbRoles (args : List ArgSource) : List ThetaRole :=
  (args.filter (·.fromVerb)).map (·.role)

/-! ### DG argument licensing

In DG, the verb has a valency frame specifying required dependents.
The resultative construction adds additional dependent slots. -/

/-- DG frame: verb's base valency + construction-added deps. -/
structure DGFrame where
  /-- Verb's inherent argument requirements -/
  verbArgs : List ArgSlot
  /-- Arguments added by the resultative construction -/
  constructionArgs : List ArgSlot
  deriving Repr

/-- The combined DG argument frame. -/
def DGFrame.allArgs (f : DGFrame) : List ArgSlot :=
  f.verbArgs ++ f.constructionArgs

/-! ## §2. Convergence on canonical resultatives

All three theories predict the same argument frame for "She hammered the
metal flat": agent, patient, and the result (mapped to `goal`, the
substrate's resultGoal). -/

/-- Minimalist prediction for "hammer the metal flat". -/
def minimalist_hammer_flat : ArgFrame :=
  [.agent, .patient, .goal]

/-- CxG prediction for "hammer the metal flat": *hammer* contributes agent
and patient (both fused with the construction's); the construction alone
contributes the result. -/
def cxg_hammer_flat : List ArgSource :=
  [ ⟨.agent, true, true⟩
  , ⟨.patient, true, true⟩
  , ⟨.goal, false, true⟩ ]

/-- DG prediction for "hammer the metal flat".

    Verb "hammer" has valency {subj, obj}.
    Resultative construction adds {result-complement}. -/
def dg_hammer_flat : DGFrame :=
  { verbArgs :=
      [ { depType := .nsubj, dir := .left, required := true }
      , { depType := .obj, dir := .right, required := true } ]
  , constructionArgs :=
      [ { depType := .amod, dir := .right, required := true
        , cat := some UD.UPOS.ADJ } ] }

/-- All three theories predict the same number of surface arguments
    for "hammer flat": 3 (agent + patient + result). -/
theorem convergence_hammer_flat_arg_count :
    minimalist_hammer_flat.length = 3 ∧
    cxg_hammer_flat.length = 3 ∧
    dg_hammer_flat.allArgs.length = 3 := ⟨rfl, rfl, rfl⟩

/-- The theta criterion is satisfied for the canonical resultative. -/
theorem theta_criterion_canonical :
    thetaCriterionSatisfied minimalist_hammer_flat = true := by decide

/-- FAR is satisfied for the canonical CxG resultative: every surface
argument has a source. -/
theorem far_canonical : farSatisfied cxg_hammer_flat = true := by decide

/-- The canonical fusions are coherent: agent with agent, patient with
patient (Semantic Coherence, Principle 44). -/
theorem coherence_canonical :
    semanticCoherenceSatisfied [(.agent, .agent), (.patient, .patient)] = true := by
  decide

/-- FAR is a real filter: an argument licensed by neither the verb nor
the construction fails it. -/
theorem far_rejects_unsourced :
    farSatisfied [⟨.agent, true, true⟩, ⟨.patient, false, false⟩] = false := rfl

/-! ## §3. Divergence on fake reflexives

"She laughed herself silly" reveals the key difference between the theories.

- **CxG**: *laugh* contributes only the agent; the construction contributes
  the patient ("herself") and the result.
- **Minimalism**: *laugh* is intransitive (assigns only one theta role);
  "herself" needs a theta role the verb cannot provide.
- **DG**: *laugh* has valency {subj}; the construction adds the rest. -/

/-- CxG analysis of "She laughed herself silly": only the agent is fused;
the patient and result come from the construction alone. -/
def cxg_laugh_silly : List ArgSource :=
  [ ⟨.agent, true, true⟩
  , ⟨.patient, false, true⟩
  , ⟨.goal, false, true⟩ ]

/-- Minimalist analysis: *laugh* assigns only one theta role. -/
def minimalist_laugh_silly_verb_roles : ArgFrame := [.agent]

/-- The surface frame the Minimalist analysis must somehow license. -/
def minimalist_laugh_silly_full : ArgFrame := [.agent, .patient, .goal]

/-- DG analysis of "She laughed herself silly".

    "laugh" has valency {subj} only.
    The resultative construction adds {obj, result-complement}. -/
def dg_laugh_silly : DGFrame :=
  { verbArgs :=
      [ { depType := .nsubj, dir := .left, required := true } ]
  , constructionArgs :=
      [ { depType := .obj, dir := .right, required := true }
      , { depType := .amod, dir := .right, required := true
        , cat := some UD.UPOS.ADJ } ] }

/-- CxG: the verb contributes fewer roles than the surface frame; the
construction licenses the extra arguments. -/
theorem cxg_construction_adds_patient :
    (verbRoles cxg_laugh_silly).length < cxg_laugh_silly.length := by decide

/-- The fake reflexive satisfies FAR: every argument is sourced — the
agent by fusion, the patient and result by the construction alone. -/
theorem cxg_fake_reflexive_far :
    farSatisfied cxg_laugh_silly = true := by decide

/-- The Minimalist verb alone cannot license the reflexive:
    the verb has only 1 theta role but the surface has 3 arguments.

    This is the core divergence: CxG's FAR allows the construction to
    add roles, while the theta criterion requires the verb to provide them. -/
theorem minimalist_verb_deficit :
    minimalist_laugh_silly_verb_roles.length <
    minimalist_laugh_silly_full.length := by decide

/-- DG: the construction adds 2 arguments to the verb's base valency of 1. -/
theorem dg_construction_adds_args :
    dg_laugh_silly.verbArgs.length = 1 ∧
    dg_laugh_silly.constructionArgs.length = 2 := ⟨rfl, rfl⟩

/-- Despite the different licensing mechanisms, all three theories predict
    the same surface argument count for the fake reflexive: 3. -/
theorem convergence_fake_reflexive_count :
    minimalist_laugh_silly_full.length = 3 ∧
    cxg_laugh_silly.length = 3 ∧
    dg_laugh_silly.allArgs.length = 3 := ⟨rfl, rfl, rfl⟩

/-! ## §4. Construction licensing generalizes the theta grid

CxG's system is strictly more permissive than verb-driven theta
assignment: there are frames that satisfy FAR in which the verb's own
roles undergenerate the surface arguments — exactly the fake reflexives.
The theta criterion alone cannot license these without extra machinery. -/

/-- The fake reflexive is FAR-licensed while the verb undergenerates:
construction-licensed roles are doing real work. -/
theorem construction_licensing_generalizes_theta :
    farSatisfied cxg_laugh_silly = true ∧
    (verbRoles cxg_laugh_silly).length < cxg_laugh_silly.length := by
  exact ⟨by decide, by decide⟩

end TheoryComparison
