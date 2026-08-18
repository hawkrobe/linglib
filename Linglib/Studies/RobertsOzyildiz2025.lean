import Linglib.Studies.Glass2025
import Linglib.Semantics.Causation.SEM.Bool
import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Roberts & Özyıldız 2025: The causal derivation of the contrafactive gap

[roberts-ozyildiz-2025] derive the contrafactive gap — the absence of
verbs presupposing ¬p while asserting belief in p — from the
**Predicate Lexicalization Constraint (PLC)**: presupposed content must
be causally upstream of at-issue content. A verbal predicate with
at-issue content α can carry presupposition π only if a causal chain
runs from π to α in the normative belief-formation model
p → indic(p) → acq(a)(iₚ) → B(a)(p): the fact generates indicators,
acquaintance with which causes belief.

Factives satisfy the PLC (`factive_satisfies_plc`: the chain from p to
B(a)(p) exists); strong contrafactives violate it
(`strong_contrafactive_violates_plc`: ¬p generates indicators for ¬p,
not for p, so no chain reaches B(a)(p)) — the gap follows
(`contrafactive_gap`), and structurally so
(`contrafactive_gap_is_structural`: presupposing ¬p while asserting
B(a)(¬p) is fine). Weak contrafactives like Mandarin yǐwéi escape:
their falsity inference is a postsupposition about the output context
([glass-2025]), not a presupposition inside the same eventuality, so
the PLC does not apply. `presupClassIsValid_eq_via_plc` derives
[glass-2025]'s attestation table from the causal account.

The belief-formation model is a deterministic `BoolSEM` over the
`Causation` substrate; the PLC check runs `developDetOn` over a
topologically ordered vertex list so proofs reduce structurally.
-/

namespace RobertsOzyildiz2025

open Doxastic Glass2025
open Semantics.Presupposition
open Causation Causation.Mechanism Causation.SEM

/-! ### The belief-formation causal model -/

/-- Variables of belief formation: the fact, its negation, their
    indicators, acquaintance with the indicators, and the resulting
    beliefs. An enum so the `developDet` fixpoint reduces
    structurally. -/
inductive BeliefVar
  | p | not_p
  | indic_p | indic_not_p
  | acq_a_ip | acq_a_inp
  | B_a_p | B_a_not_p
  deriving DecidableEq, Fintype, Repr

/-- The causal graph: the chain `p → indic(p) → acq(a)(iₚ) → B(a)(p)`
    and its parallel ¬p chain. -/
def beliefGraph : CausalGraph BeliefVar :=
  ⟨fun
    | .p => ∅
    | .not_p => ∅
    | .indic_p => {.p}
    | .indic_not_p => {.not_p}
    | .acq_a_ip => {.indic_p}
    | .acq_a_inp => {.indic_not_p}
    | .B_a_p => {.acq_a_ip}
    | .B_a_not_p => {.acq_a_inp}⟩

/-- The belief-formation `BoolSEM`: roots default to `false` (the input
    valuation overrides); each derived vertex copies its sole parent. -/
noncomputable def beliefSEM : BoolSEM BeliefVar :=
  { graph := beliefGraph
    mech := fun v => match v with
      | .p => const (G := beliefGraph) false
      | .not_p => const (G := beliefGraph) false
      | .indic_p => deterministic (fun ρ => ρ ⟨.p, by simp [beliefGraph]⟩)
      | .indic_not_p => deterministic (fun ρ => ρ ⟨.not_p, by simp [beliefGraph]⟩)
      | .acq_a_ip => deterministic (fun ρ => ρ ⟨.indic_p, by simp [beliefGraph]⟩)
      | .acq_a_inp => deterministic (fun ρ => ρ ⟨.indic_not_p, by simp [beliefGraph]⟩)
      | .B_a_p => deterministic (fun ρ => ρ ⟨.acq_a_ip, by simp [beliefGraph]⟩)
      | .B_a_not_p => deterministic (fun ρ => ρ ⟨.acq_a_inp, by simp [beliefGraph]⟩) }

noncomputable instance : SEM.IsDeterministic beliefSEM where
  mech_det v := match v with
    | .p => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .not_p => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .indic_p => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .indic_not_p => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .acq_a_ip => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .acq_a_inp => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .B_a_p => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .B_a_not_p => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Topologically ordered vertex list: one `stepOnceDetOn` pass
    propagates the whole chain. -/
def beliefVarList : List BeliefVar :=
  [.p, .not_p, .indic_p, .indic_not_p, .acq_a_ip, .acq_a_inp, .B_a_p, .B_a_not_p]

/-! ### The Predicate Lexicalization Constraint -/

/-- The PLC: presupposition `presup` can be lexicalized with at-issue
    content `atIssue` iff setting the presupposition true and running
    the belief-formation model produces the at-issue content. -/
noncomputable def SatisfiesPLC (presup atIssue : BeliefVar) : Prop :=
  (developDetOn beliefSEM beliefVarList 1
    (Valuation.empty.extend presup true)).hasValue atIssue true

noncomputable instance (presup atIssue : BeliefVar) :
    Decidable (SatisfiesPLC presup atIssue) :=
  Classical.dec _

/-- Factives satisfy the PLC: the chain from `p` reaches `B(a)(p)`. -/
theorem factive_satisfies_plc : SatisfiesPLC .p .B_a_p := by
  unfold SatisfiesPLC
  rfl

/-- Strong contrafactives violate the PLC: `¬p` generates indicators
    for `¬p`, not for `p`, so no chain reaches `B(a)(p)`. -/
theorem strong_contrafactive_violates_plc : ¬ SatisfiesPLC .not_p .B_a_p := by
  unfold SatisfiesPLC
  intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- The contrafactive gap: the factive/contrafactive asymmetry follows
    from the PLC. -/
theorem contrafactive_gap :
    SatisfiesPLC .p .B_a_p ∧ ¬ SatisfiesPLC .not_p .B_a_p :=
  ⟨factive_satisfies_plc, strong_contrafactive_violates_plc⟩

/-- The asymmetry is structural: presupposing `¬p` while asserting
    `B(a)(¬p)` is causally coherent — only the crossed profile is
    ruled out. -/
theorem contrafactive_gap_is_structural :
    SatisfiesPLC .p .B_a_p ∧
    ¬ SatisfiesPLC .not_p .B_a_p ∧
    SatisfiesPLC .not_p .B_a_not_p := by
  refine ⟨factive_satisfies_plc, strong_contrafactive_violates_plc, ?_⟩
  unfold SatisfiesPLC
  rfl

/-! ### Deriving the attestation table -/

/-- The causal variables checked by the PLC for each presuppositional
    class: factives pair `p` with `B(a)(p)`, contrafactives `¬p` with
    `B(a)(p)`; the PLC does not apply to nonfactives (no
    presupposition) or postsuppositional profiles. -/
def presupClassToCausalVars : PresupClass → Option (BeliefVar × BeliefVar)
  | .factive => some (.p, .B_a_p)
  | .contrafactive => some (.not_p, .B_a_p)
  | .nonfactive => none
  | .other => none

/-- PLC verdict per class: `none` where the PLC does not apply. -/
noncomputable def presupClassSatisfiesPLC (pc : PresupClass) : Option Bool :=
  match presupClassToCausalVars pc with
  | none => none
  | some (presup, atIssue) => some (decide (SatisfiesPLC presup atIssue))

/-- [glass-2025]'s attestation table is derived from the PLC: a class
    is attested iff it satisfies the PLC or the PLC does not apply. -/
theorem presupClassIsValid_eq_via_plc (pc : PresupClass) :
    presupClassIsValid pc = (presupClassSatisfiesPLC pc).getD true := by
  cases pc <;> simp [presupClassIsValid, presupClassSatisfiesPLC,
    presupClassToCausalVars]
  · exact factive_satisfies_plc
  · exact strong_contrafactive_violates_plc

/-- `PartialProp` of the hypothetical contrafactive: presupposes `¬p`,
    asserts belief in `p` — the causally incoherent profile. -/
def contrafactivePartialProp {W E : Type*} (R : E → W → W → Prop)
    (agent : E) (p : W → Prop) (worlds : List W) : PartialProp W :=
  { presup := fun w => ¬ p w
  , assertion := fun w => BoxAt R agent w worlds p }

end RobertsOzyildiz2025
