import Linglib.Semantics.Causation.Implicative

/-!
# Nadathur 2023: Causal Semantics for Implicative Verbs

The Dreyfus scenario of [nadathur-2023-implicatives] (§6.1.1, Figure 3;
introduced in [nadathur-2019] ch. 3 as "the modified Dreyfus scenario",
adapted from [baglini-francez-2016]): an eight-vertex structural causal
model discriminating where two-way *dare* is felicitous. The felicity
theorems are stated through `Semantics.Causation.Implicative.manageSem` /
`failSem` — the substrate formalization of this paper's prerequisite
account (Proposal 32) — so they instantiate the same sufficiency predicate
the rest of the codebase attributes to implicative verbs.

## Main declarations

- `Nadathur2023.dreyfusSEM`: the Dreyfus SCM (SEC = INT, MSG = INT ∧ NRV,
  COM = MSG ∧ LST ∧ ¬BRK, SPY = SEC ∧ COM), background INT = SEC = true
  with NRV, LST, BRK unresolved.
- `dare_felicitous_for_msg`: NRV (courage, *dare*'s lexical prerequisite)
  is causally necessary and sufficient for MSG — (34a), via
  `nrv_necessary_for_msg` (Def 10b) and `nrv_sufficient_for_msg`.
- `dare_infelicitous_for_com`, `dare_infelicitous_for_spy`: NRV is not
  sufficient for COM / SPY ((34c), (34d)).

## Implementation notes

The substrate's eager-default `developDet` resolves undetermined exogenous
vertices to their `const false` mechanism values, so the infelicity
verdicts hold because LST defaults to false; in the paper's stepwise
dynamics they hold because LST stays unsettled. Same verdicts, different
route — see the parallel note at `NadathurLauer2020.Bus`.

TODO: the paper also classes NRV as causally necessary (but not
sufficient) for COM and SPY; those positive necessity claims need the
achievability clause to resolve LST = true, which the eager-default
`isConsistentSuper` cannot represent — the substrate gap behind the
deferred *manage* examples (35a–d).
-/

namespace Nadathur2023

open Semantics.Causation Semantics.Causation.Mechanism Semantics.Causation.SEM
open Semantics.Causation.Implicative (manageSem failSem ImplicativeClass Prerequisite)

/-- Dreyfus scenario vertices ([nadathur-2023-implicatives] §6.1.1, Figure 3):
    INT (Dreyfus intends to spy), NRV (he has the nerve), LST (a German is
    listening on the correct frequency), BRK (the message is garbled),
    SEC (he collects secrets), MSG (he sends a radio message),
    COM (he establishes communication), SPY (he spies for the Germans). -/
inductive V | INT | NRV | LST | BRK | SEC | MSG | COM | SPY
  deriving DecidableEq, Fintype, Repr

/-- Vertices in topological order: one `stepOnceDetOn` sweep settles each
    vertex from its already-settled parents. Used by the `developDetOn`
    bridge proofs below. -/
def varList : List V :=
  [.INT, .NRV, .LST, .BRK, .SEC, .MSG, .COM, .SPY]

/-- Causal graph: SEC←{INT}, MSG←{INT,NRV}, COM←{MSG,LST,BRK},
    SPY←{SEC,COM}; INT, NRV, LST, BRK exogenous. -/
def graph : CausalGraph V := ⟨fun
  | .INT | .NRV | .LST | .BRK => ∅
  | .SEC => {.INT}
  | .MSG => {.INT, .NRV}
  | .COM => {.MSG, .LST, .BRK}
  | .SPY => {.SEC, .COM}⟩

instance : CausalGraph.IsDAG graph := CausalGraph.IsDAG.of_depth graph
  (fun | .INT => 0 | .NRV => 0 | .LST => 0 | .BRK => 0
       | .SEC => 1 | .MSG => 1 | .COM => 2 | .SPY => 3)
  (fun {u v} h => by cases v <;> cases u <;> simp_all [graph])

/-- Dreyfus SEM, with the negative `¬BRK` precondition encoded directly in
    the COM mechanism. -/
noncomputable def dreyfusSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .INT | .NRV | .LST | .BRK => const (G := graph) false
      | .SEC => deterministic (fun ρ => ρ ⟨.INT, by decide⟩)
      | .MSG => deterministic (fun ρ =>
          ρ ⟨.INT, by decide⟩ && ρ ⟨.NRV, by decide⟩)
      | .COM => deterministic (fun ρ =>
          ρ ⟨.MSG, by decide⟩ && ρ ⟨.LST, by decide⟩ && !ρ ⟨.BRK, by decide⟩)
      | .SPY => deterministic (fun ρ =>
          ρ ⟨.SEC, by decide⟩ && ρ ⟨.COM, by decide⟩) }

instance : CausalGraph.IsDAG dreyfusSEM.graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

instance : SEM.IsDeterministic dreyfusSEM where
  mech_det v := match v with
    | .INT | .NRV | .LST | .BRK =>
        inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .SEC | .MSG | .COM | .SPY =>
        inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Background: Dreyfus intends to spy and has already collected secrets
    (INT = SEC = 1); NRV, LST, BRK are unresolved. -/
def dreyfusBg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .INT true |>.extend .SEC true

/-- *dare* dispatches to the sufficiency semantics the theorems below are
    stated through, and its lexical prerequisite is courage — instantiated
    in the Dreyfus scenario by the NRV vertex. -/
theorem dare_semantics_via_manageSem :
    Features.Implicative.toSemantics dreyfusSEM ImplicativeClass.dare.polarity =
      manageSem dreyfusSEM ∧
    ImplicativeClass.dare.prerequisite = some Prerequisite.courage :=
  ⟨rfl, rfl⟩

/-- Sufficiency presupposition (32iii) for (34a): NRV is causally
    sufficient for MSG. -/
theorem nrv_sufficient_for_msg :
    manageSem dreyfusSEM dreyfusBg .NRV true .MSG true := by
  unfold manageSem SEM.causallySufficient developsToValue
  exact developDet_hasValue_of_developDetOn_hasValue
    (vs := varList) (n := 1) (by decide)

/-- Necessity presupposition (32i) for (34a): NRV is causally necessary
    (Def 10b) for MSG. Precondition and achievability reduce to
    `developDetOn` computations; the but-for clause holds because a
    consistent supersituation can fix MSG only to its background
    development (false), and NRV — fixed false or left to its default —
    zeroes the INT ∧ NRV mechanism. -/
theorem nrv_necessary_for_msg :
    Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .MSG true := by
  have hBgMsg : developDetVtx dreyfusSEM dreyfusBg V.MSG = false :=
    developDetVtx_of_developDetOn_hasValue (vs := varList) (n := 1) (by decide)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- precondition: background does not already develop NRV = true
    rw [developDetVtx_of_developDetOn_hasValue (M := dreyfusSEM)
      (vs := varList) (n := 1) (x := false) (by decide)]
    exact Bool.false_ne_true
  · -- precondition: background does not already develop MSG = true
    rw [hBgMsg]; exact Bool.false_ne_true
  · -- achievability: the extended valuation itself is the witness
    exact ⟨dreyfusBg.extend V.NRV true, Valuation.le_refl _,
      isConsistentSuper_self _ _,
      developDetVtx_of_developDetOn_hasValue (vs := varList) (n := 1) (by decide)⟩
  · -- but-for: no consistent supersituation lacking NRV = true reaches MSG = true
    intro s' _ hnrv hcons
    have hNrvFalse : developDetVtx dreyfusSEM s' V.NRV = false := by
      cases hget : s'.get V.NRV with
      | none => rw [developDetVtx_undet _ _ _ hget]; rfl
      | some xv =>
          rw [developDetVtx_extended _ _ _ _ hget]
          cases xv
          · rfl
          · exact absurd hget hnrv
    have hMsgFalse : developDetVtx dreyfusSEM s' V.MSG = false := by
      cases hget : s'.get V.MSG with
      | some xv =>
          have hxv : xv = false := (hcons V.MSG xv (by decide) hget).symm.trans hBgMsg
          rw [developDetVtx_extended _ _ _ _ hget, hxv]
      | none =>
          rw [developDetVtx_undet _ _ _ hget]
          change (developDetVtx dreyfusSEM s' V.INT &&
                  developDetVtx dreyfusSEM s' V.NRV) = false
          rw [hNrvFalse, Bool.and_false]
    rw [hMsgFalse]
    exact Bool.false_ne_true

/-- (34a) *Dreyfus dared to send a message to the Germans* — felicitous:
    "NRV is the only undetermined condition for the truth of MSG: it is
    thus both causally necessary and sufficient for MSG"
    ([nadathur-2023-implicatives] §6.1.1). Both presuppositions of two-way
    *dare* (Proposal 32 i, iii) are satisfied in context. -/
theorem dare_felicitous_for_msg :
    Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .MSG true ∧
    manageSem dreyfusSEM dreyfusBg .NRV true .MSG true :=
  ⟨nrv_necessary_for_msg, nrv_sufficient_for_msg⟩

/-- (34c) *?/# Dreyfus dared to establish communication with the Germans* —
    infelicitous: NRV is not causally sufficient for COM, whose conditions
    LST and BRK remain unresolved in the background. -/
theorem dare_infelicitous_for_com :
    failSem dreyfusSEM dreyfusBg .NRV true .COM true := by
  unfold failSem manageSem SEM.causallySufficient developsToValue
  intro h
  have hFalse : (dreyfusSEM.developDet (dreyfusBg.extend V.NRV true)).hasValue V.COM false :=
    developDet_hasValue_of_developDetOn_hasValue
      (vs := varList) (n := 1) (by decide)
  rw [Valuation.hasValue] at h hFalse
  exact Bool.noConfusion (Option.some.inj (h.symm.trans hFalse))

/-- (34d) *?/# Dreyfus dared to spy for the Germans* — infelicitous: NRV is
    not causally sufficient for SPY (its ancestors LST, BRK, COM are all
    undetermined). -/
theorem dare_infelicitous_for_spy :
    failSem dreyfusSEM dreyfusBg .NRV true .SPY true := by
  unfold failSem manageSem SEM.causallySufficient developsToValue
  intro h
  have hFalse : (dreyfusSEM.developDet (dreyfusBg.extend V.NRV true)).hasValue V.SPY false :=
    developDet_hasValue_of_developDetOn_hasValue
      (vs := varList) (n := 1) (by decide)
  rw [Valuation.hasValue] at h hFalse
  exact Bool.noConfusion (Option.some.inj (h.symm.trans hFalse))

end Nadathur2023
