import Linglib.Semantics.Causation.Implicative
import Linglib.Studies.Karttunen1971

/-!
# Nadathur 2023: Causal Semantics for Implicative Verbs

The Dreyfus scenario of [nadathur-2023-implicatives] (§6.1.1, Figure 3;
introduced in [nadathur-2019] ch. 3 as "the modified Dreyfus scenario",
adapted from [baglini-francez-2016]): an eight-vertex structural causal
model discriminating where two-way *dare* is felicitous. The felicity
theorems are stated through `Causation.Implicative.manageSem` /
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
  sufficient for COM / SPY ((34c), (34d)) — though it is necessary for
  both (`nrv_necessary_for_com`, `nrv_necessary_for_spy`), completing
  the paper's "necessary but not sufficient" verdicts.

## Implementation notes

Theorems are stated over the strict T_D development (`developDetVtx?`,
faithful to the paper's Definitions 4–5): the infelicity verdicts hold
because COM and SPY stay *unsettled* while LST and BRK are unresolved —
the paper's route. Concrete claims are discharged through the fuel
bridge (`causallyEntails_iff_fuel` / `causallyNecessary_iff_fuel`) with
the model's depth function as rank certificate, then `decide`.

TODO: the *manage* examples (35a–d) need set-valued prerequisites (the
(35c) prerequisite is the conjunction NRV ∧ LST ∧ ¬BRK, [nadathur-2023-implicatives]
fn. 21); `manageSem` currently takes a single prerequisite vertex.
-/

namespace Nadathur2023

open Causation Causation.Mechanism Causation.SEM
open Causation.Implicative (manageSem failSem ImplicativeClass Prerequisite)

/-- Dreyfus scenario vertices ([nadathur-2023-implicatives] §6.1.1, Figure 3):
    INT (Dreyfus intends to spy), NRV (he has the nerve), LST (a German is
    listening on the correct frequency), BRK (the message is garbled),
    SEC (he collects secrets), MSG (he sends a radio message),
    COM (he establishes communication), SPY (he spies for the Germans). -/
inductive V | INT | NRV | LST | BRK | SEC | MSG | COM | SPY
  deriving DecidableEq, Fintype, Repr

/-- Causal graph: SEC←{INT}, MSG←{INT,NRV}, COM←{MSG,LST,BRK},
    SPY←{SEC,COM}; INT, NRV, LST, BRK exogenous. -/
def graph : CausalGraph V := ⟨fun
  | .INT | .NRV | .LST | .BRK => ∅
  | .SEC => {.INT}
  | .MSG => {.INT, .NRV}
  | .COM => {.MSG, .LST, .BRK}
  | .SPY => {.SEC, .COM}⟩

/-- Depth certificate (also the rank for the fuel bridge). -/
def depth : V → ℕ := fun
  | .INT => 0 | .NRV => 0 | .LST => 0 | .BRK => 0
  | .SEC => 1 | .MSG => 1 | .COM => 2 | .SPY => 3

private lemma depth_lt : ∀ {u v : V}, u ∈ graph.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def ranking : CausalGraph.Ranking graph := ⟨depth, depth_lt⟩

instance : CausalGraph.IsDAG graph := ranking.isDAG

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

private lemma entails_iff {s : Valuation (fun _ : V => Bool)} {v : V} {x : Bool} :
    SEM.causallyEntails dreyfusSEM s v x ↔
      developDetVtxFuel dreyfusSEM s 4 v = some x :=
  SEM.causallyEntails_iff_fuel dreyfusSEM ranking (by cases v <;> decide) s x

private lemma necessary_iff {s : Valuation (fun _ : V => Bool)} {c e : V} :
    Implicative.necessityPresup dreyfusSEM s c true e true ↔
      SEM.causallyNecessaryFuel dreyfusSEM 4 s c true e true :=
  SEM.causallyNecessary_iff_fuel dreyfusSEM ranking
    (by intro v; cases v <;> decide) s c true e true

/-- Sufficiency presupposition (32iii) for (34a): NRV is causally
    sufficient (Def 10a) for MSG — neither fact is entailed by the
    background, and adding NRV = 1 causally entails MSG = 1. -/
theorem nrv_sufficient_for_msg :
    manageSem dreyfusSEM dreyfusBg .NRV true .MSG true :=
  ⟨⟨fun h => absurd (entails_iff.mp h) (by decide),
    fun h => absurd (entails_iff.mp h) (by decide)⟩,
   entails_iff.mpr (by decide)⟩

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
/-- Necessity presupposition (32i) for (34a): NRV is causally necessary
    (Def 10b) for MSG. Decided through the fuel bridge: the
    supersituation quantifiers range over the finite valuation space. -/
theorem nrv_necessary_for_msg :
    Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .MSG true :=
  necessary_iff.mpr (by decide)

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
    infelicitous: NRV is not causally sufficient for COM, which stays
    unsettled while LST and BRK are unresolved in the background. -/
theorem dare_infelicitous_for_com :
    failSem dreyfusSEM dreyfusBg .NRV true .COM true := by
  rintro ⟨-, hb⟩
  exact absurd (entails_iff.mp hb) (by decide)

/-- (34d) *?/# Dreyfus dared to spy for the Germans* — infelicitous: NRV
    is not causally sufficient for SPY (its conditions LST, BRK, COM are
    all undetermined). -/
theorem dare_infelicitous_for_spy :
    failSem dreyfusSEM dreyfusBg .NRV true .SPY true := by
  rintro ⟨-, hb⟩
  exact absurd (entails_iff.mp hb) (by decide)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
/-- (34c), necessity half: "⟨NRV,1⟩ is causally necessary but not
    sufficient for COM" — achievability settles the exogenous LST = 1,
    BRK = 0; every consistent path to COM = 1 runs through NRV = 1. Was
    unprovable under the eager-default dynamics (achievability could
    never resolve an exogenous unknown). -/
theorem nrv_necessary_for_com :
    Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .COM true :=
  necessary_iff.mpr (by decide)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
/-- (34d), necessity half: NRV is causally necessary but not sufficient
    for SPY ("BRK, LST, COM ∈ Anc(SPY) are all undetermined"). -/
theorem nrv_necessary_for_spy :
    Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .SPY true :=
  necessary_iff.mpr (by decide)

/-- (34c)/(34d) complete profiles: NRV is causally **necessary but not
    sufficient** for COM and for SPY — the paper's exact §6.1.1 verdicts,
    as single statements. -/
theorem nrv_necessary_not_sufficient_for_com_and_spy :
    (Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .COM true ∧
     failSem dreyfusSEM dreyfusBg .NRV true .COM true) ∧
    (Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .SPY true ∧
     failSem dreyfusSEM dreyfusBg .NRV true .SPY true) :=
  ⟨⟨nrv_necessary_for_com, dare_infelicitous_for_com⟩,
   ⟨nrv_necessary_for_spy, dare_infelicitous_for_spy⟩⟩

/-- Fact B, negative half, at (34b): *Dreyfus did not dare to send a
    message* — no consistent completion of the negative-assertion context
    realizes MSG. Instantiates
    `Implicative.no_complement_of_negative_assertion` at the Dreyfus
    model. -/
theorem no_msg_without_nerve :
    ∀ s', SEM.IsExogenousSettlement dreyfusSEM (dreyfusBg.extend .NRV false) s' →
      s'.get .MSG = none → ¬ SEM.causallyEntails dreyfusSEM s' .MSG true :=
  Implicative.no_complement_of_negative_assertion dreyfusSEM
    (by decide) (by decide) (by decide) nrv_necessary_for_msg

/-- Fact C at (34a): in the Dreyfus context, a consistent completion
    realizes MSG exactly when Dreyfus has the nerve — the prerequisite is
    sufficient and necessary, so the *dare* claim's truth value tracks
    NRV across all consistent resolutions. -/
theorem msg_iff_nerve :
    ∀ s', SEM.IsExogenousSettlement dreyfusSEM dreyfusBg s' →
      s'.get .MSG = none →
      (SEM.causallyEntails dreyfusSEM s' .MSG true ↔
       SEM.causallyEntails dreyfusSEM s' .NRV true) :=
  Implicative.complement_iff_prerequisite dreyfusSEM
    (by decide) (by decide) nrv_sufficient_for_msg nrv_necessary_for_msg

end Nadathur2023

-- ════════════════════════════════════════════════════
-- § Karttunen 1971 classification recovered
-- ════════════════════════════════════════════════════

/-! [nadathur-2023-implicatives] §2 motivates the prerequisite account
from [karttunen-1971]'s descriptive 2×2 taxonomy; the conversion lives
here (the later paper draws the comparison). The two-way cell's defining
entailment pattern is not stipulated but *derived*:
`Implicative.twoWay_entailment_profile` produces both halves of Fact B
from the sufficiency + necessity presuppositions, witnessed concretely
at the Dreyfus model by `Nadathur2023.dare_felicitous_for_msg` together
with `Nadathur2023.no_msg_without_nerve`. -/

namespace Karttunen1971

open Causation.Implicative

/-- Convert `KarttunenClass` to `ImplicativeClass`
    ([nadathur-2023-implicatives]). `aspectGoverned` is always false
    because Karttunen's 1971 analysis does not account for aspect — a
    limitation the modern analysis corrects. -/
def KarttunenClass.toImplicativeClass (k : KarttunenClass) : ImplicativeClass :=
  { polarity := k.polarity
    directionality := if k.isTwoWay then .twoWay else .oneWay
    aspectGoverned := false
    prerequisite := if k.isTwoWay then some .unspecified else none }

theorem karttunen_manage_matches :
    KarttunenClass.manage.toImplicativeClass = ImplicativeClass.manage := rfl

theorem karttunen_fail_matches :
    KarttunenClass.fail.toImplicativeClass = ImplicativeClass.fail := rfl

end Karttunen1971
