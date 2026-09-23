module

public import Linglib.Semantics.Causation.Implicative
public import Linglib.Studies.Karttunen1971a

/-!
# Nadathur (2023): Causal Semantics for Implicative Verbs

This file formalizes the Dreyfus scenario of [nadathur-2023-implicatives], introduced in
[nadathur-2019] after [baglini-francez-2016]: an eight-vertex structural causal model that
discriminates where two-way *dare* is felicitous. Its felicity presuppositions are stated
through the substrate's sufficiency and necessity semantics for implicatives, so the
theorems instantiate the same predicates the rest of the library attributes to these verbs.
Courage, the lexical prerequisite of *dare*, is causally necessary and sufficient for
sending the message (`dare_felicitous_for_msg`), but necessary and not sufficient for
establishing communication and for spying, which stay unsettled while the listener and the
garbling are unresolved (`nrv_necessary_not_sufficient_for_com_and_spy`).

## Implementation notes

The theorems are stated over the strict development of the paper's definitions and decided
over the finite model, the supersituation quantifiers ranging over the finite valuation space.

## TODO

The necessity presuppositions are decided by brute force over the valuation space under a
raised recursion limit; a structural proof through the parent equations
would remove them. The *manage* examples need set-valued prerequisites, one of them the
conjunction of courage, a listener, and an ungarbled message, while the substrate's
sufficiency semantics takes a single prerequisite vertex.

## References

* [nadathur-2023-implicatives]
* [nadathur-2019]
* [baglini-francez-2016]
-/

@[expose] public section

namespace Nadathur2023

open Causation Causation.Mechanism Causation.SEM
open Implicative (manageSem failSem ImplicativeClass Prerequisite)

/-- Dreyfus scenario vertices ([nadathur-2023-implicatives] §6.1.1, Figure 3):
    INT (Dreyfus intends to spy), NRV (he has the nerve), LST (a German is
    listening on the correct frequency), BRK (the message is garbled),
    SEC (he collects secrets), MSG (he sends a radio message),
    COM (he establishes communication), SPY (he spies for the Germans). -/
inductive V | INT | NRV | LST | BRK | SEC | MSG | COM | SPY
  deriving DecidableEq, Fintype, Repr

/-- Causal graph: SEC←{INT}, MSG←{INT,NRV}, COM←{MSG,LST,BRK},
    SPY←{SEC,COM}; INT, NRV, LST, BRK exogenous. -/
def graph : CausalGraph V := ⟨λ
  | .INT | .NRV | .LST | .BRK => ∅
  | .SEC => {.INT}
  | .MSG => {.INT, .NRV}
  | .COM => {.MSG, .LST, .BRK}
  | .SPY => {.SEC, .COM}⟩

instance : CausalGraph.IsDAG graph := .of_irrefl (by decide)

/-- Dreyfus SEM, with the negative `¬BRK` precondition encoded directly in
    the COM mechanism. -/
def dreyfusSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .INT | .NRV | .LST | .BRK => const (G := graph) false
      | .SEC => fun ρ ↦ ρ ⟨.INT, by decide⟩
      | .MSG => fun ρ ↦
          ρ ⟨.INT, by decide⟩ && ρ ⟨.NRV, by decide⟩
      | .COM => fun ρ ↦
          ρ ⟨.MSG, by decide⟩ && ρ ⟨.LST, by decide⟩ && !ρ ⟨.BRK, by decide⟩
      | .SPY => fun ρ ↦
          ρ ⟨.SEC, by decide⟩ && ρ ⟨.COM, by decide⟩ }

instance : CausalGraph.IsDAG dreyfusSEM.graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

/-- Background: Dreyfus intends to spy and has already collected secrets
    (INT = SEC = 1); NRV, LST, BRK are unresolved. -/
def dreyfusBg : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .INT true |>.extend .SEC true

/-- *dare* dispatches to the sufficiency semantics the theorems below are
    stated through, and its lexical prerequisite is courage — instantiated
    in the Dreyfus scenario by the NRV vertex. -/
theorem dare_semantics_via_manageSem :
    Implicative.toSemantics dreyfusSEM ImplicativeClass.dare.polarity =
      manageSem dreyfusSEM ∧
    ImplicativeClass.dare.prerequisite = some Prerequisite.courage :=
  ⟨rfl, rfl⟩

/-- Sufficiency presupposition (32iii) for (34a): NRV is causally
    sufficient (Def 10a) for MSG — neither fact is entailed by the
    background, and adding NRV = 1 causally entails MSG = 1. -/
theorem nrv_sufficient_for_msg :
    manageSem dreyfusSEM dreyfusBg .NRV true .MSG true := by
  decide

set_option maxRecDepth 400000 in
/-- Necessity presupposition (32i) for (34a): NRV is causally necessary
    (Def 10b) for MSG. -/
theorem nrv_necessary_for_msg :
    Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .MSG true := by
  decide +kernel

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
  decide

/-- (34d) *?/# Dreyfus dared to spy for the Germans* — infelicitous: NRV
    is not causally sufficient for SPY (its conditions LST, BRK, COM are
    all undetermined). -/
theorem dare_infelicitous_for_spy :
    failSem dreyfusSEM dreyfusBg .NRV true .SPY true := by
  decide

set_option maxRecDepth 400000 in
/-- (34c), necessity half: "⟨NRV,1⟩ is causally necessary but not
    sufficient for COM" — achievability settles the exogenous LST = 1,
    BRK = 0; every consistent path to COM = 1 runs through NRV = 1. Was
    unprovable under the eager-default dynamics (achievability could
    never resolve an exogenous unknown). -/
theorem nrv_necessary_for_com :
    Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .COM true := by
  decide +kernel

set_option maxRecDepth 400000 in
/-- (34d), necessity half: NRV is causally necessary but not sufficient
    for SPY ("BRK, LST, COM ∈ Anc(SPY) are all undetermined"). -/
theorem nrv_necessary_for_spy :
    Implicative.necessityPresup dreyfusSEM dreyfusBg .NRV true .SPY true := by
  decide +kernel

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

/-! [nadathur-2023-implicatives] §2 motivates the prerequisite account
from [karttunen-1971]'s descriptive 2×2 taxonomy; the conversion lives
here (the later paper draws the comparison). The two-way cell's defining
entailment pattern is not stipulated but *derived*:
`Implicative.twoWay_entailment_profile` produces both halves of Fact B
from the sufficiency + necessity presuppositions, and `schema_manage_presup`
recovers Karttunen's (37) presupposition itself at every consistent completion, witnessed concretely
at the Dreyfus model by `Nadathur2023.dare_felicitous_for_msg` together
with `Nadathur2023.no_msg_without_nerve`. -/

namespace Karttunen1971a

open Implicative

/-- Convert a Karttunen `Schema` to `ImplicativeClass`
    ([nadathur-2023-implicatives]). `aspectGoverned` is always false
    because Karttunen's 1971 analysis does not account for aspect — a
    limitation the modern analysis corrects. -/
def Schema.toImplicativeClass (k : Schema) : ImplicativeClass :=
  { polarity := k.polarity
    directionality := if k.TwoWay then .twoWay else .oneWay
    aspectGoverned := false
    prerequisite := if k.TwoWay then some .unspecified else none }

theorem karttunen_manage_matches :
    Schema.manage.toImplicativeClass = ImplicativeClass.manage := rfl

theorem karttunen_fail_matches :
    Schema.fail.toImplicativeClass = ImplicativeClass.fail := rfl

open Causation (SEM CausalGraph Valuation DecidableValuation) in
/-- The causal account validates Karttunen's (37): in a felicitous two-way context, at
every consistent completion the prerequisite is realized iff the complement is — the
presupposition `Schema.manage` carries, with causal entailment as the condition. -/
theorem schema_manage_presup {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    {background : Valuation α} {p : V} {xP : α p} {c : V} {xC : α c}
    (hexo : M.graph.parents p = ∅) (hp : background.get p = none)
    (hsuf : manageSem M background p xP c xC)
    (hnec : necessityPresup M background p xP c xC) (s' : Valuation α)
    (hset : SEM.IsExogenousSettlement M background s') (hc : s'.get c = none) :
    Schema.manage.condition.presup (SEM.causallyEntails M s' p xP)
      (SEM.causallyEntails M s' c xC) :=
  (complement_iff_prerequisite M hexo hp hsuf hnec s' hset hc).symm

end Karttunen1971a
