module

public import Mathlib.Data.Fintype.Prod
public import Linglib.Semantics.Causation.Implicative
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Studies.Karttunen1971a
public import Linglib.Fragments.Finnish.Verbs
public import Linglib.Data.Examples.Nadathur2023

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

The paper's Finnish verbs fall into its classes by polarity, by whether a verb entails under
both matrix polarities, and by the prerequisite it names: *onnistua* is the counterpart of
*manage*, *uskaltaa* of *dare* and *viitsiä* of *bother*, *laiminlyödä* patterns with *fail* and
*epäröidä* with *hesitate*, and *pystyä* is the one-way counterpart of the bleached verbs. The
classes agree with the polarities of the Finnish Fragment's entries (`implicative_eq`), and the
paper's minimal pairs bear them out: each claim entails its complement, the complement's
negation, or neither, as its class predicts (`rows_agree`).

## Implementation notes

The Dreyfus scenario is a causal model whose exogenous variables read the context, and the
background is an observation. The theorems are stated over the strict development of the paper's
definitions. The sufficiency verdicts are decided over the finite model; the necessity
verdicts are proved through the equations, which make every path to the effect run through the
nerve.

## TODO

The *manage* examples need set-valued prerequisites, one of them the
conjunction of courage, a listener, and an ungarbled message, while the substrate's
sufficiency semantics takes a single prerequisite vertex.

## References

* [nadathur-2023-implicatives]
* [nadathur-2019]
* [baglini-francez-2016]
-/

@[expose] public section

namespace Nadathur2023

open CausalModel
open Implicative (manageSem failSem ImplicativeClass Prerequisite)

/-- Dreyfus scenario vertices ([nadathur-2023-implicatives] §6.1.1, Figure 3):
    INT (Dreyfus intends to spy), NRV (he has the nerve), LST (a German is
    listening on the correct frequency), BRK (the message is garbled),
    SEC (he collects secrets), MSG (he sends a radio message),
    COM (he establishes communication), SPY (he spies for the Germans). -/
inductive V | INT | NRV | LST | BRK | SEC | MSG | COM | SPY
  deriving DecidableEq, Fintype, Repr

/-- In the causal graph SEC←{INT}, MSG←{INT,NRV}, COM←{MSG,LST,BRK} and SPY←{SEC,COM}, with INT,
NRV, LST and BRK exogenous. -/
def adj (w v : V) : Prop :=
  w = .INT ∧ v = .SEC ∨ (w = .INT ∨ w = .NRV) ∧ v = .MSG ∨
    (w = .MSG ∨ w = .LST ∨ w = .BRK) ∧ v = .COM ∨ (w = .SEC ∨ w = .COM) ∧ v = .SPY

instance : DecidableRel adj := fun w v ↦ by unfold adj; infer_instance

/-- The Dreyfus model, with the negative `¬BRK` precondition encoded directly in the COM equation;
the context settles INT, NRV, LST and BRK. -/
def dreyfusModel : CausalModel (Bool × Bool × Bool × Bool) V fun _ ↦ Bool where
  graph := ⟨adj⟩
  eqn
    | .INT => fun u _ ↦ u.1
    | .NRV => fun u _ ↦ u.2.1
    | .LST => fun u _ ↦ u.2.2.1
    | .BRK => fun u _ ↦ u.2.2.2
    | .SEC => fun _ x ↦ x .INT
    | .MSG => fun _ x ↦ x .INT && x .NRV
    | .COM => fun _ x ↦ x .MSG && x .LST && !x .BRK
    | .SPY => fun _ x ↦ x .SEC && x .COM

instance : DecidableRel dreyfusModel.graph.Adj := inferInstanceAs (DecidableRel adj)

instance : dreyfusModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- Background: Dreyfus intends to spy and has already collected secrets
    (INT = SEC = 1); NRV, LST, BRK are unresolved. -/
def dreyfusBg : V → Flat Bool := Function.update (Function.update ⊥ .INT ↑true) .SEC ↑true

/-- *dare* dispatches to the sufficiency semantics the theorems below are
    stated through, and its lexical prerequisite is courage — instantiated
    in the Dreyfus scenario by the NRV vertex. -/
theorem dare_semantics_via_manageSem :
    Implicative.toSemantics dreyfusModel ImplicativeClass.dare.polarity =
      manageSem dreyfusModel ∧
    ImplicativeClass.dare.prerequisite = some Prerequisite.courage :=
  ⟨rfl, rfl⟩

/-- Sufficiency presupposition (32iii) for (34a): NRV is causally
    sufficient (Def 10a) for MSG — neither fact is entailed by the
    background, and adding NRV = 1 causally entails MSG = 1. -/
theorem nrv_sufficient_for_msg : manageSem dreyfusModel dreyfusBg .NRV true .MSG true := by
  decide

/-! The no-alternative clauses follow from the equations: a variable the development settles has
settled parents and takes its equation's value at theirs, so settling MSG true needs NRV true
(MSG = INT ∧ NRV), settling COM true needs MSG true, and settling SPY true needs COM true. -/

section Equations

variable {s : V → Flat Bool}

private theorem parent_settled {v : V} {x : Bool} (h : dreyfusModel.CausallyEntails s v x)
    (hv : s v = ⊥) {w : V} (hw : dreyfusModel.graph.Adj w v) :
    ∃ z, dreyfusModel.CausallyEntails s w z := by
  rcases causallyEntails_iff.1 h with h | ⟨-, hpar, -⟩
  · rw [hv] at h; exact absurd h Flat.bot_ne_coe
  · exact hpar w hw

/-- Settling MSG true, unobserved, settles NRV true: MSG = INT ∧ NRV. -/
theorem nrv_of_msg (hs : s .MSG = ⊥) (h : dreyfusModel.CausallyEntails s .MSG true) :
    dreyfusModel.CausallyEntails s .NRV true := by
  obtain ⟨a, ha⟩ := parent_settled h hs (w := .INT) (by decide)
  obtain ⟨b, hb⟩ := parent_settled h hs (w := .NRV) (by decide)
  have hab : (a && b) = true := h.eqn_eq hs (y := fun w ↦ if w = .NRV then b else a) (fun w hw ↦ by
    rcases (by decide : ∀ w, dreyfusModel.graph.Adj w .MSG → w = .INT ∨ w = .NRV) w hw with
      rfl | rfl <;> simpa) default
  rwa [(Bool.and_eq_true_iff.1 hab).2] at hb

/-- Settling COM true, unobserved, settles MSG true: COM = MSG ∧ LST ∧ ¬BRK. -/
theorem msg_of_com (hs : s .COM = ⊥) (h : dreyfusModel.CausallyEntails s .COM true) :
    dreyfusModel.CausallyEntails s .MSG true := by
  obtain ⟨m, hm⟩ := parent_settled h hs (w := .MSG) (by decide)
  obtain ⟨l, hl⟩ := parent_settled h hs (w := .LST) (by decide)
  obtain ⟨k, hk⟩ := parent_settled h hs (w := .BRK) (by decide)
  have hmlk : (m && l && !k) = true := h.eqn_eq hs
    (y := fun w ↦ if w = .MSG then m else if w = .LST then l else k) (fun w hw ↦ by
      rcases (by decide : ∀ w, dreyfusModel.graph.Adj w .COM →
        w = .MSG ∨ w = .LST ∨ w = .BRK) w hw with rfl | rfl | rfl <;> simpa) default
  rwa [(Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hmlk).1).1] at hm

/-- Settling SPY true, unobserved, settles COM true: SPY = SEC ∧ COM. -/
theorem com_of_spy (hs : s .SPY = ⊥) (h : dreyfusModel.CausallyEntails s .SPY true) :
    dreyfusModel.CausallyEntails s .COM true := by
  obtain ⟨a, ha⟩ := parent_settled h hs (w := .SEC) (by decide)
  obtain ⟨c, hc⟩ := parent_settled h hs (w := .COM) (by decide)
  have hac : (a && c) = true := h.eqn_eq hs (y := fun w ↦ if w = .COM then c else a) (fun w hw ↦ by
    rcases (by decide : ∀ w, dreyfusModel.graph.Adj w .SPY → w = .SEC ∨ w = .COM) w hw with
      rfl | rfl <;> simpa) default
  rwa [(Bool.and_eq_true_iff.1 hac).2] at hc

end Equations

/-- The Dreyfus background with the nerve, listener and ungarbled message settled. -/
def resolved : V → Flat Bool :=
  Function.update (Function.update (Function.update dreyfusBg .NRV ↑true) .LST ↑true) .BRK ↑false

/-- Necessity presupposition (32i) for (34a): NRV is causally necessary
    (Def 10b) for MSG. -/
theorem nrv_necessary_for_msg :
    Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .MSG true :=
  ⟨by decide, ⟨_, .refl _, by decide, by decide⟩, fun _ _ hc h ↦ nrv_of_msg hc h⟩

/-- (34a) *Dreyfus dared to send a message to the Germans* — felicitous:
    "NRV is the only undetermined condition for the truth of MSG: it is
    thus both causally necessary and sufficient for MSG"
    ([nadathur-2023-implicatives] §6.1.1). Both presuppositions of two-way
    *dare* (Proposal 32 i, iii) are satisfied in context. -/
theorem dare_felicitous_for_msg :
    Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .MSG true ∧
    manageSem dreyfusModel dreyfusBg .NRV true .MSG true :=
  ⟨nrv_necessary_for_msg, nrv_sufficient_for_msg⟩

/-- (34c) *?/# Dreyfus dared to establish communication with the Germans* —
    infelicitous: NRV is not causally sufficient for COM, which stays
    unsettled while LST and BRK are unresolved in the background. -/
theorem dare_infelicitous_for_com : failSem dreyfusModel dreyfusBg .NRV true .COM true := by
  decide

/-- (34d) *?/# Dreyfus dared to spy for the Germans* — infelicitous: NRV
    is not causally sufficient for SPY (its conditions LST, BRK, COM are
    all undetermined). -/
theorem dare_infelicitous_for_spy : failSem dreyfusModel dreyfusBg .NRV true .SPY true := by
  decide

/-- (34c), necessity half: "⟨NRV,1⟩ is causally necessary but not
    sufficient for COM" — achievability settles the exogenous LST = 1,
    BRK = 0; every path to COM = 1 runs through NRV = 1. -/
theorem nrv_necessary_for_com :
    Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .COM true :=
  ⟨by decide, ⟨resolved, by decide, by decide, by decide⟩, fun _ hset hc h ↦
    nrv_of_msg (hset.eq_bot (by decide) ⟨.INT, by decide⟩) (msg_of_com hc h)⟩

/-- (34d), necessity half: NRV is causally necessary but not sufficient
    for SPY ("BRK, LST, COM ∈ Anc(SPY) are all undetermined"). -/
theorem nrv_necessary_for_spy :
    Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .SPY true :=
  ⟨by decide, ⟨resolved, by decide, by decide, by decide⟩, fun _ hset hc h ↦
    nrv_of_msg (hset.eq_bot (by decide) ⟨.INT, by decide⟩)
      (msg_of_com (hset.eq_bot (by decide) ⟨.MSG, by decide⟩) (com_of_spy hc h))⟩

/-- (34c)/(34d) complete profiles: NRV is causally **necessary but not
    sufficient** for COM and for SPY — the paper's exact §6.1.1 verdicts,
    as single statements. -/
theorem nrv_necessary_not_sufficient_for_com_and_spy :
    (Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .COM true ∧
     failSem dreyfusModel dreyfusBg .NRV true .COM true) ∧
    (Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .SPY true ∧
     failSem dreyfusModel dreyfusBg .NRV true .SPY true) :=
  ⟨⟨nrv_necessary_for_com, dare_infelicitous_for_com⟩,
   ⟨nrv_necessary_for_spy, dare_infelicitous_for_spy⟩⟩

/-- NRV is exogenous and open in the Dreyfus background. -/
theorem nrv_root : ∀ w, ¬ dreyfusModel.graph.Adj w .NRV := by decide

theorem nrv_open : ∀ x, ¬ dreyfusModel.CausallyEntails dreyfusBg .NRV x := by decide

/-- Fact B, negative half, at (34b): *Dreyfus did not dare to send a
    message* — no exogenous settlement of the negative-assertion context
    realizes MSG. Instantiates
    `Implicative.no_complement_of_negative_assertion` at the Dreyfus
    model. -/
theorem no_msg_without_nerve :
    ∀ s', dreyfusModel.IsExogenousSettlement (Function.update dreyfusBg .NRV ↑false) s' →
      s' .MSG = ⊥ → ¬ dreyfusModel.CausallyEntails s' .MSG true :=
  Implicative.no_complement_of_negative_assertion nrv_root nrv_open (by decide)
    nrv_necessary_for_msg

/-- Fact C at (34a). In the Dreyfus context, an exogenous settlement
    realizes MSG exactly when Dreyfus has the nerve — the prerequisite is
    sufficient and necessary, so the *dare* claim's truth value tracks
    NRV across all resolutions. -/
theorem msg_iff_nerve :
    ∀ s', dreyfusModel.IsExogenousSettlement dreyfusBg s' → s' .MSG = ⊥ →
      (dreyfusModel.CausallyEntails s' .MSG true ↔ dreyfusModel.CausallyEntails s' .NRV true) :=
  Implicative.complement_iff_prerequisite nrv_root nrv_open nrv_sufficient_for_msg
    nrv_necessary_for_msg

/-! ### The Finnish implicatives -/

open Implicative (Directionality)
open Data.Examples

/-- A positive implicative whose prerequisite is `p`. -/
def positiveClass (d : Directionality) (p : Prerequisite) : ImplicativeClass :=
  { polarity := .positive, directionality := d, aspectGoverned := false, prerequisite := some p }

/-- The classes of the Finnish verbs. *Malttaa* names patience, *hennoa* hard-heartedness,
*kehdata* the lack of shame and *ehtiä* time; *mahtua* names being small enough and entails only
when negated, and *pystyä*, which the paper also allows might be a modal, is unconstrained. -/
def finnish : List (Finnish.Verb × ImplicativeClass) :=
  [(Finnish.onnistua, .manage), (Finnish.uskaltaa, .dare), (Finnish.viitsiä, .bother),
    (Finnish.malttaa, positiveClass .twoWay .patience),
    (Finnish.hennoa, positiveClass .twoWay .hardHeartedness),
    (Finnish.kehdata, positiveClass .twoWay .shamelessness),
    (Finnish.ehtiä, positiveClass .twoWay .time), (Finnish.jaksaa, .jaksaa),
    (Finnish.mahtua, positiveClass .oneWay .fitness),
    (Finnish.pystyä, positiveClass .oneWay .unspecified), (Finnish.laiminlyödä, .fail),
    (Finnish.epäröidä, .hesitate)]

/-- The polarity of each class is the complement polarity of the Fragment's entry. -/
theorem implicative_eq : ∀ p ∈ finnish, p.1.implicative = some p.2.polarity := by
  decide

/-- The truth value that a claim with a verb of class `k` entails for its complement, when the
matrix is positive or negated: a two-way verb entails one under either polarity and a one-way
verb only under negation. -/
def entailed (k : ImplicativeClass) (negated : Bool) : Option Bool :=
  if k.directionality = .oneWay ∧ ¬ negated then none
  else some (decide (k.polarity = .positive) != negated)

/-- A minimal-pair member: the class of its verb, whether the matrix is negated, and the truth
value the paper says it entails for the complement. -/
structure Row where
  implicativeClass : ImplicativeClass
  negated : Bool
  entails : Option Bool

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let k ← e.parse? "verb" (finnish.map fun p ↦ (p.1.form, p.2))
  let neg ← e.parse? "matrix" [("positive", false), ("negated", true)]
  let ent ← e.parse? "entails"
    [("complement", some true), ("negation", some false), ("nothing", none)]
  some ⟨k, neg, ent⟩

/-- Every example is a row. -/
theorem isSome_ofExample : ∀ e ∈ Examples.all, (Row.ofExample e).isSome := by
  decide

/-- The rows of the paper's Finnish minimal pairs. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Each claim entails what its verb's class predicts. -/
theorem rows_agree : ∀ r ∈ rows, entailed r.implicativeClass r.negated = r.entails := by
  decide

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

/-- The causal account validates Karttunen's (37): in a felicitous two-way context, at
every exogenous settlement the prerequisite is realized iff the complement is — the
presupposition `Schema.manage` carries, with causal entailment as the condition. -/
theorem schema_manage_presup {U V : Type*} {α : V → Type*} [DecidableEq V]
    {M : CausalModel U V α} [M.IsAcyclic] {s : ∀ v, Flat (α v)} {p : V} {xP : α p} {c : V}
    {xC : α c} (hroot : ∀ w, ¬ M.graph.Adj w p) (hopen : ∀ x, ¬ M.CausallyEntails s p x)
    (hsuf : manageSem M s p xP c xC) (hnec : necessityPresup M s p xP c xC)
    (s' : ∀ v, Flat (α v)) (hset : M.IsExogenousSettlement s s') (hc : s' c = ⊥) :
    Schema.manage.condition.presup (M.CausallyEntails s' p xP) (M.CausallyEntails s' c xC) :=
  (complement_iff_prerequisite hroot hopen hsuf hnec s' hset hc).symm

end Karttunen1971a
