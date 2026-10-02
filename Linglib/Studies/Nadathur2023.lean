module

public import Mathlib.Data.Fintype.Prod
public import Linglib.Semantics.Causation.Implicative
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Studies.Karttunen1971a
public import Linglib.Fragments.Finnish.Verbs
public import Linglib.Data.Examples.Nadathur2023

/-!
# Nadathur (2023)

Nadathur's Dreyfus scenario, which she introduced in 2019 after Baglini and Francez, is an
eight-vertex causal model that discriminates where two-way *dare* is felicitous. Courage, the
prerequisite *dare* names, is causally necessary and sufficient for sending the message
(`dare_felicitous_for_msg`), but necessary and not sufficient for establishing communication and
for spying, which stay unsettled while the listener and the garbling are unresolved
(`nrv_necessary_not_sufficient_for_com_and_spy`).

The paper's Finnish implicatives fall into its classes by polarity, by whether a verb entails under
both matrix polarities, and by the prerequisite it names. The classes agree with the polarities of
the Finnish fragment's entries (`implicative_eq`), and each of the paper's minimal pairs entails
its complement, the complement's negation, or neither, as its class predicts (`rows_agree`).

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

/-- In the causal graph SEC reads INT, MSG reads INT and NRV, COM reads MSG, LST and BRK, and SPY
reads SEC and COM, with INT, NRV, LST and BRK exogenous. -/
def edges : Finset (V × V) :=
  {(.INT, .SEC), (.INT, .MSG), (.NRV, .MSG), (.MSG, .COM), (.LST, .COM), (.BRK, .COM),
    (.SEC, .SPY), (.COM, .SPY)}

/-- The context settles the intention, the nerve, the listener, and the garbling. -/
structure Context where
  INT : Bool
  NRV : Bool
  LST : Bool
  BRK : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The Dreyfus model, with the negative `¬BRK` precondition encoded directly in the COM
equation. -/
def dreyfusModel : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .INT => fun u _ ↦ u.INT
    | .NRV => fun u _ ↦ u.NRV
    | .LST => fun u _ ↦ u.LST
    | .BRK => fun u _ ↦ u.BRK
    | .SEC => fun _ x ↦ x .INT
    | .MSG => fun _ x ↦ x .INT && x .NRV
    | .COM => fun _ x ↦ x .MSG && x .LST && !x .BRK
    | .SPY => fun _ x ↦ x .SEC && x .COM

instance : DecidableRel dreyfusModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : dreyfusModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the background Dreyfus intends to spy and has already collected secrets (INT = SEC = 1),
and NRV, LST and BRK are unresolved. -/
def dreyfusBg : V → Flat Bool := [.INT ← true, .SEC ← true]

/-- *dare* dispatches to the sufficiency semantics the theorems below are
    stated through, and its lexical prerequisite is courage — instantiated
    in the Dreyfus scenario by the NRV vertex. -/
theorem dare_semantics_via_manageSem :
    Implicative.toSemantics dreyfusModel ImplicativeClass.dare.polarity =
      manageSem dreyfusModel ∧
    ImplicativeClass.dare.prerequisite = some Prerequisite.courage :=
  ⟨rfl, rfl⟩

/-- The sufficiency presupposition (32iii) of (34a) holds, NRV being causally sufficient
(Def 10a) for MSG. Neither fact is entailed by the background, and adding NRV = 1 causally entails
MSG = 1. -/
theorem nrv_sufficient_for_msg : manageSem dreyfusModel dreyfusBg .NRV true .MSG true := by
  decide

/-! The no-alternative clauses follow from the equations: a variable the development settles
settles each parent to the value its equation needs (`CausalModel.CausallyEntails.parent_eq`), so
settling MSG true needs NRV true, settling COM true needs MSG true, and settling SPY true needs
COM true. -/

section Equations

variable {s : V → Flat Bool}

/-- Settling MSG true, unobserved, settles NRV true, since MSG = INT ∧ NRV. -/
theorem nrv_of_msg (hs : s .MSG = ⊥) (h : dreyfusModel.CausallyEntails s .MSG true) :
    dreyfusModel.CausallyEntails s .NRV true :=
  h.parent_eq hs (by decide) fun _ _ hy ↦ by simpa using (Bool.and_eq_true_iff.1 hy).2

/-- Settling COM true, unobserved, settles MSG true, since COM = MSG ∧ LST ∧ ¬BRK. -/
theorem msg_of_com (hs : s .COM = ⊥) (h : dreyfusModel.CausallyEntails s .COM true) :
    dreyfusModel.CausallyEntails s .MSG true :=
  h.parent_eq hs (by decide) fun _ _ hy ↦ by
    simpa using (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hy).1).1

/-- Settling SPY true, unobserved, settles COM true, since SPY = SEC ∧ COM. -/
theorem com_of_spy (hs : s .SPY = ⊥) (h : dreyfusModel.CausallyEntails s .SPY true) :
    dreyfusModel.CausallyEntails s .COM true :=
  h.parent_eq hs (by decide) fun _ _ hy ↦ by simpa using (Bool.and_eq_true_iff.1 hy).2

end Equations

/-- The Dreyfus background with the nerve, listener and ungarbled message settled. -/
def resolved : V → Flat Bool :=
  Function.update (Function.update (Function.update dreyfusBg .NRV ↑true) .LST ↑true) .BRK ↑false

/-- The necessity presupposition (32i) of (34a) holds, NRV being causally necessary (Def 10b) for
MSG. -/
theorem nrv_necessary_for_msg :
    Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .MSG true :=
  ⟨by decide, by decide, ⟨_, .refl _, by decide, by decide⟩, fun _ _ hc h ↦ nrv_of_msg hc h⟩

/-- (34a) *Dreyfus dared to send a message to the Germans* is felicitous. NRV is the only
undetermined condition for MSG, so it is both causally necessary and sufficient for it, and both
presuppositions of two-way *dare* (Proposal 32 i, iii) are satisfied in context. -/
theorem dare_felicitous_for_msg :
    Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .MSG true ∧
    manageSem dreyfusModel dreyfusBg .NRV true .MSG true :=
  ⟨nrv_necessary_for_msg, nrv_sufficient_for_msg⟩

/-- (34c) *?/# Dreyfus dared to establish communication with the Germans* is infelicitous. NRV is
not causally sufficient for COM, which stays unsettled while LST and BRK are unresolved in the
background. -/
theorem dare_infelicitous_for_com : failSem dreyfusModel dreyfusBg .NRV true .COM true := by
  decide

/-- (34d) *?/# Dreyfus dared to spy for the Germans* is infelicitous. NRV is not causally
sufficient for SPY, whose conditions LST, BRK and COM are all undetermined. -/
theorem dare_infelicitous_for_spy : failSem dreyfusModel dreyfusBg .NRV true .SPY true := by
  decide

/-- In (34c) NRV is nevertheless causally necessary for COM. Achievability settles the exogenous
LST = 1 and BRK = 0, and every path to COM = 1 runs through NRV = 1. -/
theorem nrv_necessary_for_com :
    Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .COM true :=
  ⟨by decide, by decide, ⟨resolved, by decide, by decide, by decide⟩, fun _ hset hc h ↦
    nrv_of_msg (hset.eq_bot (by decide) ⟨.INT, by decide⟩) (msg_of_com hc h)⟩

/-- In (34d) NRV is nevertheless causally necessary for SPY. -/
theorem nrv_necessary_for_spy :
    Implicative.necessityPresup dreyfusModel dreyfusBg .NRV true .SPY true :=
  ⟨by decide, by decide, ⟨resolved, by decide, by decide, by decide⟩, fun _ hset hc h ↦
    nrv_of_msg (hset.eq_bot (by decide) ⟨.INT, by decide⟩)
      (msg_of_com (hset.eq_bot (by decide) ⟨.MSG, by decide⟩) (com_of_spy hc h))⟩

/-- NRV is causally necessary but not sufficient for COM and for SPY, the verdicts on (34c) and
(34d). -/
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

/-- (34b) *Dreyfus did not dare to send a message* precludes the message, the negative half of
Fact B: no exogenous settlement of the negative-assertion context realizes MSG. -/
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
def Row.ofDatum (e : Datum) : Option Row := do
  let k ← e.parse? "verb" (finnish.map fun p ↦ (p.1.form, p.2))
  let neg ← e.parse? "matrix" [("positive", false), ("negated", true)]
  let ent ← e.parse? "entails"
    [("complement", some true), ("negation", some false), ("nothing", none)]
  some ⟨k, neg, ent⟩

/-- Every example is a row. -/
theorem isSome_ofDatum : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome := by
  decide

/-- The rows of the paper's Finnish minimal pairs. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

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
