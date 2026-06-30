import Linglib.Semantics.Aspect.Cumulativity
import Linglib.Semantics.Events.Adjacency
import Linglib.Semantics.Spatial.Trace
import Linglib.Features.Aktionsart
import Linglib.Data.Examples.Krifka1998
import Mathlib.Data.Finset.Basic

/-!
# [krifka-1998] *The Origins of Telicity*

Exercises the K98 incrementality (§3) and movement (§4) substrate with the
paper's deepest results: CUM/QUA propagation, telicity by initial/final parts,
and the path-bounded movement-relation analysis.

The substrate predicates (MO, MSO, MSE, SINC, INC, CumTheta — K98 §3.2) live
in `Semantics/Events/`; the σ-trace pullback in `Semantics/Spatial/Trace.lean`.
This file inlines the §4 movement-relation predicates (formerly in
`Semantics/Events/MovementRelations.lean`).

## Main definitions

* `IsInitialPart` / `IsFinalPart` / `IsTelic` — K98 §2.5 telicity, with
  `isTelic_of_qua` the `QUA → TEL` direction.
* `EXP` / `SEINC` / `ADJ` / `SMR` / `MovementClosure` / `MR` — K98 §4 movement
  substrate (TANG_H-free), with `mr_of_smr` and the `Event Time` instantiations
  `expEv` / `seincEv` / `smrPath` / `mrPath`.

## Main statements

* `eat_apples_cum_propositional` / `eat_two_apples_qua_propositional` — K98 §3.3
  CUM/QUA propagation on abstract θ, fired on a constructive `IsSincVerb` toy
  (`eat_two_apples_toy_qua`, `eat_some_apples_toy_cum`).
* `telic_licenses_inX` / `durative_atelic_licenses_forX` — §3 for/in diagnostics.
* `walked_from_to_telic_propositional` / `walked_towards_atelic_propositional` —
  σ-pullback backing the *walked from X to Y* / *walked towards X* analyses.
* `pathShapeToTelicity_matches_motionData` — the substrate reproduces the §4.5
  path-shape → telicity judgments of the `Data.Examples.Krifka1998` motion rows.

## TODO

* TEL ⊋ QUA strict witness: a telic non-QUA predicate (K98's 3-to-4-pm case)
  needs a concrete event model; `isTelic_of_qua` covers only `QUA → TEL`.
* TANG_H tangentiality (K98 eq. 17) on directed paths, without which `MR`
  admits telekinetic concatenations (K98 eq. 70.c).
* Cross-dimensional movements (K98 §4.6: heat, bake, whip).
* Full ADJ axioms on adjacency (K98 §2.3 eq. 14.b).
-/

namespace Krifka1998

open Features
open _root_.Mereology
open Semantics.ArgumentStructure (UP CumTheta IsCumThetaVerb)
open Semantics.Aspect.Incremental (SINC IsSincVerb IsIncVerb)
open Semantics.Aspect.Cumulativity (VP cum_propagation qua_propagation)
open Semantics.Spatial (Trace)
open Features (forXPrediction inXPrediction)

/-! ### K98 §3.3 propagation (typeclass form)

    `cum_propagation` / `qua_propagation` on abstract θ + OBJ instances. -/

section PropositionalPropagation

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- *eat apples* (K98 §3.3): a CUM object through any θ propagates to a CUM VP. -/
theorem eat_apples_cum_propositional
    {θ : α → β → Prop} [IsCumThetaVerb θ]
    {Apples : α → Prop} (hApples : CUM Apples) :
    CUM (VP θ Apples) :=
  cum_propagation hApples

/-- *eat two apples* (K98 §3.3): a QUA object through a SINC verb gives a QUA VP. -/
theorem eat_two_apples_qua_propositional
    {θ : α → β → Prop} [IsSincVerb θ]
    {TwoApples : α → Prop} (hTwoApples : QUA TwoApples) :
    QUA (VP θ TwoApples) :=
  qua_propagation hTwoApples

end PropositionalPropagation

/-! ### Diagnostic Bridge -/

/-! CUM/QUA → for/in diagnostic compatibility: atelic (CUM) VPs accept
    "for X", telic (QUA) VPs accept "in X". -/

/-- Telic VPs (QUA) license "in X" adverbials. -/
theorem telic_licenses_inX (c : VendlerClass) (h : c.telicity = .telic) :
    inXPrediction c = .accept := by
  cases c <;> simp_all [VendlerClass.telicity, inXPrediction]

/-- Durative atelic (CUM) VPs license "for X" adverbials. -/
theorem durative_atelic_licenses_forX (c : VendlerClass)
    (h : c.telicity = .atelic) (hd : c.duration = .durative) :
    forXPrediction c = .accept := by
  cases c <;> simp_all [VendlerClass.telicity, VendlerClass.duration, forXPrediction]

/-! ### Concrete `IsSincVerb` Toy + Applied Propagation -/

section ToyEatInstance

/-- Toy 3-apple universe: `Finset (Fin 3)` with ⊔ = ∪ and ≤/< as ⊆/⊊. -/
abbrev Apple : Type := Finset (Fin 3)

/-- Toy eating event, identified with the set of apples eaten (same lattice as `Apple`). -/
abbrev EatEvent : Type := Finset (Fin 3)

/-- The identity theme `eatThemeToy a e := a = e`, the canonical SINC example. -/
def eatThemeToy (a : Apple) (e : EatEvent) : Prop := a = e

/-- The SINC structure for `eatThemeToy`; every condition follows from the identity. -/
private def eatThemeToy_sinc : SINC eatThemeToy where
  mso := fun x e e' hθ hlt => ⟨e', by rw [hθ]; exact hlt, rfl⟩
  uo := fun x e e' hθ hle => ⟨e', by rw [hθ]; exact hle, rfl, fun z _ hz => hz⟩
  mse := fun x e y hθ hlt => ⟨y, by rw [← hθ]; exact hlt, rfl⟩
  ue := fun x e y hθ hle => ⟨y, by rw [← hθ]; exact hle, rfl, by intro e'' _ he''; exact he''.symm⟩
  extended := ⟨{0, 1}, {0}, {0, 1}, {0}, by decide, by decide, rfl, rfl⟩

/-- `eatThemeToy` is a strictly incremental verb-theme relation (via `IsSincVerb.mk'`). -/
instance : IsSincVerb eatThemeToy :=
  IsSincVerb.mk' eatThemeToy_sinc
    (by intro x y e hx hy; rw [hx, hy])
    (by intro x y e e' hx hy; show x ⊔ y = e ⊔ e'; rw [hx, hy])

/-! #### Concrete OBJ predicates -/

/-- "two specific apples": the singleton predicate `(· = {0, 1})`, QUA. -/
def twoApples : Apple → Prop := fun a => a = ({0, 1} : Finset (Fin 3))

/-- "(some) apples": non-emptiness, the toy's CUM bare plural. -/
def someApples : Apple → Prop := fun a => a.Nonempty

/-- `twoApples` is QUA: a singleton predicate is trivially an antichain. -/
theorem twoApples_qua : QUA twoApples :=
  -- `twoApples` is the singleton predicate `(· = {0,1})`, trivially an antichain.
  Mereology.qua_of_forall fun x y hx hlt hy => by rw [hx, hy] at hlt; exact hlt.ne rfl

/-- `someApples` is CUM: nonempty ⊔ nonempty is nonempty. -/
theorem someApples_cum : CUM someApples := by
  intro x hx y _hy
  -- hx : x.Nonempty ⇒ x ⊔ y = x ∪ y is nonempty
  exact hx.mono (by intro a ha; exact Finset.mem_union.mpr (Or.inl ha))

/-! #### K98 §3.3 propagation theorems fire on the toy -/

/-- *eat two apples* on the toy: SINC verb + QUA object → QUA VP. -/
theorem eat_two_apples_toy_qua : QUA (VP eatThemeToy twoApples) :=
  qua_propagation twoApples_qua

/-- *eat (some) apples* on the toy: CumTheta verb + CUM object → CUM VP. -/
theorem eat_some_apples_toy_cum : CUM (VP eatThemeToy someApples) :=
  cum_propagation someApples_cum

end ToyEatInstance

section Telicity

variable {β : Type*} [PartialOrder β] (precedes : β → β → Prop)

/-- K98 §2.5 eq. 36 INI: `e' ≤ e` and no part of `e` precedes `e'` (printed `≤D` read as `≤`). -/
def IsInitialPart (e' e : β) : Prop :=
  e' ≤ e ∧ ¬ ∃ e'', e'' ≤ e ∧ precedes e'' e'

/-- K98 §2.5 eq. 36 FIN: `e' ≤ e` and no part of `e` follows `e'`. -/
def IsFinalPart (e' e : β) : Prop :=
  e' ≤ e ∧ ¬ ∃ e'', e'' ≤ e ∧ precedes e' e''

/-- The whole is an initial part of itself when no part of it precedes it. -/
theorem isInitialPart_self (e : β) (h : ¬ ∃ e'', e'' ≤ e ∧ precedes e'' e) :
    IsInitialPart precedes e e :=
  ⟨le_rfl, h⟩

/-- The whole is a final part of itself when no part of it follows it. -/
theorem isFinalPart_self (e : β) (h : ¬ ∃ e'', e'' ≤ e ∧ precedes e e'') :
    IsFinalPart precedes e e :=
  ⟨le_rfl, h⟩

/-- K98 §2.5 eq. 37 TEL: every P-part of a P-instance is its initial and final part. -/
def IsTelic (P : β → Prop) : Prop :=
  ∀ e e', P e → P e' → e' ≤ e → IsInitialPart precedes e' e ∧ IsFinalPart precedes e' e

/-- K98 §2.5: quantized predicates are telic (`QUA → TEL`), given `hax` (K98 eq. 35). -/
theorem isTelic_of_qua {P : β → Prop}
    (hax : ∀ a b : β, a ≤ b → ¬ precedes a b ∧ ¬ precedes b a) (hQ : QUA P) :
    IsTelic precedes P := by
  intro e e' hPe hPe' hle
  have heq : e' = e := by by_contra hne; exact hQ hPe' hPe hne hle
  rw [heq]
  exact ⟨isInitialPart_self precedes e fun ⟨e'', h, hp⟩ => (hax e'' e h).1 hp,
         isFinalPart_self precedes e fun ⟨e'', h, hp⟩ => (hax e'' e h).2 hp⟩

end Telicity

/-! ### K98 §4 propositional substrate -/

section K98PropositionalSubstrate

open Semantics.ArgumentStructure (MO)

/-- K98 §4.1 eq. 63 EXP: θ-arguments of temporally-ordered events do not overlap. -/
def EXP {α β : Type*} [SemilatticeSup α]
    (precedes : β → β → Prop) (θ : α → β → Prop) : Prop :=
  ∀ (x y : α) (e e' : β),
    θ x e → θ y e' → precedes e e' → ¬ Overlap x y

/-- K98 §4.1 eq. 65 SEINC: strictly expansive incremental. EXP ∧ MO. -/
def SEINC {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ : α → β → Prop) : Prop :=
  EXP precedes θ ∧ MO θ

/-- K98 §4.2 eq. 68 ADJ: sub-event temporal adjacency ↔ sub-path spatial adjacency. -/
def ADJ {α β : Type*} [PartialOrder α] [PartialOrder β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop)
    (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y z : α) (e' e'' : β),
    θ x e → e' ≤ e → e'' ≤ e → y ≤ x → z ≤ x →
    θ y e' → θ z e'' → (adjβ e' e'' ↔ adjα y z)

/-- K98 §4.2 eq. 69 SMR: ADJ + MO + first-arg constrained to paths. -/
def SMR {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop)
    (isPath : α → Prop) (θ : α → β → Prop) : Prop :=
  ADJ adjα adjβ θ ∧ MO θ ∧ ∀ x e, θ x e → isPath x

/-- K98 §4.3 eq. 71: smallest θ-extension closed under precedence-respecting sums. -/
abbrev MovementClosure {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ' : α → β → Prop) : α → β → Prop :=
  Semantics.Aspect.PrecedenceClosure precedes θ'

/-- K98 §4.3 eq. 71 MR (TANG_H-free): θ is the `MovementClosure` of some SMR θ'. -/
def MR {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    (adjα : α → α → Prop) (adjβ : β → β → Prop) (precedes : β → β → Prop)
    (isPath : α → Prop) (θ : α → β → Prop) : Prop :=
  ∃ θ' : α → β → Prop,
    SMR adjα adjβ isPath θ' ∧
    ∀ x e, θ x e ↔ MovementClosure precedes θ' x e

/-- Every SMR is itself an MR, given closure under precedence-respecting sums. -/
theorem mr_of_smr {α β : Type*} [PartialOrder α] [PartialOrder β]
    [SemilatticeSup α] [SemilatticeSup β]
    {adjα : α → α → Prop} {adjβ : β → β → Prop} {precedes : β → β → Prop}
    {isPath : α → Prop} {θ : α → β → Prop}
    (h : SMR adjα adjβ isPath θ)
    (hClosed : ∀ x1 x2 e1 e2, θ x1 e1 → θ x2 e2 → precedes e1 e2 →
               θ (x1 ⊔ x2) (e1 ⊔ e2)) :
    MR adjα adjβ precedes isPath θ :=
  ⟨θ, h, fun x e => ⟨Semantics.Aspect.PrecedenceClosure.base,
    fun hcl => Semantics.Aspect.PrecedenceClosure.closure_subset
      (fun _ _ h => h) hClosed hcl⟩⟩

end K98PropositionalSubstrate

/-! ### σ-pullback invocations (bounded/unbounded path → telic/atelic VP) -/

section SpatialTracePullback

open Semantics.Spatial.Path

variable {Loc Time : Type*} [LinearOrder Time]
variable [Event.Mereology Time] [ClassicalMereology (Event Time)] [SemilatticeSup (Path Loc)]
variable [st : Trace Loc Time]

/-- Bounded path (QUA) ↦ telic VP via the σ-pullback (K98 §4.5 *walked from X to Y*). -/
theorem walked_from_to_telic_propositional
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    QUA (P ∘ st.σ) :=
  Trace.bounded_path_telic hinj hP

/-- Unbounded path (CUM) ↦ atelic VP via the σ-pullback (K98 §4.5 *walked towards X*). -/
theorem walked_towards_atelic_propositional
    {P : Path Loc → Prop} (hP : CUM P) :
    CUM (P ∘ st.σ) :=
  Trace.unbounded_path_atelic hP

end SpatialTracePullback

/-! ### K98 §4.5 motion data: path shape predicts telicity -/

section MotionData

open Data.Examples (LinguisticExample)
open Semantics.Spatial.Path (PathShape)
open Semantics.Spatial.Trace (pathShapeToTelicity)

/-- A motion VP datum: the path shape K98 assigns and the telicity it predicts. -/
structure MotionDatum where
  pathShape : PathShape
  expectedTelicity : Telicity
  deriving DecidableEq, Repr

private def parsePathShape : String → Option PathShape
  | "bounded" => some .bounded
  | "source" => some .source
  | "unbounded" => some .unbounded
  | _ => none

private def parseTelicity : String → Option Telicity
  | "telic" => some .telic
  | "atelic" => some .atelic
  | _ => none

/-- Lift a `Data.Examples.Krifka1998` row to a `MotionDatum` via its paper features. -/
def fromExample (e : LinguisticExample) : Option MotionDatum := do
  let ps ← parsePathShape (← e.paperFeatures.lookup "pathShape")
  let tel ← parseTelicity (← e.paperFeatures.lookup "expectedTelicity")
  some { pathShape := ps, expectedTelicity := tel }

/-- The K98 §4.5 motion VP data, lifted from the JSON example rows. -/
def motionData : List MotionDatum :=
  Examples.all.filterMap fromExample

/-- `pathShapeToTelicity` reproduces the paper's telicity for every motion VP. -/
theorem pathShapeToTelicity_matches_motionData :
    ∀ d ∈ motionData, pathShapeToTelicity d.pathShape = d.expectedTelicity := by
  decide

end MotionData

/-! ### EXP / SEINC instances on `Event Time` (K98 §4.1) -/

section Expansiveness

variable {α : Type*} [SemilatticeSup α]
variable {Time : Type*} [LinearOrder Time]

/-- EXP-as-property of any θ : α → Event Time → Prop using `Event.precedes`. -/
abbrev expEv (θ : α → Event Time → Prop) : Prop :=
  EXP (Event.precedes (Time := Time)) θ

/-- SEINC-as-property of θ over `Event Time` using `Event.precedes`. -/
abbrev seincEv [Event.Mereology Time] [ClassicalMereology (Event Time)]
    (θ : α → Event Time → Prop) : Prop :=
  SEINC (Event.precedes (Time := Time)) θ

end Expansiveness

/-! ### SMR / MR instances on `Path Loc → Event Time → Prop` (K98 §4.2-4.3) -/

section MovementInstances

open Semantics.Spatial.Path

variable {Loc Time : Type*} [LinearOrder Time]
variable [Event.Mereology Time] [ClassicalMereology (Event Time)]
variable [PartialOrder (Path Loc)] [SemilatticeSup (Path Loc)]

/-- SMR specialized to paths and events with concrete adjacency. -/
abbrev smrPath (θ : Path Loc → Event Time → Prop) : Prop :=
  SMR Path.adjacent (Event.adjacent (Time := Time))
    (fun _ : Path Loc => True) θ

/-- MR specialized to paths and events with concrete adjacency + precedence. -/
abbrev mrPath (θ : Path Loc → Event Time → Prop) : Prop :=
  MR Path.adjacent (Event.adjacent (Time := Time)) (Event.precedes (Time := Time))
    (fun _ : Path Loc => True) θ

end MovementInstances

end Krifka1998
