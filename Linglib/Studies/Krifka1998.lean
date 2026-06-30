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

/-- *eat apples* propositional: K98 §3.3 CUM propagation. Given any
    `[IsCumThetaVerb θ]` (eat's role — and any of the K98 verb classes
    via upward instances) and a CUM object (apples), VP is CUM. -/
theorem eat_apples_cum_propositional
    {θ : α → β → Prop} [IsCumThetaVerb θ]
    {Apples : α → Prop} (hApples : CUM Apples) :
    CUM (VP θ Apples) :=
  cum_propagation hApples

/-- *eat two apples* propositional: K98 §3.3 QUA propagation. Given
    `[IsSincVerb θ]` (eat's role, bundling SINC + UP) and a QUA
    object (two apples), VP is QUA. -/
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

/-- Durative atelic VPs (CUM + durative) license "for X" adverbials.
    Semelfactives are atelic but punctual — "for X" coerces to iterative. -/
theorem durative_atelic_licenses_forX (c : VendlerClass)
    (h : c.telicity = .atelic) (hd : c.duration = .durative) :
    forXPrediction c = .accept := by
  cases c <;> simp_all [VendlerClass.telicity, VendlerClass.duration, forXPrediction]

/-! ### Concrete `IsSincVerb` Toy + Applied Propagation -/

/-! `eat_apples_cum_propositional` / `eat_two_apples_qua_propositional` are
    parametric over abstract θ; here a constructive `IsSincVerb` instance
    *fires* both, showing K98 §3.3's typeclass-bundled postulates admit
    non-axiomatic realizations.

    The toy: a 3-apple universe `Finset (Fin 3)` (⊔ = ∪, < = ⊊), with the
    identity theme `eatThemeToy a e := a = e` giving the SINC bijection. It is
    a toy, not a faithful denotation of *eat*. -/

section ToyEatInstance

/-- Toy 3-apple universe. `Finset (Fin 3)` carries `SemilatticeSup`
    automatically (join is `Finset.union`); `≤`/`<` are `⊆`/`⊊`. -/
abbrev Apple : Type := Finset (Fin 3)

/-- Toy "eating event" — identified with the set of apples eaten.
    Same powerset lattice as `Apple`, yielding the bijection that
    SINC requires. -/
abbrev EatEvent : Type := Finset (Fin 3)

/-- The identity-as-relation theme: `eatThemeToy a e` iff the apple
    set `a` equals the apple set eaten in event `e`. The canonical
    SINC example, exhibiting a 1-1 correspondence between proper
    sub-objects (subsets of `a`) and proper sub-events. -/
def eatThemeToy (a : Apple) (e : EatEvent) : Prop := a = e

/-- The SINC structure for `eatThemeToy`: all five conditions follow from
    the identity, with `extended` witnessed by `{0} ⊂ {0, 1}`. -/
private def eatThemeToy_sinc : SINC eatThemeToy where
  mso := by
    intro x e e' hθ hlt
    refine ⟨e', ?_, rfl⟩
    rw [hθ]; exact hlt
  uo := by
    intro x e e' hθ hle
    refine ⟨e', ?_, rfl, ?_⟩
    · rw [hθ]; exact hle
    · intro z _ hz; exact hz
  mse := by
    intro x e y hθ hlt
    refine ⟨y, ?_, rfl⟩
    rw [← hθ]; exact hlt
  ue := by
    intro x e y hθ hle
    refine ⟨y, ?_, rfl, ?_⟩
    · rw [← hθ]; exact hle
    · intro e'' _ he''; exact he''.symm
  extended := by
    refine ⟨{0, 1}, {0}, {0, 1}, {0}, ?_, ?_, rfl, rfl⟩ <;> decide

/-- UP for `eatThemeToy`: identity-as-relation gives x = y trivially. -/
private theorem eatThemeToy_up : UP eatThemeToy := by
  intro x y e hx hy
  show x = y
  rw [hx, hy]

/-- CumTheta for `eatThemeToy`: identity-as-relation preserves sums. -/
private theorem eatThemeToy_cumTheta : CumTheta eatThemeToy := by
  intro x y e e' hx hy
  show x ⊔ y = e ⊔ e'
  rw [hx, hy]

/-- `eatThemeToy` is a strictly incremental verb-theme relation.
    Constructed via the `IsSincVerb.mk'` smart constructor, which
    derives the inherited `inc : INC eatThemeToy` field automatically
    via `inc_of_sinc`. -/
instance : IsSincVerb eatThemeToy :=
  IsSincVerb.mk' eatThemeToy_sinc eatThemeToy_up eatThemeToy_cumTheta

/-- Synthesis test: `[IsIncVerb eatThemeToy]` is auto-synthesised from
    the `IsSincVerb` instance via the `extends` chain (K98 §3.6:
    "every SINC verb is also INC"). Fires without explicit derivation. -/
example : IsIncVerb eatThemeToy := inferInstance

/-- Synthesis test: `[IsCumThetaVerb eatThemeToy]` is auto-synthesised
    from the `IsSincVerb` instance via the `extends` chain transitively. -/
example : IsCumThetaVerb eatThemeToy := inferInstance

/-! #### Concrete OBJ predicates -/

/-- "two specific apples" — the singleton predicate `λ a, a = {0, 1}`.
    QUA: no proper subset of `{0, 1}` is also `{0, 1}`. -/
def twoApples : Apple → Prop := fun a => a = ({0, 1} : Finset (Fin 3))

/-- "(some) apples" — non-emptiness in the powerset lattice. CUM:
    nonempty ∪ nonempty is nonempty. The natural bare-plural
    interpretation in this toy. -/
def someApples : Apple → Prop := fun a => a.Nonempty

/-- `twoApples` is QUA: a proper part of `{0, 1}` cannot also equal
    `{0, 1}`. This is the standard "exact-cardinality NPs are
    quantized" property at the K89/K98 level. -/
theorem twoApples_qua : QUA twoApples :=
  -- `twoApples` is the singleton predicate `(· = {0,1})`, trivially an antichain.
  Mereology.qua_of_forall fun x y hx hlt hy => by rw [hx, hy] at hlt; exact hlt.ne rfl

/-- `someApples` is CUM: nonempty ⊔ nonempty = nonempty. Bare plurals
    propagate cumulativity (K89 §3 / K98 §3.3). -/
theorem someApples_cum : CUM someApples := by
  intro x hx y _hy
  -- hx : x.Nonempty ⇒ x ⊔ y = x ∪ y is nonempty
  exact hx.mono (by intro a ha; exact Finset.mem_union.mpr (Or.inl ha))

/-! #### K98 §3.3 propagation theorems fire on the toy -/

/-- *eat two apples* on the toy: SINC + UP verb + QUA object → QUA VP.
    Direct invocation of substrate's typeclass-canonical
    `qua_propagation`; `[IsSincVerb eatThemeToy]` synthesises
    automatically from the instance above. -/
theorem eat_two_apples_toy_qua : QUA (VP eatThemeToy twoApples) :=
  qua_propagation twoApples_qua

/-- *eat (some) apples* on the toy: CumTheta verb + CUM object → CUM VP.
    Direct invocation of substrate's `cum_propagation`;
    `[IsCumThetaVerb eatThemeToy]` synthesises from `[IsSincVerb …]`
    via `instIsCumThetaVerbOfIsSincVerb`. -/
theorem eat_some_apples_toy_cum : CUM (VP eatThemeToy someApples) :=
  cum_propagation someApples_cum

end ToyEatInstance

/-! ## Part II — K98 §4: Telicity by Precedence and Adjacency -/

/-! ### K98 §2.5 — Initial/final parts and telicity (TEL)

K98 §2.5 eq. 36 defines the initial/final parts of an event via the precedence
relation `«E`; eq. 37 defines telicity (TEL): every P-part of a P-event is both
an initial and a final part of it. TEL is strictly weaker than `QUA` — every
quantized predicate is telic (`isTelic_of_qua`), but not conversely (K98's
3-to-4-pm predicate). Generic over a part order and a precedence relation,
mirroring the §4 substrate; specialize with `Event.precedes`. -/

section Telicity

variable {β : Type*} [PartialOrder β] (precedes : β → β → Prop)

/-- K98 §2.5 eq. 36 INI: `e'` is an initial part of `e` iff `e' ≤ e` and no
    part of `e` precedes `e'`. Krifka prints the outer relation as `≤D`, but
    the event signature carries only event parthood and the prose says *part
    of e* — so both relations are the single part order `≤`. -/
def IsInitialPart (e' e : β) : Prop :=
  e' ≤ e ∧ ¬ ∃ e'', e'' ≤ e ∧ precedes e'' e'

/-- K98 §2.5 eq. 36 FIN: `e'` is a final part of `e` iff `e' ≤ e` and no
    part of `e` follows `e'`. -/
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

/-- K98 §2.5 eq. 37 telicity (TEL): a predicate `P` is telic iff every P-part
    `e'` of a P-instance `e` is both an initial and a final part of `e`.
    Telicity is a property of `P`, not of any particular event. -/
def IsTelic (P : β → Prop) : Prop :=
  ∀ e e', P e → P e' → e' ≤ e → IsInitialPart precedes e' e ∧ IsFinalPart precedes e' e

/-- K98 §2.5: quantized predicates are telic (the `QUA → TEL` half of
    TEL ⊋ QUA). A `QUA` predicate's only P-part of `e` is `e` itself, which is
    its own initial and final part provided no part of `e` precedes it — K98
    eq. 35, here `hax`. `Event.precedes` does not satisfy `hax` (`isBefore`
    uses `≤`, so it is reflexive on points; the strict `<` form would). -/
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

/-- K98 §4.1 eq. 63 EXP: expansion. If x is θ-related to e and y to a
    temporally-following e', then x and y do not overlap. -/
def EXP {α β : Type*} [SemilatticeSup α]
    (precedes : β → β → Prop) (θ : α → β → Prop) : Prop :=
  ∀ (x y : α) (e e' : β),
    θ x e → θ y e' → precedes e e' → ¬ Overlap x y

/-- K98 §4.1 eq. 65 SEINC: strictly expansive incremental. EXP ∧ MO. -/
def SEINC {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ : α → β → Prop) : Prop :=
  EXP precedes θ ∧ MO θ

/-- K98 §4.2 eq. 68 ADJ: temporal adjacency on sub-events ↔ spatial
    adjacency on sub-paths. The Lean form adds extra `z ≤ x` and
    `e'' ≤ e` premises vs the printed equation. -/
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

/-- K98 §4.3 eq. 71 closure: smallest relation containing θ' and closed
    under precedence-respecting sums. K98's TANG_H clause (eq. 17) is
    OMITTED — see module TODO. Specialization of
    `Semantics.Aspect.PrecedenceClosure` with `cond := precedes`. -/
abbrev MovementClosure {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (precedes : β → β → Prop) (θ' : α → β → Prop) : α → β → Prop :=
  Semantics.Aspect.PrecedenceClosure precedes θ'

/-- K98 §4.3 eq. 71 MR (TANG_H-free): θ is a movement relation iff
    there exists an SMR θ' such that θ is the `MovementClosure` of θ'. -/
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

/-- Bounded path predicate (QUA) ↦ telic VP via the σ-pullback. Backs
    the K98 §4.5 *walked from X to Y* analysis at the Bool-tag level. -/
theorem walked_from_to_telic_propositional
    (hinj : Function.Injective st.σ)
    {P : Path Loc → Prop} (hP : QUA P) :
    QUA (P ∘ st.σ) :=
  Trace.bounded_path_telic hinj hP

/-- Unbounded path predicate (CUM) ↦ atelic VP via the σ-pullback. Backs
    the K98 §4.5 *walked towards X* analysis at the Bool-tag level. -/
theorem walked_towards_atelic_propositional
    {P : Path Loc → Prop} (hP : CUM P) :
    CUM (P ∘ st.σ) :=
  Trace.unbounded_path_atelic hP

end SpatialTracePullback

/-! ### K98 §4.5 motion data: path shape predicts telicity

    Each `Data.Examples.Krifka1998` motion VP row tags its path shape and the
    paper's telicity judgment; the substrate `pathShapeToTelicity` reproduces
    every judgment. -/

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

/-- Lift a `Data.Examples.Krifka1998` row to a `MotionDatum` via its
    `pathShape` / `expectedTelicity` paper features. -/
def fromExample (e : LinguisticExample) : Option MotionDatum := do
  let ps ← parsePathShape (← e.paperFeatures.lookup "pathShape")
  let tel ← parseTelicity (← e.paperFeatures.lookup "expectedTelicity")
  some { pathShape := ps, expectedTelicity := tel }

/-- The K98 §4.5 motion VP data, lifted from the JSON example rows. -/
def motionData : List MotionDatum :=
  Examples.all.filterMap fromExample

/-- Substrate prediction: `pathShapeToTelicity` reproduces the paper's telicity
    judgment for every motion VP (bounded/source → telic, unbounded → atelic). -/
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

/-- SEINC-as-property using `Event.precedes`. The derived
    `[SemilatticeSup (Event Time)]` comes from `[ClassicalMereology (Event Time)]`. -/
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
