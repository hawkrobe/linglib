import Linglib.Discourse.Centering.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Nat
/-!
# Centering Theory — Transitions
[grosz-joshi-weinstein-1995]
The three transition types (continuation / retaining / shifting) and
their classification. `classifyTransitionStrict` is faithful to GJW
Def 4; `classifyTransitionExtended` applies the worked-example
convention for the segment-initial case.
-/
set_option autoImplicit false
namespace Discourse.Centering
/-! ### Transition Type -/
/-- Three transition types between consecutive utterances
    ([grosz-joshi-weinstein-1995] Def 4). -/
inductive Transition where
  | continuation
  | retaining
  | shifting
  deriving DecidableEq, Repr
/-- Rule 2 preference order: continuation > retaining > shifting. -/
@[simp] def Transition.rank : Transition → Nat
  | .continuation => 2
  | .retaining    => 1
  | .shifting     => 0
/-- LinearOrder via rank, exposing `<`, `≤`, `max` for Rule 2 statements. -/
instance : LinearOrder Transition :=
  LinearOrder.lift' Transition.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [Transition.rank])
theorem continuation_gt_retaining :
    (Transition.continuation : Transition) > .retaining := by decide
theorem retaining_gt_shifting :
    (Transition.retaining : Transition) > .shifting := by decide
/-! ### Strict and Extended Classification -/
variable {E R : Type*}
/-- Internal classifier given both Cbs: equal Cbs continue/retain
    by Cp alignment; unequal Cbs shift. -/
def classifyTransitionInternal [DecidableEq E]
    (curCb : E) (curCp : Option E) (prevCb : E) : Transition :=
  if prevCb = curCb then
    if curCp = some curCb then .continuation else .retaining
  else .shifting
/-- Strict classification (faithful to GJW Def 4): returns `none` in
    the segment-initial case where the prior Cb is undefined. -/
def classifyTransitionStrict
    [DecidableEq E] [CfRankerOf E R] {U : Type*} [Realizes U E]
    (prev : Utterance E R) (cur : U) (curCp : Option E)
    (prevCb : Option E) : Option Transition :=
  match cb prev cur, prevCb with
  | none, _      => some .shifting
  | _, none      => none  -- segment-initial: paper Def 4 is silent
  | some curCb, some pcb => some (classifyTransitionInternal curCb curCp pcb)
/-- Extended classification: applies the worked-example convention
    for the segment-initial case (treats missing prior Cb as if equal
    to current Cb). -/
def classifyTransitionExtended
    [DecidableEq E] [CfRankerOf E R] {U : Type*} [Realizes U E]
    (prev : Utterance E R) (cur : U) (curCp : Option E)
    (prevCb : Option E) : Transition :=
  match cb prev cur with
  | none => .shifting
  | some curCb =>
    classifyTransitionInternal curCb curCp (prevCb.getD curCb)
/-- The two classifications agree whenever the strict variant is
    defined. -/
theorem extended_eq_strict_when_defined
    [DecidableEq E] [CfRankerOf E R] {U : Type*} [Realizes U E]
    (prev : Utterance E R) (cur : U) (curCp : Option E)
    (prevCb : Option E) (t : Transition)
    (h : classifyTransitionStrict prev cur curCp prevCb = some t) :
    classifyTransitionExtended prev cur curCp prevCb = t := by
  unfold classifyTransitionStrict at h
  unfold classifyTransitionExtended
  match hcb : cb prev cur, prevCb with
  | none, _ =>
    simp only [hcb] at h ⊢
    cases h
    rfl
  | some _, none =>
    simp only [hcb] at h
    cases h
  | some _, some _ =>
    simp only [hcb] at h ⊢
    exact Option.some.inj h
end Discourse.Centering
