import Linglib.Theories.Discourse.Coherence.Centering.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Nat

/-!
# Centering Theory — Transitions
@cite{grosz-joshi-weinstein-1995} §3, §4

The three transition types and their classification, split into a
**strict** version (paper Definition 4) and an **extended** version
(paper convention for the segment-initial case).

## Why a split?

@cite{grosz-joshi-weinstein-1995} Definition 4 only classifies
transitions where both `Cb(U_n)` and `Cb(U_{n+1})` exist. The paper
also discusses **segment-initial transitions** where the prior Cb is
undefined; for these, the worked examples (e.g., Discourses 1 and 20)
implicitly use a "treat-as-continuation when Cb=Cp" convention. We
make this distinction explicit:

* `classifyTransitionStrict` — returns `Option Transition`, returning
  `none` precisely when the paper's Definition 4 is silent.
* `classifyTransitionExtended` — total function with the
  segment-initial convention applied.

The earlier monolithic `classifyTransition` (in the study file) was
the extended version; downstream code that needs the strict reading
should use the strict variant.

Rule 2 (transition preference: continuation > retaining > shifting)
lives in `Rules.lean`.
-/

set_option autoImplicit false

namespace Discourse.Coherence.Centering

-- ════════════════════════════════════════════════════
-- § 1. Transition Type
-- ════════════════════════════════════════════════════

/-- Three transition types between U_n and U_{n+1}
    (@cite{grosz-joshi-weinstein-1995} §3, Def 4):

    * **continuation**: `Cb(U_{n+1}) = Cb(U_n)` AND `Cb(U_{n+1})` is
      the most-highly-ranked element of `Cf(U_{n+1})`.
    * **retaining**: `Cb(U_{n+1}) = Cb(U_n)`, but is *not* the
      most-highly-ranked element of `Cf(U_{n+1})`.
    * **shifting**: `Cb(U_{n+1}) ≠ Cb(U_n)` (including the case where
      no Cb of U_{n+1} exists, by convention). -/
inductive Transition where
  | continuation
  | retaining
  | shifting
  deriving DecidableEq, Repr

/-- @cite{grosz-joshi-weinstein-1995} **Rule 2** preference order:
    continuation > retaining > shifting. -/
@[simp] def Transition.rank : Transition → Nat
  | .continuation => 2
  | .retaining    => 1
  | .shifting     => 0

/-- **Why a `LinearOrder` (not just a `Bool` comparator)?** Rule 2 is
    fundamentally a *preference* relation: given two candidate next
    utterances, the centering-preferred one is whichever yields the
    higher-ranked transition. Exposing this as `LinearOrder` (via
    `LinearOrder.lift'` over the `Nat` rank) makes `<`, `≤`, `max`,
    and `Decidable` comparisons available for free, and lets downstream
    code state Rule 2 with the standard order vocabulary instead of a
    bespoke `prefersOver : Transition → Transition → Bool`. -/
instance : LinearOrder Transition :=
  LinearOrder.lift' Transition.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [Transition.rank])

theorem continuation_gt_retaining :
    (Transition.continuation : Transition) > .retaining := by decide

theorem retaining_gt_shifting :
    (Transition.retaining : Transition) > .shifting := by decide

-- ════════════════════════════════════════════════════
-- § 2. Strict and Extended Classification
-- ════════════════════════════════════════════════════

variable {E R : Type}

/-- **Internal** transition classifier, given that *both* Cbs are
    known. Captures the segment-internal case shared by the strict and
    extended versions: equal Cbs continue/retain (depending on Cp
    alignment); unequal Cbs shift. -/
def classifyTransitionInternal [DecidableEq E]
    (curCb : E) (curCp : Option E) (prevCb : E) : Transition :=
  if prevCb = curCb then
    if curCp = some curCb then .continuation else .retaining
  else .shifting

/-- **Strict** transition classification, faithful to
    @cite{grosz-joshi-weinstein-1995} Def 4: returns `none` precisely
    when the paper's definition is silent (segment-initial case where
    the prior Cb is undefined but the current Cb exists). -/
def classifyTransitionStrict
    [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) (curCp : Option E)
    (prevCb : Option E) : Option Transition :=
  match cb prev cur, prevCb with
  | none, _      => some .shifting
  | _, none      => none  -- segment-initial: paper Def 4 is silent
  | some curCb, some pcb => some (classifyTransitionInternal curCb curCp pcb)

/-- **Extended** transition classification, applying the worked-example
    convention for the segment-initial case (paper §4): when there is
    no prior Cb, treat it as if `prevCb = curCb` so the segment-initial
    pair becomes a continuation iff the current Cb equals the current
    Cp, and a retaining otherwise.

    This matches the labels used in the paper for Discourses 1 and 20
    even though Definition 4 does not formally cover the segment-initial
    pair. -/
def classifyTransitionExtended
    [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
    (prev : Utterance E R) (cur : U) (curCp : Option E)
    (prevCb : Option E) : Transition :=
  match cb prev cur with
  | none => .shifting
  | some curCb =>
    classifyTransitionInternal curCb curCp (prevCb.getD curCb)

/-- The two classifications agree whenever the strict variant is
    defined. Both delegate to `classifyTransitionInternal` in the
    segment-internal case, so the agreement is essentially by
    construction; only the `curCb = none` and segment-initial branches
    need handling. -/
theorem extended_eq_strict_when_defined
    [DecidableEq E] [CfRanker R] {U : Type} [Realizes U E]
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

end Discourse.Coherence.Centering
