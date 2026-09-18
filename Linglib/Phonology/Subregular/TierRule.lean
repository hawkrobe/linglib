/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Option
import Linglib.Phonology.Subregular.OSL

/-!
# Tier-based alternation rules

A tier rule is [belth-2026]'s generalization `Rel(A, F) / C __ ∘ proj(·, T)`: a class `A`
of targets, a feature `F` read and written through a lens, a class `C` of triggers, a tier
`T`, the relation `Agree` or `Disagree`, an Elsewhere default, and a direction. The rule
applies iteratively over the tier: each target takes its value from the tier-adjacent
output segment when that segment is a trigger, so a written target triggers what follows.
The run is a three-state Mealy machine on the tier whose state is the value the last output
tier segment offers (`TierRule.toMealy`), and the output tier-based strictly 2-local rule of
[burness-mcmullin-2020] (`TierRule.spreadRule`, the tier form of
[chandlee-eyraud-heinz-2015]'s OSL functions) computes the same function
(`TierRule.spreadRule_applyOnTier`), so every tier rule is Mealy-computable and
subsequential in its direction, on any tier.

## Main definitions

* `TierRule`: the rule.
* `TierRule.scan`, `TierRule.apply`: the left-to-right run over the tier, and the run in
  the rule's direction.
* `TierRule.triggerValue`: the value a string passes on to what follows it.
* `TierRule.toMealy`, `TierRule.spreadRule`: the machine and the OSL rule computing the run.

## Main results

* `TierRule.spreadRule_applyOnTier`: the OSL rule run over the tier is the Mealy run.
* `TierRule.tier_scan`: restricted to the tier, the run is the 2-OSL rule.
* `TierRule.apply_isSubsequential`, `TierRule.scan_isMealyComputable`: the run is
  finite-state in the rule's direction, on any tier.

## Implementation notes

A tier segment outside `C` stops the value, and a target after it takes the default, which
is how [belth-2026]'s Khalkha rounding rule blocks; a tier segment in `C` that is not a
target imposes its own value. A trigger unspecified for `F` also yields the default, where
[belth-2026] counts a failed application. The lens laws are required on targets only, since
only targets are written. A right-context rule is the left-context rule on the reversed
string. Multi-feature dependencies, such as Turkish rounding parasitic on backness, are
not expressible: `F` is one feature.

## References

* [belth-2026]
* [burness-mcmullin-2020]
* [chandlee-eyraud-heinz-2015]
-/

namespace Subregular

/-- [belth-2026]'s `Agree` and `Disagree`: whether a target copies or negates its
trigger's value. -/
inductive Relation where
  | agree
  | disagree
  deriving DecidableEq, Repr

/-- The value the relation writes into a target from its trigger's value. -/
def Relation.act : Relation → Bool → Bool
  | .agree, v => v
  | .disagree, v => !v

/-- A tier rule consists of a tier, the triggers, the targets, the relation, a lens reading
and writing the feature on targets, an Elsewhere default, and a direction. -/
structure TierRule (α : Type*) where
  /-- The tier: the segments the rule sees. -/
  tier : α → Prop
  [decTier : DecidablePred tier]
  /-- The segments a target copies its value from. -/
  IsTrigger : α → Prop
  [decTrigger : DecidablePred IsTrigger]
  /-- The segments that alternate. -/
  IsTarget : α → Prop
  [decTarget : DecidablePred IsTarget]
  /-- Whether a target agrees or disagrees with its trigger. -/
  relation : Relation := .agree
  /-- Read the feature; `none` when the segment is unspecified for it. -/
  value : α → Option Bool
  /-- Write the feature into a segment. -/
  write : Bool → α → α
  /-- Reading back a value written into a target gives that value. -/
  value_write : ∀ v s, IsTarget s → value (write v s) = some v
  /-- Writing the value a target already carries leaves it unchanged. -/
  write_value : ∀ v s, IsTarget s → value s = some v → write v s = s
  /-- The Elsewhere value a target takes when no value reaches it. -/
  default : Option Bool := none
  /-- The direction of application; a right-context rule scans right to left. -/
  direction : ScanDirection := .left

attribute [instance] TierRule.decTier TierRule.decTrigger TierRule.decTarget

namespace TierRule

variable {α : Type*} (r : TierRule α)

/-- The value a segment offers to the next target: its value if it is a trigger, nothing
otherwise. -/
def transmits (s : α) : Option Bool := if r.IsTrigger s then r.value s else none

/-- The segment output at `s` when the value `v` has reached it. -/
def emit (v : Option Bool) (s : α) : α :=
  if r.IsTarget s then ((v.map r.relation.act).or r.default).elim s (r.write · s) else s

theorem value_eq_of_transmits_eq_some {s : α} {v : Bool} (h : r.transmits s = some v) :
    r.value s = some v := by
  unfold transmits at h; split_ifs at h; exact h

theorem emit_of_not_target {s : α} (h : ¬ r.IsTarget s) (v : Option Bool) : r.emit v s = s :=
  ite_eq_right h

theorem emit_some_of_target {s : α} (h : r.IsTarget s) (v : Bool) :
    r.emit (some v) s = r.write (r.relation.act v) s :=
  ite_eq_left h

theorem emit_none_of_default_eq_none (hd : r.default = none) (s : α) : r.emit none s = s := by
  unfold emit; rw [hd]; split_ifs <;> rfl

/-- A segment already carrying the value reaching it is emitted unchanged. -/
theorem emit_some_eq_self {s : α} {v : Bool} (h : r.value s = some (r.relation.act v)) :
    r.emit (some v) s = s := by
  unfold emit; split_ifs with ht
  · simp [r.write_value _ s ht h]
  · rfl

/-! ### The run -/

/-- The machine computing the rule, whose state is the value the last output tier segment
offers and which passes off-tier segments through untouched. -/
def toMealy : Mealy (Option Bool) α α where
  initial := none
  step v s := if r.tier s then r.transmits (r.emit v s) else v
  output v s := if r.tier s then r.emit v s else s

@[simp] theorem toMealy_initial : r.toMealy.initial = none := rfl

@[simp] theorem toMealy_step (v : Option Bool) (s : α) :
    r.toMealy.step v s = if r.tier s then r.transmits (r.emit v s) else v :=
  rfl

@[simp] theorem toMealy_output (v : Option Bool) (s : α) :
    r.toMealy.output v s = if r.tier s then r.emit v s else s :=
  rfl

/-- The left-to-right run over the tier, in which each target takes the value that reaches
it. -/
def scan : List α → List α := r.toMealy.run

/-- The run in the rule's direction. -/
def apply : List α → List α :=
  match r.direction with
  | .left => r.scan
  | .right => List.revConj r.scan

/-- The value a string passes on to what follows it in the rule's direction, the machine's
state after the string. -/
def triggerValue (w : List α) : Option Bool :=
  match r.direction with
  | .left => r.toMealy.stateAfter none w
  | .right => r.toMealy.stateAfter none w.reverse

@[simp] theorem scan_nil : r.scan [] = [] := rfl

@[simp] theorem length_scan (w : List α) : (r.scan w).length = w.length :=
  r.toMealy.length_run w

@[simp] theorem length_apply (w : List α) : (r.apply w).length = w.length := by
  unfold apply; cases r.direction <;> simp [List.revConj]

theorem scan_isMealyComputable : IsMealyComputable r.scan := r.toMealy.isMealyComputable

theorem scan_isLeftSubsequential : IsLeftSubsequential r.scan :=
  r.scan_isMealyComputable.isLeftSubsequential

/-- The rule's string function is subsequential in the rule's direction, on any tier. -/
theorem apply_isSubsequential : IsSubsequential r.direction r.apply := by
  unfold apply
  cases r.direction
  · exact r.scan_isLeftSubsequential
  · show IsLeftSubsequential (List.revConj (List.revConj r.scan))
    rw [List.revConj_revConj]
    exact r.scan_isLeftSubsequential

/-! ### The run as a tier-based OSL rule -/

/-- The rule as a 2-OSL rule ([chandlee-eyraud-heinz-2015]) in which each target takes the
value the previous output segment offers. -/
def spreadRule : OSLRule 2 α α where
  windowOutput window s := [r.emit (window.getLast?.bind r.transmits) s]

@[simp] theorem spreadRule_windowOutput (window : List α) (s : α) :
    r.spreadRule.windowOutput window s = [r.emit (window.getLast?.bind r.transmits) s] :=
  rfl

/-- The OSL rule run over the tier ([burness-mcmullin-2020]) is the Mealy run, the rule's
output window being the machine's state read off the last output segment. -/
theorem spreadRule_applyOnTier : r.spreadRule.applyOnTier r.tier = r.scan := by
  funext w
  suffices ∀ (window : List α) (v : Option Bool), window.getLast?.bind r.transmits = v →
      r.spreadRule.applyOnTierAux r.tier window w = r.toMealy.runFrom v w from
    this [] none rfl
  induction w with
  | nil => intros; rfl
  | cons x xs ih =>
    intro window v hv
    rw [OSLRule.applyOnTierAux_cons, Mealy.runFrom_cons, toMealy_output, toMealy_step]
    split_ifs with hx
    · rw [spreadRule_windowOutput, hv, List.singleton_append]
      refine congrArg _ (ih _ _ ?_)
      rw [List.rtake, List.length_append, List.length_singleton, Nat.add_sub_cancel,
        List.drop_left, List.getLast?_singleton, Option.bind_some]
    · exact congrArg _ (ih window v hv)

theorem tier_emit (hw : ∀ v s, r.tier s → r.tier (r.write v s)) {s : α} (hs : r.tier s)
    (v : Option Bool) : r.tier (r.emit v s) := by
  unfold emit; split_ifs
  · rcases (v.map r.relation.act).or r.default with _ | b
    · exact hs
    · exact hw b s hs
  · exact hs

/-- Restricted to the tier, the run is the 2-OSL rule, provided the write keeps a segment on
the tier. -/
theorem tier_scan (hw : ∀ v s, r.tier s → r.tier (r.write v s)) (w : List α) :
    (r.scan w).filter (decide <| r.tier ·) = r.spreadRule.apply (w.filter (decide <| r.tier ·)) := by
  rw [← spreadRule_applyOnTier]
  exact r.spreadRule.filter_applyOnTier (fun _ s hs y hy => by
    rw [spreadRule_windowOutput, List.mem_singleton] at hy
    exact hy ▸ r.tier_emit hw hs _) w

end TierRule

end Subregular
