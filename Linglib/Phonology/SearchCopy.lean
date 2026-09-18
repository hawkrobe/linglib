/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.DropRight
import Linglib.Phonology.Subregular.OSL

/-!
# Search and copy

A search-and-copy rule is the Harmonic Search-and-Copy procedure of [nevins-2010]: a needy
segment, one unspecified for a feature, searches in one direction for the closest segment
visible to it and copies that segment's value, or the opposite value for dissimilation, and
takes a last-resort default when the search fails. The procedure is stated by its
visibility predicate, direction and feature; a target may further require its source to
meet a condition of its own, and a visible source failing it halts the search with the
default, which is defective intervention, since the search gets no second chance. A copied
value is donated onward, so harmony iterates morpheme by morpheme, and every visible valued
segment donates whether or not it searches itself. Mailhot and Reiss's SEARCH and COPY rule
components, as [bale-reiss-2018] present them, are a sibling formulation with simultaneous
application over the input. [belth-2026]'s learner constructs one, written
`Rel(A, F) / C __ ∘ proj(·, T)` with `A` the targets, `C` the sources and `T` the visible
segments, and [nevins-2010] reads [rose-walker-2011]'s blockers and transparent segments as
defective interveners and invisible segments.

Run over a word, the rule is a Mealy machine on the visible segments whose state is the
closest visible segment read so far (`SearchCopy.toMealy`), the memory window of
[burness-mcmullin-nevins-2024]'s tier-based strictly local reading of the procedure, and
the output tier-based strictly 2-local rule of [burness-mcmullin-2019] computes the same
function (`SearchCopy.toOSLRule_applyOnTier`). So a rule for one feature in one direction
is a tier-based strictly local function, the result of Andersson, Dolatian and Hao that
[burness-mcmullin-nevins-2024] report, and subsequential in its direction over a finite
alphabet (`SearchCopy.apply_isSubsequential`), as Gainor, Lai and Heinz found of
[nevins-2010]'s analyses.

## Main definitions

* `SearchCopy`: a rule, with its visible segments, targets, sources, relation, lens on the
  feature, default and direction.
* `SearchCopy.scan`, `SearchCopy.apply`: the left-to-right run over the visible segments,
  and the run in the rule's direction.
* `SearchCopy.sourceAfter`, `SearchCopy.sourceValue`: the closest visible segment of a
  string and the value it offers to what follows.
* `SearchCopy.toMealy`, `SearchCopy.toOSLRule`: the machine and the OSL rule computing the
  run.

## Main results

* `SearchCopy.toOSLRule_applyOnTier`: the OSL rule run over the visible segments is the
  Mealy run.
* `SearchCopy.filter_scan`: restricted to the visible segments, the run is the 2-OSL rule.
* `SearchCopy.apply_isSubsequential`, `SearchCopy.scan_isMealyComputable`: the run is
  finite-state in the rule's direction over a finite alphabet.

## Implementation notes

The window holds the last visible output segment, so a copied value is donated onward, as
[nevins-2010]'s derivations of stacked Turkish suffixes show; [burness-mcmullin-nevins-2024]
instead model the procedure by an input-oriented function with the needy segments off the
tier, which agrees whenever a needy segment's nearest visible source precedes it in the
input, and the run is [nevins-2010]'s cyclic derivation only where morphological order runs
away from the root in the search direction. `IsSource` is more general than [nevins-2010]'s
conditions on a source, which are identity for an orthogonal feature or morphological
affiliation. A source unspecified for the feature yields the default, where [belth-2026]
counts a failed application, and a default of `none`, outside both sources, leaves a
failed target unspecified for the fixed-point results of `Harmony.System`. The lens laws
hold on targets only, since only targets are written. Not modelled are search in both
directions at once, sonority hurdles, the distance parameters of [nevins-2010]'s fifth
chapter, more than one feature per search, and the patterns [burness-mcmullin-nevins-2024]
place beyond the procedure: icy targets, persistent search and circumambient harmony.

## References

* [nevins-2010]
* [bale-reiss-2018]
* [burness-mcmullin-nevins-2024]
* [burness-mcmullin-2019]
* [chandlee-eyraud-heinz-2015]
* [belth-2026]
* [rose-walker-2011]
-/

namespace Phonology

/-- Whether a target copies its source's value or, for dissimilation, the opposite value. -/
inductive SearchCopy.Relation where
  | agree
  | disagree
  deriving DecidableEq, Repr

/-- The value the relation writes into a target from its source's value. -/
def SearchCopy.Relation.act : SearchCopy.Relation → Bool → Bool
  | .agree, v => v
  | .disagree, v => !v

@[simp] theorem SearchCopy.Relation.act_agree (v : Bool) : Relation.agree.act v = v := rfl

@[simp] theorem SearchCopy.Relation.act_disagree (v : Bool) : Relation.disagree.act v = !v := rfl

/-- A search-and-copy rule consists of the visible segments, the targets, the sources each
target may copy from, the relation, a lens reading and writing the feature on targets, a
last-resort default, and a direction. -/
structure SearchCopy (α : Type*) where
  /-- The visible segments, the rule's tier. -/
  tier : α → Prop
  [decTier : DecidablePred tier]
  /-- The needy segments, which search. -/
  IsTarget : α → Prop
  [decTarget : DecidablePred IsTarget]
  /-- `IsSource s t` holds when the visible segment `s` may donate to the target `t`. -/
  IsSource : α → α → Prop
  [decSource : DecidableRel IsSource]
  /-- Whether a target copies or negates its source's value. -/
  relation : SearchCopy.Relation := .agree
  /-- The feature's value on a segment, `none` when the segment is unspecified for it. -/
  value : α → Option Bool
  /-- The segment with the feature's value written into it. -/
  write : Bool → α → α
  /-- Reading back a value written into a target gives that value. -/
  value_write : ∀ v s, IsTarget s → value (write v s) = some v
  /-- Writing the value a target already carries leaves it unchanged. -/
  write_value : ∀ v s, IsTarget s → value s = some v → write v s = s
  /-- The last-resort value a target takes when its search fails. -/
  default : Option Bool := none
  /-- The direction of search; a rightward search scans right to left. -/
  direction : ScanDirection := .left

attribute [instance] SearchCopy.decTier SearchCopy.decTarget SearchCopy.decSource

namespace SearchCopy

variable {α : Type*} (r : SearchCopy α)

/-- The value the target `t` finds in the window `w`, the window segment's value when it may
donate to `t`. -/
def found (t : α) (w : Option α) : Option Bool :=
  w.bind fun c => if r.IsSource c t then r.value c else none

/-- The value the search of `t` yields from the window `w`, the default when it finds
nothing. -/
def copied (t : α) (w : Option α) : Option Bool :=
  ((r.found t w).map r.relation.act).or r.default

/-- The segment output at `s` with the window `w`. -/
def emit (w : Option α) (s : α) : α :=
  if r.IsTarget s then (r.copied s w).elim s (r.write · s) else s

/-- The write keeps a visible segment visible. -/
def TierClosed : Prop := ∀ v s, r.tier s → r.tier (r.write v s)

@[simp] theorem found_none (t : α) : r.found t none = none := rfl

@[simp] theorem found_some (t c : α) :
    r.found t (some c) = if r.IsSource c t then r.value c else none :=
  rfl

theorem found_some_of_isSource {t c : α} (h : r.IsSource c t) :
    r.found t (some c) = r.value c := by
  simp [h]

theorem found_some_of_not_isSource {t c : α} (h : ¬ r.IsSource c t) :
    r.found t (some c) = none := by
  simp [h]

theorem emit_of_not_isTarget {s : α} (h : ¬ r.IsTarget s) (w : Option α) : r.emit w s = s :=
  ite_eq_right h

theorem emit_of_isTarget {s : α} (h : r.IsTarget s) (w : Option α) :
    r.emit w s = (r.copied s w).elim s (r.write · s) :=
  ite_eq_left h

/-- A target whose search finds nothing is left unchanged when there is no default. -/
theorem emit_of_found_eq_none (hd : r.default = none) {s : α} {w : Option α}
    (hf : r.found s w = none) : r.emit w s = s := by
  unfold emit copied; rw [hf, hd]; split_ifs <;> rfl

/-- A target already carrying the value its search finds is emitted unchanged. -/
theorem emit_eq_self {s : α} {w : Option α} {v : Bool} (hf : r.found s w = some v)
    (h : r.value s = some (r.relation.act v)) : r.emit w s = s := by
  unfold emit copied; rw [hf]; split_ifs with ht
  · simp [r.write_value _ s ht h]
  · rfl

/-! ### The run -/

/-- The machine computing the rule, whose state is the closest visible segment read so far
and which passes invisible segments through untouched. -/
def toMealy : Mealy (Option α) α α where
  start := none
  step w s := if r.tier s then some (r.emit w s) else w
  output w s := if r.tier s then r.emit w s else s

@[simp] theorem toMealy_start : r.toMealy.start = none := rfl

@[simp] theorem toMealy_step (w : Option α) (s : α) :
    r.toMealy.step w s = if r.tier s then some (r.emit w s) else w :=
  rfl

@[simp] theorem toMealy_output (w : Option α) (s : α) :
    r.toMealy.output w s = if r.tier s then r.emit w s else s :=
  rfl

theorem toMealy_runFrom_cons_of_tier {x : α} (hx : r.tier x) (w : Option α) (xs : List α) :
    r.toMealy.runFrom w (x :: xs) = r.emit w x :: r.toMealy.runFrom (some (r.emit w x)) xs := by
  rw [Mealy.runFrom_cons, toMealy_output, toMealy_step, ite_eq_left hx, ite_eq_left hx]

theorem toMealy_runFrom_cons_of_not_tier {x : α} (hx : ¬ r.tier x) (w : Option α)
    (xs : List α) : r.toMealy.runFrom w (x :: xs) = x :: r.toMealy.runFrom w xs := by
  rw [Mealy.runFrom_cons, toMealy_output, toMealy_step, ite_eq_right hx, ite_eq_right hx]

/-- The left-to-right run over the visible segments, in which each target copies from the
closest visible segment before it. -/
def scan : List α → List α := r.toMealy.run

theorem scan_eq_runFrom (w : List α) : r.scan w = r.toMealy.runFrom none w := rfl

/-- The run in the rule's direction. -/
def apply : List α → List α :=
  match r.direction with
  | .left => r.toMealy.run
  | .right => r.toMealy.runRight

/-- The closest visible segment of a string for a target that follows it in the rule's
direction. -/
def sourceAfter (w : List α) : Option α :=
  match r.direction with
  | .left => r.toMealy.stateAfter none w
  | .right => r.toMealy.stateAfter none w.reverse

/-- The value a string offers to a target that follows it in the rule's direction. -/
def sourceValue (w : List α) : Option Bool := (r.sourceAfter w).bind r.value

@[simp] theorem scan_nil : r.scan [] = [] := rfl

@[simp] theorem length_scan (w : List α) : (r.scan w).length = w.length :=
  r.toMealy.length_run w

@[simp] theorem length_apply (w : List α) : (r.apply w).length = w.length := by
  unfold apply; cases r.direction <;> simp

theorem scan_isMealyComputable [Fintype α] : IsMealyComputable r.scan :=
  r.toMealy.isMealyComputable

theorem scan_isLeftSubsequential [Fintype α] : IsLeftSubsequential r.scan :=
  r.scan_isMealyComputable.isLeftSubsequential

/-- The rule's string function is subsequential in the rule's direction over a finite
alphabet. -/
theorem apply_isSubsequential [Fintype α] : IsSubsequential r.direction r.apply := by
  unfold apply
  cases r.direction
  · exact r.scan_isLeftSubsequential
  · show IsLeftSubsequential (List.revConj (List.revConj r.scan))
    rw [List.revConj_revConj]
    exact r.scan_isLeftSubsequential

/-! ### The run as a tier-based OSL rule -/

/-- The rule as a 2-OSL rule ([chandlee-eyraud-heinz-2015]) in which each target copies from
the previous output segment. -/
def toOSLRule : Subregular.OSLRule 2 α α where
  windowOutput window s := [r.emit window.getLast? s]

@[simp] theorem toOSLRule_windowOutput (window : List α) (s : α) :
    r.toOSLRule.windowOutput window s = [r.emit window.getLast? s] :=
  rfl

/-- The OSL rule run over the visible segments ([burness-mcmullin-2019]) is the Mealy run,
the rule's output window being the machine's state. -/
theorem toOSLRule_applyOnTier : r.toOSLRule.applyOnTier r.tier = r.scan := by
  funext w
  suffices ∀ (window : List α) (v : Option α), window.getLast? = v →
      r.toOSLRule.applyOnTierAux r.tier window w = r.toMealy.runFrom v w from
    this [] none rfl
  induction w with
  | nil => intros; rfl
  | cons x xs ih =>
    intro window v hv
    rw [Subregular.OSLRule.applyOnTierAux_cons]
    split_ifs with hx
    · rw [r.toMealy_runFrom_cons_of_tier hx, toOSLRule_windowOutput, hv, List.singleton_append]
      refine congrArg _ (ih _ _ ?_)
      rw [List.rtake_concat_succ, List.rtake_zero, List.nil_append, List.getLast?_singleton]
    · rw [r.toMealy_runFrom_cons_of_not_tier hx]
      exact congrArg _ (ih window v hv)

theorem tier_emit (hw : r.TierClosed) {s : α} (hs : r.tier s) (w : Option α) :
    r.tier (r.emit w s) := by
  unfold emit; split_ifs
  · rcases r.copied s w with _ | b
    · exact hs
    · exact hw b s hs
  · exact hs

/-- Restricted to the visible segments, the run is the 2-OSL rule, provided the write keeps
a segment visible. -/
theorem filter_scan (hw : r.TierClosed) (w : List α) :
    (r.scan w).filter (decide <| r.tier ·) = r.toOSLRule.apply (w.filter (decide <| r.tier ·)) := by
  rw [← toOSLRule_applyOnTier]
  exact r.toOSLRule.filter_applyOnTier (fun _ s hs y hy => by
    rw [toOSLRule_windowOutput, List.mem_singleton] at hy
    exact hy ▸ r.tier_emit hw hs _) w

end SearchCopy

end Phonology
