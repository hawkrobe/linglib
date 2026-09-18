/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.ForbiddenPairs
import Linglib.Phonology.Harmony.Basic
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.OSL

/-!
# Harmony systems

A harmony system is a `Phonology.Harmony.Pattern` together with its trigger and target
classes ([rose-walker-2011]) and a write of the harmonic value into a segment. Its run over
a word is [belth-2026]'s tier rule applied iteratively: each target on the tier takes the
value of the tier-adjacent output segment when that segment is a trigger. The run is
computed by a three-state Mealy machine on the tier whose state is the value the last output
tier segment offers (`System.toMealy`), and by the output tier-based strictly 2-local rule of
[burness-mcmullin-2020] (`System.spreadRule`, the tier form of
[chandlee-eyraud-heinz-2015]'s OSL functions); the two agree
(`System.spreadRule_applyOnTier`), so every system is Mealy-computable and subsequential in
its direction of spreading, on any tier. Harmonic words are fixed points of the run
(`System.transduce_eq_self_of_harmonic`); when every tier segment triggers and undergoes,
the fixed points are exactly the harmonic words, which form a TSL₂ language
(`Pattern.harmonic_iff_mem_tsl`, [aksenova-rawski-graf-heinz-2024]).

## Main definitions

* `System`: a pattern, the trigger and target classes, and a feature write obeying the two
  lens laws; `System.mk'` compiles the [rose-walker-2011] roles over `Phonology.Segment`.
* `System.transduce`: the left-to-right run over the tier; `System.harmonize` runs in the
  pattern's direction, and `System.triggerValue` is the value a stem passes to its suffixes.
* `System.toMealy`, `System.spreadRule`: the machine and the OSL rule computing the run.

## Main results

* `System.spreadRule_applyOnTier`: the OSL rule run over the tier is the Mealy run.
* `System.harmonize_isSubsequential`, `System.transduce_isMealyComputable`: the run is
  finite-state in the pattern's direction, on any tier.
* `System.tier_transduce`: restricted to the tier, the run is the 2-OSL rule.
* `System.transduce_eq_self_of_harmonic`, `System.harmonic_iff_transduce_eq_self`,
  `System.harmonic_transduce`: the run's fixed points and image against the pattern's
  surface harmonicity.
* `System.transduce_eq_map`: when every tier segment triggers and undergoes, the run writes
  the first tier segment's value everywhere.

## Implementation notes

The roles are [belth-2026]'s rule `Agree(A, F) / C __ ∘ proj(·, T)`: `IsTarget` is `A`,
`IsTrigger` is `C`, the pattern's tier is `T`, and its valuation is `F`. A blocker is on the
tier without being a trigger, so the value stops at it; a blocker that is a trigger imposes
its own value ([ritter-vanderhulst-2024-themes]); a transparent segment is off the tier; an
icy target ([jurgec-2011]) undergoes but, by its stored participation, is never copied from.
There is no default value: a target reached by no value is left as it is. Bidirectional
patterns are run left to right; the outward-from-root pass is not modelled, and
`Pattern.Harmonic` reads the tier left to right, so the fixed-point results are stated for
`transduce`. This is the tier-based account, one live analysis among autosegmental spreading
([goldsmith-1976]), Agreement by Correspondence ([rose-walker-2004]) and OT alignment, and a
single tier is not always enough: Uyghur backness harmony is not TSL ([mayer-major-2018]).

## References

* [rose-walker-2011]
* [belth-2026]
* [chandlee-eyraud-heinz-2015]
* [burness-mcmullin-2020]
* [aksenova-rawski-graf-heinz-2024]
* [ritter-vanderhulst-2024-themes]
* [jurgec-2011]
* [goldsmith-1976]
* [rose-walker-2004]
* [mayer-major-2018]
-/

namespace Phonology.Harmony

/-- The scan direction of a pattern, bidirectional patterns being run left to right. -/
def Direction.toScanDirection : Direction → ScanDirection
  | .rightward | .bidirectional => .left
  | .leftward => .right

end Phonology.Harmony

namespace Subregular.Harmony

open Phonology (Segment Feature)
open Phonology.Harmony (Pattern)

/-! ### Systems -/

/-- A harmony system consists of a `Phonology.Harmony.Pattern`, its trigger and target
classes, and a write of the harmonic value into a segment, which with the pattern's
valuation forms a lens. -/
structure System (α : Type*) where
  /-- The descriptive pattern the system realizes. -/
  pattern : Pattern α Bool
  /-- The segments a target copies its value from. -/
  IsTrigger : α → Prop
  [decTrigger : DecidablePred IsTrigger]
  /-- The segments that undergo. -/
  IsTarget : α → Prop
  [decTarget : DecidablePred IsTarget]
  /-- Write the harmonic value into a segment. -/
  write : Bool → α → α
  /-- Reading back a written value gives that value. -/
  value_write : ∀ v s, pattern.value (write v s) = some v
  /-- Writing the value a segment already carries leaves it unchanged. -/
  write_value : ∀ v s, pattern.value s = some v → write v s = s

attribute [instance] System.decTrigger System.decTarget

namespace System

variable {α : Type*} (sys : System α)

/-- The value a segment offers to the next target, which is its harmonic value if it is a
trigger and not an icy target and nothing otherwise. -/
def transmits (s : α) : Option Bool :=
  if sys.IsTrigger s ∧ sys.pattern.participation s ≠ .icyTarget then sys.pattern.value s
  else none

/-- The segment output at `s` when the value `v` has been carried to it. -/
def emit (v : Option Bool) (s : α) : α :=
  if sys.IsTarget s then v.elim s (sys.write · s) else s

theorem value_eq_of_transmits_eq_some {s : α} {v : Bool} (h : sys.transmits s = some v) :
    sys.pattern.value s = some v := by
  unfold transmits at h; split_ifs at h; exact h

@[simp] theorem emit_none (s : α) : sys.emit none s = s := by
  unfold emit; split_ifs <;> rfl

theorem emit_of_not_target {s : α} (h : ¬ sys.IsTarget s) (v : Option Bool) :
    sys.emit v s = s :=
  ite_eq_right h

theorem emit_some_of_target {s : α} (h : sys.IsTarget s) (v : Bool) :
    sys.emit (some v) s = sys.write v s :=
  ite_eq_left h

/-- A segment already carrying the value reaching it is emitted unchanged. -/
theorem emit_eq_self {s : α} {v : Bool} (h : sys.pattern.value s = some v) :
    sys.emit (some v) s = s := by
  unfold emit; split_ifs <;> simp [sys.write_value v s h]

/-- Compiles the [rose-walker-2011] roles over `Phonology.Segment` from the harmonic feature,
the triggers, the targets, the transparent segments, the direction, and the blockers. -/
def mk' (feature : Feature) (isTrigger isTarget isTransparent : Segment → Bool)
    (direction : Phonology.Harmony.Direction := .rightward)
    (isBlocker : Segment → Bool := fun _ => false) : System Segment where
  pattern :=
    { value := fun s => s feature
      participation := fun s =>
        if isBlocker s then .opaque
        else if isTransparent s then .transparent
        else .participating
      direction := direction }
  IsTrigger s := isTrigger s = true
  IsTarget s := isTarget s = true
  write v s := Function.update s feature (some v)
  value_write _ _ := Function.update_self ..
  write_value _ _ h := h ▸ Function.update_eq_self ..

/-! ### The run -/

/-- The harmonic-value machine, whose state is the value the last output tier segment offers
and which passes off-tier segments through untouched. -/
def toMealy : Mealy (Option Bool) α α where
  initial := none
  step v s := if sys.pattern.OnTier s then sys.transmits (sys.emit v s) else v
  output v s := if sys.pattern.OnTier s then sys.emit v s else s

@[simp] theorem toMealy_initial : sys.toMealy.initial = none := rfl

@[simp] theorem toMealy_step (v : Option Bool) (s : α) :
    sys.toMealy.step v s = if sys.pattern.OnTier s then sys.transmits (sys.emit v s) else v :=
  rfl

@[simp] theorem toMealy_output (v : Option Bool) (s : α) :
    sys.toMealy.output v s = if sys.pattern.OnTier s then sys.emit v s else s :=
  rfl

/-- The left-to-right run over the tier, in which each target takes the value carried to it. -/
def transduce : List α → List α := sys.toMealy.run

/-- The run in the pattern's direction of spreading. -/
def harmonize : List α → List α :=
  match sys.pattern.direction.toScanDirection with
  | .left => sys.transduce
  | .right => List.revConj sys.transduce

/-- The harmonic value a stem passes on to its suffixes, the machine's state after the stem
read in the pattern's direction. -/
def triggerValue (stem : List α) : Option Bool :=
  match sys.pattern.direction.toScanDirection with
  | .left => sys.toMealy.stateAfter none stem
  | .right => sys.toMealy.stateAfter none stem.reverse

@[simp] theorem transduce_nil : sys.transduce [] = [] := rfl

@[simp] theorem length_transduce (w : List α) : (sys.transduce w).length = w.length :=
  sys.toMealy.length_run w

@[simp] theorem length_harmonize (w : List α) : (sys.harmonize w).length = w.length := by
  unfold harmonize; cases sys.pattern.direction.toScanDirection <;> simp [List.revConj]

theorem transduce_isMealyComputable : IsMealyComputable sys.transduce :=
  sys.toMealy.isMealyComputable

theorem transduce_isLeftSubsequential : IsLeftSubsequential sys.transduce :=
  sys.transduce_isMealyComputable.isLeftSubsequential

/-- The harmonized-string function is subsequential in the pattern's direction, on any
tier. -/
theorem harmonize_isSubsequential :
    IsSubsequential sys.pattern.direction.toScanDirection sys.harmonize := by
  unfold harmonize
  cases sys.pattern.direction.toScanDirection
  · exact sys.transduce_isLeftSubsequential
  · show IsLeftSubsequential (List.revConj (List.revConj sys.transduce))
    rw [List.revConj_revConj]
    exact sys.transduce_isLeftSubsequential

/-! ### The run as a tier-based OSL rule -/

/-- Harmony as a 2-OSL rule ([chandlee-eyraud-heinz-2015]) in which each target takes the
value the previous output segment offers. -/
def spreadRule : OSLRule 2 α α where
  windowOutput window s := [sys.emit (window.getLast?.bind sys.transmits) s]

@[simp] theorem spreadRule_windowOutput (window : List α) (s : α) :
    sys.spreadRule.windowOutput window s = [sys.emit (window.getLast?.bind sys.transmits) s] :=
  rfl

/-- The OSL rule run over the tier ([burness-mcmullin-2020]) is the Mealy run, the rule's
output window being the machine's state read off the last output segment. -/
theorem spreadRule_applyOnTier :
    sys.spreadRule.applyOnTier sys.pattern.OnTier = sys.transduce := by
  funext w
  suffices ∀ (window : List α) (v : Option Bool), window.getLast?.bind sys.transmits = v →
      sys.spreadRule.applyOnTierAux sys.pattern.OnTier window w = sys.toMealy.runFrom v w from
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

theorem onTier_emit (hw : ∀ v s, sys.pattern.OnTier s → sys.pattern.OnTier (sys.write v s))
    {s : α} (hs : sys.pattern.OnTier s) (v : Option Bool) : sys.pattern.OnTier (sys.emit v s) := by
  unfold emit; split_ifs
  · cases v with
    | none => exact hs
    | some v => exact hw v s hs
  · exact hs

/-- Restricted to the tier, the run is the 2-OSL rule, provided the write keeps a segment on
the tier. -/
theorem tier_transduce (hw : ∀ v s, sys.pattern.OnTier s → sys.pattern.OnTier (sys.write v s))
    (w : List α) : sys.pattern.tier (sys.transduce w) = sys.spreadRule.apply (sys.pattern.tier w) := by
  rw [← spreadRule_applyOnTier]
  exact sys.spreadRule.filter_applyOnTier (fun _ s hs y hy => by
    rw [spreadRule_windowOutput, List.mem_singleton] at hy
    exact hy ▸ sys.onTier_emit hw hs _) w

/-! ### Fixed points and image -/

/-- After the tier segment `a?`, a word whose tier continues it compatibly is left
unchanged, provided blockers do not undergo. -/
private theorem runFrom_eq_self (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) :
    ∀ (w : List α) (a? : Option α),
      (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible →
        sys.toMealy.runFrom (a?.bind sys.transmits) w = w
  | [], _, _ => rfl
  | x :: xs, a?, h => by
    rw [Mealy.runFrom_cons, toMealy_output, toMealy_step]
    by_cases hx : sys.pattern.OnTier x
    · rw [sys.pattern.tier_cons_of_onTier hx] at h
      have hemit : sys.emit (a?.bind sys.transmits) x = x := by
        cases a? with
        | none => exact sys.emit_none x
        | some a =>
          rw [Option.bind_some]
          by_cases ht : sys.IsTarget x
          · rcases (List.isChain_cons_cons.mp h).1 with hicy | hop | hval
            · rw [transmits, ite_eq_right (fun h => h.2 hicy), emit_none]
            · exact absurd ht (hb x hop)
            · rcases hv : sys.transmits a with _ | v
              · exact sys.emit_none x
              · exact sys.emit_eq_self (hval ▸ sys.value_eq_of_transmits_eq_some hv)
          · exact sys.emit_of_not_target ht _
      rw [ite_eq_left hx, ite_eq_left hx, hemit]
      refine congrArg _ (runFrom_eq_self hb xs (some x) ?_)
      cases a? with
      | none => exact h
      | some a => exact (List.isChain_cons_cons.mp h).2
    · rw [sys.pattern.tier_cons_of_not_onTier hx] at h
      rw [ite_eq_right hx, ite_eq_right hx]
      exact congrArg _ (runFrom_eq_self hb xs a? h)

/-- A harmonic word is a fixed point of the run, provided blockers do not undergo. -/
theorem transduce_eq_self_of_harmonic
    (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) {w : List α}
    (h : sys.pattern.Harmonic w) : sys.transduce w = w :=
  sys.runFrom_eq_self hb w none h

/-- A system is saturated when every tier segment undergoes and offers a value; on such a
system the run decides the surface language. -/
def Saturated : Prop :=
  ∀ s, sys.pattern.OnTier s → sys.IsTarget s ∧ (sys.transmits s).isSome

private theorem harmonic_of_runFrom_eq_self (hs : sys.Saturated) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.pattern.OnTier a) →
      sys.toMealy.runFrom (a?.bind sys.transmits) w = w →
        (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible
  | [], none, _, _ => List.isChain_nil
  | [], some _, _, _ => List.isChain_singleton _
  | x :: xs, a?, ha, h => by
    rw [Mealy.runFrom_cons, toMealy_output, toMealy_step] at h
    by_cases hx : sys.pattern.OnTier x
    · rw [ite_eq_left hx, ite_eq_left hx] at h
      obtain ⟨hemit, hrest⟩ := List.cons.inj h
      rw [hemit] at hrest
      have ih := harmonic_of_runFrom_eq_self hs xs (some x) (fun _ h => Option.mem_some_iff.mp h ▸ hx) hrest
      rw [sys.pattern.tier_cons_of_onTier hx]
      cases a? with
      | none => exact ih
      | some a =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs a (ha a rfl)).2
        rw [Option.bind_some, hv, sys.emit_some_of_target (hs x hx).1] at hemit
        exact Or.inr (Or.inr ((sys.value_eq_of_transmits_eq_some hv).trans
          (hemit ▸ (sys.value_write v x)).symm))
    · rw [ite_eq_right hx, ite_eq_right hx] at h
      rw [sys.pattern.tier_cons_of_not_onTier hx]
      exact harmonic_of_runFrom_eq_self hs xs a? ha (List.cons.inj h).2

/-- On a saturated system the harmonic words are exactly the fixed points of the run. -/
theorem harmonic_iff_transduce_eq_self (hs : sys.Saturated)
    (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) (w : List α) :
    sys.pattern.Harmonic w ↔ sys.transduce w = w :=
  ⟨sys.transduce_eq_self_of_harmonic hb,
    sys.harmonic_of_runFrom_eq_self hs w none (fun _ h => by cases h)⟩

private theorem runFrom_some_eq_map (hs : sys.Saturated)
    (ht : ∀ v s, sys.transmits (sys.write v s) = some v) (v : Bool) :
    ∀ w : List α, sys.toMealy.runFrom (some v) w =
      w.map fun s => if sys.pattern.OnTier s then sys.write v s else s
  | [] => rfl
  | x :: xs => by
    rw [Mealy.runFrom_cons, toMealy_output, toMealy_step, List.map_cons]
    by_cases hx : sys.pattern.OnTier x
    · rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx, sys.emit_some_of_target (hs x hx).1,
        ht, runFrom_some_eq_map hs ht v xs]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx, runFrom_some_eq_map hs ht v xs]

/-- On a saturated system whose writes are transmitted, the run writes the first tier
segment's value into every tier segment. -/
theorem transduce_eq_map (hs : sys.Saturated)
    (ht : ∀ v s, sys.transmits (sys.write v s) = some v) (w : List α) :
    sys.transduce w = w.map fun s =>
      if sys.pattern.OnTier s then ((sys.pattern.tier w).head?.bind sys.transmits).elim s
        (sys.write · s) else s := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rw [transduce, Mealy.run, toMealy_initial, Mealy.runFrom_cons, toMealy_output, toMealy_step,
      List.map_cons]
    by_cases hx : sys.pattern.OnTier x
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs x hx).2
      rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx, emit_none, hv,
        sys.pattern.tier_cons_of_onTier hx, List.head?_cons, Option.bind_some, hv,
        Option.elim_some, sys.write_value v x (sys.value_eq_of_transmits_eq_some hv),
        sys.runFrom_some_eq_map hs ht]
      simp only [Option.elim_some]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx, sys.pattern.tier_cons_of_not_onTier hx]
      exact congrArg _ ih

private theorem runFrom_harmonic (hs : sys.Saturated)
    (ht : ∀ v s, sys.transmits (sys.write v s) = some v)
    (hw : ∀ v s, sys.pattern.OnTier s → sys.pattern.OnTier (sys.write v s)) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.pattern.OnTier a) →
      (a?.toList ++ sys.pattern.tier (sys.toMealy.runFrom (a?.bind sys.transmits) w)).IsChain
        sys.pattern.Compatible
  | [], none, _ => List.isChain_nil
  | [], some _, _ => List.isChain_singleton _
  | x :: xs, a?, ha => by
    rw [Mealy.runFrom_cons, toMealy_output, toMealy_step]
    by_cases hx : sys.pattern.OnTier x
    · rw [ite_eq_left hx, ite_eq_left hx]
      have he : sys.pattern.OnTier (sys.emit (a?.bind sys.transmits) x) := sys.onTier_emit hw hx _
      rw [sys.pattern.tier_cons_of_onTier he]
      have ih := runFrom_harmonic hs ht hw xs (some (sys.emit (a?.bind sys.transmits) x))
        (fun _ h => Option.mem_some_iff.mp h ▸ he)
      cases a? with
      | none => exact ih
      | some a =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs a (ha a rfl)).2
        rw [Option.bind_some, hv] at ih ⊢
        rw [sys.emit_some_of_target (hs x hx).1]
        exact Or.inr (Or.inr ((sys.value_eq_of_transmits_eq_some hv).trans
          (sys.value_write v x).symm))
    · rw [ite_eq_right hx, ite_eq_right hx, sys.pattern.tier_cons_of_not_onTier hx]
      exact runFrom_harmonic hs ht hw xs a? ha

/-- On a saturated system whose writes are transmitted and stay on the tier, the run's output
is harmonic. -/
theorem harmonic_transduce (hs : sys.Saturated)
    (ht : ∀ v s, sys.transmits (sys.write v s) = some v)
    (hw : ∀ v s, sys.pattern.OnTier s → sys.pattern.OnTier (sys.write v s)) (w : List α) :
    sys.pattern.Harmonic (sys.transduce w) :=
  sys.runFrom_harmonic hs ht hw w none (fun _ h => by cases h)

end System

end Subregular.Harmony

namespace Phonology.Harmony

open Subregular TierStrictlyLocalGrammar

variable {α V : Type*}

/-- Harmony is TSL₂ by construction, since the tier supplies both the unbounded distance
strictly local grammars lack and the blocking strictly piecewise grammars lack
([aksenova-rawski-graf-heinz-2024]; for the latter,
`McMullin2016.blockingLang_not_isStrictlyPiecewise`). -/
theorem Pattern.harmonic_iff_mem_tsl (p : Pattern α V) (w : List α) :
    p.Harmonic w ↔ w ∈ (ofForbiddenPairs (¬ p.Compatible · ·) p.OnTier).language := by
  simp only [mem_ofForbiddenPairs_language_iff_filter_isChain, Pattern.Harmonic, Pattern.tier,
    not_not]

end Phonology.Harmony
