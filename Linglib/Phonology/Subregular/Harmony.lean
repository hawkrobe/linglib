/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.ForbiddenPairs
import Linglib.Phonology.Harmony.Basic
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.TierRule

/-!
# Harmony systems

A harmony system is a `Subregular.TierRule` with the `Agree` relation together with its
blockers: [rose-walker-2011]'s triggers, targets, blockers and transparent segments are the
rule's context class, its target class, the tier segments it marks opaque, and the segments
off its tier. The system presents a `Phonology.Harmony.Pattern` (`System.pattern`), whose
icy targets ([jurgec-2011]) are the targets that do not trigger. Harmonic words are fixed
points of the run (`System.scan_eq_self_of_harmonic`); when every tier segment triggers and
undergoes, the fixed points are exactly the harmonic words
(`System.harmonic_iff_scan_eq_self`), which form a TSL₂ language
(`Pattern.harmonic_iff_mem_tsl`, [aksenova-rawski-graf-heinz-2024]).

## Main definitions

* `System`: a tier rule with `Agree` and a class of blockers; `System.mk'` compiles the
  [rose-walker-2011] roles over `Phonology.Segment`.
* `System.pattern`: the pattern the system presents.
* `System.Saturated`: every tier segment triggers and undergoes.

## Main results

* `System.scan_eq_self_of_harmonic`, `System.harmonic_iff_scan_eq_self`,
  `System.harmonic_scan`: the run's fixed points and image against the pattern's surface
  harmonicity.
* `System.scan_eq_map`: on a saturated system the run writes the first tier segment's value
  into every tier segment.
* `Pattern.harmonic_iff_mem_tsl`.

## Implementation notes

The fixed-point results assume no Elsewhere default: a default writes a value the surface
phonotactic cannot see, so the run of a system with a default has unspecified fixed points
outside the harmonic words. They also read the tier left to right, as `Pattern.Harmonic`
does, so they are stated for `scan`; `apply` runs in the pattern's direction, and a
bidirectional pattern, whose outward-from-root pass is not modelled, is run left to right.
A blocker that is a trigger imposes its own value ([ritter-vanderhulst-2024-themes]); one
that is not stops the value. This is the tier-based account, one live analysis among
autosegmental spreading ([goldsmith-1976]), Agreement by Correspondence
([rose-walker-2004]) and OT alignment, and a single tier is not always enough: Uyghur
backness harmony is not TSL ([mayer-major-2018]).

## References

* [rose-walker-2011]
* [belth-2026]
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

/-- The direction of spreading of a scan. -/
def Direction.ofScanDirection : ScanDirection → Direction
  | .left => .rightward
  | .right => .leftward

end Phonology.Harmony

namespace Subregular.Harmony

open Phonology (Segment Feature)
open Phonology.Harmony (Pattern Participation Direction)

/-! ### Systems -/

/-- A harmony system is a tier rule with the `Agree` relation together with its blockers, the
tier segments that do not undergo and are exempt from agreeing with what precedes them. -/
structure System (α : Type*) extends TierRule α where
  /-- The blockers. -/
  IsOpaque : α → Prop
  [decOpaque : DecidablePred IsOpaque]
  /-- Harmony is agreement. -/
  relation_eq : relation = .agree := by rfl

attribute [instance] System.decOpaque

namespace System

variable {α : Type*} (sys : System α)

/-- The pattern a system presents: a segment off the tier is transparent, a blocker is
opaque, a target that does not trigger is icy, and every other tier segment participates. -/
def pattern : Pattern α Bool where
  value := sys.value
  participation s :=
    if sys.tier s then
      if sys.IsOpaque s then .opaque
      else if sys.IsTarget s ∧ ¬ sys.IsTrigger s then .icyTarget
      else .participating
    else .transparent
  direction := Direction.ofScanDirection sys.direction

@[simp] theorem pattern_value : sys.pattern.value = sys.value := rfl

theorem pattern_participation (s : α) : sys.pattern.participation s =
    if sys.tier s then
      if sys.IsOpaque s then .opaque
      else if sys.IsTarget s ∧ ¬ sys.IsTrigger s then .icyTarget
      else .participating
    else .transparent :=
  rfl

@[simp] theorem pattern_onTier (s : α) : sys.pattern.OnTier s ↔ sys.tier s := by
  unfold Pattern.OnTier; rw [pattern_participation]; split_ifs <;> simp_all

theorem pattern_tier (w : List α) : sys.pattern.tier w = w.filter (decide <| sys.tier ·) :=
  List.filter_congr fun s _ => by simp

theorem isOpaque_of_participation {s : α} (h : sys.pattern.participation s = .opaque) :
    sys.IsOpaque s := by
  rw [pattern_participation] at h; split_ifs at h; simp_all

theorem not_isTrigger_of_participation {s : α}
    (h : sys.pattern.participation s = .icyTarget) : ¬ sys.IsTrigger s := by
  rw [pattern_participation] at h; split_ifs at h; simp_all

theorem transmits_eq_none_of_participation {s : α}
    (h : sys.pattern.participation s = .icyTarget) : sys.transmits s = none :=
  ite_eq_right (sys.not_isTrigger_of_participation h)

theorem emit_some_of_target {s : α} (h : sys.IsTarget s) (v : Bool) :
    sys.emit (some v) s = sys.write v s := by
  rw [sys.toTierRule.emit_some_of_target h, sys.relation_eq]; rfl

/-- A segment already carrying the value reaching it is emitted unchanged. -/
theorem emit_eq_self {s : α} {v : Bool} (h : sys.value s = some v) :
    sys.emit (some v) s = s :=
  sys.toTierRule.emit_some_eq_self (by rw [sys.relation_eq]; exact h)

/-- Compiles the [rose-walker-2011] roles over `Phonology.Segment` from the harmonic feature,
the triggers, the targets, the transparent segments, the direction, the blockers, and the
Elsewhere default. -/
def mk' (feature : Feature) (isTrigger isTarget isTransparent : Segment → Bool)
    (direction : Direction := .rightward) (isBlocker : Segment → Bool := fun _ => false)
    (default : Option Bool := none) : System Segment where
  tier s := isTransparent s = false
  IsTrigger s := isTrigger s = true
  IsTarget s := isTarget s = true
  value s := s feature
  write v s := Function.update s feature (some v)
  value_write _ _ _ := Function.update_self ..
  write_value _ _ _ h := h ▸ Function.update_eq_self ..
  default := default
  direction := direction.toScanDirection
  IsOpaque s := isBlocker s = true

/-! ### Fixed points and image -/

/-- After the tier segment `a?`, a word whose tier continues it compatibly is left
unchanged, provided there is no default and blockers do not undergo. -/
private theorem runFrom_eq_self (hd : sys.default = none)
    (hb : ∀ s, sys.IsOpaque s → ¬ sys.IsTarget s) : ∀ (w : List α) (a? : Option α),
      (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible →
        sys.toMealy.runFrom (a?.bind sys.transmits) w = w
  | [], _, _ => rfl
  | x :: xs, a?, h => by
    rw [Mealy.runFrom_cons, TierRule.toMealy_output, TierRule.toMealy_step]
    by_cases hx : sys.tier x
    · rw [sys.pattern.tier_cons_of_onTier ((sys.pattern_onTier x).mpr hx)] at h
      have hemit : sys.emit (a?.bind sys.transmits) x = x := by
        cases a? with
        | none => exact sys.toTierRule.emit_none_of_default_eq_none hd x
        | some a =>
          rw [Option.bind_some]
          by_cases ht : sys.IsTarget x
          · rcases (List.isChain_cons_cons.mp h).1 with hicy | hop | hval
            · rw [sys.transmits_eq_none_of_participation hicy]
              exact sys.toTierRule.emit_none_of_default_eq_none hd x
            · exact absurd ht (hb x (sys.isOpaque_of_participation hop))
            · rcases hv : sys.transmits a with _ | v
              · exact sys.toTierRule.emit_none_of_default_eq_none hd x
              · exact sys.emit_eq_self ((show sys.value a = sys.value x from hval) ▸
                  sys.toTierRule.value_eq_of_transmits_eq_some hv)
          · exact sys.toTierRule.emit_of_not_target ht _
      rw [ite_eq_left hx, ite_eq_left hx, hemit]
      refine congrArg _ (runFrom_eq_self hd hb xs (some x) ?_)
      cases a? with
      | none => exact h
      | some a => exact (List.isChain_cons_cons.mp h).2
    · rw [sys.pattern.tier_cons_of_not_onTier (fun h' => hx ((sys.pattern_onTier x).mp h'))]
        at h
      rw [ite_eq_right hx, ite_eq_right hx]
      exact congrArg _ (runFrom_eq_self hd hb xs a? h)

/-- A harmonic word is a fixed point of the run, provided there is no default and blockers
do not undergo. -/
theorem scan_eq_self_of_harmonic (hd : sys.default = none)
    (hb : ∀ s, sys.IsOpaque s → ¬ sys.IsTarget s) {w : List α} (h : sys.pattern.Harmonic w) :
    sys.scan w = w :=
  sys.runFrom_eq_self hd hb w none h

/-- A system is saturated when every tier segment undergoes and offers a value; on such a
system the run decides the surface language. -/
def Saturated : Prop := ∀ s, sys.tier s → sys.IsTarget s ∧ (sys.transmits s).isSome

private theorem harmonic_of_runFrom_eq_self (hs : sys.Saturated) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.tier a) →
      sys.toMealy.runFrom (a?.bind sys.transmits) w = w →
        (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible
  | [], none, _, _ => List.isChain_nil
  | [], some _, _, _ => List.isChain_singleton _
  | x :: xs, a?, ha, h => by
    rw [Mealy.runFrom_cons, TierRule.toMealy_output, TierRule.toMealy_step] at h
    by_cases hx : sys.tier x
    · rw [ite_eq_left hx, ite_eq_left hx] at h
      obtain ⟨hemit, hrest⟩ := List.cons.inj h
      rw [hemit] at hrest
      have ih := harmonic_of_runFrom_eq_self hs xs (some x)
        (fun _ h => Option.mem_some_iff.mp h ▸ hx) hrest
      rw [sys.pattern.tier_cons_of_onTier ((sys.pattern_onTier x).mpr hx)]
      cases a? with
      | none => exact ih
      | some a =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs a (ha a rfl)).2
        rw [Option.bind_some, hv, sys.emit_some_of_target (hs x hx).1] at hemit
        have hvx : sys.value x = some v := by
          have := sys.value_write v x (hs x hx).1; rwa [hemit] at this
        exact Or.inr (Or.inr
          ((sys.toTierRule.value_eq_of_transmits_eq_some hv).trans hvx.symm))
    · rw [ite_eq_right hx, ite_eq_right hx] at h
      rw [sys.pattern.tier_cons_of_not_onTier (fun h' => hx ((sys.pattern_onTier x).mp h'))]
      exact harmonic_of_runFrom_eq_self hs xs a? ha (List.cons.inj h).2

/-- On a saturated system without a default the harmonic words are exactly the fixed points
of the run. -/
theorem harmonic_iff_scan_eq_self (hs : sys.Saturated) (hd : sys.default = none)
    (hb : ∀ s, sys.IsOpaque s → ¬ sys.IsTarget s) (w : List α) :
    sys.pattern.Harmonic w ↔ sys.scan w = w :=
  ⟨sys.scan_eq_self_of_harmonic hd hb,
    sys.harmonic_of_runFrom_eq_self hs w none (fun _ h => by cases h)⟩

private theorem runFrom_some_eq_map (hs : sys.Saturated)
    (ht : ∀ v s, sys.transmits (sys.write v s) = some v) (v : Bool) :
    ∀ w : List α, sys.toMealy.runFrom (some v) w =
      w.map fun s => if sys.tier s then sys.write v s else s
  | [] => rfl
  | x :: xs => by
    rw [Mealy.runFrom_cons, TierRule.toMealy_output, TierRule.toMealy_step, List.map_cons]
    by_cases hx : sys.tier x
    · rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx, sys.emit_some_of_target (hs x hx).1,
        ht, runFrom_some_eq_map hs ht v xs]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx, runFrom_some_eq_map hs ht v xs]

/-- On a saturated system without a default whose writes are transmitted, the run writes the
first tier segment's value into every tier segment. -/
theorem scan_eq_map (hs : sys.Saturated) (ht : ∀ v s, sys.transmits (sys.write v s) = some v)
    (hd : sys.default = none) (w : List α) : sys.scan w = w.map fun s =>
      if sys.tier s then ((sys.pattern.tier w).head?.bind sys.transmits).elim s (sys.write · s)
      else s := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rw [TierRule.scan, Mealy.run, TierRule.toMealy_initial, Mealy.runFrom_cons,
      TierRule.toMealy_output, TierRule.toMealy_step, List.map_cons]
    by_cases hx : sys.tier x
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs x hx).2
      rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx,
        sys.toTierRule.emit_none_of_default_eq_none hd, hv,
        sys.pattern.tier_cons_of_onTier ((sys.pattern_onTier x).mpr hx), List.head?_cons,
        Option.bind_some, hv,
        Option.elim_some, sys.write_value v x (hs x hx).1
          (sys.toTierRule.value_eq_of_transmits_eq_some hv), sys.runFrom_some_eq_map hs ht]
      simp only [Option.elim_some]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx,
        sys.pattern.tier_cons_of_not_onTier (fun h' => hx ((sys.pattern_onTier x).mp h'))]
      exact congrArg _ ih

private theorem runFrom_harmonic (hs : sys.Saturated)
    (ht : ∀ v s, sys.transmits (sys.write v s) = some v)
    (hw : ∀ v s, sys.tier s → sys.tier (sys.write v s)) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.tier a) →
      (a?.toList ++ sys.pattern.tier (sys.toMealy.runFrom (a?.bind sys.transmits) w)).IsChain
        sys.pattern.Compatible
  | [], none, _ => List.isChain_nil
  | [], some _, _ => List.isChain_singleton _
  | x :: xs, a?, ha => by
    rw [Mealy.runFrom_cons, TierRule.toMealy_output, TierRule.toMealy_step]
    by_cases hx : sys.tier x
    · rw [ite_eq_left hx, ite_eq_left hx]
      have he : sys.tier (sys.emit (a?.bind sys.transmits) x) :=
        sys.toTierRule.tier_emit hw hx _
      rw [sys.pattern.tier_cons_of_onTier ((sys.pattern_onTier _).mpr he)]
      have ih := runFrom_harmonic hs ht hw xs (some (sys.emit (a?.bind sys.transmits) x))
        (fun _ h => Option.mem_some_iff.mp h ▸ he)
      cases a? with
      | none => exact ih
      | some a =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs a (ha a rfl)).2
        rw [Option.bind_some, hv] at ih ⊢
        rw [sys.emit_some_of_target (hs x hx).1]
        exact Or.inr (Or.inr ((sys.toTierRule.value_eq_of_transmits_eq_some hv).trans
          (sys.value_write v x (hs x hx).1).symm))
    · rw [ite_eq_right hx, ite_eq_right hx,
        sys.pattern.tier_cons_of_not_onTier (fun h' => hx ((sys.pattern_onTier x).mp h'))]
      exact runFrom_harmonic hs ht hw xs a? ha

/-- On a saturated system whose writes are transmitted and stay on the tier, the run's output
is harmonic. -/
theorem harmonic_scan (hs : sys.Saturated) (ht : ∀ v s, sys.transmits (sys.write v s) = some v)
    (hw : ∀ v s, sys.tier s → sys.tier (sys.write v s)) (w : List α) :
    sys.pattern.Harmonic (sys.scan w) :=
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
