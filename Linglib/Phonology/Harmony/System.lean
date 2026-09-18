/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.ForbiddenPairs
import Linglib.Phonology.Harmony.Basic
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.SearchCopy

/-!
# Harmony systems

A harmony system is a `Phonology.SearchCopy` rule with the `Agree` relation together with
its blockers: [rose-walker-2011]'s triggers, targets, blockers and transparent segments are
the rule's sources, its targets, the visible segments it marks opaque, and the invisible
segments. The system presents a `Phonology.Harmony.Pattern` (`System.pattern`), whose icy
targets ([jurgec-2011]) are the targets no target may copy from. Harmonic words are fixed
points of the run (`System.scan_eq_self_of_harmonic`); when every visible segment is a
target and a source, the fixed points are exactly the harmonic words
(`System.harmonic_iff_scan_eq_self`), which form a TSL₂ language
(`Pattern.harmonic_iff_mem_tsl`, [aksenova-rawski-graf-heinz-2024]).

## Main definitions

* `System`: a search-and-copy rule with `Agree` and a class of blockers; `System.mk'`
  compiles the [rose-walker-2011] roles over `Phonology.Segment`.
* `System.pattern`: the pattern the system presents.
* `System.Saturated`: every visible segment is a target and a source and carries a value.

## Main results

* `System.scan_eq_self_of_harmonic`, `System.harmonic_iff_scan_eq_self`,
  `System.harmonic_scan`: the run's fixed points and image against the pattern's surface
  harmonicity.
* `System.scan_eq_map`: on a saturated system the run writes the first visible segment's
  value into every visible segment.
* `Pattern.harmonic_iff_mem_tsl`.

## Implementation notes

The fixed-point results assume no default: a default writes a value the surface phonotactic
cannot see, so the run of a system with a default has unspecified fixed points outside the
harmonic words. They read the tier left to right, as `Pattern.Harmonic` does, so they are
stated for `scan`; `apply` runs in the pattern's direction, and a bidirectional pattern,
whose outward-from-root pass is not modelled, is run left to right. A blocker that is a
source imposes its own value ([ritter-vanderhulst-2024-themes]); one that is not stops the
value. This is the tier-based account, one live analysis among autosegmental spreading
([goldsmith-1976]), Agreement by Correspondence ([rose-walker-2004]) and OT alignment, and
a single tier is not always enough: Uyghur backness harmony is not TSL ([mayer-major-2018]).

## References

* [rose-walker-2011]
* [nevins-2010]
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

open Phonology (Segment Feature SearchCopy)

/-! ### Systems -/

/-- A harmony system is a search-and-copy rule with the `Agree` relation together with its
blockers, the visible segments that do not undergo and are exempt from agreeing with what
precedes them. -/
structure System (α : Type*) extends SearchCopy α where
  /-- The blockers. -/
  IsOpaque : α → Prop
  [decOpaque : DecidablePred IsOpaque]
  /-- Harmony is agreement. -/
  relation_eq : relation = .agree := by rfl

attribute [instance] System.decOpaque

namespace System

variable {α : Type*} (sys : System α)

/-- The pattern a system presents: an invisible segment is transparent, a blocker is opaque,
a target no target may copy from is icy, and every other visible segment participates. -/
def pattern [Fintype α] : Pattern α Bool where
  value := sys.value
  participation s :=
    if sys.tier s then
      if sys.IsOpaque s then .opaque
      else if sys.IsTarget s ∧ ∀ t, ¬ sys.IsSource t s then .icyTarget
      else .participating
    else .transparent
  direction := Direction.ofScanDirection sys.direction

section Pattern

variable [Fintype α]

@[simp] theorem pattern_value : sys.pattern.value = sys.value := rfl

theorem pattern_participation (s : α) : sys.pattern.participation s =
    if sys.tier s then
      if sys.IsOpaque s then .opaque
      else if sys.IsTarget s ∧ ∀ t, ¬ sys.IsSource t s then .icyTarget
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

theorem not_isSource_of_participation {s : α} (h : sys.pattern.participation s = .icyTarget)
    (t : α) : ¬ sys.IsSource t s := by
  rw [pattern_participation] at h; split_ifs at h; simp_all

end Pattern

theorem emit_some_of_target {s : α} (h : sys.IsTarget s) (w : Option α) (v : Bool)
    (hf : sys.found s w = some v) : sys.emit w s = sys.write v s := by
  rw [sys.toSearchCopy.emit_of_target h, hf, sys.relation_eq]; rfl

/-- A segment already carrying the value it finds is emitted unchanged. -/
theorem emit_eq_self {s : α} {w : Option α} {v : Bool} (hf : sys.found s w = some v)
    (h : sys.value s = some v) : sys.emit w s = s :=
  sys.toSearchCopy.emit_eq_self hf (by rw [sys.relation_eq]; exact h)

/-- Compiles the [rose-walker-2011] roles over `Phonology.Segment` from the harmonic feature,
the triggers, the targets, the transparent segments, the direction, the blockers, and the
default. -/
def mk' (feature : Feature) (isTrigger isTarget isTransparent : Segment → Bool)
    (direction : Direction := .rightward) (isBlocker : Segment → Bool := fun _ => false)
    (default : Option Bool := none) : System Segment where
  tier s := isTransparent s = false
  IsTarget s := isTarget s = true
  IsSource _ s := isTrigger s = true
  value s := s feature
  write v s := Function.update s feature (some v)
  value_write _ _ _ := Function.update_self ..
  write_value _ _ _ h := h ▸ Function.update_eq_self ..
  default := default
  direction := direction.toScanDirection
  IsOpaque s := isBlocker s = true

/-! ### Fixed points and image -/

/-- A system is saturated when every visible segment is a target and a source and carries a
value; on such a system the run decides the surface language. -/
def Saturated : Prop :=
  ∀ s, sys.tier s → sys.IsTarget s ∧ (∀ t, sys.IsSource t s) ∧ (sys.value s).isSome

private theorem runFrom_some_eq_map (hs : sys.Saturated)
    (hw : ∀ v s, sys.tier s → sys.tier (sys.write v s)) (v : Bool) :
    ∀ (w : List α) (a : α), sys.tier a → sys.value a = some v →
      sys.toMealy.runFrom (some a) w = w.map fun s => if sys.tier s then sys.write v s else s
  | [], _, _, _ => rfl
  | x :: xs, a, ha, hv => by
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, SearchCopy.toMealy_step, List.map_cons]
    by_cases hx : sys.tier x
    · have he : sys.emit (some a) x = sys.write v x :=
        sys.emit_some_of_target (hs x hx).1 _ v
          (by rw [sys.found_some_of_isSource ((hs a ha).2.1 x), hv])
      rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx, he,
        runFrom_some_eq_map hs hw v xs (sys.write v x) (hw v x hx) (sys.value_write v x (hs x hx).1)]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx, runFrom_some_eq_map hs hw v xs a ha hv]

variable [Fintype α]

/-- After the visible segment `a?`, a word whose tier continues it compatibly is left
unchanged, provided there is no default and blockers do not undergo. -/
private theorem runFrom_eq_self (hd : sys.default = none)
    (hb : ∀ s, sys.IsOpaque s → ¬ sys.IsTarget s) : ∀ (w : List α) (a? : Option α),
      (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible →
        sys.toMealy.runFrom a? w = w
  | [], _, _ => rfl
  | x :: xs, a?, h => by
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, SearchCopy.toMealy_step]
    by_cases hx : sys.tier x
    · rw [sys.pattern.tier_cons_of_onTier ((sys.pattern_onTier x).mpr hx)] at h
      have hemit : sys.emit a? x = x := by
        cases a? with
        | none => exact sys.toSearchCopy.emit_of_found_eq_none hd (sys.found_none x)
        | some a =>
          by_cases ht : sys.IsTarget x
          · by_cases hs : sys.IsSource x a
            · rcases (List.isChain_cons_cons.mp h).1 with hicy | hop | hval
              · exact absurd hs (sys.not_isSource_of_participation hicy x)
              · exact absurd ht (hb x (sys.isOpaque_of_participation hop))
              · rcases hv : sys.value a with _ | v
                · exact sys.toSearchCopy.emit_of_found_eq_none hd
                    (by rw [sys.found_some_of_isSource hs, hv])
                · exact sys.emit_eq_self (by rw [sys.found_some_of_isSource hs, hv])
                    ((show sys.value a = sys.value x from hval) ▸ hv)
            · exact sys.toSearchCopy.emit_of_found_eq_none hd
                (sys.found_some_of_not_isSource hs)
          · exact sys.toSearchCopy.emit_of_not_target ht _
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

private theorem harmonic_of_runFrom_eq_self (hs : sys.Saturated) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.tier a) →
      sys.toMealy.runFrom a? w = w →
        (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible
  | [], none, _, _ => List.isChain_nil
  | [], some _, _, _ => List.isChain_singleton _
  | x :: xs, a?, ha, h => by
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, SearchCopy.toMealy_step] at h
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
        obtain ⟨_, hsrc, hv⟩ := hs a (ha a rfl)
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
        rw [sys.emit_some_of_target (hs x hx).1 _ v
          (by rw [sys.found_some_of_isSource (hsrc x), hv])] at hemit
        have hvx : sys.value x = some v := by
          have := sys.value_write v x (hs x hx).1; rwa [hemit] at this
        exact Or.inr (Or.inr (hv.trans hvx.symm))
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

/-- On a saturated system without a default whose writes stay visible, the run writes the
first visible segment's value into every visible segment. -/
theorem scan_eq_map (hs : sys.Saturated) (hw : ∀ v s, sys.tier s → sys.tier (sys.write v s))
    (hd : sys.default = none) (w : List α) : sys.scan w = w.map fun s =>
      if sys.tier s then ((sys.pattern.tier w).head?.bind sys.value).elim s (sys.write · s)
      else s := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rw [SearchCopy.scan, Mealy.run, SearchCopy.toMealy_initial, Mealy.runFrom_cons,
      SearchCopy.toMealy_output, SearchCopy.toMealy_step, List.map_cons]
    by_cases hx : sys.tier x
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs x hx).2.2
      rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx,
        sys.toSearchCopy.emit_of_found_eq_none hd (sys.found_none x),
        sys.pattern.tier_cons_of_onTier ((sys.pattern_onTier x).mpr hx), List.head?_cons,
        Option.bind_some, hv, Option.elim_some, sys.write_value v x (hs x hx).1 hv,
        sys.runFrom_some_eq_map hs hw v xs x hx hv]
      simp only [Option.elim_some]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx,
        sys.pattern.tier_cons_of_not_onTier (fun h' => hx ((sys.pattern_onTier x).mp h'))]
      exact congrArg _ ih

private theorem runFrom_harmonic (hs : sys.Saturated)
    (hw : ∀ v s, sys.tier s → sys.tier (sys.write v s)) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.tier a) →
      (a?.toList ++ sys.pattern.tier (sys.toMealy.runFrom a? w)).IsChain sys.pattern.Compatible
  | [], none, _ => List.isChain_nil
  | [], some _, _ => List.isChain_singleton _
  | x :: xs, a?, ha => by
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, SearchCopy.toMealy_step]
    by_cases hx : sys.tier x
    · rw [ite_eq_left hx, ite_eq_left hx]
      have he : sys.tier (sys.emit a? x) := sys.toSearchCopy.tier_emit hw hx _
      rw [sys.pattern.tier_cons_of_onTier ((sys.pattern_onTier _).mpr he)]
      have ih := runFrom_harmonic hs hw xs (some (sys.emit a? x))
        (fun _ h => Option.mem_some_iff.mp h ▸ he)
      cases a? with
      | none => exact ih
      | some a =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih⟩
        obtain ⟨_, hsrc, hv⟩ := hs a (ha a rfl)
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
        have he' : sys.emit (some a) x = sys.write v x :=
          sys.emit_some_of_target (hs x hx).1 _ v
            (by rw [sys.found_some_of_isSource (hsrc x), hv])
        rw [he'] at ih ⊢
        exact Or.inr (Or.inr (hv.trans (sys.value_write v x (hs x hx).1).symm))
    · rw [ite_eq_right hx, ite_eq_right hx,
        sys.pattern.tier_cons_of_not_onTier (fun h' => hx ((sys.pattern_onTier x).mp h'))]
      exact runFrom_harmonic hs hw xs a? ha

/-- On a saturated system whose writes stay visible, the run's output is harmonic. -/
theorem harmonic_scan (hs : sys.Saturated) (hw : ∀ v s, sys.tier s → sys.tier (sys.write v s))
    (w : List α) : sys.pattern.Harmonic (sys.scan w) :=
  sys.runFrom_harmonic hs hw w none (fun _ h => by cases h)

end System

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
