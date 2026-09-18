/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Harmony.Basic
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.SearchCopy

/-!
# Harmony systems

A harmony system is [rose-walker-2011]'s descriptive object: a `Phonology.Harmony.Pattern`,
whose participation classes are the triggers, blockers and transparent segments, together
with the targets and a write of the harmonic value into them. It commits to no mechanism.
Its search-and-copy reading (`System.searchCopy`) is [nevins-2010]'s procedure with the
pattern's tier as the visible segments, its participating segments as the sources and its
direction as the direction of search; the rival accounts, autosegmental spreading
([goldsmith-1976]), Agreement by Correspondence ([rose-walker-2004]) and OT alignment, are
not derived here. Under that reading a harmonic word is a fixed point of the run
(`System.scan_eq_self_of_harmonic`), and on a saturated system the fixed points are exactly
the harmonic words (`System.harmonic_iff_scan_eq_self`), the TSL₂ language of
`Pattern.harmonic_iff_mem_tsl`.

## Main definitions

* `System`: a pattern, its targets and its write; `System.mk'` compiles the
  [rose-walker-2011] roles over `Phonology.Segment`.
* `System.searchCopy`: the search-and-copy reading.
* `System.Saturated`: every visible segment is a participating target with a value.

## Main results

* `System.scan_eq_self_of_harmonic`, `System.harmonic_iff_scan_eq_self`,
  `System.harmonic_scan`: the run's fixed points and image against the pattern's surface
  harmonicity.
* `System.scan_eq_map`: on a saturated system the run writes the first visible segment's
  value into every visible segment.

## Implementation notes

Under the search-and-copy reading a blocker is a visible non-source: the search stops at it
and the target takes the default, as in [nevins-2010]'s defective intervention and
[belth-2026]'s Khalkha rule. [ritter-vanderhulst-2024-themes]'s reading, on which a blocker
imposes its own value, is the case where the blocker's pattern value is the default;
`Pattern.Harmonic` follows that reading, so the fixed-point results assume no default and
blockers that are not targets. Every participating segment donates whether or not it is a
target, as [nevins-2010] requires. An icy target is a target that is not a source, which the
reading expresses because participation is stored on the segment; on bare segments
[burness-mcmullin-nevins-2024] show that search and copy cannot. A bidirectional pattern is
run left to right; the outward-from-root pass is not modelled. A single tier is not always
enough: Uyghur backness harmony is not TSL ([mayer-major-2018]).

## References

* [rose-walker-2011]
* [nevins-2010]
* [ritter-vanderhulst-2024-themes]
* [burness-mcmullin-nevins-2024]
* [belth-2026]
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

open Phonology (Segment Feature SearchCopy)

/-! ### Systems -/

/-- A harmony system consists of a pattern, the targets, a write of the harmonic value into
a target, which with the pattern's valuation forms a lens on the targets, and a last-resort
default. -/
structure System (α : Type*) where
  /-- The descriptive pattern. -/
  pattern : Pattern α Bool
  /-- The segments that undergo. -/
  IsTarget : α → Prop
  [decTarget : DecidablePred IsTarget]
  /-- Write the harmonic value into a segment. -/
  write : Bool → α → α
  /-- Reading back a value written into a target gives that value. -/
  value_write : ∀ v s, IsTarget s → pattern.value (write v s) = some v
  /-- Writing the value a target already carries leaves it unchanged. -/
  write_value : ∀ v s, IsTarget s → pattern.value s = some v → write v s = s
  /-- The value a target takes when no source reaches it. -/
  default : Option Bool := none

attribute [instance] System.decTarget

namespace System

variable {α : Type*} (sys : System α)

/-- The search-and-copy reading of a system: the pattern's tier is the visible segments,
its participating segments are the sources, and its direction is the direction of search. -/
def searchCopy : SearchCopy α where
  tier := sys.pattern.OnTier
  IsTarget := sys.IsTarget
  IsSource _ s := sys.pattern.participation s = .participating
  value := sys.pattern.value
  write := sys.write
  value_write := sys.value_write
  write_value := sys.write_value
  default := sys.default
  direction := sys.pattern.direction.toScanDirection

@[simp] theorem searchCopy_tier : sys.searchCopy.tier = sys.pattern.OnTier := rfl

@[simp] theorem searchCopy_isTarget : sys.searchCopy.IsTarget = sys.IsTarget := rfl

@[simp] theorem searchCopy_isSource (t s : α) :
    sys.searchCopy.IsSource t s ↔ sys.pattern.participation s = .participating :=
  Iff.rfl

@[simp] theorem searchCopy_value : sys.searchCopy.value = sys.pattern.value := rfl

@[simp] theorem searchCopy_write : sys.searchCopy.write = sys.write := rfl

@[simp] theorem searchCopy_default : sys.searchCopy.default = sys.default := rfl

@[simp] theorem searchCopy_direction :
    sys.searchCopy.direction = sys.pattern.direction.toScanDirection := rfl

theorem found_some_of_participating {a : α} (h : sys.pattern.participation a = .participating)
    (t : α) : sys.searchCopy.found t (some a) = sys.pattern.value a :=
  sys.searchCopy.found_some_of_isSource h

theorem found_some_of_not_participating {a : α}
    (h : sys.pattern.participation a ≠ .participating) (t : α) :
    sys.searchCopy.found t (some a) = none :=
  sys.searchCopy.found_some_of_not_isSource h

theorem emit_some_of_target {s : α} (h : sys.IsTarget s) (w : Option α) (v : Bool)
    (hf : sys.searchCopy.found s w = some v) : sys.searchCopy.emit w s = sys.write v s := by
  rw [sys.searchCopy.emit_of_target h, hf]; rfl

/-- Compiles the [rose-walker-2011] roles over `Phonology.Segment` from the harmonic feature,
the targets, the transparent segments, the direction, the blockers, and the default; every
other segment is a trigger. -/
def mk' (feature : Feature) (isTarget isTransparent : Segment → Bool)
    (direction : Direction := .rightward) (isBlocker : Segment → Bool := fun _ => false)
    (default : Option Bool := none) : System Segment where
  pattern :=
    { value := fun s => s feature
      participation := fun s =>
        if isBlocker s then .opaque
        else if isTransparent s then .transparent
        else .participating
      direction := direction }
  IsTarget s := isTarget s = true
  write v s := Function.update s feature (some v)
  value_write _ _ _ := Function.update_self ..
  write_value _ _ _ h := h ▸ Function.update_eq_self ..
  default := default

/-! ### Fixed points and image -/

/-- After the visible segment `a?`, a word whose tier continues it compatibly is left
unchanged, provided there is no default and blockers do not undergo. -/
private theorem runFrom_eq_self (hd : sys.default = none)
    (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) :
    ∀ (w : List α) (a? : Option α),
      (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible →
        sys.searchCopy.toMealy.runFrom a? w = w
  | [], _, _ => rfl
  | x :: xs, a?, h => by
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, SearchCopy.toMealy_step]
    by_cases hx : sys.searchCopy.tier x
    · rw [sys.pattern.tier_cons_of_onTier hx] at h
      have hemit : sys.searchCopy.emit a? x = x := by
        cases a? with
        | none => exact sys.searchCopy.emit_of_found_eq_none hd (sys.searchCopy.found_none x)
        | some a =>
          by_cases ht : sys.IsTarget x
          · by_cases hs : sys.pattern.participation a = .participating
            · rcases (List.isChain_cons_cons.mp h).1 with hicy | hop | hval
              · rw [hicy] at hs; cases hs
              · exact absurd ht (hb x hop)
              · rcases hv : sys.pattern.value a with _ | v
                · exact sys.searchCopy.emit_of_found_eq_none hd
                    (by rw [sys.found_some_of_participating hs, hv])
                · exact sys.searchCopy.emit_eq_self
                    (by rw [sys.found_some_of_participating hs, hv]) (hval ▸ hv)
            · exact sys.searchCopy.emit_of_found_eq_none hd
                (sys.found_some_of_not_participating hs x)
          · exact sys.searchCopy.emit_of_not_target ht _
      rw [ite_eq_left hx, ite_eq_left hx, hemit]
      refine congrArg _ (runFrom_eq_self hd hb xs (some x) ?_)
      cases a? with
      | none => exact h
      | some a => exact (List.isChain_cons_cons.mp h).2
    · rw [sys.pattern.tier_cons_of_not_onTier hx] at h
      rw [ite_eq_right hx, ite_eq_right hx]
      exact congrArg _ (runFrom_eq_self hd hb xs a? h)

/-- A harmonic word is a fixed point of the run, provided there is no default and blockers
do not undergo. -/
theorem scan_eq_self_of_harmonic (hd : sys.default = none)
    (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) {w : List α}
    (h : sys.pattern.Harmonic w) : sys.searchCopy.scan w = w :=
  sys.runFrom_eq_self hd hb w none h

/-- A system is saturated when every visible segment is a participating target with a value;
on such a system the run decides the surface language. -/
def Saturated : Prop :=
  ∀ s, sys.pattern.OnTier s →
    sys.IsTarget s ∧ sys.pattern.participation s = .participating ∧ (sys.pattern.value s).isSome

private theorem harmonic_of_runFrom_eq_self (hs : sys.Saturated) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.pattern.OnTier a) →
      sys.searchCopy.toMealy.runFrom a? w = w →
        (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible
  | [], none, _, _ => List.isChain_nil
  | [], some _, _, _ => List.isChain_singleton _
  | x :: xs, a?, ha, h => by
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, SearchCopy.toMealy_step] at h
    by_cases hx : sys.searchCopy.tier x
    · rw [ite_eq_left hx, ite_eq_left hx] at h
      obtain ⟨hemit, hrest⟩ := List.cons.inj h
      rw [hemit] at hrest
      have ih := harmonic_of_runFrom_eq_self hs xs (some x)
        (fun _ h => Option.mem_some_iff.mp h ▸ hx) hrest
      rw [sys.pattern.tier_cons_of_onTier hx]
      cases a? with
      | none => exact ih
      | some a =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih⟩
        obtain ⟨_, hpa, hv⟩ := hs a (ha a rfl)
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
        rw [sys.emit_some_of_target (hs x hx).1 _ v
          (by rw [sys.found_some_of_participating hpa, hv])] at hemit
        have hvx : sys.pattern.value x = some v := by
          have := sys.value_write v x (hs x hx).1; rwa [hemit] at this
        exact Or.inr (Or.inr (hv.trans hvx.symm))
    · rw [ite_eq_right hx, ite_eq_right hx] at h
      rw [sys.pattern.tier_cons_of_not_onTier hx]
      exact harmonic_of_runFrom_eq_self hs xs a? ha (List.cons.inj h).2

/-- On a saturated system without a default the harmonic words are exactly the fixed points
of the run. -/
theorem harmonic_iff_scan_eq_self (hs : sys.Saturated) (hd : sys.default = none)
    (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) (w : List α) :
    sys.pattern.Harmonic w ↔ sys.searchCopy.scan w = w :=
  ⟨sys.scan_eq_self_of_harmonic hd hb,
    sys.harmonic_of_runFrom_eq_self hs w none (fun _ h => by cases h)⟩

private theorem runFrom_some_eq_map (hs : sys.Saturated)
    (hw : ∀ v s, sys.pattern.OnTier s → sys.pattern.OnTier (sys.write v s)) (v : Bool) :
    ∀ (w : List α) (a : α), sys.pattern.OnTier a → sys.pattern.value a = some v →
      sys.searchCopy.toMealy.runFrom (some a) w =
        w.map fun s => if sys.pattern.OnTier s then sys.write v s else s
  | [], _, _, _ => rfl
  | x :: xs, a, ha, hv => by
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, SearchCopy.toMealy_step,
      List.map_cons]
    by_cases hx : sys.searchCopy.tier x
    · have he : sys.searchCopy.emit (some a) x = sys.write v x :=
        sys.emit_some_of_target (hs x hx).1 _ v
          (by rw [sys.found_some_of_participating (hs a ha).2.1, hv])
      rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left (show sys.pattern.OnTier x from hx), he,
        runFrom_some_eq_map hs hw v xs (sys.write v x) (hw v x hx)
          (sys.value_write v x (hs x hx).1)]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right (show ¬ sys.pattern.OnTier x from hx),
        runFrom_some_eq_map hs hw v xs a ha hv]

/-- On a saturated system without a default whose writes stay visible, the run writes the
first visible segment's value into every visible segment. -/
theorem scan_eq_map (hs : sys.Saturated)
    (hw : ∀ v s, sys.pattern.OnTier s → sys.pattern.OnTier (sys.write v s))
    (hd : sys.default = none) (w : List α) : sys.searchCopy.scan w = w.map fun s =>
      if sys.pattern.OnTier s then
        ((sys.pattern.tier w).head?.bind sys.pattern.value).elim s (sys.write · s)
      else s := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rw [SearchCopy.scan, Mealy.run, SearchCopy.toMealy_initial, Mealy.runFrom_cons,
      SearchCopy.toMealy_output, SearchCopy.toMealy_step, List.map_cons]
    by_cases hx : sys.searchCopy.tier x
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs x hx).2.2
      rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left (show sys.pattern.OnTier x from hx),
        sys.searchCopy.emit_of_found_eq_none hd (sys.searchCopy.found_none x),
        sys.pattern.tier_cons_of_onTier hx, List.head?_cons, Option.bind_some, hv,
        Option.elim_some, sys.write_value v x (hs x hx).1 hv,
        sys.runFrom_some_eq_map hs hw v xs x hx hv]
      simp only [Option.elim_some]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right (show ¬ sys.pattern.OnTier x from hx),
        sys.pattern.tier_cons_of_not_onTier hx]
      exact congrArg _ ih

private theorem runFrom_harmonic (hs : sys.Saturated)
    (hw : ∀ v s, sys.pattern.OnTier s → sys.pattern.OnTier (sys.write v s)) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.pattern.OnTier a) →
      (a?.toList ++ sys.pattern.tier (sys.searchCopy.toMealy.runFrom a? w)).IsChain
        sys.pattern.Compatible
  | [], none, _ => List.isChain_nil
  | [], some _, _ => List.isChain_singleton _
  | x :: xs, a?, ha => by
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, SearchCopy.toMealy_step]
    by_cases hx : sys.searchCopy.tier x
    · rw [ite_eq_left hx, ite_eq_left hx]
      have he : sys.pattern.OnTier (sys.searchCopy.emit a? x) := sys.searchCopy.tier_emit hw hx _
      rw [sys.pattern.tier_cons_of_onTier he]
      have ih := runFrom_harmonic hs hw xs (some (sys.searchCopy.emit a? x))
        (fun _ h => Option.mem_some_iff.mp h ▸ he)
      cases a? with
      | none => exact ih
      | some a =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih⟩
        obtain ⟨_, hpa, hv⟩ := hs a (ha a rfl)
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
        have he' : sys.searchCopy.emit (some a) x = sys.write v x :=
          sys.emit_some_of_target (hs x hx).1 _ v
            (by rw [sys.found_some_of_participating hpa, hv])
        rw [he'] at ih ⊢
        exact Or.inr (Or.inr (hv.trans (sys.value_write v x (hs x hx).1).symm))
    · rw [ite_eq_right hx, ite_eq_right hx, sys.pattern.tier_cons_of_not_onTier hx]
      exact runFrom_harmonic hs hw xs a? ha

/-- On a saturated system whose writes stay visible, the run's output is harmonic. -/
theorem harmonic_scan (hs : sys.Saturated)
    (hw : ∀ v s, sys.pattern.OnTier s → sys.pattern.OnTier (sys.write v s)) (w : List α) :
    sys.pattern.Harmonic (sys.searchCopy.scan w) :=
  sys.runFrom_harmonic hs hw w none (fun _ h => by cases h)

end System

end Phonology.Harmony
