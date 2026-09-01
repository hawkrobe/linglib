/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Forall2
import Mathlib.Logic.Function.Defs
import Linglib.Phonology.Tone.Basic

/-!
# Register: the terracing realization of `[raised]`

The syntagmatic reading of `[raised]` ([snider-1999], [lionnet-2025]): each `[-raised]`
node lowers the register for everything that follows and each `[+raised]` node raises it,
so a node sequence is realized as the running sum of its shifts from a baseline —
terracing, as in the register-only systems of Drubea and Numèè and in the catathesis of
Japanese and English intonation ([beckman-pierrehumbert-1986]).

## Main definitions

* `TRN.pitchEffect` — the shift a node contributes.
* `realizePitch` — the pitch levels of a sequence from a baseline, the running sums
  (`List.scanl`); `pitchDeltas`, the same from `0`.

## Main results

* `realizePitch_eq_pitchDeltas_shift` — a baseline only shifts the deltas.
* `realizePitch_mono` — realization is monotone in the baseline and, pointwise, in the
  shifts: the basis of catathesis blocking.
-/

namespace Tone

open Function

/-- The register shift a node contributes: `[-raised]` lowers, `[+raised]` raises, an
unspecified `[raised]` is inert. -/
def TRN.pitchEffect (t : TRN) : Int :=
  match t.raised with
  | none => 0
  | some false => -1
  | some true => 1

/-- **Terracing**: the pitch levels of a node sequence from a baseline, each shift
cumulative — the running sums of the shifts. -/
def realizePitch (level : Int) (ts : List TRN) : List Int :=
  ((ts.map TRN.pitchEffect).scanl (· + ·) level).tail

@[simp] theorem realizePitch_nil (level : Int) : realizePitch level [] = [] := rfl

@[simp] theorem realizePitch_cons (level : Int) (t : TRN) (rest : List TRN) :
    realizePitch level (t :: rest) =
      (level + t.pitchEffect) :: realizePitch (level + t.pitchEffect) rest := by
  cases rest <;> simp [realizePitch, List.scanl]

@[simp] theorem length_realizePitch (level : Int) (ts : List TRN) :
    (realizePitch level ts).length = ts.length := by
  simp [realizePitch]

/-- The register shifts from the start: no privileged pitch, only the differences. -/
def pitchDeltas (ts : List TRN) : List Int := realizePitch 0 ts

/-- A baseline only shifts the deltas. -/
theorem realizePitch_eq_pitchDeltas_shift (level : Int) (ts : List TRN) :
    realizePitch level ts = (pitchDeltas ts).map (· + level) := by
  suffices h : ∀ n d : Int, realizePitch (n + d) ts = (realizePitch n ts).map (· + d) by
    simpa [pitchDeltas] using h 0 level
  intro n d
  induction ts generalizing n with
  | nil => rfl
  | cons t rest ih =>
    simp only [realizePitch_cons, List.map_cons]
    rw [show n + d + t.pitchEffect = n + t.pitchEffect + d by omega, ih]

/-- **Monotonicity**: pointwise lower shifts and a lower baseline give pointwise lower
pitch. Structural basis of catathesis blocking ([beckman-pierrehumbert-1986]): a register
reset at a phrase boundary leaves everything after it higher than continued compression
would. -/
theorem realizePitch_mono {ts₁ ts₂ : List TRN}
    (hts : List.Forall₂ ((· ≤ ·) on TRN.pitchEffect) ts₁ ts₂) {n m : Int} (hnm : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realizePitch n ts₁) (realizePitch m ts₂) := by
  induction hts generalizing n m with
  | nil => exact .nil
  | cons hhead _ ih =>
    have hstep := Int.add_le_add hnm hhead
    simp only [realizePitch_cons]
    exact .cons hstep (ih hstep)

/-- A higher baseline gives pointwise higher pitch for a fixed sequence. -/
theorem realizePitch_baseline_mono (ts : List TRN) {n m : Int} (h : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realizePitch n ts) (realizePitch m ts) :=
  realizePitch_mono (List.forall₂_same.mpr fun _ _ => le_rfl) h

end Tone
