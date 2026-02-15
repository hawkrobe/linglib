import Linglib.Phenomena.ConditionalModality.Data
import Mathlib.Data.Rat.Cast.Order

/-!
# Degree Collapse — Kratzer 2012 §2.5

Modal strength as a degree: the proportion of best worlds where the
prejacent holds. This formalizes Kratzer's observation that ordering sources
create a spectrum of modal strength between bare possibility and necessity.

- Strength 1 = all best worlds satisfy p → necessity
- Strength 0 = no best world satisfies p → impossibility
- 0 < strength < 1 = graded possibility

Reuses the rain/wet-streets scenario from `ConditionalModality/Data.lean`
to maximize interconnection density.

Reference: Kratzer, A. (2012). Modals and Conditionals. OUP. Ch. 2 §2.5.
-/

namespace Phenomena.Modality.DegreeCollapse

open IntensionalSemantics.Attitude.Intensional (World)
open IntensionalSemantics.Modal.Kratzer
open Phenomena.ConditionalModality

/-! ## Modal strength as a rational degree -/

/-- **Modal strength**: the proportion of best worlds satisfying p.

    When the set of best worlds is empty (inconsistent base), strength is 0.
    Otherwise, strength = |{w ∈ Best : p(w)}| / |Best|.

    This captures Kratzer's graded modality: the ordering source modulates
    modal strength between bare possibility and necessity. -/
def modalStrength (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) : ℚ :=
  let best := bestWorlds f g w
  if best.isEmpty then 0
  else (best.filter p).length / best.length

/-! ## Concrete scenario: Rain / Wet Streets

We reuse `ConditionalModality.Data`'s rain scenario. With the normalcy
ordering, best = {w0} (normal rain), so streetWet has strength 1.
Without normalcy ordering, best = all rain-worlds {w0, w1}, and
streetWet holds only at w0, so strength = 1/2. -/

/-- **With normalcy ordering**: strength = 1. Best = {w0}, streetWet w0 = true. -/
theorem strength_with_normalcy (w : World) :
    modalStrength (restrictedBase emptyBackground rained) normalcySource streetWet w = 1 := by
  cases w <;> native_decide

/-- **Without normalcy ordering**: strength = 1/2. Best = {w0, w1},
    streetWet w0 = true, streetWet w1 = false. -/
theorem strength_without_normalcy (w : World) :
    modalStrength (restrictedBase emptyBackground rained) emptyBackground streetWet w = 1 / 2 := by
  cases w <;> native_decide

/-! ## General theorems linking strength to modal operators -/

/-- **Strength 1 ↔ necessity** (when best worlds are nonempty). -/
theorem strength_one_iff_necessity (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World)
    (hNonempty : ¬(bestWorlds f g w).isEmpty) :
    modalStrength f g p w = 1 ↔ necessity f g p w = true := by
  simp only [modalStrength, necessity]
  split
  · -- best.isEmpty = true: contradiction
    rename_i h; exact absurd h (by simpa using hNonempty)
  · -- best.isEmpty = false
    rename_i hNe
    have hLen_pos : 0 < (bestWorlds f g w).length := by
      cases hb : bestWorlds f g w with
      | nil => simp [hb, List.isEmpty] at hNe
      | cons _ _ => exact Nat.zero_lt_succ _
    have hCast_ne : (↑(bestWorlds f g w).length : ℚ) ≠ 0 := by
      exact_mod_cast hLen_pos.ne'
    constructor
    · -- Forward: strength = 1 → necessity
      intro hStr
      rw [div_eq_one_iff_eq hCast_ne] at hStr
      have hEqNat : ((bestWorlds f g w).filter p).length = (bestWorlds f g w).length := by
        exact_mod_cast hStr
      have hFilterEq : (bestWorlds f g w).filter p = bestWorlds f g w :=
        List.filter_sublist.eq_of_length hEqNat
      rw [List.all_eq_true]
      exact List.filter_eq_self.mp hFilterEq
    · -- Backward: necessity → strength = 1
      intro hAll
      have hFilterEq : (bestWorlds f g w).filter p = bestWorlds f g w :=
        List.filter_eq_self.mpr (List.all_eq_true.mp hAll)
      rw [hFilterEq]
      exact div_self hCast_ne

/-- **Positive strength ↔ possibility** (when best worlds are nonempty). -/
theorem strength_pos_iff_possibility (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World)
    (hNonempty : ¬(bestWorlds f g w).isEmpty) :
    modalStrength f g p w > 0 ↔ possibility f g p w = true := by
  simp only [modalStrength, possibility]
  split
  · -- best.isEmpty = true: contradiction
    rename_i h; exact absurd h (by simpa using hNonempty)
  · -- best.isEmpty = false
    rename_i hNe
    have hLen_pos : 0 < (bestWorlds f g w).length := by
      cases hb : bestWorlds f g w with
      | nil => simp [hb, List.isEmpty] at hNe
      | cons _ _ => exact Nat.zero_lt_succ _
    have hCast_pos : (0 : ℚ) < ↑(bestWorlds f g w).length := by exact_mod_cast hLen_pos
    constructor
    · -- Forward: strength > 0 → possibility
      intro hStr
      rw [List.any_eq_true]
      have hFilterPos : 0 < ((bestWorlds f g w).filter p).length := by
        by_contra hc
        push_neg at hc
        have hZero : ((bestWorlds f g w).filter p).length = 0 := Nat.eq_zero_of_le_zero hc
        simp only [hZero, Nat.cast_zero, zero_div] at hStr
        exact lt_irrefl 0 hStr
      have hNeNil : (bestWorlds f g w).filter p ≠ [] := by
        intro heq; simp [heq] at hFilterPos
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hNeNil
      rw [List.mem_filter] at hx
      exact ⟨x, hx.1, hx.2⟩
    · -- Backward: possibility → strength > 0
      intro hAny
      rw [List.any_eq_true] at hAny
      obtain ⟨x, hxB, hpx⟩ := hAny
      have hMem : x ∈ (bestWorlds f g w).filter p := List.mem_filter.mpr ⟨hxB, hpx⟩
      have hFilterPos : 0 < ((bestWorlds f g w).filter p).length :=
        List.length_pos_of_mem hMem
      exact div_pos (by exact_mod_cast hFilterPos) hCast_pos

/-- **Empty ordering gives strength = proportion of all accessible worlds.** -/
theorem empty_ordering_strength (f : ModalBase) (p : BProp World) (w : World)
    (hNe : ¬(accessibleWorlds f w).isEmpty) :
    modalStrength f (λ _ => []) p w =
    ↑((accessibleWorlds f w).filter p).length / ↑(accessibleWorlds f w).length := by
  unfold modalStrength
  rw [empty_ordering_simple f w]
  simp [hNe]

end Phenomena.Modality.DegreeCollapse
