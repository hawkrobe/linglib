import Linglib.Phenomena.Modality.Studies.Kratzer2012Scenario
import Mathlib.Data.Rat.Cast.Order

/-!
# Degree Collapse — @cite{kratzer-2012} §2.5

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

open Semantics.Attitudes.Intensional (World)
open Semantics.Modality.Kratzer
open Phenomena.Modality.ConditionalModality

/-! ## Modal strength as a rational degree -/

/-- **Modal strength**: the proportion of best worlds satisfying p.

    When the set of best worlds is empty (inconsistent base), strength is 0.
    Otherwise, strength = |{w ∈ Best : p(w)}| / |Best|.

    This captures Kratzer's graded modality: the ordering source modulates
    modal strength between bare possibility and necessity. -/
def modalStrength (f : ModalBase World) (g : OrderingSource World)
    (p : BProp World) (w : World) : ℚ :=
  let best := bestWorlds f g w
  if best = ∅ then 0
  else (best.filter p).card / best.card

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
theorem strength_one_iff_necessity (f : ModalBase World) (g : OrderingSource World)
    (p : BProp World) (w : World)
    (hNonempty : (bestWorlds f g w).Nonempty) :
    modalStrength f g p w = 1 ↔ necessity f g p w := by
  rw [necessity_iff_all]
  simp only [modalStrength]
  have hNe : bestWorlds f g w ≠ ∅ := hNonempty.ne_empty
  simp only [hNe, ↓reduceIte]
  have hCard_pos : 0 < (bestWorlds f g w).card := Finset.card_pos.mpr hNonempty
  have hCast_ne : (↑(bestWorlds f g w).card : ℚ) ≠ 0 := by exact_mod_cast hCard_pos.ne'
  constructor
  · intro hStr
    rw [div_eq_one_iff_eq hCast_ne] at hStr
    have hCardEq : ((bestWorlds f g w).filter p).card = (bestWorlds f g w).card := by
      exact_mod_cast hStr
    have hFilterEq : (bestWorlds f g w).filter p = bestWorlds f g w :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (le_of_eq hCardEq.symm)
    intro w' hw'
    have hw'_filter : w' ∈ (bestWorlds f g w).filter p := hFilterEq.symm ▸ hw'
    exact (Finset.mem_filter.mp hw'_filter).2
  · intro hAll
    rw [Finset.filter_true_of_mem hAll]
    exact div_self hCast_ne

/-- **Positive strength ↔ possibility** (when best worlds are nonempty). -/
theorem strength_pos_iff_possibility (f : ModalBase World) (g : OrderingSource World)
    (p : BProp World) (w : World)
    (hNonempty : (bestWorlds f g w).Nonempty) :
    modalStrength f g p w > 0 ↔ possibility f g p w := by
  rw [possibility_iff_any]
  simp only [modalStrength]
  have hNe : bestWorlds f g w ≠ ∅ := hNonempty.ne_empty
  simp only [hNe, ↓reduceIte]
  have hCard_pos : 0 < (bestWorlds f g w).card := Finset.card_pos.mpr hNonempty
  have hCast_pos : (0 : ℚ) < ↑(bestWorlds f g w).card := by exact_mod_cast hCard_pos
  constructor
  · intro hStr
    have hFilterPos : 0 < ((bestWorlds f g w).filter p).card := by
      by_contra hc
      push Not at hc
      have hZero : ((bestWorlds f g w).filter p).card = 0 := Nat.eq_zero_of_le_zero hc
      simp only [hZero, Nat.cast_zero, zero_div] at hStr
      exact lt_irrefl 0 hStr
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hFilterPos
    exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
  · intro ⟨x, hxB, hpx⟩
    have hMem : x ∈ (bestWorlds f g w).filter p := Finset.mem_filter.mpr ⟨hxB, hpx⟩
    have hFilterPos : 0 < ((bestWorlds f g w).filter p).card :=
      Finset.card_pos.mpr ⟨x, hMem⟩
    exact div_pos (by exact_mod_cast hFilterPos) hCast_pos

/-- **Empty ordering gives strength = proportion of all accessible worlds.** -/
theorem empty_ordering_strength (f : ModalBase World) (p : BProp World) (w : World)
    (hNe : (accessibleWorlds f w).Nonempty) :
    modalStrength f (λ _ => []) p w =
    ↑((accessibleWorlds f w).filter p).card / ↑(accessibleWorlds f w).card := by
  unfold modalStrength
  rw [empty_ordering_simple f w]
  simp [hNe.ne_empty]

end Phenomena.Modality.DegreeCollapse
