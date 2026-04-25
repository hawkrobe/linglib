import Linglib.Phenomena.Modality.Studies.Kratzer2012Scenario
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Card

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

open Semantics.Modality.Kratzer
open Phenomena.Modality.ConditionalModality

/-! ## Modal strength as a rational degree -/

/-- **Modal strength**: the proportion of best worlds satisfying p.

    When the set of best worlds is empty (or infinite, in which case
    `Set.ncard` returns 0), strength is 0. Otherwise,
    strength = |{w ∈ Best : p(w)}| / |Best|.

    This captures Kratzer's graded modality: the ordering source modulates
    modal strength between bare possibility and necessity. -/
noncomputable def modalStrength (f : ModalBase World) (g : OrderingSource World)
    (p : World → Prop) (w : World) : ℚ :=
  let best := bestWorlds f g w
  if best.ncard = 0 then 0
  else (best ∩ {w' | p w'}).ncard / best.ncard

/-! ## Concrete scenario: Rain / Wet Streets

We reuse `ConditionalModality.Data`'s rain scenario. With the normalcy
ordering, best = {w0} (normal rain), so streetWet has strength 1.
Without normalcy ordering, best = all rain-worlds {w0, w1}, and
streetWet holds only at w0, so strength = 1/2. -/

/-- With the normalcy ordering, the only best world is `w0`. -/
theorem best_normalcy :
    bestWorlds (restrictedBase emptyBackground rained) normalcySource (0 : World) = {(0 : World)} := by
  ext w'
  constructor
  · rintro ⟨hAcc, hBest⟩
    -- hAcc : w' ∈ accessibleWorlds (restrictedBase emptyBackground rained) (0 : World)
    -- means rained w' (since emptyBackground adds nothing)
    have hRained : rained w' := by
      have := hAcc rained (by simp [restrictedBase])
      exact this
    -- hBest : ∀ w'' accessible, atLeastAsGoodAs (normalcySource (0 : World)) w' w''
    -- Apply hBest to (1 : World) (which is accessible: rained w1)
    have hAccW1 : (1 : World) ∈ accessibleWorlds (restrictedBase emptyBackground rained) (0 : World) := by
      intro p hp
      simp [restrictedBase, emptyBackground] at hp
      subst hp
      exact w1_rained_dry.1
    have hBetterW1 := hBest (1 : World) hAccW1
    -- atLeastAsGoodAs uses normalcySource, which is [λ w' => ¬(rained w' ∧ ¬ streetWet w')]
    -- For w1: rained w1 ∧ ¬streetWet w1 holds, so ¬(rained ∧ ¬streetWet) FAILS at w1
    -- For w' to be at least as good as w1: every prop satisfied by w1 must be satisfied by w'
    -- Since w1 doesn't satisfy the normalcy prop, this is vacuous; not useful.
    -- We need to use the OTHER direction: w' must satisfy the normalcy prop if accessible
    -- Actually, the constraint is: w' ≤ w1, i.e. for any normalcy prop p satisfied by w1, w' satisfies it
    -- But w1 satisfies no normalcy props, so this gives us nothing about w'.
    -- Let me use a different test: apply hBest to (0 : World) to ensure w' ≤ w0
    -- w0 satisfies the normalcy prop (¬(rained ∧ ¬streetWet) = ¬(T ∧ F) = T)
    have hAccW0 : (0 : World) ∈ accessibleWorlds (restrictedBase emptyBackground rained) (0 : World) := by
      intro p hp
      simp [restrictedBase, emptyBackground] at hp
      subst hp
      exact w0_rained_wet.1
    have hBetterW0 := hBest (0 : World) hAccW0
    -- hBetterW0 : atLeastAsGoodAs (normalcySource (0 : World)) w' (0 : World)
    -- w0 satisfies the normalcy prop, so w' must too
    have hNormalcyAtW0 : ¬ (rained (0 : World) ∧ ¬ streetWet (0 : World)) := by
      intro ⟨_, hNW⟩; exact hNW trivial
    have hNormalcyAtWp : ¬ (rained w' ∧ ¬ streetWet w') := by
      have := hBetterW0 (λ w' => ¬ (rained w' ∧ ¬ streetWet w'))
                       (by simp [normalcySource]) hNormalcyAtW0
      exact this
    -- So either ¬rained w' or streetWet w'
    -- Since hRained : rained w', we have streetWet w'
    have hWet : streetWet w' := by
      by_contra hNW
      exact hNormalcyAtWp ⟨hRained, hNW⟩
    -- Now: rained w' ∧ streetWet w' → w' = (0 : World) (only w0 has both)
    match w' with
    | 0 => rfl
    | 1 => exact absurd hWet w1_rained_dry.2
    | 2 => exact absurd hRained w2_dry_wet.1
    | 3 => exact absurd hRained w3_dry_dry.1
  · rintro rfl
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [restrictedBase, emptyBackground] at hp
      subst hp
      exact w0_rained_wet.1
    · intro w'' _hw''
      -- Need: atLeastAsGoodAs (normalcySource (0 : World)) (0 : World) w''
      -- The only normalcy prop simplifies to (rained → streetWet);
      -- (0 : World) satisfies it since streetWet (0 : World) = True.
      intro p hp _hpw
      simp [normalcySource] at hp
      subst hp
      intro _; exact trivial

/-- Without the normalcy ordering, both `w0` and `w1` are best. -/
theorem best_empty :
    bestWorlds (restrictedBase emptyBackground rained) emptyBackground (0 : World) =
    {w | rained w} := by
  ext w'
  constructor
  · rintro ⟨hAcc, _⟩
    exact hAcc rained (by simp [restrictedBase])
  · intro hRained
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [restrictedBase, emptyBackground] at hp
      subst hp
      exact hRained
    · intro w'' _
      intro p hp; simp [emptyBackground] at hp

/-- The set `{w | rained w}` equals `{(0 : World), (1 : World)}`. -/
theorem rained_set_eq : ({w | rained w} : Set World) = {(0 : World), (1 : World)} := by
  ext w
  match w with
  | 0 => simp [rained]
  | 1 => simp [rained]
  | 2 => simp [rained]
  | 3 => simp [rained]

/-- `ncard` of a singleton is 1. -/
private theorem ncard_singleton_w0 : ({(0 : World)} : Set World).ncard = 1 := by
  rw [Set.ncard_singleton]

/-- `ncard` of `{(0 : World), (1 : World)}` is 2. -/
private theorem ncard_pair_w0_w1 : ({(0 : World), (1 : World)} : Set World).ncard = 2 := by
  rw [Set.ncard_pair]
  intro h; cases h

/-- **With normalcy ordering**: strength = 1. Best = {w0}, streetWet w0 = true. -/
theorem strength_with_normalcy :
    modalStrength (restrictedBase emptyBackground rained) normalcySource streetWet (0 : World) = 1 := by
  unfold modalStrength
  simp only
  rw [best_normalcy, ncard_singleton_w0]
  have hInter : (({(0 : World)} : Set World) ∩ {w' | streetWet w'}) = {(0 : World)} := by
    ext w; constructor
    · rintro ⟨h1, _⟩; exact h1
    · rintro rfl; exact ⟨rfl, trivial⟩
  rw [hInter, ncard_singleton_w0]
  simp

/-- **Without normalcy ordering**: strength = 1/2. Best = {w0, w1},
    streetWet w0 = true, streetWet w1 = false. -/
theorem strength_without_normalcy :
    modalStrength (restrictedBase emptyBackground rained) emptyBackground streetWet (0 : World) = 1 / 2 := by
  unfold modalStrength
  simp only
  rw [best_empty, rained_set_eq, ncard_pair_w0_w1]
  have hInter : (({(0 : World), (1 : World)} : Set World) ∩ {w' | streetWet w'}) = {(0 : World)} := by
    ext w
    match w with
    | 0 => simp [streetWet]
    | 1 => simp [streetWet]
    | 2 => simp [streetWet]
    | 3 => simp [streetWet]
  rw [hInter, ncard_singleton_w0]
  norm_num

/-! ## General theorems linking strength to modal operators -/

/-- **Strength 1 ↔ necessity** (when best worlds are nonempty and finite). -/
theorem strength_one_iff_necessity (f : ModalBase World) (g : OrderingSource World)
    (p : World → Prop) (w : World)
    (hNonempty : (bestWorlds f g w).Nonempty)
    (hFin : (bestWorlds f g w).Finite) :
    modalStrength f g p w = 1 ↔ necessity f g p w := by
  rw [necessity_iff_all]
  unfold modalStrength
  simp only
  have hCardPos : 0 < (bestWorlds f g w).ncard := Set.ncard_pos hFin |>.mpr hNonempty
  have hCardNe : (bestWorlds f g w).ncard ≠ 0 := hCardPos.ne'
  simp only [hCardNe, ↓reduceIte]
  have hCastNe : ((bestWorlds f g w).ncard : ℚ) ≠ 0 := by exact_mod_cast hCardNe
  constructor
  · intro hStr
    rw [div_eq_one_iff_eq hCastNe] at hStr
    have hCardEq : (bestWorlds f g w ∩ {w' | p w'}).ncard = (bestWorlds f g w).ncard := by
      exact_mod_cast hStr
    -- Inter ⊆ best, and they have equal ncard, so they're equal
    have hSubset : bestWorlds f g w ∩ {w' | p w'} ⊆ bestWorlds f g w :=
      Set.inter_subset_left
    have hInterFin : (bestWorlds f g w ∩ {w' | p w'}).Finite :=
      hFin.subset hSubset
    have hEq : bestWorlds f g w ∩ {w' | p w'} = bestWorlds f g w :=
      Set.eq_of_subset_of_ncard_le hSubset (by rw [hCardEq]) hFin
    intro w' hw'
    have : w' ∈ bestWorlds f g w ∩ {w' | p w'} := hEq.symm ▸ hw'
    exact this.2
  · intro hAll
    have hEq : bestWorlds f g w ∩ {w' | p w'} = bestWorlds f g w := by
      apply Set.inter_eq_left.mpr
      intro w' hw'
      exact hAll w' hw'
    rw [hEq]
    exact div_self hCastNe

/-- **Positive strength ↔ possibility** (when best worlds are nonempty and finite). -/
theorem strength_pos_iff_possibility (f : ModalBase World) (g : OrderingSource World)
    (p : World → Prop) (w : World)
    (hNonempty : (bestWorlds f g w).Nonempty)
    (hFin : (bestWorlds f g w).Finite) :
    modalStrength f g p w > 0 ↔ possibility f g p w := by
  rw [possibility_iff_any]
  unfold modalStrength
  simp only
  have hCardPos : 0 < (bestWorlds f g w).ncard := Set.ncard_pos hFin |>.mpr hNonempty
  have hCardNe : (bestWorlds f g w).ncard ≠ 0 := hCardPos.ne'
  simp only [hCardNe, ↓reduceIte]
  have hCastPos : (0 : ℚ) < ((bestWorlds f g w).ncard : ℚ) := by exact_mod_cast hCardPos
  have hInterFin : (bestWorlds f g w ∩ {w' | p w'}).Finite :=
    hFin.subset Set.inter_subset_left
  constructor
  · intro hStr
    have hInterPos : 0 < (bestWorlds f g w ∩ {w' | p w'}).ncard := by
      by_contra hc
      push Not at hc
      have hZero : (bestWorlds f g w ∩ {w' | p w'}).ncard = 0 :=
        Nat.eq_zero_of_le_zero hc
      rw [hZero] at hStr
      simp at hStr
    obtain ⟨x, hx⟩ := (Set.ncard_pos hInterFin).mp hInterPos
    exact ⟨x, hx.1, hx.2⟩
  · rintro ⟨x, hxBest, hpx⟩
    have hMem : x ∈ bestWorlds f g w ∩ {w' | p w'} := ⟨hxBest, hpx⟩
    have hInterPos : 0 < (bestWorlds f g w ∩ {w' | p w'}).ncard :=
      (Set.ncard_pos hInterFin).mpr ⟨x, hMem⟩
    exact div_pos (by exact_mod_cast hInterPos) hCastPos

/-- **Empty ordering gives strength = proportion of all accessible worlds.** -/
theorem empty_ordering_strength (f : ModalBase World) (p : World → Prop) (w : World)
    (hNe : (accessibleWorlds f w).Nonempty)
    (hFin : (accessibleWorlds f w).Finite) :
    modalStrength f (λ _ => []) p w =
    ((accessibleWorlds f w ∩ {w' | p w'}).ncard : ℚ) / (accessibleWorlds f w).ncard := by
  unfold modalStrength
  simp only
  rw [empty_ordering_simple f w]
  have hCardPos : 0 < (accessibleWorlds f w).ncard := Set.ncard_pos hFin |>.mpr hNe
  have hCardNe : (accessibleWorlds f w).ncard ≠ 0 := hCardPos.ne'
  simp [hCardNe]

end Phenomena.Modality.DegreeCollapse
