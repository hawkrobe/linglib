module

public import Linglib.Semantics.Modality.Necessity

/-!
# Strong and weak necessity

Von Fintel and Iatridou distinguish two necessity forces over Kratzer's conversational
backgrounds. Strong necessity (*must*, *have to*) is necessity over the best accessible worlds
(`strongNecessity`); weak necessity (*ought*, *should*) is necessity over the best of those
under a secondary ordering source (`weakNecessity`), the lexicographic refinement in which a
later ordering source undoes the ties left by an earlier one. Selecting within the best worlds
can only shrink the domain, so strong necessity entails weak necessity (`strong_entails_weak`)
and not conversely (`weak_not_entails_strong`); with an empty secondary ordering source the two
coincide (`weak_eq_strong_no_secondary`).

## References

* [von-fintel-iatridou-2008]
* [kratzer-1981]
* [kratzer-2012]
-/

@[expose] public section

namespace Modality.Directive

open Modality

variable {W : Type*}

/-- Strong necessity, *must φ*, is Kratzer's necessity over the best accessible worlds. -/
def strongNecessity (f g : ConvBackground W) (p : W → Prop) (w : W) : Prop :=
  necessity f g p w

/-- Weak necessity, *ought φ*, is necessity over the `g'`-best of the `g`-best accessible
worlds. -/
def weakNecessity (f g g' : ConvBackground W) (p : W → Prop) (w : W) : Prop :=
  ∀ w' ∈ bestAmong (bestWorlds f g w) (g' w), p w'

/-- Strong necessity entails weak necessity: the `g'`-best of the `g`-best worlds are
`g`-best. -/
theorem strong_entails_weak (f g g' : ConvBackground W) (p : W → Prop) (w : W)
    (h : strongNecessity f g p w) : weakNecessity f g g' p w := by
  rw [strongNecessity, necessity_iff] at h
  intro w' hw'
  exact h w' (bestAmong_subset _ _ hw')

/-- Weak necessity does not entail strong necessity: with two tied accessible worlds and a
secondary ordering source singling out the one where `p` holds, *ought p* is true and *must p*
false. -/
theorem weak_not_entails_strong :
    ¬ ∀ (W : Type) (f g g' : ConvBackground W) (p : W → Prop) (w : W),
        weakNecessity f g g' p w → strongNecessity f g p w := by
  intro h
  let f : ConvBackground Bool := ⊥
  let g : ConvBackground Bool := fun _ ↦ {fun _ ↦ True}
  let g' : ConvBackground Bool := fun _ ↦ {fun w ↦ w = true}
  let p : Bool → Prop := fun w ↦ w = true
  have hAcc : ∀ w' : Bool, w' ∈ f.accessibleWorlds true := by simp [f]
  have hTriv : ∀ a b : Bool, atLeastAsGoodAs (g true) a b := by simp [g, atLeastAsGoodAs_iff]
  have hBestAll : ∀ w' : Bool, w' ∈ bestWorlds f g true := by
    intro w'
    refine ⟨hAcc w', ?_⟩
    intro v _ _
    exact hTriv w' v
  have hWeak : weakNecessity f g g' p true := by
    rintro w' ⟨_, hmin⟩
    cases w' with
    | true => rfl
    | false =>
      have hTF : atLeastAsGoodAs (g' true) true false := by simp [g', atLeastAsGoodAs_iff]
      have hFT := hmin (hBestAll true) hTF
      exact absurd (hFT (fun w ↦ w = true) (Set.mem_singleton _) rfl) Bool.false_ne_true
  have hNot : ¬ strongNecessity f g p true := fun hStrong ↦
    Bool.false_ne_true (hStrong false (hBestAll false))
  exact hNot (h Bool f g g' p true hWeak)

/-- With an empty secondary ordering source, weak necessity is strong necessity. -/
theorem weak_eq_strong_no_secondary (f g : ConvBackground W) (p : W → Prop)
    (w : W) : weakNecessity f g (⊥ : ConvBackground W) p w ↔ strongNecessity f g p w := by
  unfold weakNecessity strongNecessity
  rw [show bestAmong (bestWorlds f g w) ((⊥ : ConvBackground W) w) =
    bestWorlds f g w from bestAmong_empty _]
  exact (necessity_iff f g p w).symm

end Modality.Directive
