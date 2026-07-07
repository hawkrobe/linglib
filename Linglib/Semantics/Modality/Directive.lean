import Linglib.Semantics.Modality.Kratzer.Flavor

/-!
# Directive Modality: Strong and Weak Necessity
[kratzer-2012] [von-fintel-iatridou-2008]

[von-fintel-iatridou-2008] argue that natural languages systematically
distinguish **strong necessity** ("must", "have to") from **weak necessity**
("ought", "should"). The difference is not in modal force — both are universal
quantifiers over best worlds — but in the ordering source.

## Core Analysis

Strong and weak necessity share the same modal base (circumstantial) but differ
in ordering:

- **Strong necessity** (must φ): necessity under ordering g
- **Weak necessity** (ought φ): necessity over the g'-best of the
  g-best worlds

The secondary ordering g' selects *within* the primary best set — the
lexicographic refinement of [kratzer-1981]'s Conclusion, where later
ordering sources undo the ties left by their predecessors. Selecting
within a set can only shrink it, so the universal quantification is
over a subset, making the claim weaker (easier to satisfy).

## Key Result

`strong_entails_weak`: strong necessity entails weak necessity, since
the g'-best of the g-best worlds are g-best (`bestAmong_sub`).

`weak_not_entails_strong`: the converse fails. A concrete counterexample shows
that refining the ordering can eliminate a world where φ fails, making weak
necessity hold while strong necessity does not.

## Connection to Kratzer Framework

Strong necessity IS Kratzer's standard `necessity` from `Kratzer.lean`.
Weak necessity adds a secondary ordering source via `combineOrdering`.
The `DeonticStrength` structure pairs primary and secondary norms,
bridging to `DeonticFlavor`.
-/

namespace Semantics.Modality.Directive

open Semantics.Modality.Kratzer

variable {W : Type*}

/-! ## Combined ordering sources -/

/-- Combine two ordering sources by concatenation.
    The combined source g₁ ∪ g₂ yields the union of ideals from both. -/
def combineOrdering (g₁ g₂ : OrderingSource W) : OrderingSource W :=
  λ w => g₁ w ++ g₂ w

/-- The primary ordering is contained in the combined one. -/
theorem primary_sub_combined (g g' : OrderingSource W) (w : W) :
    ∀ p, p ∈ g w → p ∈ combineOrdering g g' w :=
  λ _ hp => List.mem_append_left _ hp

/-- Combining with empty ordering preserves the original. -/
theorem combine_empty_right (g : OrderingSource W) (w : W) :
    combineOrdering g (emptyBackground (W := W)) w = g w := by
  unfold combineOrdering emptyBackground
  exact List.append_nil _

/-! ## Strong and weak necessity -/

/-- **Strong necessity** ("must φ"): standard Kratzer necessity. -/
def strongNecessity (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  necessity f g p w

/-- **Weak necessity** ("ought φ"): necessity over the g'-best of the
    g-best worlds — the lexicographic refinement of [kratzer-1981]'s
    Conclusion. -/
def weakNecessity (f : ModalBase W) (g g' : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  ∀ w' ∈ bestAmong (bestWorlds f g w) (g' w), p w'

/-! ## Main entailment -/

/-- **Strong entails weak**: if "must φ" holds, then "ought φ" holds. -/
theorem strong_entails_weak (f : ModalBase W) (g g' : OrderingSource W)
    (p : W → Prop) (w : W)
    (h : strongNecessity f g p w) :
    weakNecessity f g g' p w := by
  rw [strongNecessity, necessity_iff_all] at h
  intro w' hw'
  exact h w' (bestAmong_sub _ _ hw')

/-! ## The converse fails -/

/-- Weak necessity does NOT entail strong necessity.

    Counterexample: W = Bool. g is the trivial ordering (all worlds tied),
    so both worlds are g-best; g' identifies `true`, so only `true` is
    g'-best among them. With p = (· = true), weakNecessity holds but
    strongNecessity fails at the g-best world `false`. -/
theorem weak_not_entails_strong :
    ¬(∀ (W : Type)
        (f : ModalBase W) (g g' : OrderingSource W) (p : W → Prop) (w : W),
        weakNecessity f g g' p w → strongNecessity f g p w) := by
  intro h
  let f : ModalBase Bool := emptyBackground
  let g : OrderingSource Bool := fun _ => [fun _ => True]
  let g' : OrderingSource Bool := fun _ => [fun w => w = true]
  let p : Bool → Prop := fun w => w = true
  have hAcc : ∀ w' : Bool, w' ∈ accessibleWorlds f true := by
    intro w' q hq
    cases hq
  have hTriv : ∀ a b : Bool, atLeastAsGoodAs (g true) a b := by
    intro a b q hq _
    cases hq with
    | head => trivial
    | tail _ h => cases h
  have hBestAll : ∀ w' : Bool, w' ∈ bestWorlds f g true := by
    intro w'
    refine ⟨hAcc w', ?_⟩
    intro v _ _
    exact hTriv w' v
  -- Weak necessity holds: only `true` is g'-best among the g-best.
  have hWeak : weakNecessity f g g' p true := by
    rintro w' ⟨_, hmin⟩
    cases w' with
    | true => rfl
    | false =>
      have hTF : atLeastAsGoodAs (g' true) true false := by
        intro q hq _
        cases hq with
        | head => rfl
        | tail _ h => cases h
      have hFT := hmin true (hBestAll true) hTF
      exact absurd (hFT (fun w => w = true) List.mem_cons_self rfl)
        Bool.false_ne_true
  -- Strong necessity fails at the g-best world `false`.
  have hNot : ¬ strongNecessity f g p true := fun hStrong =>
    Bool.false_ne_true (hStrong false (hBestAll false))
  exact hNot (h Bool f g g' p true hWeak)

/-! ## Deontic application -/

structure DeonticStrength (W : Type*) where
  primary : DeonticFlavor W
  secondaryNorms : OrderingSource W

def DeonticStrength.must (d : DeonticStrength W)
    (p : W → Prop) (w : W) : Prop :=
  strongNecessity d.primary.circumstances d.primary.norms p w

def DeonticStrength.ought (d : DeonticStrength W)
    (p : W → Prop) (w : W) : Prop :=
  weakNecessity d.primary.circumstances d.primary.norms d.secondaryNorms p w

theorem deontic_must_eq_kratzer (d : DeonticFlavor W)
    (p : W → Prop) (w : W) :
    necessity d.circumstances d.norms p w ↔
    strongNecessity d.circumstances d.norms p w :=
  Iff.rfl

theorem deontic_must_entails_ought (d : DeonticStrength W)
    (p : W → Prop) (w : W)
    (h : d.must p w) :
    d.ought p w :=
  strong_entails_weak d.primary.circumstances d.primary.norms d.secondaryNorms p w h

theorem weak_eq_strong_no_secondary (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    weakNecessity f g (emptyBackground (W := W)) p w ↔
    strongNecessity f g p w := by
  unfold weakNecessity strongNecessity
  rw [show bestAmong (bestWorlds f g w) ((emptyBackground (W := W)) w) =
    bestWorlds f g w from bestAmong_empty _]
  exact (necessity_iff_all f g p w).symm

end Semantics.Modality.Directive
