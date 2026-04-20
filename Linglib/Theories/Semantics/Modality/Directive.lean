import Linglib.Theories.Semantics.Modality.Kratzer.Flavor

/-!
# Directive Modality: Strong and Weak Necessity
@cite{kratzer-2012} @cite{von-fintel-iatridou-2008}

@cite{von-fintel-iatridou-2008} argue that natural languages systematically
distinguish **strong necessity** ("must", "have to") from **weak necessity**
("ought", "should"). The difference is not in modal force — both are universal
quantifiers over best worlds — but in the ordering source.

## Core Analysis

Strong and weak necessity share the same modal base (circumstantial) but differ
in ordering:

- **Strong necessity** (must φ): necessity under ordering g
- **Weak necessity** (ought φ): necessity under refined ordering g ∪ g'

The secondary ordering g' adds criteria beyond the primary norms, creating a
more discriminating ranking. More criteria → smaller "best" set → the universal
quantification is over a subset, making it a weaker (easier to satisfy) claim.

## Key Result

`strong_entails_weak`: strong necessity entails weak necessity. If all g-best
worlds have φ, then all (g∪g')-best worlds have φ, because the refined best
set is a subset of the original.

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

/-- **Weak necessity** ("ought φ"): Kratzer necessity under refined ordering g ∪ g'. -/
def weakNecessity (f : ModalBase W) (g g' : OrderingSource W)
    (p : W → Prop) (w : W) : Prop :=
  necessity f (combineOrdering g g') p w

/-! ## Ordering extension lemma -/

private theorem ordering_extension_mono (A extra : List (W → Prop)) (w z : W)
    (h : atLeastAsGoodAs (A ++ extra) w z) :
    atLeastAsGoodAs A w z :=
  fun p hp hpz => h p (List.mem_append_left _ hp) hpz

/-! ## Best worlds monotonicity -/

/-- Refining the ordering can only shrink the set of best worlds. -/
theorem best_refines (f : ModalBase W) (g g' : OrderingSource W) (w : W) :
    ∀ w', w' ∈ bestWorlds f (combineOrdering g g') w →
          w' ∈ bestWorlds f g w := by
  intro w' hw'
  refine ⟨hw'.1, fun w'' hw'' => ?_⟩
  exact ordering_extension_mono (g w) (g' w) w' w'' (hw'.2 w'' hw'')

/-! ## Main entailment -/

/-- **Strong entails weak**: if "must φ" holds, then "ought φ" holds. -/
theorem strong_entails_weak (f : ModalBase W) (g g' : OrderingSource W)
    (p : W → Prop) (w : W)
    (h : strongNecessity f g p w) :
    weakNecessity f g g' p w := by
  rw [strongNecessity, necessity_iff_all] at h
  rw [weakNecessity, necessity_iff_all]
  intro w' hw'
  exact h w' (best_refines f g g' w w' hw')

/-! ## The converse fails -/

/-- Weak necessity does NOT entail strong necessity.

    Counterexample: W = Bool. g is the trivial ordering (all worlds tied);
    g' identifies `true`. Under g, both `true` and `false` are best; under
    g∪g', only `true` is best. With p = (· = true), weakNecessity holds
    (only `true` ∈ best), but strongNecessity fails (`false` ∈ best, p false). -/
theorem weak_not_entails_strong :
    ¬(∀ (W : Type)
        (f : ModalBase W) (g g' : OrderingSource W) (p : W → Prop) (w : W),
        weakNecessity f g g' p w → strongNecessity f g p w) := by
  intro h
  let f : ModalBase Bool := emptyBackground
  let g : OrderingSource Bool := fun _ => [fun _ => True]
  let g' : OrderingSource Bool := fun _ => [fun w => w = true]
  let p : Bool → Prop := fun w => w = true
  -- All worlds are accessible (empty modal base).
  have hAcc : ∀ w' : Bool, w' ∈ accessibleWorlds f true := by
    intro w'
    intro q hq
    cases hq
  -- Weak necessity holds: only `true` is best under g∪g'.
  have hWeak : weakNecessity f g g' p true := by
    intro w' hw'
    obtain ⟨_, hBest⟩ := hw'
    have hIdent : (fun w : Bool => w = true) ∈ combineOrdering g g' true := by
      simp [combineOrdering, g, g']
    exact hBest true (hAcc true) (fun w => w = true) hIdent rfl
  -- Strong necessity fails: `false` is best under g (trivial), but p false is false.
  have hNot : ¬ strongNecessity f g p true := by
    intro hStrong
    have hFalseBest : false ∈ bestWorlds f g true := by
      refine ⟨hAcc false, fun w'' _ q hq _ => ?_⟩
      simp [g] at hq
      rw [hq]
      trivial
    exact Bool.false_ne_true (hStrong false hFalseBest)
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
  simp only [weakNecessity, strongNecessity, necessity_iff_all]
  constructor <;> intro h
  · rwa [show bestWorlds f (combineOrdering g (emptyBackground (W := W))) w =
      bestWorlds f g w from by unfold combineOrdering emptyBackground; simp] at h
  · rwa [show bestWorlds f g w = bestWorlds f (combineOrdering g (emptyBackground (W := W))) w
      from by unfold combineOrdering emptyBackground; simp] at h

end Semantics.Modality.Directive
