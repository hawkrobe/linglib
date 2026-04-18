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

variable {W : Type*} [DecidableEq W] [Fintype W]

/-! ## Combined ordering sources -/

/-- Combine two ordering sources by concatenation.
    The combined source g₁ ∪ g₂ yields the union of ideals from both. -/
def combineOrdering (g₁ g₂ : OrderingSource W) : OrderingSource W :=
  λ w => g₁ w ++ g₂ w

omit [DecidableEq W] [Fintype W] in
/-- The primary ordering is contained in the combined one. -/
theorem primary_sub_combined (g g' : OrderingSource W) (w : W) :
    ∀ p, p ∈ g w → p ∈ combineOrdering g g' w :=
  λ _ hp => List.mem_append_left _ hp

omit [DecidableEq W] [Fintype W] in
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

omit [DecidableEq W] [Fintype W] in
private theorem ordering_extension_mono (A extra : List (W → Bool)) (w z : W)
    (h : atLeastAsGoodAs (A ++ extra) w z = true) :
    atLeastAsGoodAs A w z = true := by
  unfold atLeastAsGoodAs satisfiedPropositions at h ⊢
  rw [List.filter_append, List.all_append] at h
  cases hA : (A.filter (λ p => p z)).all (λ p => p w) with
  | true => rfl
  | false => simp [hA] at h

/-! ## Best worlds monotonicity -/

/-- Refining the ordering can only shrink the set of best worlds. -/
theorem best_refines (f : ModalBase W) (g g' : OrderingSource W) (w : W) :
    ∀ w', w' ∈ bestWorlds f (combineOrdering g g') w →
          w' ∈ bestWorlds f g w := by
  intro w' hw'
  unfold bestWorlds at hw' ⊢
  unfold combineOrdering at hw'
  simp only [Finset.mem_filter, decide_eq_true_eq] at hw' ⊢
  exact ⟨hw'.1, fun w'' hw'' =>
    ordering_extension_mono (g w) (g' w) w' w'' (hw'.2 w'' hw'')⟩

/-! ## Main entailment -/

/-- **Strong entails weak**: if "must φ" holds, then "ought φ" holds. -/
theorem strong_entails_weak (f : ModalBase W) (g g' : OrderingSource W)
    (p : W → Prop) [DecidablePred p] (w : W)
    (h : strongNecessity f g p w) :
    weakNecessity f g g' p w := by
  rw [strongNecessity, necessity_iff_all] at h
  rw [weakNecessity, necessity_iff_all]
  intro w' hw'
  exact h w' (best_refines f g g' w w' hw')

/-! ## The converse fails -/

/-- Weak necessity does NOT entail strong necessity.

    Counterexample: worlds are a 3-element type. g-best = {a, b} (tied).
    g' distinguishes them (b wins). Under g∪g', best = {b}.
    If p(b) holds but p(a) fails, weak necessity holds but strong fails. -/
theorem weak_not_entails_strong :
    ¬(∀ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
        (f : ModalBase W) (g g' : OrderingSource W) (p : W → Prop) (_ : DecidablePred p) (w : W),
        weakNecessity f g g' p w → strongNecessity f g p w) := by
  intro h
  -- Use Bool as a 2-element world type
  have := h Bool instDecidableEqBool inferInstance
    (fun _ => [])  -- empty modal base: all worlds accessible
    (fun _ => [fun w => w == true || w == false])  -- trivial ordering: all tied
    (fun _ => [fun w => w])  -- secondary ordering: true > false
    (fun w => w = true)  -- p: holds at true
    (by intro w; cases w <;> infer_instance)
    true
  rw [weakNecessity, necessity_iff_all] at this
  rw [strongNecessity, necessity_iff_all] at this
  have hWeak : ∀ w' ∈ bestWorlds (emptyBackground (W := Bool))
    (combineOrdering (fun _ => [fun w => w == true || w == false])
      (fun _ => [fun w => w])) true,
    w' = true := by decide
  have hStrong := this hWeak
  have : ¬ ∀ w' ∈ bestWorlds (emptyBackground (W := Bool))
    (fun _ => [fun w => w == true || w == false]) true,
    w' = true := by decide
  exact this hStrong

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
    (p : W → Prop) [DecidablePred p] (w : W)
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
