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
open Semantics.Attitudes.Intensional
open Core.Proposition

/-! ## Combined ordering sources -/

/-- Combine two ordering sources by concatenation.
    The combined source g₁ ∪ g₂ yields the union of ideals from both. -/
def combineOrdering (g₁ g₂ : OrderingSource) : OrderingSource :=
  λ w => g₁ w ++ g₂ w

/-- The primary ordering is contained in the combined one:
    every ideal in g is also in g ∪ g'. -/
theorem primary_sub_combined (g g' : OrderingSource) (w : World) :
    ∀ p, p ∈ g w → p ∈ combineOrdering g g' w :=
  λ _ hp => List.mem_append_left _ hp

/-- Combining with empty ordering preserves the original. -/
theorem combine_empty_right (g : OrderingSource) (w : World) :
    combineOrdering g emptyBackground w = g w := by
  unfold combineOrdering emptyBackground
  exact List.append_nil _

/-! ## Strong and weak necessity -/

/-- **Strong necessity** ("must φ"): standard Kratzer necessity under
    modal base f and ordering source g. -/
def strongNecessity (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) : Bool :=
  necessity f g p w

/-- **Weak necessity** ("ought φ"): Kratzer necessity under modal base f
    and a *refined* ordering g ∪ g', where g' is a secondary ordering
    source (e.g., stereotypical expectations beyond strict norms). -/
def weakNecessity (f : ModalBase) (g g' : OrderingSource)
    (p : BProp World) (w : World) : Bool :=
  necessity f (combineOrdering g g') p w

/-! ## Ordering extension lemma -/

/-- Extending the ordering source preserves the "at least as good" relation.

    If w ≤_{A++B} z (w is at least as good as z under more criteria), then
    w ≤_A z (the relation holds a fortiori under fewer criteria).

    More criteria makes the ordering more discriminating: w must satisfy
    more of z's satisfied propositions to dominate. So the extended
    relation is a subset of the original. -/
private theorem ordering_extension_mono (A extra : List (BProp World)) (w z : World)
    (h : atLeastAsGoodAs (A ++ extra) w z = true) :
    atLeastAsGoodAs A w z = true := by
  unfold atLeastAsGoodAs satisfiedPropositions at h ⊢
  rw [List.filter_append, List.all_append] at h
  cases hA : (A.filter (λ p => p z)).all (λ p => p w) with
  | true => rfl
  | false => simp [hA] at h

/-! ## Best worlds monotonicity -/

/-- Refining the ordering can only shrink the set of best worlds.

    Best(f, g∪g') ⊆ Best(f, g): adding criteria to the ordering eliminates
    worlds that were previously tied. A world that dominates all others under
    the more discriminating ordering a fortiori dominates under the coarser one. -/
theorem best_refines (f : ModalBase) (g g' : OrderingSource) (w : World) :
    ∀ w', w' ∈ bestWorlds f (combineOrdering g g') w →
          w' ∈ bestWorlds f g w := by
  intro w' hw'
  unfold bestWorlds at hw' ⊢
  unfold combineOrdering at hw'
  simp only [List.mem_filter, List.all_eq_true] at hw' ⊢
  exact ⟨hw'.1, λ w'' hw'' =>
    ordering_extension_mono (g w) (g' w) w' w'' (hw'.2 w'' hw'')⟩

/-! ## Main entailment -/

/-- **Strong entails weak**: if "must φ" holds (under ordering g), then
    "ought φ" holds (under any refinement g ∪ g').

    ∀w' ∈ Best(f,g). φ(w') → ∀w' ∈ Best(f, g∪g'). φ(w')

    This captures the linguistic intuition: "must φ" is a stronger claim
    than "ought φ" — the former entails the latter but not vice versa. -/
theorem strong_entails_weak (f : ModalBase) (g g' : OrderingSource)
    (p : BProp World) (w : World)
    (h : strongNecessity f g p w = true) :
    weakNecessity f g g' p w = true := by
  unfold strongNecessity at h
  unfold weakNecessity
  unfold necessity at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro w' hw'
  exact h w' (best_refines f g g' w w' hw')

/-! ## The converse fails -/

/-- Weak necessity does NOT entail strong necessity.

    Counterexample: g-best worlds are {w0, w1}. The secondary ordering g'
    distinguishes them, making w1 strictly better. Under g∪g', only w1
    is best. If p holds at w1 but not w0, weak necessity holds but strong
    necessity fails. -/
theorem weak_not_entails_strong :
    ¬(∀ (f : ModalBase) (g g' : OrderingSource) (p : BProp World) (w : World),
        weakNecessity f g g' p w = true → strongNecessity f g p w = true) := by
  intro h
  -- g: worlds satisfying (w0 ∨ w1) are best — {w0, w1}
  -- g': refines to worlds satisfying w1 — under g∪g', only {w1} is best
  -- p = (· == w1): holds at w1 but not w0
  exact absurd
    (h emptyBackground
      (λ _ => [λ w => w == .w0 || w == .w1])
      (λ _ => [λ w => w == .w1])
      (λ w => w == .w1) .w0
      (by decide))
    (by decide)

/-! ## Deontic application -/

/-- A deontic scenario with strong and weak norms.

    Contains a `DeonticFlavor` (circumstantial base + primary norms) and adds
    a secondary ordering source for weak necessity. This makes the structural
    relationship to Kratzer's framework explicit: strong necessity IS the
    primary `DeonticFlavor`; weak necessity refines it.

    - Primary norms g (via `DeonticFlavor`): legal/institutional obligations
    - Secondary norms g': social expectations, stereotypical behavior

    "Must" quantifies over worlds satisfying legal obligations;
    "ought" further refines by social expectations. -/
structure DeonticStrength where
  /-- The primary deontic scenario (circumstantial base + primary norms) -/
  primary : DeonticFlavor
  /-- Secondary norms (social, stereotypical) -/
  secondaryNorms : OrderingSource

/-- Strong deontic necessity: "You must do X" (legal obligation). -/
def DeonticStrength.must (d : DeonticStrength)
    (p : BProp World) (w : World) : Bool :=
  strongNecessity d.primary.circumstances d.primary.norms p w

/-- Weak deontic necessity: "You ought to do X" (refined by social norms). -/
def DeonticStrength.ought (d : DeonticStrength)
    (p : BProp World) (w : World) : Bool :=
  weakNecessity d.primary.circumstances d.primary.norms d.secondaryNorms p w

/-- Bridge to Kratzer's DeonticFlavor: strong necessity with DeonticFlavor
    is exactly standard Kratzer necessity. -/
theorem deontic_must_eq_kratzer (d : DeonticFlavor)
    (p : BProp World) (w : World) :
    necessity d.circumstances d.norms p w =
    strongNecessity d.circumstances d.norms p w := rfl

/-- Must entails ought for any deontic scenario. -/
theorem deontic_must_entails_ought (d : DeonticStrength)
    (p : BProp World) (w : World)
    (h : d.must p w = true) :
    d.ought p w = true :=
  strong_entails_weak d.primary.circumstances d.primary.norms d.secondaryNorms p w h

/-- With no secondary norms, weak necessity reduces to strong necessity. -/
theorem weak_eq_strong_no_secondary (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    weakNecessity f g emptyBackground p w =
    strongNecessity f g p w := by
  unfold weakNecessity strongNecessity necessity bestWorlds combineOrdering emptyBackground
  simp only [List.append_nil]

/-! ## Bridge: Kratzer semantics ↔ typological force

The typological `ModalForce.weakNecessity` corresponds to Kratzer's
`necessity` evaluated with a refined ordering source (g ∪ g'). Strong
necessity is `necessity` with the primary ordering source alone. The
entailment chain □ → □w → ◇ is the semantic content of
`ModalForce.atLeastAsStrong`. -/

/-- Strong necessity under Kratzer params IS `ModalForce.necessity`. -/
theorem strongNecessity_is_necessity (f : ModalBase) (g : OrderingSource)
    (p : BProp World) (w : World) :
    strongNecessity f g p w = (KratzerTheory ⟨f, g⟩).eval .necessity p w := rfl

/-- Weak necessity under Kratzer params with refinement IS
    `ModalForce.weakNecessity` evaluated under combined ordering. -/
theorem weakNecessity_is_weakForce (f : ModalBase) (g g' : OrderingSource)
    (p : BProp World) (w : World) :
    weakNecessity f g g' p w =
    (KratzerTheory ⟨f, combineOrdering g g'⟩).eval .weakNecessity p w := rfl

end Semantics.Modality.Directive
