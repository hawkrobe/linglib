import Linglib.Core.Order.SimilarityOrdering
import Mathlib.Data.Set.Finite.Basic

/-!
# Conditional desire semantics

`a wants p` holds at `w` iff for every belief-world `w'`, every `p`-world maximally
similar to `w'` is more desirable than every `¬p`-world maximally similar to `w'` —
[heim-1992]'s (31), with the comparison restricted to the belief state as in her (39),
on [lewis-1973] / [stalnaker-1968] similarity. `Defined` is the (40) amendment: the
ascription is undefined when `p` or `¬p` is already believed. Under it an antisymmetric
desirability relation cannot make both `p` and `¬p` wanted (`Want.not_compl`).

## Main declarations

- `Frame`: a similarity ordering together with comparative desirability at each
  evaluation world.
- `Frame.closest`: `Sim_w'(Bel ∩ p)`, the `p`-worlds in the belief state maximally
  similar to `w'`.
- `Want`, `Defined`, `Want.not_compl`.
-/

namespace Desire.Conditional

open Core.Order (SimilarityOrdering)

variable {W : Type*}

/-- A similarity ordering on worlds with comparative desirability: `pref w x y` says that
at evaluation world `w`, `x` is more desirable than `y`. -/
structure Frame (W : Type*) where
  /-- The similarity ordering. -/
  sim : SimilarityOrdering W
  /-- Comparative desirability at each evaluation world. -/
  pref : W → W → W → Prop

variable (F : Frame W) (bel : Set W) (w : W) (p : Set W)

/-- `Sim_w'(Bel ∩ p)`: the belief-worlds satisfying `p` that are maximally similar to
`w'`. -/
def Frame.closest (w' : W) : Set W := F.sim.closest w' (bel ∩ p)

/-- `a wants p` at `w`: for every belief-world `w'`, every closest `p`-world to `w'` is
more desirable than every closest `¬p`-world to `w'`. -/
def Want : Prop :=
  ∀ w' ∈ bel, ∀ x ∈ F.closest bel p w', ∀ y ∈ F.closest bel pᶜ w', F.pref w x y

/-- The (40) amendment: neither `p` nor `¬p` is already believed. -/
def Defined : Prop := (bel ∩ p).Nonempty ∧ (bel ∩ pᶜ).Nonempty

section Decidable

instance [Fintype W] [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] (w' : W) :
    DecidablePred (· ∈ F.closest bel p w') :=
  inferInstanceAs (DecidablePred (· ∈ F.sim.closest w' (bel ∩ p)))

instance [Fintype W] [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)]
    [∀ w, DecidableRel (F.pref w)] : Decidable (Want F bel w p) :=
  inferInstanceAs
    (Decidable (∀ w' ∈ bel, ∀ x ∈ F.closest bel p w', ∀ y ∈ F.closest bel pᶜ w', F.pref w x y))

instance [Fintype W] [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] :
    Decidable (Defined bel p) :=
  inferInstanceAs (Decidable ((∃ x, x ∈ bel ∩ p) ∧ ∃ x, x ∈ bel ∩ pᶜ))

end Decidable

variable {F bel p w}

/-- Under (40) and antisymmetric desirability, `p` and `¬p` cannot both be wanted. -/
theorem Want.not_compl [Finite W] [Std.Antisymm (F.pref w)] (hd : Defined bel p)
    (hp : Want F bel w p) : ¬ Want F bel w pᶜ := by
  intro hnp
  obtain ⟨⟨w', hw'⟩, hn⟩ := hd
  obtain ⟨x, hx⟩ := F.sim.closest_nonempty w' (Set.toFinite _ : Set.Finite _) ⟨w', hw'⟩
  obtain ⟨y, hy⟩ := F.sim.closest_nonempty w' (Set.toFinite _ : Set.Finite _) hn
  have hxy : x = y :=
    antisymm (hp w' hw'.1 x hx y hy)
      (hnp w' hw'.1 y hy x (by simpa [Frame.closest] using hx))
  exact (F.sim.closest_subset _ _ hy).2 (hxy ▸ (F.sim.closest_subset _ _ hx).2)

end Desire.Conditional
