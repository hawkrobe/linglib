import Linglib.Core.Order.PreferenceStructure

/-!
# World Preorder Induced by Maximal Preferences
@cite{condoravdi-lauer-anankastics} @cite{kratzer-1981} @cite{portner-2018}

The world-side preorder `w ≤ v` iff `w` satisfies every maximal preference
that `v` satisfies. The Kratzer-style derivation of a world ordering from
an ordering source, applied to `maxElts`. Used by
@cite{condoravdi-lauer-anankastics} (88): `g_epA(w) = max[EP(Ad, w)]`.

The bridge to a `List`-valued `Theories.Semantics.Modality.Kratzer.OrderingSource`
requires either a finiteness witness or a non-constructive enumeration; that
bridge lives downstream.
-/

namespace Core.Order.PreferenceStructure

universe u

variable {W : Type u}

/-- The world-level preorder induced by maximal preferences:
    `maxInducedLe w v` iff `w` verifies every maximal preference that
    `v` verifies. -/
def maxInducedLe (P : PreferenceStructure W) : W → W → Prop :=
  fun w v => ∀ p ∈ P.maxElts, v ∈ p → w ∈ p

theorem maxInducedLe_refl (P : PreferenceStructure W) (w : W) :
    P.maxInducedLe w w := fun _ _ hw => hw

theorem maxInducedLe_trans (P : PreferenceStructure W) {w v u : W}
    (hwv : P.maxInducedLe w v) (hvu : P.maxInducedLe v u) :
    P.maxInducedLe w u :=
  fun p hp hu => hwv p hp (hvu p hp hu)

end Core.Order.PreferenceStructure

