import Linglib.Core.Order.PreferenceStructure

/-!
# Effective Preference Structures
@cite{condoravdi-lauer-2012} @cite{lauer-2013} @cite{condoravdi-lauer-2016}

The agent's distinguished `PreferenceStructure` used to guide action choice
(@cite{condoravdi-lauer-2016} (68): `EP(a, w)`). Distinguished from
arbitrary preference structures by the consistency + realism axioms
(@cite{condoravdi-lauer-2012} (66)–(67)).
-/

namespace Core.Order

universe u

variable {W : Type u}

/-- An **effective preference structure** at world `w`, relative to the
    agent's information state `B : Set W`: a `PreferenceStructure` that
    is consistent and realistic w.r.t. `B`. -/
structure EffectivePreference (W : Type u) (B : Set W)
    extends PreferenceStructure W where
  isConsistent : toPreferenceStructure.consistent B
  isRealistic  : toPreferenceStructure.realistic B

namespace EffectivePreference

variable {B : Set W}

/-- The agent's *effective preferences*: the maximal elements of the
    effective preference structure. -/
abbrev effectivePrefs (E : EffectivePreference W B) : Set (Set W) :=
  E.toPreferenceStructure.maxElts

/-- Smart constructor: realism is derivable from consistency
    (`PreferenceStructure.consistent_implies_realistic`). -/
def ofConsistent (P : PreferenceStructure W) (hC : P.consistent B) :
    EffectivePreference W B where
  toPreferenceStructure := P
  isConsistent := hC
  isRealistic  := P.consistent_implies_realistic hC

end EffectivePreference

end Core.Order
