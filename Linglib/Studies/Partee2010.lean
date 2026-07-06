import Linglib.Semantics.Degree.Gradability.Classification
import Linglib.Semantics.Composition.Coercion
import Linglib.Studies.Kamp1975
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.Partee2010

/-!
# Partee (2010): Privative Adjectives: Subsective plus Coercion
[partee-2010]

[partee-2010] argues no adjectives are genuinely
[kamp-1975]-privative: apparent privatives are subsective after
NVP-driven noun-coercion ([kamp-partee-1995] formulae 18, 20).
Polish NP-splitting data from [nowak-2000] is the empirical wedge.

## Main results

* `isPrivative_no_LicensedCoercion`: Kamp-privative adjectives admit
  no `LicensedCoercion` — the formal obstruction motivating reanalysis.
* `fakeReanalysis : ParteeReanalysis Kamp1975.fakeAdj` — the
  constructive reanalysis of Kamp's paradigm privative as subsective-
  after-coercion.
* Witness bridges from Kamp's `grayAdj`/`skillfulAdj`/`allegedAdj`
  to `RevisedClass` cases.
-/

namespace Partee2010

open Degree.Classification
open Semantics.Composition.Coercion

variable {W E : Type*}

/-- Kamp-privative adjectives admit no NVP-licensed coercion. For any
    shift, NVP requires a positive witness `x` with `adj shift w x ∧
    shift w x`; privativity forces `adj shift w x → ¬ shift w x`. -/
theorem isPrivative_no_LicensedCoercion {adj : AdjMeaning W E}
    (hp : isPrivative adj) (N : Property W E) (w : W) :
    IsEmpty (LicensedCoercion N adj w) :=
  ⟨fun lc => by
    obtain ⟨x, hadj, hshift⟩ := lc.satisfies_nvp.1
    exact hp lc.shift w x hadj hshift⟩

/-- Specialisation to `Kamp1975.fakeAdj`. -/
theorem fakeAdj_no_LicensedCoercion (N : Property Kamp1975.W2 Kamp1975.E3)
    (w : Kamp1975.W2) :
    IsEmpty (LicensedCoercion N Kamp1975.fakeAdj w) :=
  isPrivative_no_LicensedCoercion Kamp1975.fake_privative N w

/-- Reanalysis of `Kamp1975.fakeAdj`: widen `N` by `∨` with `fakeAdj
    N`, take the reanalysed meaning to be membership-in-`N`-and-of-
    fake-type. Inert hypothesis is vacuously satisfied because the
    direct application of `fakeAdj N` to entities in `N` is empty
    (privative). -/
def fakeReanalysis : ParteeReanalysis Kamp1975.fakeAdj where
  noun_shift N := fun w x => N w x ∨ Kamp1975.fakeAdj N w x
  adj_subsective := fun N _ x => N _ x ∧ x = Kamp1975.E3.b
  shift_supseteq _ _ _ hN := Or.inl hN
  is_subsective _ _ _ h := h.1
  shift_inert N w hne := by
    obtain ⟨x, hadj, hN⟩ := hne.1
    exact absurd hN (Kamp1975.fake_privative N w x hadj)

/-! ### `RevisedClass` witness bridges -/

theorem grayAdj_RevisedClass_intersective :
    RevisedClass.intersective.satisfies Kamp1975.grayAdj :=
  Kamp1975.gray_intersective

theorem skillfulAdj_RevisedClass_subsective :
    RevisedClass.subsective.satisfies Kamp1975.skillfulAdj :=
  Kamp1975.skillful_subsective

theorem allegedAdj_RevisedClass_nonSubsective :
    RevisedClass.nonSubsective.satisfies Kamp1975.allegedAdj :=
  Kamp1975.alleged_not_subsective

end Partee2010
