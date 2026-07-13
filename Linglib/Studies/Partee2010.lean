import Linglib.Semantics.Modification.Classification
import Linglib.Semantics.Modification.Coercion
import Linglib.Studies.Kamp1975
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.Partee2010

/-!
# Partee (2010): Privative Adjectives: Subsective plus Coercion
[partee-2010]

[partee-2010] argues no adjectives are genuinely
[kamp-1975]-privative: apparent privatives are subsective after
NVP-driven noun-coercion (the NVP and HPP of [kamp-partee-1995] p. 161,
restated as formulae (18) and (20) in [partee-2010] § 4). Polish
NP-splitting data from [nowak-2000] is the empirical wedge.

## Main results

* `isPrivative_no_LicensedCoercion`: Kamp-privative adjectives admit
  no `LicensedCoercion` — the formal obstruction motivating reanalysis.
* `fakeReanalysis : SubsectiveReanalysis Kamp1975.fakeAdj` — the
  constructive reanalysis of Kamp's paradigm privative — with
  `fakeCoercion`, the coercion it licenses (the positive half of the
  obstruction), and `fakeReanalysis_RevisedClass_subsective`, placing
  the reanalysed meaning in `RevisedClass.subsective`.
* `split_tracks_subsectivity`: over the [nowak-2000] sample, NP-split
  acceptability tracks the reading's class (splittable ⟺ not
  non-subsective) — the § 3 generalization.
* Witness bridges from Kamp's `grayAdj`/`skillfulAdj`/`allegedAdj`
  to `RevisedClass` cases.
-/

namespace Partee2010

open Modification Modifier

variable {W E : Type*}

/-! ### The obstruction: privatives admit no licensed coercion -/

/-- Kamp-privative adjectives admit no NVP-licensed coercion. For any
    shift, NVP requires a positive witness `x` with `adj shift w x ∧
    shift w x`; privativity forces `adj shift w x → ¬ shift w x`. -/
theorem isPrivative_no_LicensedCoercion {adj : Modifier (Property W E)}
    (hp : isPrivative adj) (N : Property W E) (w : W) :
    IsEmpty (LicensedCoercion N adj w) :=
  ⟨fun lc => by
    obtain ⟨x, hshift, hadj⟩ := lc.satisfies_nvp.1
    exact isPrivative_iff.mp hp lc.shift w x hadj hshift⟩

/-- Specialisation to `Kamp1975.fakeAdj`. -/
theorem fakeAdj_no_LicensedCoercion (N : Property Kamp1975.W2 Kamp1975.E3)
    (w : Kamp1975.W2) :
    IsEmpty (LicensedCoercion N Kamp1975.fakeAdj w) :=
  isPrivative_no_LicensedCoercion Kamp1975.fake_privative N w

/-! ### The reanalysis, and the coercion it licenses -/

/-- Reanalysis of `Kamp1975.fakeAdj`: widen `N` by `∨` with `fakeAdj
    N`, take the reanalysed meaning to be membership-in-`N`-and-of-
    fake-type. Inert hypothesis is vacuously satisfied because the
    direct application of `fakeAdj N` to entities in `N` is empty
    (privative). -/
def fakeReanalysis : SubsectiveReanalysis Kamp1975.fakeAdj where
  nounShift N := fun w x => N w x ∨ Kamp1975.fakeAdj N w x
  adjSubsective := fun N w x => N w x ∧ x = Kamp1975.E3.b
  le_nounShift _ _ _ hN := Or.inl hN
  is_subsective _ _ _ h := h.1
  shift_inert N w hne := by
    obtain ⟨x, hN, hadj⟩ := hne.1
    exact absurd hN (isPrivative_iff.mp Kamp1975.fake_privative N w x hadj)

/-- A toy noun for the fur scenario: `a` is (real) fur. -/
def furN : Property Kamp1975.W2 Kamp1975.E3 := fun _ x => x = .a

/-- With the noun widened to "real or fake fur", the reanalysed meaning
    is non-vacuous in the shifted domain: `b` is fake fur (positive
    extension), `a` is real fur (negative extension). -/
theorem fakeReanalysis_isNonVacuous (w : Kamp1975.W2) :
    isNonVacuous (fakeReanalysis.adjSubsective (fakeReanalysis.nounShift furN)) w
      (fakeReanalysis.nounShift furN w) :=
  have hb : fakeReanalysis.nounShift furN w .b := Or.inr ⟨trivial, fun h => nomatch h⟩
  ⟨⟨.b, hb, hb, rfl⟩, ⟨.a, Or.inl rfl, fun h => nomatch h.2⟩⟩

/-- The coercion `fakeReanalysis` licenses at the fur noun — the
    positive counterpart to `fakeAdj_no_LicensedCoercion`: the
    *reanalysed* meaning admits exactly the coercion the *classical*
    privative typing forbids. -/
def fakeCoercion (w : Kamp1975.W2) :
    LicensedCoercion furN fakeReanalysis.adjSubsective w :=
  fakeReanalysis.licensedCoercion (fakeReanalysis_isNonVacuous w)

/-- The reanalysed meaning lands in `RevisedClass.subsective`: the
    "former privatives are subsective after coercion" collapse, as a
    theorem rather than prose. -/
theorem fakeReanalysis_RevisedClass_subsective :
    RevisedClass.subsective.satisfies fakeReanalysis.adjSubsective :=
  fakeReanalysis.is_subsective

/-! ### § 3: the splitting diagnostic -/

/-- [partee-2010] § 3's diagnostic prediction: NP-splitting is available
    exactly outside the non-subsective class. -/
abbrev predictsSplit (c : RevisedClass) : Prop := c ≠ .nonSubsective

/-- The [nowak-2000] split sample: each split datum (or reading, for
    ambiguous *biedny*) paired with the class [partee-2010] § 3 assigns
    to the adjective's reading. -/
def splitSample : List (Features.Judgment × RevisedClass) :=
  [(Examples.ex_11b.judgment, .intersective),   -- przystojny 'handsome'
   (Examples.ex_12b.judgment, .intersective),   -- nowy 'new'
   (Examples.ex_13a.judgment, .intersective),   -- rozległy 'vast'
   (Examples.ex_13b.judgment, .intersective),
   (Examples.ex_14a.judgment, .nonSubsective),  -- były 'former'
   (Examples.ex_14b.judgment, .nonSubsective)]
  ++ (Examples.biedny_ambiguity.readings.map Prod.snd).zip
      [.intersective, .nonSubsective]           -- biedny 'not rich'/'pitiful'

/-- Splitting tracks (non)subsectivity, not privativity: over the
    [nowak-2000] sample a split is acceptable iff the reading's class
    predicts it. The reading-level *biedny* rows carry the paper's
    sharpest claim: the diagnostic tracks the reading, not the
    lexeme. -/
theorem split_tracks_subsectivity :
    ∀ p ∈ splitSample, (p.1 = .acceptable ↔ predictsSplit p.2) := by
  decide

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
