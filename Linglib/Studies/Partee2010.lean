module

public import Linglib.Semantics.Modification.Classification
public import Linglib.Semantics.Modification.Coercion
public import Linglib.Studies.Kamp1975
public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Partee2010

/-!
# Partee (2010): Privative Adjectives: Subsective plus Coercion

Partee argues that no adjective is privative in Kamp's sense. An apparent privative such as
*fake* is subsective once the noun is coerced to a wider meaning, *fur* to real or fake fur, as
Kamp and Partee's non-vacuity and head primacy principles demand. A Kamp-privative adjective
admits no such coercion, while the reanalysed *fake* does and is subsective. Nowak's Polish
NP-splitting data are the diagnostic: a split is acceptable exactly outside the non-subsective
class, tracking the reading rather than the word for the ambiguous *biedny*.

## Main statements

* `isPrivative_no_LicensedCoercion`: a Kamp-privative adjective admits no licensed coercion.
* `fakeCoercion`, `fakeReanalysis_RevisedClass_subsective`: the reanalysed *fake* licenses the
  widening of *fur* and is subsective.
* `split_tracks_subsectivity`: splitting tracks the class of the adjective's reading.

## Implementation notes

The coercion apparatus is that of `Semantics/Modification/Coercion.lean`, the Polish rows are
the generated examples of `Data/Examples/Partee2010`, and Kamp's paradigm adjectives come from
`Studies/Kamp1975.lean`.

## References

* [partee-2010]
* [kamp-1975]
* [kamp-partee-1995]
* [nowak-2000]
-/

@[expose] public section

namespace Partee2010

open Modification Modifier

variable {W E : Type*}

/-! ### The revised hierarchy

Partee's footnote 1 (p. 277) observes that the meaning postulates give no linear order of the
four classes, only the three-class scale intersective ⊂ subsective ⊂ unrestricted, with the
privatives a subset of the unrestricted class disjoint from the subsectives. Reanalysing the
privatives as subsective leaves that scale. -/

/-- The classes of Partee's revised hierarchy, in which the privative class is eliminated in
favour of subsective adjectives with coercion of the noun. -/
inductive RevisedClass where
  /-- Intersective adjectives, `⟦A N⟧ = ⟦Q⟧ ∩ ⟦N⟧`. -/
  | intersective
  /-- Subsective adjectives, `⟦A N⟧ ⊆ ⟦N⟧`, which take in the former privatives once the noun
  is coerced. -/
  | subsective
  /-- Adjectives without an entailment, such as *alleged*, *potential* and *putative*. -/
  | nonSubsective
  deriving DecidableEq

/-- `c.satisfies adj` is the meaning postulate of class `c`. Every intersective modifier is also
subsective (`Modifier.IsIntersective.isSubsective`). The postulate for `nonSubsective`, the
failure of subsectivity, also holds of Kamp's privatives, which the revised hierarchy no longer
recognizes as a class. -/
def RevisedClass.satisfies : RevisedClass → Modifier (Property W E) → Prop
  | .intersective => IsIntersective
  | .subsective => IsSubsective
  | .nonSubsective => fun adj ↦ ¬ IsSubsective adj

/-! ### The obstruction: privatives admit no licensed coercion -/

/-- A Kamp-privative adjective admits no coercion licensed by non-vacuity, since non-vacuity in
the widened noun needs something in both the noun and the adjective's value. -/
theorem isPrivative_no_LicensedCoercion {adj : Modifier (Property W E)}
    (hp : IsPrivative adj) (N : Property W E) (w : W) :
    IsEmpty (LicensedCoercion N adj w) :=
  ⟨fun lc ↦ not_isNonVacuous_of_isPrivative hp lc.shift w lc.satisfies_nvp⟩

/-- Kamp's *fake* admits no licensed coercion. -/
theorem fakeAdj_no_LicensedCoercion (N : Property Kamp1975.W2 Kamp1975.E3)
    (w : Kamp1975.W2) :
    IsEmpty (LicensedCoercion N Kamp1975.fakeAdj w) :=
  isPrivative_no_LicensedCoercion Kamp1975.fake_privative N w

/-! ### The reanalysis, and the coercion it licenses -/

/-- The reanalysis of Kamp's *fake* widens a noun to the things that are either Ns or fake Ns
and reads *fake* subsectively as being of the fake type. Since *fake* is privative, it is never
non-vacuous on the literal noun, so the last-resort condition holds trivially. -/
def fakeReanalysis : SubsectiveReanalysis Kamp1975.fakeAdj where
  nounShift N := fun w x ↦ N w x ∨ Kamp1975.fakeAdj N w x
  adjSubsective := fun N w x ↦ N w x ∧ x = Kamp1975.E3.b
  le_nounShift _ _ _ hN := Or.inl hN
  is_subsective _ _ _ h := h.1
  shift_inert N w hne := by
    obtain ⟨x, hN, hadj⟩ := hne.1
    exact absurd hN (isPrivative_iff.mp Kamp1975.fake_privative N w x hadj)

/-- The toy noun *fur*, of which `a` is the one real instance. -/
def furN : Property Kamp1975.W2 Kamp1975.E3 := fun _ x ↦ x = .a

/-- With *fur* widened to real or fake fur, the reanalysed *fake* is non-vacuous in the widened
noun, since `b` is fake fur and `a` is real fur. -/
theorem fakeReanalysis_isNonVacuous (w : Kamp1975.W2) :
    IsNonVacuous (fakeReanalysis.adjSubsective (fakeReanalysis.nounShift furN)) w
      (fakeReanalysis.nounShift furN w) :=
  have hb : fakeReanalysis.nounShift furN w .b := Or.inr ⟨trivial, fun h ↦ nomatch h⟩
  ⟨⟨.b, hb, hb, rfl⟩, ⟨.a, Or.inl rfl, fun h ↦ nomatch h.2⟩⟩

/-- The reanalysed *fake* licenses the coercion of *fur* that the privative *fake* cannot
(`fakeAdj_no_LicensedCoercion`). -/
def fakeCoercion (w : Kamp1975.W2) :
    LicensedCoercion furN fakeReanalysis.adjSubsective w :=
  fakeReanalysis.licensedCoercion (fakeReanalysis_isNonVacuous w)

/-- The reanalysed *fake* is subsective, so the former privative falls in the subsective
class. -/
theorem fakeReanalysis_RevisedClass_subsective :
    RevisedClass.subsective.satisfies fakeReanalysis.adjSubsective :=
  fakeReanalysis.is_subsective

/-! ### The splitting diagnostic -/

/-- NP-splitting is predicted exactly outside the non-subsective class. -/
abbrev predictsSplit (c : RevisedClass) : Prop := c ≠ .nonSubsective

/-- The split sample of [nowak-2000] pairs each split datum, or each reading of the ambiguous
*biedny*, with the class the paper assigns to the adjective's reading. -/
def splitSample : List (Judgment × RevisedClass) :=
  [(Examples.ex_11b.judgment, .intersective),   -- przystojny 'handsome'
   (Examples.ex_12b.judgment, .intersective),   -- nowy 'new'
   (Examples.ex_13a.judgment, .intersective),   -- rozległy 'vast'
   (Examples.ex_13b.judgment, .intersective),
   (Examples.ex_14a.judgment, .nonSubsective),  -- były 'former'
   (Examples.ex_14b.judgment, .nonSubsective)]
  ++ (Examples.biedny_ambiguity.readings.map Prod.snd).zip
      [.intersective, .nonSubsective]           -- biedny 'not rich'/'pitiful'

/-- Over the sample of [nowak-2000] a split is acceptable exactly when the class of the
adjective's reading predicts it, so splitting tracks subsectivity rather than privativity, and
for *biedny* it tracks the reading rather than the word. -/
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
