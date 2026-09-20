import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Types whose terms are segments

This file defines `SegmentLike`, the class of types whose terms can be read as segments. A
language's phonemes form a small type of their own, with a name for each phoneme and a proof
by cases for each claim about all of them, while rules and harmony systems act on `Segment`,
the type of feature bundles. `SegmentLike P` relates the two. It gives a map from `P` to
`Segment` that sends distinct terms to distinct segments, and a term of `P` is then used
wherever a segment is expected, alone or in a list. The design follows mathlib's `SetLike`.

The file also defines `Segment.ofChart`, the usual way to give a phoneme its segment. It reads
a PHOIBLE chart entry, merges over it the values on which a grammar departs from the chart,
and keeps the result on the features the grammar treats as contrastive.

## Main definitions

* `Phonology.Segment.ofChart`: the segment of a chart entry, a departure and a contrastive
  feature set.
* `Phonology.SegmentLike`: a type with an injective map to `Segment`, used as a coercion.
* `Phonology.SegmentLike.inventory`: the segments of a finite such type.
* `segment_constants`: a command naming the segment of each constructor of a type.

## Main results

* `Phonology.Segment.ofChart_apply`: on a contrastive feature where the departure is silent,
  the segment has the chart's value.
* `Phonology.SegmentLike.coe_injective`: distinct terms are distinct segments.

## Implementation notes

Injectivity is a field of the class, as it is in `SetLike`, so an instance cannot omit it.
It is what detects a contrast lost in the passage from PHOIBLE's features to the smaller set
here, as between a long and a short vowel or a plain and a fortis stop. The recipe of
`Segment.ofChart` is a function and not part of the class, so a type built some other way can
be an instance.

## References

* [moran-mccloy-2019]
* [hayes-2009]
-/

namespace Phonology

open Data.PHOIBLE

/-- The segment of a chart entry `m` has the values of `departure` where that is specified and
those of `m` elsewhere, kept on the features in `contrastive`. -/
def Segment.ofChart (m : FeatureMatrix) (departure : Segment := ⊥)
    (contrastive : Finset Feature := Finset.univ) : Segment :=
  Bundle.restrict contrastive (Bundle.merge departure m.toSegment)

theorem Segment.ofChart_apply {m : FeatureMatrix} {departure : Segment}
    {contrastive : Finset Feature} {f : Feature} (hf : f ∈ contrastive)
    (hd : departure f = none) : Segment.ofChart m departure contrastive f = m.toSegment f := by
  rw [Segment.ofChart, Bundle.restrict_apply_of_mem _ hf, Bundle.merge_apply_of_eq_none hd]

/-- `SegmentLike P` says that the terms of `P` can be read as segments, distinct terms as
distinct segments. -/
class SegmentLike (P : Type*) where
  /-- The segment of a term. -/
  coe : P → Segment
  /-- Distinct terms are distinct segments. -/
  coe_injective' : Function.Injective coe

namespace SegmentLike

variable {P : Type*} [SegmentLike P]

instance : CoeOut P Segment := ⟨coe⟩

instance : CoeOut (List P) (List Segment) := ⟨List.map coe⟩

theorem coe_injective : Function.Injective (coe : P → Segment) := coe_injective'

@[simp] theorem coe_inj {x y : P} : (x : Segment) = y ↔ x = y := coe_injective.eq_iff

/-- The segments of a finite type of segments. -/
def inventory (P : Type*) [SegmentLike P] [Fintype P] : Finset Segment :=
  Finset.univ.map ⟨coe, coe_injective (P := P)⟩

@[simp] theorem mem_inventory [Fintype P] {s : Segment} :
    s ∈ inventory P ↔ ∃ x : P, (x : Segment) = s := by
  simp [inventory]

end SegmentLike

open Lean Elab Command in
/-- `segment_constants P` defines, for each constructor `c` of the type `P`, a constant `c` in
the current namespace that is the segment of `P.c`. A grammar whose underlying forms mix
phonemes with archiphonemes then writes both as segments, as in `[A, c, A, K]`, without
opening the constructors of `P`, which would capture one-letter pattern variables. -/
elab "segment_constants " T:ident : command => do
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo T
  let some (.inductInfo iv) := (← getEnv).find? tn
    | throwError "{tn} is not an inductive type"
  for c in iv.ctors do
    let doc := mkNode ``Lean.Parser.Command.docComment
      #[mkAtom "/--", mkAtom s!"The segment of `{c}`. -/"]
    elabCommand (← `($doc:docComment def $(mkIdent (.mkSimple c.getString!)) : Phonology.Segment :=
      (($(mkIdent c) : $(mkIdent tn)) : Phonology.Segment)))

end Phonology
