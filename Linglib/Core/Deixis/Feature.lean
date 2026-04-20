/-!
# Deictic Features: Demonstrative Distance and Person Orientation
@cite{moroney-2021}

Framework-agnostic enumeration of deictic features carried by demonstratives.
Promoted from `Fragments/Shan/Definiteness.SpatialRelation` (which carried
just `proximal | distal`) for cross-fragment reuse.

## Coverage

The four constructors cover the WALS Ch. 41 distance-system typology:

- **Two-way systems** (~54% of attested languages): use `proximal | distal`.
  English (this/that), Mandarin (zhe/na), French (ce N-ci/ce N-la), Shan
  (nâj/nân), Magahi (i/ũ), and most Indo-European languages.

- **Three-way distance-oriented systems**: use `proximal | medial | distal`.
  Latin (hic/iste/ille), Spanish (este/ese/aquel), Hunzib.

- **Distance-neutral demonstratives** (Modern German *dieser*, Hawaiian
  no-contrast forms): use `unspecified`.

## Out of scope at this enum

Adding more granularity (person-orientation, visibility, elevation, posture)
should follow the *concrete-then-abstract* discipline: add a constructor
when a fragment actually needs it, not in anticipation. Specifically:

- **Person-oriented three-way systems** (Japanese ko/so/a, Korean i/ku/ce):
  add `nearSpeaker | nearHearer | awayFromBoth` constructors when the first
  fragment needs them.
- **Visibility contrasts** (Quechua, Kwakwaka'wakw, ASL): add `visible |
  invisible` constructors when a fragment needs them.
- **Elevation contrasts** (Dyirbal, Nepali): add when needed.

This is the centralized type referenced by `Core.Nominal.NominalKind.deictic`
(forthcoming) and by demonstrative entries in `Fragments/`.
-/

namespace Core.Deixis

/-- Deictic features carried by demonstratives. Minimal enum sufficient for
    two-way and three-way distance systems plus distance-neutral
    demonstratives; extend when a fragment requires finer granularity
    (person orientation, visibility, elevation). -/
inductive Feature where
  /-- Close to speaker (e.g. English *this*, Mandarin *zhe*, Shan *nâj*). -/
  | proximal
  /-- Intermediate distance (e.g. Latin *iste*, Spanish *ese*).
      For three-way distance-oriented systems only — person-oriented
      three-way systems (Japanese, Korean) need separate constructors. -/
  | medial
  /-- Far from speaker (e.g. English *that*, Mandarin *na*, Shan *nân*). -/
  | distal
  /-- Distance-neutral demonstrative (e.g. Modern German *dieser*).
      Used when a demonstrative is morphologically present but does not
      encode a distance contrast. -/
  | unspecified
  deriving DecidableEq, Repr

/-- A demonstrative encodes a distance contrast iff its feature is one of
    proximal/medial/distal (not `unspecified`). -/
def Feature.EncodesDistance (f : Feature) : Prop :=
  f ≠ .unspecified

instance : DecidablePred Feature.EncodesDistance :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Distance-encoding features are exactly the non-`unspecified` ones. -/
theorem encodesDistance_iff (f : Feature) :
    f.EncodesDistance ↔ f ≠ .unspecified := Iff.rfl

end Core.Deixis
