import Linglib.Core.Lexical.UD

/-!
# Surface Gender
@cite{corbett-1991} @cite{kramer-2020}

Descriptive (atheoretical) classification of surface gender values attested
cross-linguistically. This type records the *observable* gender of a noun —
what agreement class it triggers — without committing to the mechanism of
gender assignment.

The distinction between **sex-based** systems (masculine/feminine/neuter) and
**animacy-based** systems (animate/inanimate) follows @cite{corbett-1991}'s
WALS Chapter 31. @cite{kramer-2020} argues that these surface categories
arise from a single underlying mechanism (phi-features on the nominalizing
head *n*), parameterized by feature dimension; that analysis lives in
`Theories.Morphology.DM.Categorizer`.

For languages with many noun classes (Bantu, Mixtec), the fragment retains
its own fine-grained `Gender` type and provides a bridge to `SurfaceGender`
via a `.primary` function.
-/

namespace Core

/-- Surface gender categories attested cross-linguistically.

    These are the descriptive labels a grammar assigns to nouns based on
    agreement patterns. For the structural analysis, see
    `Theories.Morphology.DM.GenderFeature`. -/
inductive SurfaceGender where
  /-- Masculine: male humans/higher animates; default in many sex-based systems. -/
  | masculine
  /-- Feminine: female humans/higher animates; marked in many sex-based systems. -/
  | feminine
  /-- Neuter: neither masculine nor feminine; inanimate default in 3-gender systems. -/
  | neuter
  /-- Common: merged masculine + feminine (Swedish, Danish). -/
  | common
  /-- Animate: animate referents in animacy-based systems (Teop, Algonquian). -/
  | animate
  /-- Inanimate: inanimate referents in animacy-based systems. -/
  | inanimate
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Whether this gender is from a sex-based system. -/
def SurfaceGender.isSexBased : SurfaceGender → Bool
  | .masculine | .feminine | .neuter | .common => true
  | .animate | .inanimate => false

/-- Whether this gender is from an animacy-based system. -/
def SurfaceGender.isAnimacyBased : SurfaceGender → Bool
  | .animate | .inanimate => true
  | _ => false

/-- Map surface gender to Universal Dependencies gender where a natural
    correspondence exists. Animacy-based genders have no standard UD
    equivalent. -/
def SurfaceGender.toUDGender : SurfaceGender → Option UD.Gender
  | .masculine => some .Masc
  | .feminine  => some .Fem
  | .neuter    => some .Neut
  | .common    => some .Com
  | .animate   => none
  | .inanimate => none

/-- Inverse: map UD gender to surface gender. Total (every UD gender has
    a surface gender equivalent). -/
def SurfaceGender.ofUDGender : UD.Gender → SurfaceGender
  | .Masc => .masculine
  | .Fem  => .feminine
  | .Neut => .neuter
  | .Com  => .common

/-- Round-trip: UD → Surface → UD is the identity. -/
theorem SurfaceGender.roundtrip_ud (g : UD.Gender) :
    (SurfaceGender.ofUDGender g).toUDGender = some g := by
  cases g <;> rfl

end Core
