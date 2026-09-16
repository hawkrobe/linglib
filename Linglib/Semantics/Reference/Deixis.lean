/-!
# Deixis

The deictic feature of a demonstrative: proximal, medial, or distal, or unspecified for a
demonstrative that encodes no distance contrast. Two-way systems, English *this* and *that* or
Shan *nâj* and *nân* ([moroney-2021]), use the proximal and distal values; three-way
distance-oriented systems, Latin *hic*, *iste*, *ille*, add the medial one; German *dieser* is
unspecified. Finer contrasts, person orientation, visibility or elevation, are added when a
fragment needs them. A description carries its feature as `Reference.Description.demonstrative`,
and a word-class-neutral carrier exposes it through the `Demonstrative` class.

## References

* [moroney-2021]
* [patel-grosz-grosz-2017]
-/

namespace Reference

/-- Deictic features carried by demonstratives. Minimal enum sufficient for
    two-way and three-way distance systems plus distance-neutral
    demonstratives; extend when a fragment requires finer granularity
    (person orientation, visibility, elevation). -/
inductive Deixis where
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
def Deixis.EncodesDistance (f : Deixis) : Prop :=
  f ≠ .unspecified

instance : DecidablePred Deixis.EncodesDistance :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Distance-encoding features are exactly the non-`unspecified` ones. -/
theorem Deixis.encodesDistance_iff (f : Deixis) :
    f.EncodesDistance ↔ f ≠ .unspecified := Iff.rfl

end Reference

/-! ### The demonstrative capability

`[Demonstrative α]` is the *spatial-deixis* property itself — the genuinely demonstrative axis,
word-class-neutral (a demonstrative pronoun *this*, determiner *this* book, or adverb *here* all
instance it). This is the lesson of [patel-grosz-grosz-2017]: the morphological "demonstrative
pronoun" label is **not** the property. They show German *der/die/das* — long called demonstrative
pronouns — are strong-article *personal* pronouns with no spatial deixis (footnote 1: "it is far
from clear that there is anything truly 'demonstrative' about" them); the genuine German
demonstrative is *dieser*. So a carrier counts as a demonstrative iff it carries a
`Reference.Deixis`, not by morphological label — *dieser* and *this* instance `Demonstrative`,
*der* does not (it is a `PersonalPronoun`). Mirrors the word-class-neutral `Indefinite` capability. -/

/-- A carrier that encodes a deictic (demonstrative) contrast: it exposes a
    `Reference.Deixis` (proximal/medial/distal, or `unspecified` for a distance-neutral
    demonstrative like German *dieser*). The deictic feature varies per element (*this* proximal vs
    *that* distal), so this is a genuine per-element accessor. -/
class Demonstrative (α : Type _) where
  /-- The deictic feature the carrier encodes. -/
  deixis : α → Reference.Deixis
