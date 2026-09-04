import Linglib.Phonology.Segmental.Defs
import Linglib.Phonology.FeatureGeometry

/-!
# Segmental feature classes

The theory-neutral grouping of [hayes-2009]'s features — the manner and major-class features,
the laryngeal features, and the features of the three oral articulators, under a root
standing for the whole segment — as an instance of `FeatureGeometry`, with Place the union of
the articulator classes rather than a node. Whether Place is a constituent, where
[continuant] and [nasal] attach, and how vowel place relates to consonant place is where the
geometries of [clements-1985], [sagey-1986] and [halle-vaux-wolfe-2000] part ways, so each is
an instance in its study and the substrate commits to none. Designated articulators are the
articulator features a segment is specified for ([halle-vaux-wolfe-2000] §1.2.2), and a
complex segment has more than one ([sagey-1986]). Agreement on the place class,
[brown-meyer-2024]'s AGREE[place], is `Set.EqOn` on `Feature.Category.place`.

## Main definitions

* `Feature.Category`, `Feature.category` — the consensus grouping and its `FeatureGeometry`
  instance.
* `Feature.Category.place` — the place class, the union of the three articulator classes.
* `Segment.articulators`, `Segment.IsComplex` — designated articulators and complex segments.

## Implementation notes

The instance follows the recipe of `Phonology/FeatureGeometry.lean`: a parent function, `up`,
`PartialOrder.lift`, and the chain axiom by `decide`. The grouping is total, so the root's class
is the whole inventory.

## References

* [hayes-2009] — the feature inventory and its chart grouping.
* [padgett-2002] — Place as the set of place features (p. 83).
* [sagey-1986] — articulator nodes and complex segments.
* [halle-vaux-wolfe-2000] — designated articulators as features (§1.2.2), [k͡p] against [kʷ]
  (p. 435).
* [clements-1985] — the class-node geometry the instances descend from.
* [brown-meyer-2024] — AGREE[place] over the place class.
-/

namespace Phonology

open FeatureGeometry

/-! ### The consensus classification -/

/-- The theory-neutral grouping of the features, [hayes-2009]'s chart read as [padgett-2002]'s
classes: the manner and major-class features, the laryngeal features, and the features of the
three oral articulators, under a root standing for the whole segment. Place is the union of
the articulator classes and not a node. -/
inductive Feature.Category where
  | root | manner | laryngeal | labial | coronal | dorsal
  deriving DecidableEq, Repr, Fintype

namespace Feature.Category

/-- Every class hangs from the root. -/
def parent : Category → Option Category
  | .root => none
  | _ => some .root

/-- A class and its ancestors. -/
def up (c : Category) : Finset Category :=
  ((List.range 2).filterMap λ i => (· >>= parent)^[i] (some c)).toFinset

instance : PartialOrder Category := PartialOrder.lift up (by decide)

instance : DecidableLE Category := λ a b => inferInstanceAs (Decidable (up a ⊆ up b))

instance : OrderBot Category where
  bot := .root
  bot_le := by decide

end Feature.Category

/-- The class of each feature, by [hayes-2009]'s chart. -/
def Feature.category : Feature → Feature.Category
  | .syllabic | .consonantal | .sonorant | .approximant | .continuant | .delayedRelease
  | .nasal | .lateral | .strident | .tap | .trill => .manner
  | .voice | .spreadGlottis | .constrGlottis => .laryngeal
  | .labial | .round | .labiodental => .labial
  | .coronal | .anterior | .distributed => .coronal
  | .dorsal | .high | .low | .front | .back | .tense => .dorsal

instance : FeatureGeometry Feature Feature.Category where
  isChain_Iic := by unfold IsChain Set.Pairwise; decide +revert
  node f := some f.category

/-- The place class: the union of the three articulator classes ([padgett-2002] p. 83's
"Place simply stands for the set {[labial], [coronal], [dorsal], …}"). -/
def Feature.Category.place : Finset Feature :=
  naturalClass labial ∪ naturalClass coronal ∪ naturalClass dorsal

/-! ### Complex segments -/

/-- The designated articulators of a segment, as the articulator features it is specified `+`
for ([halle-vaux-wolfe-2000] §1.2.2). -/
def Segment.articulators (s : Segment) : Finset Feature :=
  ({.labial, .coronal, .dorsal} : Finset Feature).filter (s · = some true)

/-- A complex segment has more than one designated articulator: the labiovelar [k͡p] carries
[labial] and [dorsal], the labialised [kʷ] only [dorsal] beside [+round] ([sagey-1986];
[halle-vaux-wolfe-2000] p. 435). -/
def Segment.IsComplex (s : Segment) : Prop := 1 < s.articulators.card

instance : DecidablePred Segment.IsComplex := λ _ => inferInstanceAs (Decidable (1 < _))

end Phonology
