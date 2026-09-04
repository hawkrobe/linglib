import Linglib.Phonology.Segmental.Defs
import Linglib.Core.Data.Fintype.Sets
import Mathlib.Data.Finset.Card

/-!
# Feature classes

The grouping of Hayes's features by the sections of his feature chapter — manner
(§4.4, including the sonority features), laryngeal (§4.7), and the three major articulators
(§4.6.1) with their dependents, [round] and [labiodental] under labial (§4.6.3), [anterior],
[distributed], [strident] and [lateral] under coronal (§4.6.2), and the vowel features (§4.5)
under dorsal (§4.6.4) — as plain finite sets, with Place their union (Padgett p. 83).
The grouping is the inventory's own and makes no constituency claim, with no root, no order
and no `FeatureGeometry` instance, because the current textbooks agree on the flat classes
but not on a tree: Hayes draws none, nor do Bale and Reiss; Gussenhoven and Jacobs
draw one with a supralaryngeal node and no manner constituent (the consensus tree of
Broe), Davenport and Hannahs one with a manner class node, and Zsiga one
with the manner features at the root together with the statement that no consensus exists,
parting ways exactly where Clements, Sagey, and Halle, Vaux and Wolfe do, on
the supralaryngeal node, a manner constituent, and the homes of [continuant], [strident],
[lateral], [nasal] and [tense]. Trees are therefore instances of
`Phonology/FeatureGeometry.lean` in the studies of the works that argue for them, and
agreement on a class — Brown and Meyer's AGREE[place] — is `Set.EqOn` on the class.
Designated articulators are the articulator features a segment is specified for
(Halle, Vaux and Wolfe §1.2.2), and a complex segment has more than one (Sagey).

## Main definitions

* `FeatureClass`, `Feature.featureClass` — the five classes and each feature's class.
* `FeatureClass.features`, `FeatureClass.place` — a class's features, and the place class as
  the union of the articulator classes.
* `Segment.articulators`, `Segment.IsComplex` — designated articulators and complex segments.

## Main results

* `FeatureClass.mem_features`, `FeatureClass.mem_place` — membership in a class and in the
  place class.

## Implementation notes

The contested placements are Hayes's: [strident] and [lateral] are coronal where
Gussenhoven and Jacobs, Davenport and Hannahs and Clements make them manner
features, and [tense] is a vowel feature under dorsal where the tree-drawing textbooks give
[ATR] its own radical or pharyngeal node. Agreement on a class or on the place class is
decidable, so AGREE-style facts about Fragment segments close by `decide`.

## References

* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [J. Padgett, *Feature Classes in Phonology* (2002)][padgett-2002]
* [A. Bale and C. Reiss, *Phonology: A Formal Introduction* (2018)][bale-reiss-2018]
* [C. Gussenhoven and H. Jacobs, *Understanding Phonology* (2017)][gussenhoven-jacobs-2017]
* [M. Broe, *An Introduction to Feature Geometry* (1992)][broe-1992]
* [M. Davenport and S. J. Hannahs, *Introducing Phonetics and Phonology*
  (2020)][davenport-hannahs-2020]
* [E. C. Zsiga, *The Phonology/Phonetics Interface* (2020)][zsiga-2020]
* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
* [M. Halle, B. Vaux and A. Wolfe, *On Feature Spreading and the Representation of Place of
  Articulation* (2000)][halle-vaux-wolfe-2000]
* [J. Brown and J. Meyer, *Assimilation and Morpheme Boundaries in Mgira* (2024)][brown-meyer-2024]
-/

namespace Phonology

/-! ### The classes -/

/-- Hayes's five feature classes: manner, laryngeal, and the three major articulators. -/
inductive FeatureClass where
  | manner | laryngeal | labial | coronal | dorsal
  deriving DecidableEq, Repr, Fintype

/-- The class of each feature, by the sections of Hayes's feature chapter (see the module
docstring). -/
def Feature.featureClass : Feature → FeatureClass
  | .syllabic | .consonantal | .sonorant | .approximant | .continuant | .delayedRelease
  | .nasal | .tap | .trill => .manner
  | .voice | .spreadGlottis | .constrGlottis => .laryngeal
  | .labial | .round | .labiodental => .labial
  | .coronal | .anterior | .distributed | .strident | .lateral => .coronal
  | .dorsal | .high | .low | .front | .back | .tense => .dorsal

namespace FeatureClass

/-- The features of a class. -/
def features (c : FeatureClass) : Finset Feature := Finset.univ.filter (·.featureClass = c)

/-- The place class: the union of the three articulator classes (Padgett p. 83's "Place
simply stands for the set {[labial], [coronal], [dorsal], …}"). -/
def place : Finset Feature := labial.features ∪ coronal.features ∪ dorsal.features

variable {f : Feature} {c : FeatureClass}

theorem mem_features : f ∈ c.features ↔ f.featureClass = c := by simp [features]

theorem mem_place :
    f ∈ place ↔
      f.featureClass = .labial ∨ f.featureClass = .coronal ∨ f.featureClass = .dorsal := by
  simp [place, mem_features]

instance (s₁ s₂ : Segment) (c : FeatureClass) : Decidable (Set.EqOn s₁ s₂ ↑c.features) :=
  Set.decidableEqOnOfFintype _ _ _

instance (s₁ s₂ : Segment) : Decidable (Set.EqOn s₁ s₂ ↑place) :=
  Set.decidableEqOnOfFintype _ _ _

end FeatureClass

/-! ### Complex segments -/

/-- The designated articulators of a segment, as the articulator features it is specified `+`
for (Halle, Vaux and Wolfe §1.2.2). -/
def Segment.articulators (s : Segment) : Finset Feature :=
  ({.labial, .coronal, .dorsal} : Finset Feature).filter (s · = some true)

/-- A complex segment has more than one designated articulator: the labiovelar [k͡p] carries
[labial] and [dorsal], the labialised [kʷ] only [dorsal] beside [+round] (Sagey;
Halle, Vaux and Wolfe p. 435). -/
def Segment.IsComplex (s : Segment) : Prop := 1 < s.articulators.card

instance : DecidablePred Segment.IsComplex := λ _ => inferInstanceAs (Decidable (1 < _))

end Phonology
