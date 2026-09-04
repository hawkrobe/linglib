import Linglib.Phonology.FeatureGeometry
import Linglib.Phonology.Segmental.Classes

/-!
# Halle, Vaux and Wolfe (2000): feature spreading and the representation of place

Halle, Vaux and Wolfe review the four innovations proposed since Clements — Unified
Feature Theory, Vowel-Place Theory, Partial Spreading and Strict Locality — records that no
consensus exists on which to adopt (§1.1), and proposes Revised Articulator Theory, which keeps
Partial Spreading and rejects the other three. Its tree (1) groups the features of the six
articulators under the nodes Lips, Tongue Blade, Tongue Body, Soft Palate, Tongue Root and
Larynx, with Place over the three oral articulators, Guttural over tongue root and larynx, and
the articulator-free features [continuant], [strident], [lateral] and [suction] beside the root
features [consonantal] and [sonorant] attached to the root. Designated articulators are terminal
features rather than nodes, so the labiovelar [k͡p] carries both [labial] and [dorsal] while the
labialised [kʷ] carries [dorsal] beside [+round] (§1.2.2, p. 435). Spreading operates on
terminal features (§1.2.3), so a rule may spread any subset of a node's features and the tree
only names the natural sets.

## Main definitions

* `Node`, `Node.parent`, `node` — tree (1) as a `FeatureGeometry` instance over Hayes's
  inventory.
* `kp`, `kw` — the feature complements of the labiovelar and the labialised velar (p. 435).

## Main results

* `articulatorFree_mem_naturalClass_iff` — an articulator-free or root feature lies in the
  root's class and no other.
* `nasal_notMem_place`, `place_eq_union` — Soft Palate is not under Place, and Place is exactly
  the three oral articulators.
* `isComplex_kp`, `not_isComplex_kw` — [k͡p] is complex and [kʷ] is not.

## Implementation notes

Features of Hayes's inventory absent from (1) are placed by the paper's own
articulator-bound/free criterion (§1.2): [approximant], [delayed release], [tap], [trill] and
[syllabic] are articulator-free and go to the root, [labiodental] to Lips, [front] to Tongue
Body, and [voice], executed by the larynx, to Larynx; [tense] is left unplaced, since the paper's
tongue-root features are [ATR] and [RTR] and Hayes's [tense] is not identified with them.
[suction], [rhinal], [ATR], [RTR], [radical], [stiff vocal folds], [slack vocal folds] and
[glottal] have no counterpart in the inventory, so Tongue Root dominates nothing here.

## TODO

* §2's arguments against Unified Feature Theory and Vowel-Place Theory, §3's analyses (Barra
  Gaelic vowel copy, Irish nasal place and dorsal assimilation) and §1.2.4's full specification.

## References

* [M. Halle, B. Vaux and A. Wolfe, *On Feature Spreading and the Representation of Place of
  Articulation* (2000)][halle-vaux-wolfe-2000]
* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
-/

namespace HalleVauxWolfe2000

open Phonology Phonology.FeatureGeometry

/-! ### Tree (1) -/

/-- The nodes of tree (1): the root; Place over Lips, Tongue Blade and Tongue Body; Soft Palate;
Guttural over Tongue Root and Larynx. -/
inductive Node where
  | root | place | lips | tongueBlade | tongueBody | softPalate | guttural | tongueRoot | larynx
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The node immediately dominating each node; the root alone has none. -/
def parent : Node → Option Node
  | .root => none
  | .place | .softPalate | .guttural => some .root
  | .lips | .tongueBlade | .tongueBody => some .place
  | .tongueRoot | .larynx => some .guttural

/-- A node and its ancestors; the tree has depth two. -/
def up (n : Node) : Finset Node :=
  ((List.range 3).filterMap λ i => (· >>= parent)^[i] (some n)).toFinset

instance : PartialOrder Node := PartialOrder.lift up (by decide)

instance : DecidableLE Node := λ a b => inferInstanceAs (Decidable (up a ⊆ up b))

instance : OrderBot Node where
  bot := .root
  bot_le := by decide

end Node

/-- The terminal features of (1), read over Hayes's inventory (see the module
docstring for the features the paper does not list). -/
def node : Feature → Option Node
  | .consonantal | .sonorant | .continuant | .strident | .lateral
  | .syllabic | .approximant | .delayedRelease | .tap | .trill => some .root
  | .labial | .round | .labiodental => some .lips
  | .coronal | .anterior | .distributed => some .tongueBlade
  | .dorsal | .high | .low | .back | .front => some .tongueBody
  | .nasal => some .softPalate
  | .voice | .spreadGlottis | .constrGlottis => some .larynx
  | .tense => none

instance : FeatureGeometry Feature Node where
  isChain_Iic := by unfold IsChain Set.Pairwise; decide +revert
  node := node

/-! ### Articulator-free features and Place -/

/-- The articulator-free features and the root features belong to the root's class alone: no
articulator node dominates them. -/
theorem articulatorFree_mem_naturalClass_iff :
    ∀ f ∈ ({.consonantal, .sonorant, .continuant, .strident, .lateral} : Finset Feature),
      ∀ a : Node, f ∈ naturalClass a ↔ a = ⊥ := by
  decide

/-- Soft Palate is a sister of Place, not under it. -/
theorem nasal_notMem_place : Feature.nasal ∉ naturalClass Node.place := by decide

/-- Place dominates exactly the three oral articulators. -/
theorem place_eq_union :
    naturalClass Node.place =
      naturalClass Node.lips ∪ naturalClass Node.tongueBlade ∪ naturalClass Node.tongueBody := by
  decide

/-! ### Designated articulators (p. 435) -/

/-- The labiovelar stop: `[dorsal, labial, +consonantal, −sonorant, −round, −continuant]`. -/
def kp : Segment :=
  Segment.ofSpecs [(.dorsal, true), (.labial, true), (.consonantal, true), (.sonorant, false),
    (.round, false), (.continuant, false)]

/-- The labialised velar stop: `[dorsal, +consonantal, −sonorant, +round, −continuant]`, with no
specification for [labial]. -/
def kw : Segment :=
  Segment.ofSpecs [(.dorsal, true), (.consonantal, true), (.sonorant, false), (.round, true),
    (.continuant, false)]

theorem isComplex_kp : kp.IsComplex := by decide

theorem not_isComplex_kw : ¬ kw.IsComplex := by decide

end HalleVauxWolfe2000
