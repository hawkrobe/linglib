import Linglib.Phonology.FeatureGeometry
import Linglib.Phonology.Segmental.FeatureClass
import Linglib.Data.Examples.HalleVauxWolfe2000

/-!
# Halle, Vaux, and Wolfe (2000): On Feature Spreading and the Representation of Place of Articulation

This file formalizes the feature tree of [halle-vaux-wolfe-2000]'s Revised Articulator Theory.
The paper reviews the four innovations proposed since [clements-1985], Unified Feature Theory,
Vowel-Place Theory, Strict Locality, and Partial Spreading, records that no consensus exists on
which to adopt (section 1.1), and keeps only Partial Spreading. Its tree (1) groups the features
of the six articulators under the nodes Lips, Tongue Blade, Tongue Body, Soft Palate, Tongue
Root, and Larynx, with Place over the three oral articulators, Guttural over tongue root and
larynx, and the articulator-free features [continuant], [strident], [lateral], and [suction]
beside the root features [consonantal] and [sonorant] at the root, `Node` and `node`, an instance
of `Phonology.FeatureGeometry` over Hayes's inventory; so an articulator-free feature lies in the
root's class and no other, `articulatorFree_mem_naturalClass_iff`, Soft Palate is not under
Place, `nasal_notMem_place`, and Place is exactly the three oral articulators, `place_eq_union`.
Designated articulators are unary terminal features rather than nodes (section 1.2.2), so the
labiovelar [k͡p] carries both [labial] and [dorsal] while the labialised [kʷ] carries [dorsal]
beside [+round], their (4), `kp` and `kw`, and only the first is a complex segment,
`isComplex_kp` and `not_isComplex_kw`. Spreading operates on terminal features (section 1.2.3),
so a rule may spread any subset of a node's features and the tree only names the natural sets:
Irish Nasal Place Assimilation spreads the Place class and so carries each oral articulator's
class while leaving the sister Soft Palate alone, `placeAssimilation_eqOn_tongueBody` and
`placeAssimilation_nasal`, and Dorsal Assimilation (44) spreads the terminal [dorsal] alone,
leaving the target's [back] untouched, `dorsalAssimilation_back`, where spreading the Tongue
Body node would carry it, `tongueBody_spread_back`, the refuted prediction (45) of a Place-node
analysis (section 2.2.4). The Irish forms are the rows of `Data.Examples.HalleVauxWolfe2000`.

## Implementation notes

Features of Hayes's inventory absent from (1) are placed by the paper's own articulator-bound
or free criterion (section 1.2): [approximant], [delayed release], [tap], [trill], and [syllabic]
are articulator-free and go to the root, [labiodental] to Lips, [front] to Tongue Body, and
[voice], executed by the larynx, to Larynx; [tense] is left unplaced, since the paper's
tongue-root features are [ATR] and [RTR] and Hayes's [tense] is not identified with them.
[suction], [rhinal], [ATR], [RTR], [radical], [stiff vocal folds], [slack vocal folds], and
[glottal] have no counterpart in the inventory, so Tongue Root dominates nothing here.

## TODO

* Section 2's arguments against Unified Feature Theory and Vowel-Place Theory, section 3's
  analyses (Barra Gaelic vowel copy, Irish nasal place and dorsal assimilation), and section
  1.2.4's full specification.

## References

* [halle-vaux-wolfe-2000]
* [clements-1985]
* [hayes-2009]
* [sagey-1986]
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

/-! ### Terminal spreading, sections 1.2.3 and 2.2.4 -/

variable (src tgt : Segment)

/-- Irish Nasal Place Assimilation spreads the terminal features under Place from `src` onto
`tgt`, the substrate's `Finset.piecewise` on the Place class. -/
def placeAssimilation : Segment := (naturalClass (F := Feature) Node.place).piecewise src tgt

/-- Spreading Place carries the whole Tongue Body class, `eqOn_piecewise_of_le`; in the same way
the Lips and Tongue Blade classes. -/
theorem placeAssimilation_eqOn_tongueBody :
    Set.EqOn (placeAssimilation src tgt) src ↑(naturalClass (F := Feature) Node.tongueBody) :=
  eqOn_piecewise_of_le src tgt (by decide)

/-- Soft Palate is a sister of Place, so Place assimilation leaves [nasal] where it was: the
assimilated nasal is still a nasal, `eqOn_piecewise_of_not_le`. -/
theorem placeAssimilation_nasal : placeAssimilation src tgt .nasal = tgt .nasal :=
  eqOn_piecewise_of_not_le (a := Node.place) (b := Node.softPalate) src tgt (by decide) (by decide)
    (by decide : Feature.nasal ∈ naturalClass (F := Feature) Node.softPalate)

/-- Irish Dorsal Assimilation (44) spreads the designated articulator alone: the terminal
feature [dorsal], not the Tongue Body node. -/
def dorsalAssimilation : Segment := ({Feature.dorsal} : Finset Feature).piecewise src tgt

/-- (44): spreading the terminal [dorsal] leaves the target's secondary articulation, its
[back] value, untouched, which is how the palatalised nasal of (44a) keeps its palatalisation
and the plain nasal of (44b) stays plain. -/
theorem dorsalAssimilation_back : dorsalAssimilation src tgt .back = tgt .back :=
  Finset.piecewise_eq_of_notMem _ _ _ (by decide)

/-- (45): spreading the Tongue Body node instead would carry [back] along with [dorsal], the
prediction of a Place-node analysis of (44) that the data refute. -/
theorem tongueBody_spread_back :
    (naturalClass (F := Feature) Node.tongueBody).piecewise src tgt .back = src .back :=
  Finset.piecewise_eq_of_mem _ _ _ (by decide)

end HalleVauxWolfe2000
