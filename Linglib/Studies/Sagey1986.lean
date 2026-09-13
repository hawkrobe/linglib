import Linglib.Phonology.FeatureGeometry
import Linglib.Phonology.Segmental.FeatureClass
import Linglib.Phonology.Autosegmental.NonCrossing
import Linglib.Core.Order.Interval
import Mathlib.Data.Set.Pairwise.Basic

/-!
# Sagey (1986): The Representation of Features and Relations in Non-Linear Phonology

This file formalizes the feature geometry of the dissertation and its account of association
lines. The geometry has a class node for each independently functioning articulator, the
larynx, the soft palate, the lips, the tongue front and the tongue body, grouped under a
laryngeal and a supralaryngeal node with a place node over the three oral articulators, and
each terminal feature hangs from one class node, the degree-of-closure features `[continuant]`
and `[consonantal]` directly from the root (`Node`, `node`). A class node is present or absent,
never minus, and a terminal feature under an articulator node implies that articulator
(`Segment.Licensed`). Three consequences follow from the natural classes of the tree: place
assimilation leaves degree of closure and nasality untouched, as in Kpelle and Sanskrit
(`degreeOfClosure_mem_naturalClass_iff`), features of distinct articulators can stand in no
dependency, so the rounding-under-height structure proposed for Yawelmani is unrepresentable
(`disjoint_naturalClass_of_articulators`), and a rounded coronal is a complex segment, so a
language that admits one articulator under the place node rounds only labials
(`isComplex_of_round_of_coronal`).

Association lines represent overlap in time rather than simultaneity (`Association.Valid`),
which lets a contour segment share one timing slot and a geminate one melody. Two valid
associations cannot cross (`Association.Valid.not_crosses`), so the well-formedness condition
of [goldsmith-1976] is eliminated: the index-level No-Crossing Constraint of
`Phonology/Autosegmental/NonCrossing` holds of any link set realised by valid associations
(`isNonCrossing_of_valid`).

## Implementation notes

The substrate's features are mapped onto the dissertation's: `[voice]` stands in for the
laryngeal stiffness and slackness features, `[lateral]` is placed under the supralaryngeal
node, which the Klamath evidence supports without fixing the node below it, and the acoustic
residue `[sonorant]` and `[strident]` together with the features the dissertation lacks are
left unplaced. The major-articulator pointer from the root and the phonetic default degree of
closure of minor articulators are not formalized; the root placement of the degree-of-closure
features that motivates the pointer is.

## References

* [sagey-1986]
* [goldsmith-1976]
* [clements-1985]
-/

namespace Sagey1986

open Phonology Phonology.FeatureGeometry Autosegmental

/-! ### The articulator geometry -/

/-- The class nodes: the root; the laryngeal and supralaryngeal nodes; the soft palate and
place nodes under the latter; the articulators labial, coronal and dorsal under place. -/
inductive Node where
  | root
  | laryngeal
  | supralaryngeal
  | softPalate
  | place
  | labial
  | coronal
  | dorsal
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The node immediately dominating each node; the root alone has none. -/
def parent : Node → Option Node
  | .root => none
  | .laryngeal | .supralaryngeal => some .root
  | .softPalate | .place => some .supralaryngeal
  | .labial | .coronal | .dorsal => some .place

/-- A node and its ancestors; the tree has depth three. -/
def up (n : Node) : Finset Node :=
  ((List.range 4).filterMap λ i => (· >>= parent)^[i] (some n)).toFinset

instance : PartialOrder Node := PartialOrder.lift up (by decide)

instance : DecidableLE Node := λ a b => inferInstanceAs (Decidable (up a ⊆ up b))

instance : OrderBot Node where
  bot := .root
  bot_le := by decide

/-- The class feature of an articulator node, present exactly when the articulator is active
in the segment. -/
def feature? : Node → Option Feature
  | .labial => some .labial
  | .coronal => some .coronal
  | .dorsal => some .dorsal
  | _ => none

/-- The articulator nodes under place, whose distinct combinations are the complex segments. -/
def articulators : Finset Node := {.labial, .coronal, .dorsal}

/-- Distinct articulators are independent: neither dominates the other. -/
theorem not_le_of_mem_articulators {a b : Node} (ha : a ∈ articulators) (hb : b ∈ articulators)
    (hab : a ≠ b) : ¬ a ≤ b := by
  revert a b; decide

end Node

/-- The class node each terminal feature hangs from: the degree-of-closure features from the
root, the glottal features from the laryngeal node, nasality from the soft palate, laterality
from the supralaryngeal node, and the place features from their articulators. -/
def node : Feature → Option Node
  | .continuant | .consonantal => some .root
  | .voice | .spreadGlottis | .constrGlottis => some .laryngeal
  | .nasal => some .softPalate
  | .lateral => some .supralaryngeal
  | .labial | .round => some .labial
  | .coronal | .anterior | .distributed => some .coronal
  | .dorsal | .high | .low | .back => some .dorsal
  | .syllabic | .sonorant | .approximant | .delayedRelease | .strident | .tap | .trill
  | .labiodental | .front | .tense => none

instance : FeatureGeometry Feature Node where
  isChain_Iic := by unfold IsChain Set.Pairwise; decide +revert
  node := node

/-! ### Natural classes -/

/-- The degree-of-closure features belong to the root's class alone: spreading any class node
below the root, as place assimilation does, leaves the degree of closure untouched. -/
theorem degreeOfClosure_mem_naturalClass_iff :
    ∀ f ∈ ({.continuant, .consonantal} : Finset Feature), ∀ a : Node,
      f ∈ naturalClass a ↔ a = ⊥ := by
  decide

/-- Nasality is in the classes of the soft palate node and its ancestors alone: place
assimilation leaves it, and spreading the supralaryngeal node carries it, as in Klamath. -/
theorem nasal_mem_naturalClass_iff (a : Node) : .nasal ∈ naturalClass a ↔ a ≤ .softPalate := by
  revert a; decide

/-- Distinct articulators have disjoint classes: a feature of one, such as rounding, can depend
on no node of another, such as height. -/
theorem disjoint_naturalClass_of_articulators {a b : Node} (ha : a ∈ Node.articulators)
    (hb : b ∈ Node.articulators) (hab : a ≠ b) :
    Disjoint (naturalClass a : Finset Feature) (naturalClass b) :=
  disjoint_naturalClass (Node.not_le_of_mem_articulators ha hb hab)
    (Node.not_le_of_mem_articulators hb ha hab.symm)

/-! ### Complex segments -/

/-- A segment is licensed when every terminal feature it specifies under an articulator node,
whichever its value, activates that articulator. -/
def _root_.Phonology.Segment.Licensed (s : Segment) : Prop :=
  ∀ f, (s f).isSome → ∀ n ∈ node f, ∀ g ∈ n.feature?, s g = some true

instance (s : Segment) : Decidable s.Licensed := by unfold Segment.Licensed; infer_instance

/-- A rounded coronal is complex, since rounding activates the labial articulator; a language
that admits one articulator under the place node therefore rounds only labials. -/
theorem isComplex_of_round_of_coronal {s : Segment} (hs : s.Licensed) (hr : (s .round).isSome)
    (hc : s .coronal = some true) : s.IsComplex := by
  have hl : s .labial = some true := hs .round hr .labial rfl .labial rfl
  exact Finset.one_lt_card.2 ⟨.labial, by simp [Segment.articulators, hl], .coronal,
    by simp [Segment.articulators, hc], by decide⟩

/-- The double occlusions of Halle's survey and the Kinyarwanda triple occlusion: the
labiovelar, labiocoronal, coronovelar and labiocoronovelar stops. -/
def kp : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.labial, true), (.dorsal, true)]

def pt : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.labial, true), (.coronal, true), (.anterior, true)]

def click : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.coronal, true), (.dorsal, true)]

def tkw : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.labial, true), (.round, true), (.coronal, true), (.anterior, true), (.dorsal, true)]

/-- The rounded labial nasal of Aneityum, whose inventory admits one articulator under place. -/
def mw : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.nasal, true), (.labial, true), (.round, true)]

/-- Every multiple occlusion is complex, and the rounded labial is licensed yet simple. -/
theorem occlusions_isComplex :
    kp.IsComplex ∧ pt.IsComplex ∧ click.IsComplex ∧ tkw.IsComplex ∧
      mw.Licensed ∧ ¬ mw.IsComplex := by
  decide

/-! ### Association lines -/

section Association

variable {T : Type*} [LinearOrder T]

/-- An association line between a timing position and a melodic element, each occupying an
interval of time. -/
structure Association (T : Type*) [LinearOrder T] where
  timing : NonemptyInterval T
  melody : NonemptyInterval T

/-- An association line represents overlap in time: some instant of the melody is simultaneous
with some instant of the timing position. -/
def Association.Valid (a : Association T) : Prop := a.timing.overlaps a.melody

instance (a : Association T) : Decidable a.Valid :=
  inferInstanceAs (Decidable (a.timing.overlaps a.melody))

/-- Two associations cross when their timing positions are ordered one way and their melodies
the other. -/
def Association.Crosses (a b : Association T) : Prop :=
  a.timing.precedes b.timing ∧ b.melody.precedes a.melody

/-- Valid associations do not cross: the two precedences and the two overlaps would chain
into an instant preceding itself, so the relations a crossing encodes are contradictory. -/
theorem Association.Valid.not_crosses {a b : Association T} (ha : a.Valid) (hb : b.Valid) :
    ¬ a.Crosses b := by
  rintro ⟨ht, hm⟩
  exact lt_irrefl _ (((hm.trans_le ha.2).trans ht).trans_le hb.1)

/-- A set of association lines satisfies the No-Crossing Constraint when no two of them
cross. -/
def IsNoCrossing (S : Set (Association T)) : Prop := S.Pairwise λ a b => ¬ a.Crosses b

/-- Any set of valid associations satisfies the No-Crossing Constraint. -/
theorem isNoCrossing_of_forall_valid {S : Set (Association T)} (h : ∀ a ∈ S, a.Valid) :
    IsNoCrossing S :=
  λ _ ha _ hb _ => (h _ ha).not_crosses (h _ hb)

/-- A realisation of two tiers in time: intervals for the timing positions and for the melodic
elements, each tier's order realised as precedence. -/
structure TierRealization (T : Type*) [LinearOrder T] where
  timing : ℕ → NonemptyInterval T
  melody : ℕ → NonemptyInterval T
  timing_precedes : ∀ {i j : ℕ}, i < j → (timing i).precedes (timing j)
  melody_precedes : ∀ {k l : ℕ}, k < l → (melody k).precedes (melody l)

/-- The association realising the link of melodic element `k` to timing position `i`. -/
def TierRealization.assoc (R : TierRealization T) (k i : ℕ) : Association T :=
  ⟨R.timing i, R.melody k⟩

/-- Goldsmith's index-level No-Crossing Constraint is derived: a link set whose links are all
realised as valid associations satisfies it. -/
theorem isNonCrossing_of_valid (R : TierRealization T) {links : Finset (ℕ × ℕ)}
    (h : ∀ p ∈ links, (R.assoc p.1 p.2).Valid) : IsNonCrossing links := by
  rw [isNonCrossing_iff]
  intro l₁ hl₁ l₂ hl₂ hlt
  by_contra hgt
  push Not at hgt
  exact (h l₂ hl₂).not_crosses (h l₁ hl₁) ⟨R.timing_precedes hgt, R.melody_precedes hlt⟩

/-- Position `n` of either tier occupies the interval from `2n` to `2n + 1`. -/
def TierRealization.canonical : TierRealization ℤ where
  timing n := ⟨⟨2 * n, 2 * n + 1⟩, by omega⟩
  melody n := ⟨⟨2 * n, 2 * n + 1⟩, by omega⟩
  timing_precedes h := by simp only [NonemptyInterval.precedes]; omega
  melody_precedes h := by simp only [NonemptyInterval.precedes]; omega

/-- Every diagonal link is valid under the canonical realisation, so the hypothesis of
`isNonCrossing_of_valid` is satisfiable. -/
theorem canonical_diagonal_valid (n : ℕ) : (TierRealization.canonical.assoc n n).Valid := by
  simp only [Association.Valid, TierRealization.canonical, TierRealization.assoc,
    NonemptyInterval.overlaps]
  omega

end Association

private def assoc (ts tf ms mf : ℤ) (ht : ts ≤ tf := by omega) (hm : ms ≤ mf := by omega) :
    Association ℤ :=
  ⟨⟨⟨ts, tf⟩, ht⟩, ⟨⟨ms, mf⟩, hm⟩⟩

/-- A contour segment, two melodies sequenced within one timing slot, and a geminate, one
melody spanning two timing slots, are both pairs of valid associations, which simultaneity
would forbid by identifying the two melodies, or the two slots. -/
theorem contour_geminate_valid :
    ((assoc 0 4 0 2).Valid ∧ (assoc 0 4 2 4).Valid) ∧
      ((assoc 0 1 0 3).Valid ∧ (assoc 2 3 0 3).Valid) := by
  decide

end Sagey1986
