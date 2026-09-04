import Linglib.Fragments.English.Phonology
import Linglib.Core.Data.Fintype.Sets
import Mathlib.Data.Finset.Piecewise

/-!
# Clements (1985): the geometry of phonological features

[clements-1985] replaces the SPE feature matrix by a tree of class nodes: a root node
linked to the CV tier, a laryngeal and a supralaryngeal node below it, a manner and a
place node below supralaryngeal, and each terminal feature hanging from one class node
(his (3) and Appendix; §4 gives the content of each node). Assimilation is the spreading
of one node ((5), after [mohanan-1983]), so the theory admits three types, total (the
root), partial (a class node) and single-feature, and a rule that must reach two
features with no common class node below supralaryngeal is total supralaryngeal
assimilation, which is why the SPE rule (14) with `[αnasal]` in place of `[αanterior]`
is unattested. The evidence is English coronal place assimilation ((10)–(13)), Icelandic
preaspiration ((6)–(7), after [thrainsson-1978]), Klamath lateral rules ((8)–(9), after
[barker-1964]), Sierra Popoluca nasalisation and release ((15)–(20), after [elson-1947]
and [steriade-1982]'s Shared Features Convention) and the Kikuyu and palatalisation cases
of §5, and §4 splits the place features into a primary set P, present in consonants and
vowels, and a secondary set S, normally absent from plain consonants. Only the root,
laryngeal, supralaryngeal and place nodes survive into the geometry of
`Phonology/Segmental/Geometry.lean`; the manner node, which the paper itself flags as
possibly superfluous, does not.

## Main definitions

* `Node`, `Node.parent`, `Node.Dominates`, `Node.features` — the five class nodes of (3),
  the tree, dominance, and the natural class a node dominates.
* `classNode?` — the class node each terminal feature hangs from (§4); features the paper
  does not place have none.
* `PlaceSet`, `placeSet?`, `PlaceSet.features` — the primary/secondary split of the place
  features (§4).
* `Spreading`, `Spreading.features`, `Spreading.apply` — what one rule may spread, the
  root, a class node or one feature ((5)), and the assimilation it effects.
* `CoronalAssimilation.Applies`, `coronalAssimilation` — the English rule (12).

## Main results

* `features_subset_of_dominates`, `disjoint_features` — natural classes nest along
  dominance and are disjoint across incomparable nodes, so spreading a node leaves its
  sisters' features untouched (`Spreading.apply_eqOn_of_not_dominates`).
* `supralaryngeal_subset_of_nasal_of_distributed`,
  `apply_eqOn_supralaryngeal_of_nasal_of_distributed` — every spreading that reaches
  both `[nasal]` and `[distributed]` is total supralaryngeal assimilation, the argument
  against the `[αnasal]` variant of (14); `eq_root_of_continuant_of_voice` is the Kikuyu
  case of §5.1 and `supralaryngeal_subset_of_anterior_of_continuant` the palatalisation
  case of §5.2.
* `coronalAssimilation_n_θ`, `coronalAssimilation_t_θ`, `coronalAssimilation_d_θ`,
  `coronalAssimilation_n_esh` — *tenth*, *eighth*, *hundredth*, *insure* from table (11):
  the target takes the trigger's place features and nothing else.
* `preaspiration` — spreading the vowel's supralaryngeal node onto the delinked first half
  of an aspirated geminate keeps the stop's laryngeal features ((7)).
* `mem_place_features_iff`, `primary_separates_stops` — the place features are P ∪ S, and
  P alone separates the English stop places (table (22)).

## Implementation notes

`classNode?` is defined on the features the paper names and is `none` elsewhere, so
`Node.root.features` is the paper's inventory rather than all of [hayes-2009]'s;
`[labial]` counts as primary by table (22). Spreading is `Finset.piecewise` on a node's
natural class, so the trigger's unspecified features under the node replace the target's,
as the delinking convention of (13) requires; single-feature spreading is
`Features.Bundle.assimilate` (`Spreading.apply_feature`). The English segments are the
Fragment's; its /r/ is [+anterior] where table (10) has [−anterior, −distributed], so the
retroflex row of (11) (*tree*, *dream*, *enrol*) is not derived. The SPE rule (14) needs
α-variables that `Subregular.LocalRewrite` does not provide, so the comparison with (12)
is stated on the geometric side only.

## TODO

* The Sierra Popoluca release argument ((17)–(20)): the Shared Features Convention merges
  the two `[−continuant]` nodes of a homorganic cluster into one doubly linked node, so
  the insertion rule (18), which needs two such nodes, is blocked. This needs
  feature-level linking (`Autosegmental/AR.lean`), not the segment-wise spreading here.
* §4's consonant–vowel asymmetries follow from plain consonants lacking S features and
  vowels always carrying them; the Fragment's vowels do not specify `[back]` and
  `[round]`, so no instance is stated.

## References

* [clements-1985]
* [mohanan-1983] — the root node and the three assimilation types.
* [thrainsson-1978] — Icelandic preaspiration.
* [barker-1964] — Klamath.
* [elson-1947] — Sierra Popoluca.
* [steriade-1982] — the Shared Features Convention and Kolami epenthesis.
* [chomsky-halle-1968] — the rule format of (14).
* [hayes-2009] — the Fragment's feature inventory.
-/

namespace Clements1985

open Phonology English.Phonology

attribute [local instance] Set.decidableEqOnOfFintype

/-! ### Class nodes -/

/-- The class nodes of (3): the root, linked to the CV tier; laryngeal and supralaryngeal
below it; manner and place below supralaryngeal. -/
inductive Node where
  | root | laryngeal | supralaryngeal | manner | place
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The node immediately dominating each node; the root alone has none. -/
def parent : Node → Option Node
  | .root => none
  | .laryngeal | .supralaryngeal => some .root
  | .manner | .place => some .supralaryngeal

/-- `a` dominates `b`: `a` lies on the path from `b` to the root, `b` included (Appendix);
the tree has depth two, so the chain is unrolled. -/
def Dominates (a b : Node) : Prop :=
  a = b ∨ b.parent = some a ∨ b.parent.bind parent = some a

instance : DecidableRel Dominates := λ _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

end Node

/-! ### Terminal features (§4) -/

/-- The class node a terminal feature hangs from: `[spread]`, `[constricted]` and
`[voiced]` under laryngeal; `[consonantal]`, `[sonorant]`, `[continuant]`, `[lateral]`,
`[strident]` and, tentatively, `[nasal]` under manner; the place features under place.
Features the paper does not place have none. -/
def classNode? : Feature → Option Node
  | .voice | .spreadGlottis | .constrGlottis => some .laryngeal
  | .consonantal | .sonorant | .continuant | .lateral | .strident | .nasal => some .manner
  | .labial | .coronal | .anterior | .distributed | .high | .back | .round => some .place
  | _ => none

/-- The two sets of place features: P, distinguishing place in consonants, and S,
distinguishing place in vowels (§4). -/
inductive PlaceSet where
  | primary | secondary
  deriving DecidableEq, Repr

/-- `[coronal]`, `[anterior]`, `[distributed]` and, by table (22), `[labial]` are primary;
`[high]`, `[back]` and `[round]` are secondary. -/
def placeSet? : Feature → Option PlaceSet
  | .labial | .coronal | .anterior | .distributed => some .primary
  | .high | .back | .round => some .secondary
  | _ => none

/-- The natural class of a node: the terminal features it dominates ("each feature
characterises every node that dominates it", Appendix). -/
def Node.features (a : Node) : Finset Feature :=
  Finset.univ.filter λ f => ∃ b, classNode? f = some b ∧ a.Dominates b

/-- The features of a place set. -/
def PlaceSet.features (π : PlaceSet) : Finset Feature :=
  Finset.univ.filter (placeSet? · = some π)

variable {a b : Node} (f : Feature)

theorem mem_features_iff : f ∈ a.features ↔ ∃ b, classNode? f = some b ∧ a.Dominates b := by
  simp [Node.features]

/-- The root is characterised by every feature of the representation (Appendix). -/
theorem mem_root_features_iff : f ∈ Node.root.features ↔ (classNode? f).isSome := by
  cases f <;> decide

/-- The place features are exactly P ∪ S. -/
theorem mem_place_features_iff : f ∈ Node.place.features ↔ (placeSet? f).isSome := by
  cases f <;> decide

/-! ### Nesting and disjointness -/

/-- Natural classes nest along dominance. -/
theorem features_subset_of_dominates (h : a.Dominates b) : b.features ⊆ a.features := by
  revert a b; decide

/-- Nodes neither of which dominates the other have disjoint natural classes: the sisters
laryngeal and supralaryngeal, or manner and place, share no feature. -/
theorem disjoint_features (h₁ : ¬ a.Dominates b) (h₂ : ¬ b.Dominates a) :
    Disjoint a.features b.features := by
  revert a b; decide

/-! ### Assimilation as spreading ((5)) -/

/-- What an assimilation rule spreads: the root node (total assimilation), a class node
(partial assimilation) or a single feature (single-feature assimilation), after
[mohanan-1983]; a rule spreading more than one node costs more. -/
inductive Spreading where
  | node (a : Node)
  | feature (f : Feature)
  deriving DecidableEq, Repr, Fintype

namespace Spreading

variable (σ : Spreading) (src tgt : Segment)

/-- The features a spreading carries. -/
def features : Spreading → Finset Feature
  | .node a => a.features
  | .feature f => {f}

/-- Spread from `src` onto `tgt`: the carried features take `src`'s values, specified or
not, the target's own being delinked ((13)); every other feature keeps `tgt`'s value. -/
def apply : Segment := σ.features.piecewise src tgt

theorem apply_eqOn : Set.EqOn (σ.apply src tgt) src ↑σ.features :=
  λ _ hf => Finset.piecewise_eq_of_mem _ _ _ hf

/-- Single-feature spreading is the bundle primitive `Features.Bundle.assimilate`. -/
theorem apply_feature : (feature f).apply src tgt = Features.Bundle.assimilate f src tgt :=
  Finset.piecewise_singleton _ _ _

/-- Spreading a node carries every feature of the nodes it dominates. -/
theorem apply_eqOn_of_dominates (h : a.Dominates b) :
    Set.EqOn ((node a).apply src tgt) src ↑b.features :=
  (apply_eqOn _ src tgt).mono (Finset.coe_subset.2 (features_subset_of_dominates h))

/-- Spreading a node leaves the features of every node it neither dominates nor is
dominated by untouched. -/
theorem apply_eqOn_of_not_dominates (h₁ : ¬ a.Dominates b) (h₂ : ¬ b.Dominates a) :
    Set.EqOn ((node a).apply src tgt) tgt ↑b.features :=
  λ _ hf =>
    Finset.piecewise_eq_of_notMem _ _ _ (Finset.disjoint_right.1 (disjoint_features h₁ h₂) hf)

end Spreading

/-! ### Single-node spreading against the SPE rule (14) -/

variable (σ : Spreading) (src tgt : Segment)

/-- Place spreading carries `[anterior]` and `[distributed]` together and leaves `[nasal]`
alone, so (12) is a single-node rule while its `[αnasal]` variant of (14) is not. -/
theorem anterior_distributed_subset_place :
    {Feature.anterior, Feature.distributed} ⊆ Node.place.features := by
  decide

theorem nasal_notMem_place : Feature.nasal ∉ Node.place.features := by decide

/-- No spreading reaches both `[nasal]`, a manner feature, and `[distributed]`, a place
feature, without carrying the whole supralaryngeal class (§3). -/
theorem supralaryngeal_subset_of_nasal_of_distributed (h₁ : Feature.nasal ∈ σ.features)
    (h₂ : Feature.distributed ∈ σ.features) : Node.supralaryngeal.features ⊆ σ.features := by
  revert σ; decide

/-- A rule assimilating `[nasal]` and `[distributed]` at once is total supralaryngeal
assimilation. -/
theorem apply_eqOn_supralaryngeal_of_nasal_of_distributed (h₁ : Feature.nasal ∈ σ.features)
    (h₂ : Feature.distributed ∈ σ.features) :
    Set.EqOn (σ.apply src tgt) src ↑Node.supralaryngeal.features :=
  (σ.apply_eqOn src tgt).mono
    (Finset.coe_subset.2 (supralaryngeal_subset_of_nasal_of_distributed σ h₁ h₂))

/-- Kikuyu assigns `[−continuant, +voiced]` to postnasal obstruents (§5.1, (24)): only the
root reaches a manner and a laryngeal feature at once, so the theory makes `[voiced]`
redundant there, filled in by a later rule. -/
theorem eq_root_of_continuant_of_voice (h₁ : Feature.continuant ∈ σ.features)
    (h₂ : Feature.voice ∈ σ.features) : σ = .node .root := by
  revert σ; decide

/-- English palatalisation assigns a glide's place and `[+continuant]` at once (§5.2, (25)):
one spreading doing both is supralaryngeal, so the paper decomposes it into spirantisation
and place assimilation. -/
theorem supralaryngeal_subset_of_anterior_of_continuant (h₁ : Feature.anterior ∈ σ.features)
    (h₂ : Feature.continuant ∈ σ.features) : Node.supralaryngeal.features ⊆ σ.features := by
  revert σ; decide

/-! ### English coronal place assimilation ((10)–(13)) -/

namespace CoronalAssimilation

/-- The structural description of (12): a `[−continuant, +coronal, +anterior]` target, one
of /t d n/, before a `[+consonantal, +coronal]` trigger. -/
def Applies (tgt trg : Segment) : Prop :=
  tgt.HasValue .continuant false ∧ tgt.HasValue .coronal true ∧ tgt.HasValue .anterior true ∧
    trg.HasValue .consonantal true ∧ trg.HasValue .coronal true

instance : DecidableRel Applies := λ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

end CoronalAssimilation

/-- Rule (12): where its structural description holds, spread the trigger's place node onto
the target. -/
def coronalAssimilation (tgt trg : Segment) : Segment :=
  if CoronalAssimilation.Applies tgt trg then (Spreading.node .place).apply trg tgt else tgt

/-- *tenth*: /n/ before /θ/ takes `[+distributed]` and nothing else — a dental nasal. -/
theorem coronalAssimilation_n_θ : coronalAssimilation n θ = n.setFeature .distributed true := by
  decide

/-- *eighth*: /t/ before /θ/. -/
theorem coronalAssimilation_t_θ : coronalAssimilation t θ = t.setFeature .distributed true := by
  decide

/-- *hundredth*: /d/ before /θ/. -/
theorem coronalAssimilation_d_θ : coronalAssimilation d θ = d.setFeature .distributed true := by
  decide

/-- *insure*: /n/ before /ʃ/ is postalveolar, `[−anterior, +distributed]`, and still a
non-strident nasal, `[strident]` and `[nasal]` being manner features. -/
theorem coronalAssimilation_n_esh :
    coronalAssimilation n esh = (n.setFeature .anterior false).setFeature .distributed true := by
  decide

/-- A labial trigger is no site: *impossible* falls to the separate nasal assimilation
rule. -/
example : ¬ CoronalAssimilation.Applies n p := by decide

/-- A fricative target is no site: the rule affects the stops /t d n/ only. -/
example : ¬ CoronalAssimilation.Applies s θ := by decide

/-! ### Supralaryngeal spreading: Icelandic preaspiration ((6)–(7)) -/

/-- (7): the first half of a geminate aspirated stop loses its supralaryngeal node and
takes the preceding vowel's, so the output shares every supralaryngeal feature with the
vowel and keeps only the stop's laryngeal features `[+spread, −voiced]` — an [h]. Klamath
(9a) and Sierra Popoluca (16) spread the same node from a lateral and from a nasal. -/
theorem preaspiration (v c : Segment) :
    Set.EqOn ((Spreading.node .supralaryngeal).apply v c) v ↑Node.supralaryngeal.features ∧
      Set.EqOn ((Spreading.node .supralaryngeal).apply v c) c ↑Node.laryngeal.features :=
  ⟨Spreading.apply_eqOn _ v c, Spreading.apply_eqOn_of_not_dominates v c (by decide) (by decide)⟩

/-! ### Primary and secondary place features (§4) -/

/-- Table (22): the primary features alone separate the English stop places, so `[high]`
and `[back]` are not needed for consonant place. -/
theorem primary_separates_stops :
    ∀ x ∈ [p, t, k], ∀ y ∈ [p, t, k], Set.EqOn x y ↑PlaceSet.primary.features → x = y := by
  decide

end Clements1985
