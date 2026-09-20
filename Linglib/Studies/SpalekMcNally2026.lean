import Linglib.Fragments.English.Verbs
import Linglib.Fragments.Romance.Spanish.Verbs

/-!
# Spalek & McNally (2026): The Anatomy of a Verb

This file formalizes the contrastive analysis of English *tear* and Spanish *rasgar* of
[spalek-mcnally-2026]. The two verbs are counterparts in comparative lexical databases and
share an event structure: both are simple result verbs of the break class ([levin-1993])
describing a minimal, binary-scale change, the partly uncontrolled loss of integrity of a
whole, with a causative alternation and no agentive intransitive use. They differ in root
content, the fine within-class half of a root's meaning beside its templatic kinds
([beavers-koontz-garboden-2020]): *rasgar* requires a flimsy or insubstantial patient and
implies a linear, gash-like separation without much force, where *tear* takes patients of
any robustness, implies separation in contrary directions, often with force, and is
compatible with careful action. Figurative extensions follow the root content, the case
complementary to the event-structural contrasts of [mcnally-spalek-2022]: *rasgar* disturbs
fragile states, silence and darkness, and describes linear movement through an
insubstantial medium; *tear* rends with force and describes fast motion along a path. In the
bidirectional parallel corpus the verbs are asymmetric translation equivalents: *rasgar* is
one of the rarer renderings of *tear*, whose most frequent counterpart is *arrancar*, while
*tear* is the usual rendering of *rasgar*.

The root contents are the fragment entries' `Verb.rootContent`, regions of the substrate's
`Root.Content` space. A `Situation` is a point of that space, a described event's value on
every dimension, and `Admits` says a root's regions contain it; `overlaps_iff_exists_admits`
identifies the substrate's `Overlaps` with the existence of a situation both roots admit,
the zone in which the verbs are intertranslatable. The paper's contrasts are situations one
root admits and the other rejects: the chunk of bread (14), the engraved cement (16b), the
carefully torn foil (17), the rooster and the silence (18), and the ball tearing through the
rough (23); the soft contact lenses (16a) are admitted by both.

## Implementation notes

The translation counts of the paper's Tables 1 and 2 are reported in prose. Each contrast
situation is fixed on the dimension the paper names for it and agrees with the contact
lenses elsewhere, inside both roots' regions, so that each verdict turns on the named
dimension alone: robustness for the bread, result geometry for the cement, agent control
for the foil, robustness and force for the silence, force for the rough.

## References

* [spalek-mcnally-2026]
* [mcnally-spalek-2022]
* [beavers-koontz-garboden-2020]
* [levin-1993]
-/

namespace SpalekMcNally2026

open Semantics.Root Semantics.Root.Content English Spanish.Verbs

/-! ### Situations and admission -/

/-- A described situation: a value on every dimension of root content. -/
structure Situation where
  force : ForceLevel
  direction : ForceDirection
  instrument : InstrumentType
  agentControl : AgentControl
  resultGeometry : ResultGeometry
  patientRobustness : Robustness
  patientDimensionality : ObjectDimensionality
  deriving DecidableEq, Repr

/-- A root's content admits a situation when its region on every dimension contains the
situation's value. -/
def Admits (c : Content) (s : Situation) : Prop :=
  s.force ∈ c.force ∧ s.direction ∈ c.direction ∧ s.instrument ∈ c.instrument ∧
    s.agentControl ∈ c.agentControl ∧ s.resultGeometry ∈ c.resultGeometry ∧
    s.patientRobustness ∈ c.patientRobustness ∧
    s.patientDimensionality ∈ c.patientDimensionality

instance (c : Content) (s : Situation) : Decidable (Admits c s) := by
  unfold Admits; infer_instance

/-- Two roots overlap exactly when some situation is admitted by both: the overlap of the
regions is the zone of intertranslatability. -/
theorem overlaps_iff_exists_admits (p q : Content) :
    p.Overlaps q ↔ ∃ s, Admits p s ∧ Admits q s := by
  simp only [Content.Overlaps, Admits, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, ⟨c, hc, hc'⟩, ⟨d, hd, hd'⟩, ⟨e, he, he'⟩, ⟨f, hf, hf'⟩,
      ⟨g, hg, hg'⟩⟩
    exact ⟨⟨a, b, c, d, e, f, g⟩, ⟨ha, hb, hc, hd, he, hf, hg⟩, ⟨ha', hb', hc', hd', he', hf', hg'⟩⟩
  · rintro ⟨s, ⟨ha, hb, hc, hd, he, hf, hg⟩, ⟨ha', hb', hc', hd', he', hf', hg'⟩⟩
    exact ⟨⟨_, ha, ha'⟩, ⟨_, hb, hb'⟩, ⟨_, hc, hc'⟩, ⟨_, hd, hd'⟩, ⟨_, he, he'⟩, ⟨_, hf, hf'⟩,
      ⟨_, hg, hg'⟩⟩

/-! ### The paper's situations -/

/-- Tearing soft contact lenses with one's nails (16a): a flimsy patient separated by a
moderate, linear force. -/
def lenses : Situation :=
  ⟨.moderate, .unidirectional, .hands, .neutral, .separation, .flimsy, .twoD⟩

/-- Tearing a chunk off a slice of bread (14): a robust patient. -/
def bread : Situation := { lenses with patientRobustness := .robust }

/-- An awl engraving cement (16b): a gash on a surface, with no separation in contrary
directions. -/
def cement : Situation := { lenses with resultGeometry := .surfaceBreach }

/-- Children carefully tearing tin foil (17): controlled action. -/
def foil : Situation := { lenses with agentControl := .compatible }

/-- A rooster tearing the silence of the dawn (18): a fragile state, disturbed by the least
force. -/
def silence : Situation := { lenses with force := .low, patientRobustness := .insubstantial }

/-- A ball tearing through the rough (23): movement with considerable energy. -/
def rough : Situation := { lenses with force := .high }

/-- The contact lenses lie in both roots' regions. -/
theorem lenses_admitted : Admits tear_.rootContent lenses ∧ Admits rasgar.rootContent lenses := by
  decide

/-- The two roots overlap: the contact lenses witness the zone where the verbs translate each
other. -/
theorem roots_overlap : tear_.rootContent.Overlaps rasgar.rootContent :=
  (overlaps_iff_exists_admits _ _).2 ⟨lenses, lenses_admitted⟩

/-- The bread: *tear* takes a robust patient, *rasgar* does not. -/
theorem bread_contrast : Admits tear_.rootContent bread ∧ ¬ Admits rasgar.rootContent bread := by
  decide

/-- The cement: a gash without contrary separation is a *rasgar* result, not a *tear*. -/
theorem cement_contrast :
    ¬ Admits tear_.rootContent cement ∧ Admits rasgar.rootContent cement := by
  decide

/-- The foil: careful action is compatible with *tear* and not with *rasgar*. -/
theorem foil_contrast : Admits tear_.rootContent foil ∧ ¬ Admits rasgar.rootContent foil := by
  decide

/-- The silence: a fragile state disturbed without force is torn by *rasgar*, while *tear*
wants force and contrary motion. -/
theorem silence_contrast :
    ¬ Admits tear_.rootContent silence ∧ Admits rasgar.rootContent silence := by
  decide

/-- The rough: energetic motion is a *tear* extension and not a *rasgar* one, whose flimsy
patients call for no such force. -/
theorem rough_contrast : Admits tear_.rootContent rough ∧ ¬ Admits rasgar.rootContent rough := by
  decide

end SpalekMcNally2026
