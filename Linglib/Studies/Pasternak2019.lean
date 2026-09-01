import Linglib.Semantics.Degree.Quantifier
import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Mereology

/-!
# Pasternak (2019): intensity in the mereology of mental states

[pasternak-2019] treats intensity as a monotonic measure function on mental states: a more
intense state is bigger along a part-whole dimension, so *Ann hates Bill more than Matt hates
Jeff* is a verbal comparative of the same shape as *more snow* and *ran more*
([wellwood-2015]), its measure obeying the monotonicity constraint
([schwarzschild-2006]) that pseudopartitives, *out the wazoo*, adverbial measure phrases and
nominal and verbal comparatives all impose (`Degree.admissibleMeasure`). A mental-state verb
carries its predicate and its intensity measure (`MentalStateVerb`), thematic roles come
from a `ThematicFrame`, the degree-relative entry *α V x at degree d* is `holdsAtDegree`,
and the intensity comparative is `Degree.maxComparative` with matrix and than-clause
predicates that may differ in experiencer and theme (`intensityComparative`). The
comparative entails the matrix positive (`intensityComparative.exists_matrix`) but not the
than-clause positive — *Jack admires the chairman more than Jill does; in fact, Jill doesn't
admire him at all* — which Pasternak secures by adding a zero degree to the than-clause set
(`intensityComparativeZero_of_none`). Mental-state predicates are homogeneous, closed under
parts; his biconditional form of homogeneity is `Mereology.DIV` (`div_iff`). Under unique
witnesses on both sides the comparative reduces to comparing the two intensities
(`intensityComparative_unique`), a simplification Pasternak himself does not adopt.

## Todo

* Mandarin *duō* / *hěn duō (de)*, which needs Fragment entries.
* The two-dimensional state ontology with its vertical axis and the fineness ordering.
* The desire predicates *want*, *wish* and *regret* over point-states.

## References

* [pasternak-2019]
* [schwarzschild-2006], [wellwood-2015]
-/

namespace Pasternak2019

open Degree
open ArgumentStructure (ThematicFrame)

/-- A mental-state verb: its predicate on eventualities and its intensity measure `μ_int`;
thematic roles are assigned by a `ThematicFrame` at use sites. -/
structure MentalStateVerb (T D : Type*) [LinearOrder T] where
  /-- The verb's predicate on eventualities. -/
  predicate : Event T → Prop
  /-- The intensity measure. -/
  μint : Event T → D

variable {Entity T D : Type*} [LinearOrder T] [Preorder D] (v : MentalStateVerb T D)
  (frame : ThematicFrame Entity T)

/-- Eventualities of the verb with experiencer `α` and theme `x`. -/
def themed (α x : Entity) (e : Event T) : Prop :=
  frame.experiencer α e ∧ v.predicate e ∧ frame.theme x e

/-- *α V x at degree d*: a themed eventuality of the verb with intensity at least `d`. -/
def MentalStateVerb.holdsAtDegree (α x : Entity) (d : D) (e : Event T) : Prop :=
  themed v frame α x e ∧ d ≤ v.μint e

/-- The than-clause degrees of *β V y* are the degrees at which *β V y* holds. -/
theorem thanDegrees_themed (β y : Entity) :
    thanDegrees (themed v frame β y) v.μint = {d | ∃ e, v.holdsAtDegree frame β y d e} :=
  rfl

/-- The intensity comparative *α V x more than β V y*: `Degree.maxComparative` with the two
sides differing in experiencer and theme, measured by `μ_int`. -/
def intensityComparative (α β x y : Entity) : Prop :=
  maxComparative (themed v frame α x) (themed v frame β y) v.μint

variable {v frame} {α β x y : Entity}

/-- The comparative entails the matrix positive. -/
theorem intensityComparative.exists_matrix (h : intensityComparative v frame α β x y) :
    ∃ e, themed v frame α x e :=
  let ⟨_, _, e, he, _⟩ := h; ⟨e, he⟩

/-- With unique witnesses on both sides the comparative compares the two intensities. -/
theorem intensityComparative_unique {ea eb : Event T} (ha : themed v frame α x ea)
    (ha' : ∀ e, themed v frame α x e → e = ea) (hb : themed v frame β y eb)
    (hb' : ∀ e, themed v frame β y e → e = eb) :
    intensityComparative v frame α β x y ↔ v.μint eb < v.μint ea :=
  maxComparative_unique ha ha' hb hb'

section Zero

variable [Zero D] (v frame)

/-- The than-clause degree set with a zero degree added, so that its maximum exists when
there is no `β`-eventuality. -/
def thanDegreesZero (β y : Entity) : Set D :=
  insert 0 (thanDegrees (themed v frame β y) v.μint)

/-- The intensity comparative over `thanDegreesZero`. -/
def intensityComparativeZero (α β x y : Entity) : Prop :=
  ∃ e, themed v frame α x e ∧ ∃ δ, IsGreatest (thanDegreesZero v frame β y) δ ∧ δ < v.μint e

variable {v frame}

/-- With the zero degree, the comparative is consistent with there being no `β`-eventuality
at all: *Jack admires the chairman more than Jill does; in fact, Jill doesn't admire him*. -/
theorem intensityComparativeZero_of_none {e : Event T} (he : themed v frame α x e)
    (hpos : 0 < v.μint e) (hβ : ∀ e', themed v frame β y e' → v.μint e' ≤ 0) :
    intensityComparativeZero v frame α β x y :=
  ⟨e, he, 0, ⟨Set.mem_insert _ _, fun _ hd => (Set.mem_insert_iff.1 hd).elim le_of_eq
    fun ⟨e', he', hle⟩ => hle.trans (hβ e' he')⟩, hpos⟩

end Zero

/-- Pasternak's homogeneity of mental-state predicates, closed under parts, in his
biconditional form: a `Mereology.DIV` predicate holds of `e` iff it holds of every part. -/
theorem div_iff {α : Type*} [Preorder α] {P : α → Prop} (h : Mereology.DIV P) (e : α) :
    P e ↔ ∀ e' ≤ e, P e' :=
  ⟨fun he _ hle => h hle he, fun hall => hall e le_rfl⟩

end Pasternak2019
