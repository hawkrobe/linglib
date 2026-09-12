import Linglib.Semantics.Degree.Quantifier
import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Mereology

/-!
# Pasternak (2019): A Lot of Hatred and a Ton of Desire

This file formalizes the account in [pasternak-2019] of intensity as a monotonic measure
function on mental states. *Ann hates Bill more than Matt hates Jeff* is a verbal comparative
of the same shape as *more snow* and *ran more* ([wellwood-2015]): the matrix and than-clause
predicates are the verb's eventualities with their experiencers and themes (`themed`), and
the comparative is `Degree.maxComparative` under the intensity measure
(`intensityComparative`), carrying the presupposition that the measure is monotonic on the
salient part-whole relation among the verb's states, the monotonicity of
[schwarzschild-2006] that pseudopartitives, *out the wazoo*, adverbial measure phrases, and
nominal and verbal comparatives all impose (`Monotonic`). The comparative entails the matrix
positive but not the than-clause positive, *Jack admires the chairman more than Jill does; in
fact, Jill doesn't admire him at all*, which the zero degree in the than-clause set secures
(`intensityComparative.exists_matrix`, `intensityComparativeZero_of_none`), and under the
presupposition it compares the maximal states, Ann's hating Bill against Matt's hating Jeff
(`intensityComparative_of_greatest`). Mental-state predicates are homogeneous, a state being a
state of Ann hating Bill iff all its substates are, the biconditional form of `Mereology.DIV`
(`div_iff`); the closure under parts supplies the strips of a state whose sums make intensity
monotonic.

## Implementation notes

The zero-degree amendment to the than-clause set and the reduction of a comparative to its
greatest witnesses under a monotone measure live in `Semantics/Degree/Quantifier`
(`maxComparativeZero`, `maxComparative_of_isGreatest`); the part-whole order on eventualities
is the event mereology of `Semantics/Events/Basic`. The two-dimensional state ontology that
grounds the salient part-whole relation, the Mandarin data, and the desire predicates are not
formalized.

## TODO

* Mandarin *duō* / *hěn duō (de)*, which needs Fragment entries.
* The two-dimensional state ontology with its vertical axis and the fineness ordering.
* The desire predicates *want*, *wish*, and *regret* over point-states.

## References

* [pasternak-2019]
* [schwarzschild-2006]
* [wellwood-2015]
-/

namespace Pasternak2019

open Degree
open ArgumentStructure (ThematicFrame)

/-- A mental-state verb: its predicate on eventualities and its intensity measure; thematic
roles are assigned by a `ThematicFrame` at use sites. -/
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

/-- The intensity comparative *α V x more than β V y*: `Degree.maxComparative` with the two
sides differing in experiencer and theme, measured by the intensity measure (56a). -/
def intensityComparative (α β x y : Entity) : Prop :=
  maxComparative (themed v frame α x) (themed v frame β y) v.μint

/-- The states of the verb with theme `x`, whatever their experiencer: the domain of the
monotonicity presupposition. -/
def statesOf (x : Entity) : Set (Event T) := {e | v.predicate e ∧ frame.theme x e}

/-- The monotonicity presupposition (56b), the paper's (4) on the salient part-whole
relation: a proper part of a state of the verb with theme `x` is strictly less intense. -/
def Monotonic [Event.Mereology T] (x : Entity) : Prop := StrictMonoOn v.μint (statesOf v frame x)

variable {v frame} {α β x y : Entity}

/-- The positive entailment: the comparative entails the matrix positive. -/
theorem intensityComparative.exists_matrix (h : intensityComparative v frame α β x y) :
    ∃ e, themed v frame α x e :=
  let ⟨_, _, e, he, _⟩ := h; ⟨e, he⟩

/-- With unique witnesses on both sides the comparative compares the two intensities. -/
theorem intensityComparative_unique {ea eb : Event T} (ha : themed v frame α x ea)
    (ha' : ∀ e, themed v frame α x e → e = ea) (hb : themed v frame β y eb)
    (hb' : ∀ e, themed v frame β y e → e = eb) :
    intensityComparative v frame α β x y ↔ v.μint eb < v.μint ea :=
  maxComparative_unique ha ha' hb hb'

/-- Under the presupposition on both sides, the comparative compares the maximal states: with
`ea` Ann's state of hating Bill and `eb` Matt's of hating Jeff, the sentence holds iff `ea`
is the more intense. -/
theorem intensityComparative_of_greatest [Event.Mereology T] {ea eb : Event T}
    (hx : Monotonic v frame x) (hy : Monotonic v frame y)
    (ha : IsGreatest {e | themed v frame α x e} ea)
    (hb : IsGreatest {e | themed v frame β y e} eb) :
    intensityComparative v frame α β x y ↔ v.μint eb < v.μint ea :=
  maxComparative_of_isGreatest ha (hx.monotoneOn.mono λ _ he => ⟨he.2.1, he.2.2⟩) hb
    (hy.monotoneOn.mono λ _ he => ⟨he.2.1, he.2.2⟩)

section Zero

variable [Zero D] (v frame)

/-- The intensity comparative with the zero degree added to the than-clause set (62). -/
def intensityComparativeZero (α β x y : Entity) : Prop :=
  maxComparativeZero (themed v frame α x) (themed v frame β y) v.μint

variable {v frame}

/-- The than-clause positive is not entailed (63): with the zero degree the comparative is
consistent with there being no `β`-eventuality at all. -/
theorem intensityComparativeZero_of_none {e : Event T} (he : themed v frame α x e)
    (hpos : 0 < v.μint e) (hβ : ∀ e', themed v frame β y e' → v.μint e' ≤ 0) :
    intensityComparativeZero v frame α β x y :=
  maxComparativeZero_of_forall_le_zero he hpos hβ

end Zero

/-- Mental state homogeneity (55): a predicate closed under parts holds of `e` iff it holds of
every part of `e`. -/
theorem div_iff {α : Type*} [Preorder α] {P : α → Prop} (h : Mereology.DIV P) (e : α) :
    P e ↔ ∀ e' ≤ e, P e' :=
  ⟨λ he _ hle => h hle he, λ hall => hall e le_rfl⟩

end Pasternak2019
