import Linglib.Logic.Modal.Defs

/-!
# Clauses as predicates of anchors

Embedded clauses as predicates of *anchors* — individuals from which a
propositional domain is projected ([hacquard-2006]; [kratzer-2006]).
On the standard analysis a *that*-clause denotes a proposition,
⟦that p⟧ = p. On the projection analysis the complementizer instead
identifies p as the projection of an anchor individual, so a clause
denotes a predicate of anchors. The `Anchor` class carries the mode of
projection: CONT for content individuals ([kratzer-2006];
[moulton-2015]), SIT for situation individuals ([bondarenko-2022];
[moltmann-2021]). The sorts stay distinct types, so sort-sensitive
selection — content verbs rejecting situation clauses and vice versa,
Greek *oti* vs *pu* ([angelopoulos-2026]) — is type selection; the
compositional machinery below is shared.

Because anchor nouns (*belief*, *claim*; *situation*, *case*) denote
predicates of anchors of the same semantic type as clauses, noun and
clause combine by predicate modification ([heim-kratzer-1998]) rather
than function application: `nounComp`. Clause-selecting verbs take the
anchor as an argument, which existential closure binds at the edge of
vP (`existsClosure`). With [moulton-2015]'s doxastic verb, which
requires every accessible index to be a projection index
(`ofAccessibility`), the closed report is the classical universal modal
(`existsClosure_ofAccessibility`): the semantics of [hintikka-1962] is
a special case of the anchor architecture whenever the projection is
surjective.
-/

namespace Semantics.Attitudes

/-- An anchor sort: individuals from which a propositional domain is
    projected. `proj x` is the projection of the anchor `x` — CONT for
    content individuals, SIT for situation individuals. -/
class Anchor (α : Type*) (I : outParam Type*) where
  /-- The mode of projection: the domain an anchor projects. -/
  proj : α → I → Prop

namespace Anchor

open scoped ModalLogic

variable {α I E : Type*} [Anchor α I]

/-- The complementizer identifies a clause with the anchor's projection:
    `comp q x` iff `proj x = q`. -/
def comp (q : I → Prop) (x : α) : Prop :=
  proj x = q

/-- Predicate modification of an anchor noun with a clause:
    `nounComp noun q x i` iff `noun x i ∧ proj x = q`. -/
def nounComp (noun : α → I → Prop) (q : I → Prop) : α → I → Prop :=
  fun x i => noun x i ∧ comp q x

/-- Existential closure over the anchor argument of a clause-selecting verb
    at the edge of vP: `existsClosure V a q i` iff `∃ x, V a x i ∧ proj x = q`. -/
def existsClosure (verb : E → α → I → Prop) (agent : E) (q : I → Prop)
    (i : I) : Prop :=
  ∃ x : α, verb agent x i ∧ comp q x

/-- The doxastic clause-selecting verb of [moulton-2015]: the agent is
    related to `x` at `i` iff every index accessible from `i` is a projection
    index of `x` (Dox ⊆ proj). -/
def ofAccessibility (R : E → I → I → Prop) : E → α → I → Prop :=
  fun agent x i => ∀ i', R agent i i' → proj x i'

/-- For a surjective projection, an existentially closed report with the
    accessibility-based verb is the classical universal modal of
    [hintikka-1962]. -/
theorem existsClosure_ofAccessibility (R : E → I → I → Prop) (a : E)
    (q : I → Prop) (i : I) (hp : Function.Surjective (proj : α → I → Prop)) :
    existsClosure (ofAccessibility (α := α) R) a q i ↔ □[R a] q i :=
  ⟨fun ⟨_, hsub, hc⟩ v hv => hc ▸ hsub v hv,
   fun h => (hp q).elim fun x hx => ⟨x, fun i' hi' => hx.symm ▸ h i' hi', hx⟩⟩

end Anchor

end Semantics.Attitudes
