import Linglib.Logic.Modal.Defs

/-!
# Clauses as predicates of anchors

Embedded clauses as predicates of *anchors* — individuals from which a
propositional domain is projected ([hacquard-2006]; [kratzer-2006]).
On the standard analysis a *that*-clause denotes a proposition,
⟦that p⟧ = p. On the projection analysis the complementizer instead
identifies p as the projection of an anchor individual, so a clause
denotes a predicate of anchors. The `Anchor` class carries the mode of
projection: CONT for content individuals ([kratzer-2006]; [kratzer-2013];
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

/-!
# Content individuals

A content individual is a first-class mental state carrying propositional
content — [kratzer-2006]'s denotation for content DPs like *John's belief
that p*, *the claim*, *every rumor*, *her wish*. Content individuals are
the shared ontological sort underlying beliefs, desires, and percepts
([liefke-2024]); what distinguishes a belief from a desire or a percept
is not the sort but the attitude relation that embeds it. In Bayesian
theory-of-mind models ([baker-jara-ettinger-saxe-tenenbaum-2017],
`Pragmatics/BToM.lean`) they correspond to the type parameters over which
the observer's posterior is defined.

Content individuals are the content-mode instance of the `Anchor` class:
the projection is CONT, so `Anchor.comp` is the *that*-complementizer of
[kratzer-2006] and [moulton-2015] and `Anchor.existsClosure` composes
attitude reports. `cont_surjective` — every proposition is the content
of some individual — makes `Anchor.existsClosure_ofAccessibility`
applicable, recovering the classical doxastic semantics of
[hintikka-1962].

Two ways to relate a content individual x_c to a proposition p:
*identity*, CONT(x_c) = p, the notion of [kratzer-2006] and
[moulton-2015] (p **is** the content, `Anchor.comp`); and *entailment*,
CONT(x_c) ⊆ p, the notion of [hintikka-1962] (p **follows from** the
content, `entails`). Identity is strictly stronger:
`eq_implies_entails` and the counterexample `entails_not_implies_eq`.
-/

/-- A content individual: a first-class mental state carrying propositional
    content. The `cont` field is [kratzer-2006]'s CONT function.

    Caveat: because `cont` is the only field, this formalization identifies
    individuals with their contents — the intuition "my belief that p ≠ your
    belief that p" is NOT captured. A Kratzerian atom-plus-model shape
    (`cont : E → W → (W → Prop)`) would capture it, deferred until a study
    states an identity-vs-content theorem. -/
structure ContentIndividual (W : Type*) where
  /-- Propositional content: CONT(c) -/
  cont : W → Prop

/-- A content-selecting verb (*say*, *believe*) relates an agent to a
    content individual at a world — the content-sort sibling of
    `SituationVerb`. -/
abbrev ContentVerb (W E : Type*) := E → ContentIndividual W → W → Prop

namespace ContentIndividual

variable {W : Type*}

instance : Anchor (ContentIndividual W) W :=
  ⟨cont⟩

/-- Every proposition is the content of some individual — the belief that
    `p` — so the content-mode projection is surjective. -/
theorem cont_surjective :
    Function.Surjective (cont : ContentIndividual W → W → Prop) :=
  fun p => ⟨⟨p⟩, rfl⟩

/-- Content entailment: `xc.entails p` iff every content world of `xc` is a
    `p`-world (CONT ⊆ p) — the reading of attitude reports in
    [hintikka-1962], where [kratzer-2006] and [moulton-2015] use content
    *identity*. -/
def entails (xc : ContentIndividual W) (p : W → Prop) : Prop :=
  ∀ w, xc.cont w → p w

/-- Content identity implies content entailment. -/
theorem eq_implies_entails (xc : ContentIndividual W) (p : W → Prop) :
    xc.cont = p → xc.entails p :=
  fun h _w hw => h ▸ hw

/-- Content entailment does not imply content identity: empty content
    entails every proposition. -/
theorem entails_not_implies_eq :
    ¬ ∀ (p : Bool → Prop) (xc : ContentIndividual Bool),
      xc.entails p → xc.cont = p := fun h =>
  (iff_of_eq (congrFun (h (fun _ => True) ⟨fun _ => False⟩ fun _ hw => hw.elim)
    true)).mpr trivial

end ContentIndividual

/-!
# Situation individuals

A situation individual is a first-class entity referring to a situation —
the denotation of situation DPs like *the case that the father is absent*.
Where content nouns (*belief*, *claim*, *rumor*) range over content
individuals in the sense of [kratzer-2006], situation nouns (*situation*,
*case*, *circumstance*, *event*) range over situations in the sense of
[kratzer-1989] — partial points of evaluation ordered by parthood. The
empirical motivation for the dual sort is [bondarenko-2022]'s observation
that situation-denoting clauses show selectional behaviour distinct from
content-denoting clauses (see also [moltmann-2019], [moltmann-2021],
[moltmann-2024]): verbs that select content (*say*, *believe*) reject
situation-denoting clauses, and verbs that select situations (*be happy
that*, *regret that*) reject content-denoting clauses. The two sorts are
coordinate, not subordinate, and each instantiates `Anchor` — situation
individuals with SIT as the projection, so `Anchor.comp` is the
situation-clause complementizer and `Anchor.existsClosure` composes
situation reports.

In Modern Greek, *oti*-clauses denote content and combine with
content-selecting verbs; *pu*-clauses denote situations and combine with
situation-selecting verbs ([angelopoulos-2026], following
[bondarenko-2022]). The same cut appears with other exponents (Korean
*-ko* vs *-num kes*, Japanese *to* vs *koto*); the mapping is
language-specific and not assumed here.
-/

/-- A situation individual: a first-class entity referring to a situation,
    the situation-sort sibling of `ContentIndividual`. The `sit` field is
    the situation predicate `SIT`: the set of situations the entity refers
    to. The situation-index sort `S` is typically a
    `Intensional.SituationFrame.Index` carrying a parthood preorder, but no
    order is required here, so downstream consumers can specialize freely. -/
structure SituationIndividual (S : Type*) where
  /-- Situation predicate: SIT(s_i) -/
  sit : S → Prop

/-- A situation-selecting verb (*be happy that*, *regret*) relates an
    agent to a situation individual at a situation — the situation-sort
    sibling of `ContentVerb`. -/
abbrev SituationVerb (S E : Type*) := E → SituationIndividual S → S → Prop

instance {S : Type*} : Anchor (SituationIndividual S) S :=
  ⟨SituationIndividual.sit⟩

/-- Every situation predicate is the SIT of some individual, so the
    situation-mode projection is surjective — the situation-sort analogue
    of `ContentIndividual.cont_surjective`, making
    `Anchor.existsClosure_ofAccessibility` applicable to situation
    reports. -/
theorem SituationIndividual.sit_surjective {S : Type*} :
    Function.Surjective (SituationIndividual.sit : SituationIndividual S → S → Prop) :=
  fun p => ⟨⟨p⟩, rfl⟩
