import Linglib.Semantics.Attitudes.Anchor

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

/-- A situation-selecting verb relates an agent to a situation individual
    at a situation. -/
abbrev SituationVerb (S X : Type*) := X → SituationIndividual S → S → Prop

instance {S : Type*} : Anchor (SituationIndividual S) S :=
  ⟨SituationIndividual.sit⟩

