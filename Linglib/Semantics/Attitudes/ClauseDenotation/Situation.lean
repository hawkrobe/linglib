import Linglib.Core.Logic.Intensional.Situations
import Linglib.Tactics.OntSort

/-!
# Clause Denotation: Situation [bondarenko-2022] [moltmann-2021]
[kratzer-1989] [moltmann-2024] [moltmann-2019]

CPs as predicates of **situation individuals**, the situation-side
sibling of `ClauseDenotation/Content.lean`.

Where content nouns (*belief*, *claim*, *rumor*) range over content
individuals in the sense of [kratzer-2006], *situation* nouns
(*situation*, *case*, *circumstance*, *event*) range over situations
in the sense of [kratzer-1989] — partial points of evaluation
ordered by parthood. The empirical motivation for the dual sort is
[bondarenko-2022]'s observation that situation-denoting clauses
exhibit selectional behaviour distinct from content-denoting clauses
(see also [moltmann-2021], [moltmann-2024]).

The two licensee sorts are coordinate, not subordinate: a content
individual is not a situation, and vice versa. Verbs that select for
content (*say*, *believe*) reject situation-denoting clauses, and
verbs that select for situations (*be happy that*, *regret that*)
reject content-denoting clauses.

## Cross-linguistic motivation

In Modern Greek, *oti*-clauses denote content and combine with
content-selecting verbs; *pu*-clauses denote situations and combine
with situation-selecting verbs ([angelopoulos-2026] §3.2,
following [bondarenko-2022]). The same content/situation cut
appears in other languages with different morphological exponents
(Korean *-ko* / *-num kes*, Japanese *to* / *koto*; mapping is
language-specific and not assumed here).

## Position-orthogonality (mirroring Content.lean)

[bondarenko-2022] (transparent Syntax-Semantics mapping) and
[angelopoulos-2026] (autonomy of syntax) hold opposing views on
whether the PM-vs-FA composition mode forces distinct syntactic
positions for situation-clauses (adjunct vs argument). This file
stays neutral on the syntax-semantics correspondence; the substrate
exposes only the situation-denotation machinery.

-/

namespace Semantics.Attitudes.ClauseDenotation.Situation

-- ════════════════════════════════════════════════════
-- § 1. The Situation Individual Sort
-- ════════════════════════════════════════════════════

/-- A **situation individual**: a first-class entity referring to a
    situation, parallel to `Semantics.Attitudes.ContentIndividual`.

    The `sit` field gives the situation predicate (`SIT`): the set of
    situations the entity refers to. For a *case*-individual referring
    to "the case that the father is absent" ([angelopoulos-2026]
    ex. 35b), `sit` is the predicate that holds at exactly those
    situations where the father is absent.

    Parameter `S` is the situation-index sort; in practice this is
    typically a `Core.Logic.Intensional.SituationFrame.Index` carrying
    a parthood preorder, but this file does not require `[PartialOrder S]`
    so that downstream consumers can specialize freely. -/
@[ont_sort] structure SituationIndividual (S : Type*) where
  /-- Situation predicate: SIT(s_i) -/
  sit : S → Prop

-- ════════════════════════════════════════════════════
-- § 2. Situation Nouns
-- ════════════════════════════════════════════════════

/-- A situation noun: a situation-indexed predicate on situation individuals.

    Situation nouns — *situation*, *case*, *circumstance*, *fact*
    (in its eventive use), *event* — denote properties of situation
    individuals. Same shape as `Semantics.Attitudes.ContentNoun` but over
    `SituationIndividual` rather than `ContentIndividual`. -/
abbrev SituationNoun (S : Type*) := SituationIndividual S → S → Prop

-- ════════════════════════════════════════════════════
-- § 3. Complementizer Semantics
-- ════════════════════════════════════════════════════

/-- The situation-clause complementizer (Greek *pu*): identifies a
    situation predicate as the SIT of a situation individual.

    ⟦pu⟧(q)(x_s) ⟺ SIT(x_s) = q

    Mirrors `Semantics.Attitudes.ClauseDenotation.Content.compC` for
    *that*/*oti*. The result is a predicate on situation individuals,
    type ⟨e_s, st⟩. -/
def compPu {S : Type*} (q : S → Prop) (xs : SituationIndividual S) : Prop :=
  xs.sit = q

-- ════════════════════════════════════════════════════
-- § 4. Predicate Modification
-- ════════════════════════════════════════════════════

/-- Predicate Modification for situation-noun + situation-CP, parallel
    to `contentNounCP` for content-noun + that-CP.

    ⟦situation that q⟧ = λx_s.λs. situation(x_s)(s) ∧ SIT(x_s) = q

    Both arguments are type ⟨e_s, st⟩, so they combine by intersection. -/
def situationNounCP {S : Type*} (noun : SituationNoun S) (q : S → Prop) :
    SituationNoun S :=
  fun xs s => noun xs s ∧ compPu q xs

/-- The CP determines the situation: if x_s satisfies a situation-noun-CP
    combination, then SIT(x_s) = q. -/
theorem situationNounCP_determines_sit {S : Type*}
    (noun : SituationNoun S) (q : S → Prop) (xs : SituationIndividual S) (s : S) :
    situationNounCP noun q xs s → compPu q xs :=
  fun ⟨_, h⟩ => h

-- ════════════════════════════════════════════════════
-- § 5. Existential Closure
-- ════════════════════════════════════════════════════

/-- A situation-selecting verb: relates an agent to a situation
    individual at a situation, parallel to `AttitudeVerbCI`. -/
abbrev SituationVerb (S X : Type*) := X → SituationIndividual S → S → Prop

/-- Existential closure over situation individuals.

    Closes off the situation individual variable at the edge of vP:

      λs. ∃x_s. V(agent, x_s, s) ∧ SIT(x_s) = q

    "Maria regrets that p" is true at situation s iff there exists a
    situation individual x_s such that Maria stands in the regret
    relation to x_s at s and the SIT of x_s is q. -/
def existsSituationClosure {S X : Type*}
    (verb : SituationVerb S X) (agent : X) (q : S → Prop) (s : S) : Prop :=
  ∃ xs : SituationIndividual S, verb agent xs s ∧ compPu q xs

/-- A full situation report with a situation noun:
    "the case that p" + verb = ∃x_s. case(x_s, s) ∧ V(agent, x_s, s) ∧ SIT(x_s) = q -/
def situationWithNoun {S X : Type*}
    (noun : SituationNoun S) (verb : SituationVerb S X) (agent : X)
    (q : S → Prop) (s : S) : Prop :=
  ∃ xs : SituationIndividual S, noun xs s ∧ verb agent xs s ∧ compPu q xs

/-- Existential closure with a situation noun (no agent / matrix verb).

    "a case that p exists at s": ∃x_s. case(x_s, s) ∧ SIT(x_s) = q.
    Mirrors `existsContentNounCP`. -/
def existsSituationNounCP {S : Type*}
    (noun : SituationNoun S) (q : S → Prop) (s : S) : Prop :=
  ∃ xs : SituationIndividual S, situationNounCP noun q xs s

end Semantics.Attitudes.ClauseDenotation.Situation
