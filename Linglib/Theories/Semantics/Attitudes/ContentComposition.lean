import Linglib.Core.ContentIndividual

/-!
# Content Composition (Kratzer 2006; Moulton 2015) @cite{moulton-2015}

CPs as predicates of content individuals, not propositions.

## The Core Shift

Standard analysis: ⟦that p⟧ = p (type ⟨s,t⟩ — a proposition)

Kratzer/Moulton: ⟦that p⟧ = λx_c. CONT(x_c) = p (type ⟨e,st⟩ — a predicate
on content individuals)

The complementizer C identifies a proposition as the content of a content
individual using Kratzer's (2006) CONT function. Attitude verbs select for
content individuals (type e), and the that-clause combines via existential
closure:

  ⟦John believes that p⟧ = ∃x_c. believe(John, x_c) ∧ CONT(x_c) = p

## Key Consequences

1. Content nouns (*belief*, *claim*, *rumor*) are predicates on content
   individuals — same type as CPs — so they combine by Predicate Modification
2. That-clauses are NOT arguments of the verb; they are predicates that
   modify the ∃-closed vP
3. Attitude verb nominalizations are NASNs (Grimshaw 1990), not ASNs,
   because the content individual is ∃-bound (not an external argument)

## Cross-Linguistic Variation

- English *that*-clauses: predicates (type ⟨e,st⟩), combine by PM
- Korean *ko*-clauses: saturators (type e), function-apply directly
- German *dass*-clauses: position from V2/cluster, not from CP-as-argument

## References

- Kratzer, A. (2006). Decomposing attitude reports.
- Moulton, K. (2015). CPs: Copies and compositionality. LI 46(2), 305–342.
- Grimshaw, J. (1990). Argument Structure. MIT Press.
-/

namespace Semantics.Attitudes.ContentComposition

open Core.Proposition
open Core.BToM

-- ════════════════════════════════════════════════════
-- § 1. Complementizer Semantics
-- ════════════════════════════════════════════════════

/-- The complementizer C: takes a proposition p and identifies it as the
    content of a content individual x_c.

    ⟦C⟧(p)(x_c) ⟺ CONT(x_c) = p

    This is Moulton (2015) (15). The result is type ⟨e,st⟩ — a predicate
    on content individuals — not a proposition ⟨s,t⟩. -/
def compC {W : Type*} (p : BProp W) (xc : ContentIndividual W) : Prop :=
  xc.cont = p

-- ════════════════════════════════════════════════════
-- § 2. Content Nouns
-- ════════════════════════════════════════════════════

/-- A content noun: a world-indexed predicate on content individuals.

    Content nouns — *belief*, *claim*, *rumor*, *idea*, *wish* — denote
    properties of content individuals (Moulton 2015, §2). They are type
    ⟨e,st⟩, the same semantic type as CPs. -/
abbrev ContentNoun (W : Type*) := ContentIndividual W → W → Prop

/-- Predicate Modification for content nouns and CPs (Moulton 2015, (17)).

    ⟦belief that p⟧ = λx_c.λw. belief(x_c)(w) ∧ CONT(x_c) = p

    Because both the content noun and the CP are type ⟨e,st⟩, they combine
    by intersection (Predicate Modification, Heim & Kratzer 1998). -/
def contentNounCP {W : Type*} (noun : ContentNoun W) (p : BProp W)
    : ContentNoun W :=
  fun xc w => noun xc w ∧ compC p xc

/-- The CP determines the content: if x_c satisfies a content-noun-CP
    combination, then CONT(x_c) = p. -/
theorem contentNounCP_determines_content {W : Type*}
    (noun : ContentNoun W) (p : BProp W) (xc : ContentIndividual W) (w : W) :
    contentNounCP noun p xc w → compC p xc :=
  fun ⟨_, h⟩ => h

-- ════════════════════════════════════════════════════
-- § 3. Attitude Verbs over Content Individuals
-- ════════════════════════════════════════════════════

/-- An attitude verb in the Kratzer/Moulton architecture: relates an agent
    to a content individual (not to a proposition directly).

    *believe* : λx_c. λx_agent. λw. believe(x_agent, x_c, w) -/
abbrev AttitudeVerbCI (W E : Type*) := E → ContentIndividual W → W → Prop

/-- Existential closure over content individuals (Moulton 2015, (21)–(23)).

    Closes off the content individual variable at the edge of vP:

      λw. ∃x_c. V(agent, x_c, w) ∧ CONT(x_c) = p

    "John believes that p" is true at w iff there exists a content individual
    x_c such that John stands in the belief relation to x_c at w and the
    content of x_c is p. -/
def existsContentClosure {W E : Type*}
    (verb : AttitudeVerbCI W E) (agent : E) (p : BProp W) (w : W) : Prop :=
  ∃ xc : ContentIndividual W, verb agent xc w ∧ compC p xc

-- ════════════════════════════════════════════════════
-- § 4. Hintikka Bridge (Identity)
-- ════════════════════════════════════════════════════

/-- An attitude verb derived from a Hintikka accessibility relation.

    Given R(agent, w, w'), the verb holds of agent and x_c at w iff
    x_c's content equals the set of accessible worlds:

      V(agent, x_c, w) ⟺ CONT(x_c) = R(agent)(w)

    This shows that the classical doxastic semantics (Hintikka 1969) is a
    special case of the content-individual architecture: there is one
    canonical content individual per agent-world pair, namely
    `ContentIndividual.fromAccessibility R agent w`. -/
def hintikkaVerb {W E : Type*}
    (R : E → W → W → Bool) : AttitudeVerbCI W E :=
  fun agent xc w => xc.cont = R agent w

/-- Under a Hintikka verb, *identity* closure reduces to propositional
    identity with the accessibility set.

    ∃x_c[hintikkaVerb(R)(a, x_c, w) ∧ CONT(x_c) = p]  ⟺  R(a)(w) = p

    The existential is uniquely witnessed by the canonical content individual
    `fromAccessibility R a w`. -/
theorem hintikka_existsClosure {W E : Type*}
    (R : E → W → W → Bool) (a : E) (p : BProp W) (w : W) :
    existsContentClosure (hintikkaVerb R) a p w ↔ R a w = p := by
  simp only [existsContentClosure, hintikkaVerb, compC]
  constructor
  · rintro ⟨xc, h1, h2⟩
    exact h1.symm.trans h2
  · intro h
    exact ⟨ContentIndividual.fromAccessibility R a w, rfl, h⟩

-- ════════════════════════════════════════════════════
-- § 5. Hintikka Bridge (Entailment)
-- ════════════════════════════════════════════════════

/-- Existential closure with entailment instead of identity.

    ∃x_c. V(agent, x_c, w) ∧ CONT(x_c) ⊆ p

    This is the weaker condition: some content individual of the agent's
    has content that entails p (not necessarily equals p). -/
def existsContentEntails {W E : Type*}
    (verb : AttitudeVerbCI W E) (agent : E) (p : BProp W) (w : W) : Prop :=
  ∃ xc : ContentIndividual W, verb agent xc w ∧ xc.entails p

/-- Identity closure implies entailment closure. -/
theorem existsClosure_implies_entailsClosure {W E : Type*}
    (verb : AttitudeVerbCI W E) (agent : E) (p : BProp W) (w : W) :
    existsContentClosure verb agent p w → existsContentEntails verb agent p w := by
  rintro ⟨xc, hv, hc⟩
  exact ⟨xc, hv, xc.eq_implies_entails p hc⟩

/-- Under a Hintikka verb, *entailment* closure reduces to the standard
    universal modal — the classical Hintikka semantics.

    ∃x_c[hintikkaVerb(R)(a, x_c, w) ∧ CONT(x_c) ⊆ p]
      ⟺  ∀w'. R(a, w, w') = true → p(w') = true

    Compare with `hintikka_existsClosure` (§4), where *identity* closure
    reduces to R(a)(w) = p. The two results together make the distinction
    precise:

    | Closure mode | Reduces to              | Semantic gloss           |
    |--------------|-------------------------|--------------------------|
    | Identity     | R(a)(w) = p             | p IS the belief content  |
    | Entailment   | ∀w'. R(a,w,w') → p(w') | p FOLLOWS FROM beliefs   | -/
theorem hintikka_entailsClosure {W E : Type*}
    (R : E → W → W → Bool) (a : E) (p : BProp W) (w : W) :
    existsContentEntails (hintikkaVerb R) a p w ↔
    (∀ w', R a w w' = true → p w' = true) := by
  simp only [existsContentEntails, hintikkaVerb, ContentIndividual.entails]
  constructor
  · rintro ⟨xc, heq, hent⟩ w' hw'
    apply hent
    rw [heq]
    exact hw'
  · intro h
    exact ⟨ContentIndividual.fromAccessibility R a w, rfl, h⟩

-- ════════════════════════════════════════════════════
-- § 6. Content Noun Composition
-- ════════════════════════════════════════════════════

/-- Content-noun existential closure: "a belief that p exists at w".

    ∃x_c. noun(x_c, w) ∧ CONT(x_c) = p

    This is how content DPs like *the belief that Fred left* or *every
    rumor that p* get their denotation: the content noun restricts the
    domain of content individuals and the CP identifies the content. -/
def existsContentNounCP {W : Type*}
    (noun : ContentNoun W) (p : BProp W) (w : W) : Prop :=
  ∃ xc : ContentIndividual W, contentNounCP noun p xc w

/-- A full attitude report with a content noun:
    "John's belief that p" = ∃x_c. belief(x_c, w) ∧ V(John, x_c, w) ∧ CONT(x_c) = p -/
def attitudeWithContentNoun {W E : Type*}
    (noun : ContentNoun W) (verb : AttitudeVerbCI W E) (agent : E)
    (p : BProp W) (w : W) : Prop :=
  ∃ xc : ContentIndividual W, noun xc w ∧ verb agent xc w ∧ compC p xc

end Semantics.Attitudes.ContentComposition
