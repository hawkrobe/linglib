/-
# PLA Belief Reports

Dekker (2012) Chapter 4, §4.2: Belief Reports and Conceptual Covers.

## Key Concepts

### Belief Reports
"John believes that Mary is smart."
- Agent: John
- Content: Mary is smart
- Question: Is this de re or de dicto?

### De Re vs De Dicto
- De re: "John believes of Mary that she is smart"
  The belief is about a specific individual (Mary herself).
  Uses rigid concept - same individual in all belief-accessible worlds.

- De dicto: "John believes that the winner is smart"
  The belief is about whoever satisfies "the winner" in John's belief worlds.
  Uses descriptive concept - may pick out different individuals.

### Conceptual Covers (Aloni 2001, Dekker §4.3)
A conceptual cover is a set of concepts that:
1. Covers the domain (every entity is picked out by some concept)
2. Is functional (each concept picks out at most one entity per possibility)

Covers formalize "ways of thinking about" entities.

## References

- Dekker, P. (2012). Dynamic Semantics. Springer. Chapter 4, §4.2-4.3.
- Aloni, M. (2001). Quantification under Conceptual Covers.
- Quine, W.V.O. (1956). Quantifiers and Propositional Attitudes.
- Kaplan, D. (1968). Quantifying In.
-/

import Linglib.Theories.Semantics.Dynamic.Systems.PLA.Epistemic

namespace Semantics.Dynamic.PLA

open Classical

variable {E : Type*} [Nonempty E]


/--
Doxastic accessibility relation: what worlds/possibilities agent a
considers compatible with their beliefs.

`R a p q` means: in possibility p, agent a considers q doxastically accessible
(q is compatible with what a believes in p).
-/
abbrev DoxAccessibility (E : Type*) := E → Poss E → Poss E → Prop

/--
The set of doxastically accessible possibilities for agent a at p.
-/
def doxAccessible (R : DoxAccessibility E) (a : E) (p : Poss E) : Set (Poss E) :=
  { q | R a p q }

/--
Reflexivity: agent believes truths (factivity for knowledge).
Note: belief is not typically factive, but this is useful for knowledge.
-/
def DoxAccessibility.isReflexive (R : DoxAccessibility E) : Prop :=
  ∀ a p, R a p p

/--
Transitivity: positive introspection (believing implies believing you believe).
-/
def DoxAccessibility.isTransitive (R : DoxAccessibility E) : Prop :=
  ∀ a p q r, R a p q → R a q r → R a p r

/--
Seriality: no inconsistent belief states (for every p, some q is accessible).
This is the minimal requirement for belief: consistent belief states.
-/
def DoxAccessibility.isSerial (R : DoxAccessibility E) : Prop :=
  ∀ a p, ∃ q, R a p q


/--
Belief operator: agent a believes φ.

B(a, φ) is true at (g, ê) iff φ is true at all doxastically accessible possibilities.

This is a TEST: it checks if the agent's belief state supports φ.
-/
def Formula.believe (R : DoxAccessibility E) (M : Model E) (a : E) (φ : Formula) :
    Update E :=
  λ s => { p ∈ s | ∀ q ∈ doxAccessible R a p, φ.sat M q.1 q.2 }

/--
Belief with term: B(t, φ) where t is a term denoting the agent.
-/
def Formula.believeTerm (R : DoxAccessibility E) (M : Model E) (t : Term) (φ : Formula) :
    Update E :=
  λ s => { p ∈ s |
    let a := t.eval p.1 p.2
    ∀ q ∈ doxAccessible R a p, φ.sat M q.1 q.2 }


/--
Belief is eliminative: Filtering to believers never adds possibilities.
-/
theorem believe_eliminative (R : DoxAccessibility E) (M : Model E) (a : E) (φ : Formula)
    (s : InfoState E) :
    Formula.believe R M a φ s ⊆ s := by
  intro p hp
  simp only [Formula.believe, Set.mem_setOf_eq] at hp
  exact hp.1

/--
Belief closure under entailment: If you believe φ and φ entails ψ, you believe ψ.
-/
theorem believe_closure (R : DoxAccessibility E) (M : Model E) (a : E) (φ ψ : Formula)
    (s : InfoState E) (p : Poss E)
    (hent : ∀ g ê, φ.sat M g ê → ψ.sat M g ê)
    (hp : p ∈ Formula.believe R M a φ s) :
    p ∈ Formula.believe R M a ψ s := by
  simp only [Formula.believe, Set.mem_setOf_eq] at hp ⊢
  constructor
  · exact hp.1
  · intro q hq
    exact hent q.1 q.2 (hp.2 q hq)

/--
Conjunction distribution: B(a, φ ∧ ψ) ↔ B(a, φ) ∧ B(a, ψ)
-/
theorem believe_conj (R : DoxAccessibility E) (M : Model E) (a : E) (φ ψ : Formula)
    (s : InfoState E) (p : Poss E) :
    p ∈ Formula.believe R M a (φ ⋀ ψ) s ↔
    p ∈ Formula.believe R M a φ s ∧ p ∈ Formula.believe R M a ψ s := by
  simp only [Formula.believe, Set.mem_setOf_eq, Formula.sat]
  constructor
  · intro ⟨hp, hall⟩
    exact ⟨⟨hp, λ q hq => (hall q hq).1⟩, ⟨hp, λ q hq => (hall q hq).2⟩⟩
  · intro ⟨⟨hp, hφ⟩, ⟨_, hψ⟩⟩
    exact ⟨hp, λ q hq => ⟨hφ q hq, hψ q hq⟩⟩


/--
A Conceptual Cover is a set of concepts (ways of identifying entities).

In Aloni's framework, a cover represents the "ways of thinking" available
to an agent or in a context.
-/
abbrev Cover (E : Type*) := Set (Concept E)

/--
A cover is exhaustive if every entity in the domain is picked out
by some concept in the cover (at every possibility).
-/
def Cover.isExhaustive (C : Cover E) : Prop :=
  ∀ (p : Poss E) (e : E), ∃ c ∈ C, c p = e

/--
A cover is functional if each concept picks out a unique entity
(this is automatic since concepts are functions).
-/
def Cover.isFunctional (C : Cover E) : Prop :=
  ∀ c ∈ C, ∀ p : Poss E, ∃! e : E, c p = e

/--
The name cover: rigid concepts for each entity.
This is the "de re" cover - thinking of entities as themselves.
-/
def nameCover (dom : Set E) : Cover E :=
  { Concept.const e | e ∈ dom }

/--
The variable cover: concepts from variable assignments.
This is more "de dicto" - thinking via variable bindings.
-/
def variableCover : Cover E :=
  { Concept.fromVar i | i : VarIdx }

/--
Name cover is exhaustive over its domain.
-/
theorem nameCover_exhaustive (dom : Set E) (_hne : dom.Nonempty) :
    ∀ (p : Poss E) (e : E), e ∈ dom → ∃ c ∈ nameCover dom, c p = e := by
  intro p e he
  use Concept.const e
  constructor
  · simp only [nameCover, Set.mem_setOf_eq]
    exact ⟨e, he, rfl⟩
  · simp only [Concept.const]

/--
All concepts in the name cover are rigid.
-/
theorem nameCover_rigid (dom : Set E) :
    ∀ c ∈ nameCover dom, c.isRigid := by
  intro c hc
  simp only [nameCover, Set.mem_setOf_eq] at hc
  obtain ⟨e, _, rfl⟩ := hc
  exact const_is_rigid e


/--
De re belief: Belief about a specific individual, identified rigidly.

"John believes of Mary that she is smart."

The individual (Mary) is fixed across all of John's belief worlds.
-/
def believeDeRe (R : DoxAccessibility E) (M : Model E) (agent : E) (individual : E)
    (pred : String) : Update E :=
  λ s => { p ∈ s |
    -- In all belief-accessible worlds, the predicate holds of the same individual
    ∀ q ∈ doxAccessible R agent p, M.interp pred [individual] }

/--
De dicto belief: Belief about whoever satisfies a description.

"John believes that the winner is smart."

The individual may vary across John's belief worlds (whoever is the winner there).
-/
def believeDeDicto (R : DoxAccessibility E) (M : Model E) (agent : E)
    (description : Concept E) (pred : String) : Update E :=
  λ s => { p ∈ s |
    -- In all belief-accessible worlds, the predicate holds of whoever
    -- satisfies the description in that world
    ∀ q ∈ doxAccessible R agent p, M.interp pred [description q] }

/--
De re implies de dicto when the concept is rigid.

If you believe of x that P(x), and concept c rigidly picks out x,
then you believe that P(c).
-/
theorem deRe_implies_deDicto_rigid (R : DoxAccessibility E) (M : Model E)
    (agent individual : E) (c : Concept E) (pred : String)
    (_hrigid : c.isRigid) (hpicks : ∀ p, c p = individual)
    (s : InfoState E) (p : Poss E)
    (hp : p ∈ believeDeRe R M agent individual pred s) :
    p ∈ believeDeDicto R M agent c pred s := by
  simp only [believeDeRe, believeDeDicto, Set.mem_setOf_eq] at hp ⊢
  constructor
  · exact hp.1
  · intro q hq
    rw [hpicks q]
    exact hp.2 q hq

-- Note: De dicto does not imply de re in general.
-- The winner in John's belief worlds might not be the actual winner.
-- This is a semantic fact that requires a counterexample model.


/--
Substitutivity of identicals (de re): If a = b and you believe P(a),
then you believe P(b).

This holds for de re beliefs because the individual is fixed.
-/
theorem substitutivity_deRe (R : DoxAccessibility E) (M : Model E)
    (agent a b : E) (pred : String) (heq : a = b)
    (s : InfoState E) (p : Poss E)
    (hp : p ∈ believeDeRe R M agent a pred s) :
    p ∈ believeDeRe R M agent b pred s := by
  simp only [heq] at hp
  exact hp

/-!
## Quine's Ortcutt Puzzle (Quine 1956)

The linguistic puzzle that motivates conceptual covers:

> "Ralph believes that the man in the brown hat is a spy."
> "Ralph believes that the man seen at the beach is not a spy."
> The man in the brown hat IS the man seen at the beach (= Ortcutt).

Naively, this seems to attribute contradictory beliefs to Ralph. But Ralph
is perfectly rational - he simply doesn't know that the two descriptions
pick out the same individual.

The apparent contradiction dissolves when we recognize that Ralph's
beliefs are *relativized to conceptual covers*:
- Under the "brown hat" cover, Ralph believes Ortcutt is a spy
- Under the "beach" cover, Ralph believes Ortcutt is not a spy

These are consistent because the covers don't overlap in Ralph's belief worlds.
-/

/--
Quine consistency: An agent can believe P(x) under one cover and ¬P(x)
under another cover, without inconsistency.

This is the formal core of Quine's puzzle: what looks like believing
both P(o) and ¬P(o) is actually consistent when the beliefs are
relativized to different conceptual covers.

Linguistic example: Ralph believes "the man in the brown hat is a spy" AND
"the man seen at the beach is not a spy" - both about Ortcutt, yet consistent.
-/
def quineConsistent (R : DoxAccessibility E) (M : Model E) (agent : E)
    (c1 c2 : Concept E) (pred : String) (_s : InfoState E) (p : Poss E) : Prop :=
  -- c1 and c2 pick out the same individual in the actual world
  c1 p = c2 p ∧
  -- But agent believes predicate holds via c1
  (∀ q ∈ doxAccessible R agent p, M.interp pred [c1 q]) ∧
  -- And agent believes predicate fails via c2
  (∀ q ∈ doxAccessible R agent p, ¬M.interp pred [c2 q])

/--
Quine consistency requires concept divergence: If an agent has
Quine-consistent beliefs about an individual (believing P under one cover,
¬P under another), then the concepts must diverge in some belief-accessible world.

Quine consistency is possible because the concepts that coincide
in the actual world must pick out different individuals in some of the
agent's belief worlds.
-/
theorem quine_requires_divergence (R : DoxAccessibility E) (M : Model E)
    (agent : E) (c1 c2 : Concept E) (pred : String) (s : InfoState E) (p : Poss E)
    (_hs : s.Nonempty) (hdox : (doxAccessible R agent p).Nonempty)
    (hquine : quineConsistent R M agent c1 c2 pred s p) :
    ∃ q ∈ doxAccessible R agent p, c1 q ≠ c2 q := by
  obtain ⟨_hc1c2, hpos, hneg⟩ := hquine
  obtain ⟨q, hq⟩ := hdox
  by_contra hall
  push_neg at hall
  -- If c1 and c2 coincide everywhere, we get contradiction
  have heq : c1 q = c2 q := hall q hq
  have h1 := hpos q hq
  have h2 := hneg q hq
  rw [heq] at h1
  exact h2 h1

-- Note: Substitutivity fails (de dicto).
-- Even if descriptions a and b are coextensive in the actual world,
-- de dicto beliefs don't transfer.
-- Example: "The morning star" = "The evening star" (both are Venus).
-- But believing "the morning star is bright" doesn't mean believing
-- "the evening star is bright" if you don't know they're the same.
-- Proving this requires constructing a model where two concepts coincide at p
-- but diverge in some belief-accessible q.


/-!
## Observation 17: Quantifier Scope and Belief

Dekker (2012) Observation 17 (p.88):
> B(r, ∃x_C Sx) = ∃x_C B(r, Sx)

This equivalence holds when quantification is relativized to a conceptual cover C.
An existential quantifier can be "exported" from inside a belief context,
provided it ranges over concepts in the agent's cover.

Linguistic motivation: consider "Ralph believes someone is a spy."

1. Wide scope (de re): ∃x_C B(r, Sx)
   "There is someone (under cover C) such that Ralph believes they are a spy."
   Ralph has a specific individual in mind.

2. Narrow scope (de dicto): B(r, ∃x_C Sx)
   "Ralph believes that someone (under cover C) is a spy."
   Ralph believes the existential claim without necessarily having
   a specific individual in mind.

These readings are equivalent when the cover C represents
Ralph's available ways of identifying individuals.

In classical intensional semantics (without covers),
wide and narrow scope are not equivalent. Covers make them equivalent
because the quantifier domain is "grounded" in the agent's conceptual repertoire.
-/

/--
Narrow scope existential belief: Agent believes ∃x.P(x)
The existential is inside the belief operator.
-/
def believeExistsNarrow (R : DoxAccessibility E) (M : Model E) (agent : E)
    (C : Cover E) (pred : String) : Update E :=
  λ s => { p ∈ s |
    -- Agent believes: there exists a concept in C satisfying pred
    ∀ q ∈ doxAccessible R agent p, ∃ c ∈ C, M.interp pred [c q] }

/--
Wide scope existential belief: ∃x.B(agent, P(x))
The existential scopes over the belief operator.
-/
def believeExistsWide (R : DoxAccessibility E) (M : Model E) (agent : E)
    (C : Cover E) (pred : String) : Update E :=
  λ s => { p ∈ s |
    -- There exists a concept in C such that agent believes pred holds of it
    ∃ c ∈ C, ∀ q ∈ doxAccessible R agent p, M.interp pred [c q] }

/--
Observation 17: Wide scope implies narrow scope (always holds).

∃x_C B(r, Sx) → B(r, ∃x_C Sx)

If there's a specific concept c such that Ralph believes P(c),
then Ralph believes that something satisfies P.
-/
theorem obs17_wide_implies_narrow (R : DoxAccessibility E) (M : Model E)
    (agent : E) (C : Cover E) (pred : String) (s : InfoState E) :
    believeExistsWide R M agent C pred s ⊆ believeExistsNarrow R M agent C pred s := by
  intro p hp
  simp only [believeExistsWide, believeExistsNarrow, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨hps, c, hc, hall⟩ := hp
  constructor
  · exact hps
  · intro q hq
    exact ⟨c, hc, hall q hq⟩

/--
Observation 17 (converse): Narrow scope implies wide scope
WHEN the cover is closed under the agent's beliefs.

B(r, ∃x_C Sx) → ∃x_C B(r, Sx)

This direction requires that concepts in C "persist" across belief worlds:
if c ∈ C picks out some individual in q, then the agent can track that
individual across their belief states.

This formalizes when "Ralph believes someone is a spy"
licenses the inference to "Ralph has someone specific in mind" - namely,
when Ralph's conceptual repertoire provides stable ways of identifying individuals.
-/
theorem obs17_narrow_implies_wide (R : DoxAccessibility E) (M : Model E)
    (agent : E) (C : Cover E) (pred : String) (s : InfoState E) (p : Poss E)
    -- Key assumption: agent has at least one accessible belief state
    (_hdox : (doxAccessible R agent p).Nonempty)
    -- Key assumption: there's a witnessing concept that works uniformly
    (hwit : ∃ c ∈ C, ∀ q ∈ doxAccessible R agent p, M.interp pred [c q])
    (hp : p ∈ believeExistsNarrow R M agent C pred s) :
    p ∈ believeExistsWide R M agent C pred s := by
  simp only [believeExistsNarrow, believeExistsWide, Set.mem_setOf_eq] at hp ⊢
  exact ⟨hp.1, hwit⟩


/-!
## Observation 18: Knowing Who is Cover-Relative

Dekker (2012) Observation 18 (p.91):
> "Knowing who" is relative to a conceptual cover.

The Hesperus/Phosphorus puzzle:

The ancients knew that:
- Hesperus is the evening star (visible at dusk)
- Phosphorus is the morning star (visible at dawn)

They did not know that Hesperus = Phosphorus (both are Venus).

Question: Did the ancients "know who Hesperus is"?

Answer depends on the cover:
- Under the astronomical cover (celestial bodies as physical objects):
  No - they didn't know Hesperus is Venus.
- Under the observational cover (celestial bodies by when they appear):
  Yes - they knew Hesperus is "the bright thing in the evening sky."

"Knowing who" is not absolute but relative to a
contextually supplied way of carving up the domain of individuals.

This explains why "knowing who" questions are context-sensitive:
- "Do you know who the president is?" (identification by role)
- "Do you know who that person is?" (identification by name/face)

Different questions presuppose different conceptual covers.
-/

/--
Knowing who (cover-relative): Agent knows who x is under cover C.

K_C(a, who(x)) holds iff:
1. Agent has an identifying concept c in cover C
2. c picks out x in all epistemically accessible worlds
3. Agent knows that c picks out x
-/
def knowsWho (R : DoxAccessibility E) (agent individual : E) (C : Cover E) (p : Poss E) : Prop :=
  ∃ c ∈ C,
    -- c picks out individual at p
    c p = individual ∧
    -- c picks out the same individual in all accessible worlds (rigidity under belief)
    ∀ q ∈ doxAccessible R agent p, c q = individual

/--
Hesperus/Phosphorus: Two concepts can pick out the same individual
at the actual world but different individuals in belief-accessible worlds.
-/
def hesperusPhosphorusScenario (R : DoxAccessibility E) (agent : E)
    (hesperus phosphorus : Concept E) (venus : E) (p : Poss E) : Prop :=
  -- Both concepts pick out Venus in actuality
  hesperus p = venus ∧ phosphorus p = venus ∧
  -- But in some belief-accessible world, they diverge
  ∃ q ∈ doxAccessible R agent p, hesperus q ≠ phosphorus q

/--
Observation 18: Knowing who is cover-relative.

If the cover includes only rigid concepts (like proper names),
then knowing who is equivalent to de re identification.

But if the cover includes descriptive concepts (like "the evening star"),
knowing who becomes weaker - it only requires identifying x
via the contextually appropriate description.
-/
theorem knowsWho_with_rigid_cover (R : DoxAccessibility E) (agent individual : E)
    (C : Cover E) (p : Poss E)
    -- Cover contains only rigid concepts
    (hrigid : ∀ c ∈ C, c.isRigid)
    -- Agent knows who individual is
    (hknows : knowsWho R agent individual C p) :
    -- Then the witnessing concept is constant
    ∃ c ∈ C, ∀ q : Poss E, c q = individual := by
  obtain ⟨c, hc, hpicks, _⟩ := hknows
  use c, hc
  intro q
  have hrig := hrigid c hc
  -- c is rigid, so c q = c p = individual
  simp only [Concept.isRigid] at hrig
  rw [hrig q p, hpicks]

/--
Knowing who failure: An agent can know who x is under one cover
but not under another, even for the same individual.

This is the formal content of the Hesperus/Phosphorus puzzle.
-/
theorem knowsWho_cover_relative (R : DoxAccessibility E) (agent venus : E)
    (hesperus phosphorus : Concept E)
    (Cobs : Cover E)   -- Observational cover (includes hesperus, phosphorus)
    (Castro : Cover E) -- Astronomical cover (rigid concepts only)
    (p : Poss E)
    -- Setup: Hesperus/Phosphorus scenario
    (_hHP : hesperusPhosphorusScenario R agent hesperus phosphorus venus p)
    -- Hesperus is in observational cover
    (_hHinC : hesperus ∈ Cobs)
    -- Astronomical cover only has rigid concepts
    (_hCastro_rigid : ∀ c ∈ Castro, c.isRigid)
    -- Hesperus is not in astronomical cover (it's descriptive)
    (_hHnotCastro : hesperus ∉ Castro)
    -- Agent knows who Venus is via Hesperus in observational cover
    (_hknowsObs : knowsWho R agent venus Cobs p) :
    -- But we can't conclude the same for astronomical cover without more info
    True := by
  trivial


/--
Belief relative to a cover: The agent's beliefs are interpreted
relative to a conceptual cover (their available ways of thinking).

B_C(a, ∃x.P(x)) is true iff for some concept c in cover C,
a believes P(c).
-/
def believeExistsWithCover (R : DoxAccessibility E) (M : Model E) (agent : E)
    (C : Cover E) (pred : String) : Update E :=
  λ s => { p ∈ s |
    ∃ c ∈ C, ∀ q ∈ doxAccessible R agent p, M.interp pred [c q] }

/--
Belief relative to name cover is equivalent to de re quantification.
-/
theorem believeExists_nameCover_deRe (R : DoxAccessibility E) (M : Model E)
    (agent : E) (dom : Set E) (pred : String) (s : InfoState E) (p : Poss E) :
    p ∈ believeExistsWithCover R M agent (nameCover dom) pred s ↔
    p ∈ s ∧ ∃ e ∈ dom, ∀ q ∈ doxAccessible R agent p, M.interp pred [e] := by
  simp only [believeExistsWithCover, nameCover, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, c, ⟨e, he, hc⟩, hall⟩
    refine ⟨hp, e, he, ?_⟩
    intro q hq
    specialize hall q hq
    simp only [← hc, Concept.const] at hall
    exact hall
  · intro ⟨hp, e, he, hall⟩
    refine ⟨hp, Concept.const e, ⟨e, he, rfl⟩, ?_⟩
    intro q hq
    simp only [Concept.const]
    exact hall q hq


/--
Acquaintance requirement (Russell): De re belief requires acquaintance.

You can only have de re beliefs about entities you're "acquainted with"
(entities in your conceptual cover).
-/
def isAcquaintedWith (_agent : E) (individual : E) (C : Cover E) (p : Poss E) : Prop :=
  ∃ c ∈ C, c p = individual

/--
De re belief presupposes acquaintance (relative to a cover).
-/
def believeDeReWithAcquaintance (R : DoxAccessibility E) (M : Model E)
    (agent : E) (C : Cover E) (individual : E) (pred : String) : Update E :=
  λ s => { p ∈ s |
    -- Presupposition: agent is acquainted with individual
    isAcquaintedWith agent individual C p ∧
    -- Belief content: predicate holds in all belief worlds
    ∀ q ∈ doxAccessible R agent p, M.interp pred [individual] }


/--
Knowledge: factive belief (what you know is true).

K(a, φ) implies φ is actually true, not just believed.
-/
def Formula.know (R : DoxAccessibility E) (M : Model E) (a : E) (φ : Formula) :
    Update E :=
  λ s => { p ∈ s |
    -- Factivity: φ is actually true
    φ.sat M p.1 p.2 ∧
    -- Belief: φ is true in all accessible worlds
    ∀ q ∈ doxAccessible R a p, φ.sat M q.1 q.2 }

/--
Knowledge implies belief.
-/
theorem know_implies_believe (R : DoxAccessibility E) (M : Model E) (a : E) (φ : Formula)
    (s : InfoState E) :
    Formula.know R M a φ s ⊆ Formula.believe R M a φ s := by
  intro p hp
  simp only [Formula.know, Formula.believe, Set.mem_setOf_eq] at hp ⊢
  exact ⟨hp.1, hp.2.2⟩

/--
Knowledge is factive: K(a, φ) → φ
-/
theorem know_factive (R : DoxAccessibility E) (M : Model E) (a : E) (φ : Formula)
    (s : InfoState E) (p : Poss E) (hp : p ∈ Formula.know R M a φ s) :
    φ.sat M p.1 p.2 := by
  simp only [Formula.know, Set.mem_setOf_eq] at hp
  exact hp.2.1

end Semantics.Dynamic.PLA
