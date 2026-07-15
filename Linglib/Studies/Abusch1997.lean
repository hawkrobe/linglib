import Linglib.Semantics.Tense.Basic
import Linglib.Semantics.Tense.DeRe
import Linglib.Semantics.Dynamic.PLA.Epistemic
import Linglib.Semantics.Reference.Acquaintance
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.Abusch1997

/-!
# [abusch-1997]: Sequence of Tense and Temporal de re
[abusch-1997] [sharvit-2003] [heim-1994-comments]
[lewis-1979-attitudes] [cresswell-vonstechow-1982]

[abusch-1997]'s theory: tense morphemes are temporal pronouns
(variables with presupposed constraints and binding modes). The key
innovation is **temporal de re**: tense can take wide scope over
attitude operators via res movement, just as DPs can scope out of
attitude complements.

Two derivation styles coexist in this file:

1. **Value-level shadow** (`abusch_derives_*` against `TensePronoun.fullPresupposition`):
   tense pronoun + `Core.Order.holds` + temporal assignment.
   Captures Abusch's predictions at the value level without committing
   to the centered-world architecture. Cheap, presupposition-free.

2. **Centered-world substrate** (`abusch_derives_*_via_acquaintance` /
   `_full` / `_full_metaphysical` against
   `Tense.DeRe.TemporalDeReReading`): `Intension (KContext)
   Time` time-concept + holder-context base anchor + modal-alternative
   quantification over a `Set (WorldTimeIndex W Time)`. The Abusch §3 +
   def. 13 architecture, faithful to the [lewis-1979-attitudes] /
   [cresswell-vonstechow-1982] centered-world reduction of de re.
   The two styles are bridged by
   `Tense.DeRe.TemporalDeReReading.isFelicitousWith_iff_tensePronoun_fullPresupposition`.

The substrate is modal-base-agnostic and holder-now-honest:
`holderContext.time` is the holder's now (per §7 ULC), and
`IsRigidAcrossAlternatives` takes a `Set (WorldTimeIndex)` parameter
(with `metaphysicalAlternatives` / `doxasticAlternatives` convenience
constructors). See `Tense/DeRe.lean` docstring for what's deferred
(LF rewrite operator, etc.).

## Core Mechanisms

1. **Tense as pronoun**: `TensePronoun` (in `Tense`) with
   variable index, constraint, and binding mode.
2. **Upper Limit Constraint (ULC)**: stated by [abusch-1997] §7
   ("the now of an epistemic alternative is an upper limit for the
   denotation of tenses"); presuppositional construal due to
   [heim-1994-comments], endorsed by Abusch 1997 fn 20. Lives in
   `Semantics/Tense/Basic.lean` as `upperLimitConstraint`,
   formalized at the value level as `embeddedR ≤ matrixE`. **Note:**
   this value-level reduction strips the modal-alternative
   quantification the original formulation carries; making the modal
   layer explicit (over `HistoricalAlternatives W Time` à la [klecha-2016])
   is deferred.
3. **Temporal de re**: tense variable in the res position of an
   attitude. The value-level shadow uses `TensePronoun.fullPresupposition`:
   constraint applied to (resolved time, eval time). The LF rewrite +
   acquaintance-relation machinery (Lewis 1979 / Cresswell-von Stechow
   1982) is not formalized here.
4. **Eval-time shift via attitude embedding**: the substrate primitives
   are `Tense.evalTime_shifts_under_embedding` and
   `updateTemporal`. Abusch's "relation transmission" (feature passing
   of relation variables PAST/PRES across embedding) is *not* what this
   file currently captures — we only model the value-level eval-time
   update.

## Derivation Theorems

- Shifted reading: free past variable with presupposition against eval time
- Simultaneous reading: bound variable receives matrix event time
- Double-access: indexical present + attitude binding (placeholder; the
  full Abusch derivation involves doxastic alternatives + acquaintance
  relations + the rigid-present presupposition, not formalized here)
- Temporal de re: res movement for wide-scope tense

## Limitations

- Relative clause tense: [sharvit-2003]'s challenge (the mechanism
  doesn't extend straightforwardly to relative clauses where the tense
  takes the perspective of a participant)
- Modal-tense interaction: not addressed in [abusch-1997]'s
  framework (see [klecha-2016] for a successor)
- Counterfactual tense: not addressed
- Counterpart-relation isomorphism [abusch-1997] §12 invokes for
  the double-access reading derivation (the constraint that actual
  and belief worlds be temporally isomorphic, eliminating most of the
  4 cells in the DAR diagram on p. 43): not formalized
- Modal-layer ULC formulation: see Core Mechanism 2 above

## PLA Belief Reports and Conceptual Covers

The individual-side counterpart of temporal de re, formalized here as
the substrate the temporal account parallels. A PLA epistemic layer
([dekker-2012] ch. 4) supplies doxastic accessibility, belief/knowledge
tests, and Aloni-style conceptual covers ([aloni-2001]) — sets of
concepts ("ways of thinking about" entities) relative to which "knowing
who" and de re/de dicto are evaluated. Covers dissolve [quine-1956]'s
Ortcutt puzzle: Ralph believing "the man in the brown hat is a spy" and
"the man at the beach is not a spy" (both Ortcutt) is consistent once
the beliefs are indexed to non-overlapping covers. `isAcquaintedWith`
here and the temporal-de-re acquaintance relation are the same
`Reference.Acquaintance` substrate at different indices, making Abusch's
individual ↔ temporal de re parallel true by construction
(`pla_isAcquaintedWith_unifies_with_polymorphic`).

-/

open Time

namespace Abusch1997

open Tense
open Data.Examples (LinguisticExample)

-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- [abusch-1997] derives the shifted reading: a free past
    variable with presupposition checked against the (shifted) eval
    time. The past constraint gives R < evalTime = matrixE.

    Note: the proof closes via `embeddedFrame.isPast`'s definition,
    which only requires `tp.resolve g < matrixFrame.eventTime`. The
    `tp.constraint = .past` condition is what *Abusch's theory* says
    licenses this reading, but it isn't load-bearing in this proof —
    the conclusion follows for any tense pronoun whose resolution is
    below the matrix event time. A full Abusch derivation would
    project through `Core.Order.holds tp.constraint` from the binding mode. -/
theorem abusch_derives_shifted {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hPresup : tp.resolve g < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast_def]
  exact hPresup

/-- [abusch-1997] derives the simultaneous reading: a bound
    variable receives the matrix event time via lambda abstraction. -/
theorem abusch_derives_simultaneous {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hBind : tp.resolve g = matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPresent := by
  simp only [embeddedFrame, ReichenbachFrame.isPresent, hBind]

/-- [abusch-1997] derives the simultaneous reading via the bound
    variable mechanism: updating the temporal assignment so the tense
    variable receives matrix E. -/
theorem abusch_derives_simultaneous_via_binding {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time) :
    tp.resolve (updateTemporal g tp.varIndex matrixFrame.eventTime) =
    matrixFrame.eventTime :=
  tp.bound_resolve_eq_binder g matrixFrame.eventTime

/-- [abusch-1997]'s double-access *placeholder*: indexical present
    requires truth at BOTH speech time (indexical rigidity) AND matrix
    event time (attitude accessibility). The full Abusch derivation
    involves doxastic alternatives + acquaintance relations + the
    rigid-present presupposition; this theorem only states the surface
    conjunction. -/
theorem abusch_derives_double_access {Time : Type*}
    (p : Time → Prop) (speechTime matrixEventTime : Time)
    (h_speech : p speechTime) (h_matrix : p matrixEventTime) :
    doubleAccess p speechTime matrixEventTime :=
  ⟨h_speech, h_matrix⟩

/-- [abusch-1997] derives temporal de re: the tense variable in
    res position is evaluated in the matrix context, giving wide-scope
    temporal reference. When the resolved referent satisfies the past
    constraint against the (matrix-shifted) eval time, the de re reading
    is felicitous.

    Value-level shadow: this theorem checks `TensePronoun.fullPresupposition`,
    not Abusch's actual centered-proposition rule (paper def. 13). The
    `g` here would, in the full account, be a temporal assignment shifted
    by the attitude verb to put the matrix event time at `tp.evalTimeIndex`. -/
theorem abusch_derives_temporal_de_re {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (hPast : tp.constraint = Tense.past)
    (hBefore : tp.resolve g < tp.evalTime g) :
    tp.fullPresupposition g := by
  simp only [TensePronoun.fullPresupposition, hPast, Tense.past, Core.Order.holds_before]
  exact hBefore


/-! ### PLA belief reports and conceptual covers

The entity-side de re machinery that the temporal account parallels
([dekker-2012] ch. 4): a doxastic-accessibility relation over PLA
possibilities, belief/knowledge as eliminative tests, and Aloni-style
conceptual covers ([aloni-2001]).

De re belief ("John believes *of Mary* that she is smart") fixes the
individual rigidly across the agent's belief worlds; de dicto belief
("John believes *the winner* is smart") tracks whoever satisfies a
description in each world. A conceptual cover is a set of concepts that
covers the domain and is functional per possibility — the agent's
available "ways of thinking about" entities. -/

section

open Classical
open _root_.PLA

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

This is the PLA-indexed instance of the polymorphic
`Semantics.Reference.Acquaintance.Cover` substrate (`Acquaintance.Cover (Poss E) E`).
The two are definitionally equal — `Cover E` is the PLA-side name.
-/
abbrev Cover (E : Type*) := Set (Concept E)

/--
A cover is exhaustive if every entity is picked out by some concept in
the cover (at every possibility). PLA-specific universal-domain wrapper
around `Acquaintance.Cover.isExhaustiveOn _ Set.univ`.
-/
def Cover.isExhaustive (C : Cover E) : Prop :=
  Semantics.Reference.Acquaintance.Cover.isExhaustiveOn C Set.univ

/--
The name cover: rigid concepts for each entity. PLA-side reference to
the polymorphic `Semantics.Reference.Acquaintance.nameCover` at index
`Idx := Poss E`. Definitionally equal; the polymorphic version is
preferred in new proofs (this `abbrev` exists for PLA-literature
readers familiar with the original naming).
-/
abbrev nameCover (dom : Set E) : Cover E :=
  Semantics.Reference.Acquaintance.nameCover (Idx := Poss E) dom

/--
The variable cover: concepts from variable assignments.
This is more "de dicto" - thinking via variable bindings.
-/
def variableCover : Cover E :=
  { Concept.fromVar i | i : VarIdx }


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

/-! #### Quine's Ortcutt puzzle
[quine-1956]

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


/-! #### Observation 20: quantifier scope and belief

[dekker-2012] Observation 20 (Quantifier Import and Export, p.95):
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
Observation 20 (wide → narrow): Wide scope implies narrow scope (always holds).

∃x_C B(r, Sx) → B(r, ∃x_C Sx)

If there's a specific concept c such that Ralph believes P(c),
then Ralph believes that something satisfies P.
-/
theorem obs20_wide_implies_narrow (R : DoxAccessibility E) (M : Model E)
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
Observation 20 (equivalence characterization): Wide and narrow scope
are equivalent iff there exists a uniform witnessing concept.

The narrow → wide direction requires Skolemization: turning per-world
witnesses (∀q, ∃c) into a uniform witness (∃c, ∀q). This holds when:
- The cover is finite and doxastic state is finite (by pigeonhole)
- The cover satisfies a "tracking" condition (concepts persist across worlds)

We state the precise equivalence condition rather than assuming it.
-/
theorem obs20_equiv_iff_uniform_witness (R : DoxAccessibility E) (M : Model E)
    (agent : E) (C : Cover E) (pred : String) (s : InfoState E) (p : Poss E)
    (hp : p ∈ s) :
    p ∈ believeExistsWide R M agent C pred s ↔
    p ∈ s ∧ ∃ c ∈ C, ∀ q ∈ doxAccessible R agent p, M.interp pred [c q] := by
  simp only [believeExistsWide, Set.mem_setOf_eq]


/-! #### Observation 21: knowing who is cover-relative

[dekker-2012] Observation 21 (Knowing and not Knowing Who, p.97):
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
Observation 21: Knowing who is cover-relative.

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
Knowing who under one cover does not transfer to another cover.

If the agent knows who x is under cover C₁, this does NOT imply
they know who x is under a different cover C₂.

This is the formal content of the Hesperus/Phosphorus puzzle:
the ancients knew "who Hesperus is" under an observational cover
but not under an astronomical cover.
-/
theorem knowsWho_not_transferable (R : DoxAccessibility E) (agent individual : E)
    (_C₁ C₂ : Cover E) (p : Poss E)
    (_hknows : knowsWho R agent individual _C₁ p)
    -- No concept in C₂ rigidly tracks individual across belief worlds
    (hno_rigid : ∀ c ∈ C₂, c p = individual →
      ∃ q ∈ doxAccessible R agent p, c q ≠ individual) :
    ¬knowsWho R agent individual C₂ p := by
  intro ⟨c₂, hc₂, hpicks₂, hunif₂⟩
  obtain ⟨q, hq, hneq⟩ := hno_rigid c₂ hc₂ hpicks₂
  exact hneq (hunif₂ q hq)


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
  simp only [believeExistsWithCover, nameCover,
    Semantics.Reference.Acquaintance.nameCover, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, c, ⟨e, he, hc⟩, hall⟩
    refine ⟨hp, e, he, ?_⟩
    intro q hq
    specialize hall q hq
    simp only [hc, Intensional.Intension.rigid] at hall
    exact hall
  · intro ⟨hp, e, he, hall⟩
    refine ⟨hp, Intensional.Intension.rigid e, ⟨e, he, rfl⟩, ?_⟩
    intro q hq
    simp only [Intensional.Intension.rigid]
    exact hall q hq


/--
Acquaintance requirement (Russell): De re belief requires acquaintance.

You can only have de re beliefs about entities you're "acquainted with"
(entities in your conceptual cover). PLA-side reference to
`Semantics.Reference.Acquaintance.isAcquaintedWith` at the PLA index
`Idx := Poss E`. Definitionally equal — the abbrev preserves the
PLA-literature naming.
-/
abbrev isAcquaintedWith (individual : E) (C : Cover E) (p : Poss E) : Prop :=
  Semantics.Reference.Acquaintance.isAcquaintedWith individual C p

/--
De re belief presupposes acquaintance (relative to a cover).
-/
def believeDeReWithAcquaintance (R : DoxAccessibility E) (M : Model E)
    (agent : E) (C : Cover E) (individual : E) (pred : String) : Update E :=
  λ s => { p ∈ s |
    -- Presupposition: agent is acquainted with individual
    isAcquaintedWith individual C p ∧
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

end

-- ════════════════════════════════════════════════════════════════
-- § Centered-World Substrate Derivations
-- ════════════════════════════════════════════════════════════════

/-- [abusch-1997]'s temporal de re via the centered-world substrate
    (`Semantics/Tense/DeRe.lean`): any `TemporalDeReReading`
    whose actual res-time precedes the holder's now satisfies the past
    constraint. Value-level felicity reduces to the actualRes ordering;
    rigidity of the concept (= acquaintance-anchored res reading) is
    not required for the value-level shadow. -/
theorem abusch_derives_temporal_de_re_via_acquaintance
    {W E P Time : Type*} [LinearOrder Time]
    (dr : Tense.DeRe.TemporalDeReReading W E P Time)
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.IsFelicitousWith Tense.past :=
  (Core.Order.holds_before dr.actualRes dr.holderContext.time).mpr hBefore

/-- [abusch-1997]'s temporal de re with **modal-alternative
    quantification** (substrate-level lift of the §3 p. 9 base-world
    condition): the time-concept identifies the same time across an
    `alternatives : Set (WorldTimeIndex W Time)`. The substrate is
    modal-base-agnostic; this theorem holds for any alternative-set
    the consumer supplies (doxastic, metaphysical, or other). The
    full `IsAbuschFelicitous` predicate combines the value-level past
    constraint with this modal rigidity.

    A rigid time-concept (constant intension) discharges the modal
    rigidity automatically — Abusch's de re reading is satisfied "for
    free" when the res is identified by a name-like rigid concept. -/
theorem abusch_derives_temporal_de_re_full
    {W E P Time : Type*} [LinearOrder Time]
    (dr : Tense.DeRe.TemporalDeReReading W E P Time)
    (hRigid : Intensional.Intension.IsRigid dr.concept)
    (alternatives : Set (Intensional.WorldTimeIndex W Time))
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.IsAbuschFelicitous alternatives Tense.past := by
  refine ⟨(Core.Order.holds_before dr.actualRes dr.holderContext.time).mpr hBefore, ?_⟩
  exact Tense.DeRe.TemporalDeReReading.isRigidAcrossAlternatives_of_isRigid
    dr hRigid alternatives

/-- **Metaphysical-instantiation specialization** of
    `abusch_derives_temporal_de_re_full`. Recovers the legacy
    `HistoricalAlternatives`-based formulation as a corollary at the
    `metaphysicalAlternatives` instance, demonstrating backward
    compatibility with Klecha 2016 DOX-shaped reasoning. -/
theorem abusch_derives_temporal_de_re_full_metaphysical
    {W E P Time : Type*} [LinearOrder Time]
    (dr : Tense.DeRe.TemporalDeReReading W E P Time)
    (hRigid : Intensional.Intension.IsRigid dr.concept)
    (history : HistoricalAlternatives W Time)
    (hBefore : dr.actualRes < dr.holderContext.time) :
    dr.IsAbuschFelicitous (dr.metaphysicalAlternatives history) Tense.past :=
  abusch_derives_temporal_de_re_full dr hRigid _ hBefore

/-- **Individual ↔ temporal de re unification**: the PLA-literature
    `isAcquaintedWith` alias above (entity-side, individual de re) and the
    polymorphic `Reference.Acquaintance.isAcquaintedWith` are the same
    predicate at the PLA index `Idx := Poss E`. Provable by `Iff.rfl`
    because the alias is a definitional wrapper (`abbrev`) of the
    polymorphic version.

    The *content* of the theorem is structural — it shows the de re
    reading proved about *individuals* and the de re reading
    `TemporalDeReReading` exposes for *times* are instantiations of
    the same acquaintance substrate, making true [abusch-1997]'s
    p. 6 prose claim ("To apply the same machinery to de re belief,
    a further constraint is required") via the `Acquaintance`
    polymorphism. -/
theorem pla_isAcquaintedWith_unifies_with_polymorphic
    {E : Type*} (individual : E)
    (C : Cover E)
    (p : PLA.Poss E) :
    isAcquaintedWith individual C p ↔
    Semantics.Reference.Acquaintance.isAcquaintedWith individual C p :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § Empirical Data: Abusch's SOT Diagnostic Sentences
-- ════════════════════════════════════════════════════════════════

/-! Reichenbach frames for the canonical Abusch-tradition SOT
    diagnostics: past-under-past (simultaneous + shifted), present-
    under-past (double-access), future-under-past (would), the ULC
    foil (forward-shifted), and temporal de re. Each embedded frame
    is constructed via the `embeddedFrame` / `simultaneousFrame` /
    `shiftedFrame` substrate operators (per CLAUDE.md
    "Theory-hub denotation as study-file constraint") rather than
    hand-stipulating S/P/R/E records. -/

/-- Matrix frame for "John said..." (past tense, perfective).
    Speech time S = 0, saying event at t = -2. Root clause: P = S;
    perfective: E = R. -/
def matrixSaid : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2

/-- "Mary was sick" — SIMULTANEOUS reading. Embedded P = matrix E = -2,
    R' = E_matrix = -2: Mary is sick at the time of the saying. -/
def embeddedSickSimultaneous : ReichenbachFrame ℤ :=
  simultaneousFrame matrixSaid (-2)

/-- "Mary was sick" — SHIFTED reading. R' = -5 < E_matrix: Mary was
    sick before the saying. -/
def embeddedSickShifted : ReichenbachFrame ℤ :=
  shiftedFrame matrixSaid (-5) (-5)

/-- "Mary is sick" (present-under-past) — DOUBLE-ACCESS reading.
    Embedded P = matrix E = -2, R' = -2, E = 0 (speech time):
    Mary is sick now AND the sickness is relevant at the time of saying. -/
def embeddedSickPresent : ReichenbachFrame ℤ :=
  embeddedFrame matrixSaid (-2) 0

/-- "Mary would leave" (future-under-past). "Would" = PAST + FUTURE:
    the leaving is after the saying. R' = -1 > E_matrix. -/
def embeddedWouldLeave : ReichenbachFrame ℤ :=
  embeddedFrame matrixSaid (-1) (-1)

/-- Hypothetical FORWARD-SHIFTED frame (ULC foil, §7). R' = -1 >
    E_matrix = -2: sick AFTER the saying. **Predicted not to exist as
    a reading** per Abusch's Upper Limit Constraint. Structurally
    coincides with `embeddedWouldLeave`'s record — the Reichenbach
    encoding cannot distinguish "ULC violation" from "valid future
    reading"; only the analyst's intent and the sentence's actual
    meaning do. -/
def embeddedSickForwardShifted : ReichenbachFrame ℤ :=
  embeddedFrame matrixSaid (-1) (-1)

/-- "John believed it was raining" — TEMPORAL DE RE. The rain event
    is located at -3 via the actual world (de re), not in John's
    belief worlds (de dicto). Embedded P = -2, R = E = -3. -/
def temporalDeRe : ReichenbachFrame ℤ :=
  embeddedFrame matrixSaid (-3) (-3)


-- ════════════════════════════════════════════════════════════════
-- § Per-Datum Verifications
-- ════════════════════════════════════════════════════════════════

/-- The simultaneous frame is `isPresent` (R = P).
    Per Abusch: a bound variable receives matrix E. -/
theorem abusch_derives_embeddedSickSimultaneous :
    embeddedSickSimultaneous.isPresent := rfl

/-- The shifted frame is `isPast` (R < P).
    Per Abusch: a free past variable below the matrix event time. -/
theorem abusch_derives_embeddedSickShifted :
    embeddedSickShifted.isPast := by
  simp only [ReichenbachFrame.isPast_def, embeddedSickShifted, shiftedFrame,
    Tense.embeddedFrame, matrixSaid]; omega

/-- The matrix "said" frame is perfective (E = R). -/
theorem matrixSaid_is_perfective : matrixSaid.isPerfective := rfl

/-- The shifted embedded frame is perfective (E = R). -/
theorem embeddedShifted_is_perfective : embeddedSickShifted.isPerfective := rfl

/-- Forward-shifted reading violates ULC: R' > E_matrix is not allowed. -/
theorem forwardShifted_violates_ulc :
    ¬ upperLimitConstraint
      embeddedSickForwardShifted.referenceTime
      matrixSaid.eventTime := by decide

/-- Simultaneous reading satisfies ULC: R' ≤ E_matrix. -/
theorem simultaneous_satisfies_ulc :
    upperLimitConstraint
      embeddedSickSimultaneous.referenceTime
      matrixSaid.eventTime := by decide

/-- Shifted reading satisfies ULC: R' < E_matrix. -/
theorem shifted_satisfies_ulc :
    upperLimitConstraint
      embeddedSickShifted.referenceTime
      matrixSaid.eventTime := by decide


end Abusch1997
