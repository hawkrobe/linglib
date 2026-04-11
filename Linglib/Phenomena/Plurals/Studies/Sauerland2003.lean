import Linglib.Core.Mereology
import Linglib.Core.PrivativePair
import Linglib.Core.Number
import Linglib.Core.Semantics.Presupposition
import Linglib.Phenomena.Plurals.Multiplicity
import Linglib.Theories.Semantics.Presupposition.PhiFeatures

/-!
# Sauerland (2003): A New Semantics for Number
@cite{sauerland-2003}

Sauerland, U. (2003). A new semantics for number.
*Proceedings of SALT 13*, 258–275.

See also @cite{sauerland-anderssen-yatsushiro-2005} for the companion
chapter "The Plural is Semantically Unmarked."

## Core Insight

Number features are **presuppositional partial identity functions** on the
entity domain, ordered by `PrivativePair.specLevel`. The general
presuppositional framework (`phiPresup`, `sgSem`, `plSem`, etc.) is in
`Theories.Semantics.Presupposition.PhiFeatures`; this file applies it to
Sauerland's specific arguments about number semantics.

## Key Results (study-specific)

- Feature-Subset Principle = `specLevel` linear order (§2)
- Maximize Presupposition derives singular preference (§3)
- Coordination forces plural on non-atomic sums (§4)
- `every = JE ∘ DER`: decomposition into definite + atomic universal,
  with JE presupposing scope predicate definedness (§5)
- Multiplicity as presuppositional competition, not at-issue Horn scale (§6);
  bridge to `Multiplicity.PluralTheory.implicature`
-/

set_option autoImplicit false

namespace Phenomena.Plurals.Studies.Sauerland2003

open Mereology (Atom AlgClosure)
open Core (PrivativePair PhiFeatures)
open Core.Presupposition (PrProp)
open Presupposition.PhiFeatures

-- ============================================================================
-- §1  Presuppositional Denotations (re-exported from PhiFeatures)
-- ============================================================================

/-- The presupposition of [Sg] is mereological atomicity. -/
theorem sg_presup_eq_atom {E : Type*} [PartialOrder E] :
    (sgSem E).presup = Atom := rfl

/-- [Pl] is always defined — its presupposition is vacuous. -/
theorem pl_always_defined {E : Type*} (x : E) :
    (plSem E).defined x := trivial

/-- [Sg] is defined exactly at atoms. -/
theorem sg_defined_iff_atom {E : Type*} [PartialOrder E] (x : E) :
    (sgSem E).defined x ↔ Atom x := Iff.rfl

-- ============================================================================
-- §2  Feature-Subset Principle
-- ============================================================================

/-!
## §2: Feature-Subset Principle

Sauerland's principle (46): if F₁ and F₂ are presuppositional features
that can be inserted in the same syntactic position, their domains must
stand in a subset relationship.

This is a consequence of the `PrivativePair` structure: the three well-formed
cells are linearly ordered by `specLevel`, so their presuppositional domains
are necessarily nested (atoms ⊂ all entities).
-/

/-- Presuppositional domain nesting: the domain of [Sg] (atoms) is
    contained in the domain of [Pl] (all entities). This is the
    Feature-Subset Principle for number: dom(Sg) ⊆ dom(Pl). -/
theorem sg_domain_subset_pl {E : Type*} [PartialOrder E] (x : E) :
    (sgSem E).defined x → (plSem E).defined x :=
  fun _ => trivial

/-- The containment is strict: there exist non-atomic entities in
    dom(Pl) \ dom(Sg). -/
theorem sg_domain_strict_subset_pl {E : Type*} [SemilatticeSup E]
    (a b : E) (_ : Atom a) (_ : Atom b) (hne : a ≠ b) :
    (plSem E).defined (a ⊔ b) ∧ ¬(sgSem E).defined (a ⊔ b) :=
  ⟨trivial, fun hAtom => hne ((hAtom a le_sup_left).trans (hAtom b le_sup_right).symm)⟩

/-- The `specLevel` ordering on `PrivativePair` is the Feature-Subset
    Principle: more specified cells have strictly smaller presuppositional
    domains. -/
theorem feature_subset_is_spec_order :
    PrivativePair.maximal.specLevel > PrivativePair.intermediate.specLevel ∧
    PrivativePair.intermediate.specLevel > PrivativePair.minimal.specLevel :=
  PrivativePair.spec_strict_order

-- ============================================================================
-- §3  Maximize Presupposition
-- ============================================================================

/-!
## §3: Maximize Presupposition Derives Singular Preference

When the referent is atomic, [Sg]'s presupposition is satisfied. Since
[Sg] and [Pl] have the same assertive content (both are identity), and
[Sg] has a strictly stronger presupposition, Maximize Presupposition
(@cite{heim-1991}) blocks [Pl]: the speaker must use [Sg].

When the referent is non-atomic, [Sg]'s presupposition fails. [Pl]
(with its vacuous presupposition) is the only available option.

This directly connects to `violatesMP` in `Structural.lean`.
-/

/-- Same assertive content: [Sg] and [Pl] both assert `True`. -/
theorem sg_pl_same_assertion {E : Type*} [PartialOrder E] (x : E) :
    (sgSem E).assertion x ↔ (plSem E).assertion x :=
  Iff.rfl

/-- [Sg]'s presupposition is strictly stronger than [Pl]'s:
    dom(Sg) ⊂ dom(Pl). Given any non-atom, it witnesses the strict
    inclusion. -/
theorem sg_strictly_stronger {E : Type*} [PartialOrder E]
    (x : E) (hNotAtom : ¬Atom x) :
    (∀ y, (sgSem E).defined y → (plSem E).defined y) ∧
    (plSem E).defined x ∧ ¬(sgSem E).defined x :=
  ⟨fun _ _ => trivial, trivial, hNotAtom⟩

/-- **Maximize Presupposition for number**: at an atomic referent,
    using [Pl] is blocked because [Sg] is available with the same
    assertion and a satisfied, stronger presupposition.
    This is why "*John are here" is ungrammatical. -/
theorem mp_blocks_plural_at_atom {E : Type*} [PartialOrder E]
    (x : E) (hAtom : Atom x) :
    (sgSem E).defined x ∧
    (plSem E).defined x ∧
    ((sgSem E).assertion x ↔ (plSem E).assertion x) :=
  ⟨hAtom, trivial, Iff.rfl⟩

/-- At a non-atomic referent, [Sg] is undefined — only [Pl] is available.
    This is why "The books were lying on the table" requires plural. -/
theorem only_plural_at_nonatom {E : Type*} [PartialOrder E]
    (x : E) (hNotAtom : ¬Atom x) :
    ¬(sgSem E).defined x ∧ (plSem E).defined x :=
  ⟨hNotAtom, trivial⟩

-- ============================================================================
-- §4  Coordination and Agreement
-- ============================================================================

/-!
## §4: Coordination Forces Plural

For "Kai and Lina are playing": each conjunct is atomic (gets [Sg]),
but their mereological sum is non-atomic. The φ-head above the
coordination must bear [Pl] because [Sg]'s presupposition fails
on the non-atomic sum.
-/

section Coordination

variable {E : Type*} [SemilatticeSup E]

/-- A coordination of two distinct atoms produces a non-atom. -/
theorem coordination_nonatom (a b : E) (_ : Atom a) (_ : Atom b)
    (hne : a ≠ b) : ¬Atom (a ⊔ b) :=
  fun hAtom => hne ((hAtom a le_sup_left).trans (hAtom b le_sup_right).symm)

/-- Each conjunct individually satisfies [Sg]. -/
theorem conjuncts_singular (a b : E) (ha : Atom a) (hb : Atom b) :
    (sgSem E).defined a ∧ (sgSem E).defined b :=
  ⟨ha, hb⟩

/-- The coordination as a whole requires [Pl]:
    [Sg] fails on the sum, [Pl] is the only option. -/
theorem coordination_requires_plural (a b : E) (ha : Atom a) (hb : Atom b)
    (hne : a ≠ b) :
    ¬(sgSem E).defined (a ⊔ b) ∧ (plSem E).defined (a ⊔ b) :=
  only_plural_at_nonatom (a ⊔ b) (coordination_nonatom a b ha hb hne)

/-- Singular agreement with coordination is possible when the
    denotation is construed as atomic (e.g., "Strawberries and cream
    is on the menu" — the combination is a single dish). -/
theorem singular_coordination_when_atomic (x : E) :
    Atom x → (sgSem E).defined x :=
  id

end Coordination

-- ============================================================================
-- §5  Every = JE ∘ DER
-- ============================================================================

/-!
## §5: Decomposition of *every*

Sauerland decomposes *every* into two morphemes:

- **DER**: the definite determiner — selects the maximal element of the
  star-closed restrictor `*R`.
- **JE**: a universal quantifier restricted to **atoms** of a group
  individual, with an existence presupposition.

`⟦JE⟧(X)(P)` is defined iff every atom of X is in the domain of P;
where defined, it asserts that P holds of every atom of X.

The [Sg] feature on φ within JE's scope restricts quantification to
atoms — this is why *every* quantifies over atomic individuals.
-/

/-- JE: universal quantifier over atoms of a group (Sauerland's (30b)).

    `⟦JE⟧(X)(P)`:
    - **presupposes**: every element of X is atomic, AND P is defined
      at every atom of X (the scope predicate's presupposition projects
      universally — this is what derives presupposition projection under
      "every", cf. (33a–b))
    - **asserts**: P holds of every atom

    The atomicity restriction comes from the [Sg] feature in φ
    below JE. The domain-of-P presupposition is what makes "every"
    a presupposition hole: "every boy invited his sister" presupposes
    every boy has a unique sister. -/
def JE {E : Type*} [PartialOrder E]
    (atoms : List E) (P : E → Prop) (domP : E → Prop := fun _ => True) :
    PrProp E where
  presup := fun _ => (∀ a ∈ atoms, Atom a) ∧ (∀ a ∈ atoms, domP a)
  assertion := fun _ => ∀ a ∈ atoms, P a

/-- JE quantifies over atoms only — non-atoms are excluded by
    the [Sg] presupposition in φ's scope position. -/
theorem je_atomic_restriction {E : Type*} [PartialOrder E]
    (atoms : List E) (P : E → Prop) (domP : E → Prop) (w : E)
    (h : (JE atoms P domP).defined w) :
    ∀ a ∈ atoms, Atom a := h.1

/-- JE presupposes that the scope predicate is defined at every atom.
    This is what derives presupposition projection under "every":
    "Every boy invited his sister" presupposes each boy has a sister. -/
theorem je_presup_projects {E : Type*} [PartialOrder E]
    (atoms : List E) (P : E → Prop) (domP : E → Prop) (w : E)
    (h : (JE atoms P domP).defined w) :
    ∀ a ∈ atoms, domP a := h.2

/-- With a total scope predicate (no presupposition), JE's
    presupposition reduces to atomicity. -/
theorem je_total_reduces {E : Type*} [PartialOrder E]
    (atoms : List E) (P : E → Prop) (w : E) :
    (JE atoms P).defined w ↔ ∀ a ∈ atoms, Atom a :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ => trivial⟩⟩

-- ============================================================================
-- §6  Multiplicity Inference
-- ============================================================================

/-!
## §6: Multiplicity Inference

The "more than one" reading of bare plurals ("Emily fed giraffes" →
more than one giraffe) arises because [Sg] and [Pl] are presuppositional
alternatives with the same assertion. Using [Pl] when [Sg]'s presupposition
would be satisfied violates Maximize Presupposition. So using [Pl]
**implicates** that [Sg]'s presupposition fails — i.e., the referent
is non-atomic (more than one).

On the modern (2020s) account (@cite{delpinal-bassi-sauerland-2024}),
this is derived via presuppositional exhaustification (pex): pex over
{⟦Sg⟧, ⟦Pl⟧} presupposes the negation of [Sg]'s presupposition (= ¬Atom).
See `Theories/Semantics/Exhaustification/PresuppositionalExhaustification.lean`.

## Bridge to `Phenomena.Plurals.Multiplicity`

This is the **implicature** theory of multiplicity
(`Multiplicity.PluralTheory.implicature`): plural literally means "one or
more," and "more than one" arises as a pragmatic inference — specifically,
an inference from presuppositional competition (Maximize Presupposition),
not from at-issue scalar competition (Horn scales).

### Presuppositional vs at-issue competition

`Alternatives.Number.numberScale` models sg/pl as a Horn scale where
singular is the "stronger" alternative. But this is misleading on
Sauerland's analysis: [Sg] and [Pl] have *identical* at-issue content
(both are identity functions — `sg_pl_same_assertion`). There is no
at-issue strength difference. The competition is entirely in the
presuppositional dimension: [Sg] has the stronger *presupposition*
(atomicity), while [Pl]'s is vacuous.

This means number competition falls under `violatesMP` (presuppositional
competition: same assertion, different presupposition strength), NOT
under `violatesConversationalPrinciple` (at-issue competition: different
truth conditions). Both operators are defined in
`Theories/Semantics/Alternatives/Structural.lean`, and the distinction
between them is exactly Sauerland's theoretical contribution.
-/

/-- The multiplicity inference: using [Pl] implicates ¬Atom.

    When a speaker uses [Pl] in an upward-entailing context, the listener
    infers that [Sg]'s presupposition (atomicity) does not hold — hence
    the referent denotes more than one individual. -/
theorem multiplicity_inference {E : Type*} [PartialOrder E] (x : E)
    (hMP : (sgSem E).defined x → False) :
    ¬Atom x :=
  hMP

/-- The competition between [Sg] and [Pl] is presuppositional, not
    at-issue: they share their assertive content but differ in
    presupposition. This is the structural signature of Maximize
    Presupposition (same assertion + strictly ordered presuppositions),
    as opposed to scalar implicature (different assertions).

    Together with `sg_strictly_stronger`, this shows that number
    competition is governed by `violatesMP`, not by
    `violatesConversationalPrinciple`. -/
theorem number_competition_is_presuppositional {E : Type*} [PartialOrder E] :
    -- Same assertive content (NOT a scalar strength difference)
    (∀ (x : E), (sgSem E).assertion x ↔ (plSem E).assertion x) ∧
    -- Domain containment (presuppositional strength ordering)
    (∀ (x : E), (sgSem E).defined x → (plSem E).defined x) :=
  ⟨fun _ => Iff.rfl, fun _ _ => trivial⟩

/-- Sauerland 2003 is the implicature theory of multiplicity: the "more
    than one" inference is pragmatic (derived by Maximize Presupposition
    or pex), not a semantic entailment of the plural morpheme. -/
theorem sauerland_is_implicature_theory :
    Multiplicity.PluralTheory.implicature ≠
    Multiplicity.PluralTheory.ambiguity ∧
    Multiplicity.PluralTheory.implicature ≠
    Multiplicity.PluralTheory.homogeneity := by
  constructor <;> intro h <;> nomatch h

/-- The monotonicity sensitivity follows from the pragmatic nature of
    the inference: scalar/presuppositional inferences arise in UE
    but not DE contexts. Cross-reference: `Multiplicity.fedGiraffes_monotonicity`. -/
theorem multiplicity_monotonicity_from_competition {E : Type*} [PartialOrder E]
    (x : E) :
    -- In UE: if [Sg] is satisfied, MP blocks [Pl] → using [Pl] implicates ¬Atom
    (Atom x → (sgSem E).defined x) ∧
    -- In DE: entailment reverses, so the weaker [Pl] is now "stronger"
    -- in the DE sense — no competition, no inference
    ((plSem E).defined x) :=
  ⟨id, trivial⟩

end Phenomena.Plurals.Studies.Sauerland2003
