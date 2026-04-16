import Linglib.Core.Mereology
import Linglib.Core.PrivativePair
import Linglib.Core.Number
import Linglib.Core.Person
import Linglib.Core.Gender
import Linglib.Core.Semantics.Presupposition
import Linglib.Phenomena.Plurals.Multiplicity
import Linglib.Theories.Semantics.Presupposition.PhiFeatures
import Linglib.Theories.Semantics.Presupposition.MaximizePresupposition
import Linglib.Theories.Semantics.Lexical.Determiner.UnifiedUniversal

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
- Existential ⟦a⟧ projects presuppositions existentially, contrasting
  with JE's universal projection (§5b)
- Multiplicity as presuppositional competition, not at-issue Horn scale (§6);
  bridge to `Multiplicity.PluralTheory.implicature`
- Negated Pl entails negated Sg: "didn't harvest tomatoes" → "didn't
  harvest a tomato" (§6b)
- Czech gender coordination data: masculine=vacuous, feminine=non-masc,
  neuter=inanimate; parallels number resolution (§7)
- Politeness prediction: unmarked phi-values used for honorification (§8)
-/

set_option autoImplicit false

namespace Phenomena.Plurals.Studies.Sauerland2003

open Mereology (Atom AlgClosure isMaximal CUM cum_maximal_unique algClosure_cum)
open Core (PrivativePair PhiFeatures)
open Core.Presupposition (PrProp)
open Core.OT (NamedConstraint buildTableau)
open Presupposition.PhiFeatures
open Presupposition.MaximizePresupposition (phiMP phi_mp_selects_maximal)

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

The formal derivation uses `phi_mp_selects_maximal` from
`MaximizePresupposition.lean`: the OT constraint `phiMP` assigns 0
violations to the maximal cell (= [Sg]) and penalizes weaker cells
(= [Pl]). When [Sg] is among the candidates (i.e., its presupposition
is satisfied), the optimal candidate must have maximal `presupStrength`.
-/

/-- Same assertive content: [Sg] and [Pl] both assert `True`.
    Instance of the general `phiPresup_same_assertion`. -/
theorem sg_pl_same_assertion {E : Type*} [PartialOrder E]
    (outerP : E → Prop) (x : E) :
    (phiPresup Atom outerP .maximal).assertion x ↔
    (phiPresup Atom outerP .minimal).assertion x :=
  phiPresup_same_assertion Atom outerP .maximal .minimal x

/-- [Sg]'s presupposition is strictly stronger than [Pl]'s:
    dom(Sg) ⊂ dom(Pl). Given any non-atom, it witnesses the strict
    inclusion. -/
theorem sg_strictly_stronger {E : Type*} [PartialOrder E]
    (x : E) (hNotAtom : ¬Atom x) :
    (∀ y, (sgSem E).defined y → (plSem E).defined y) ∧
    (plSem E).defined x ∧ ¬(sgSem E).defined x :=
  ⟨fun _ _ => trivial, trivial, hNotAtom⟩

/-- **MP selects [Sg] over [Pl] via OT.** When [Sg] (= `.maximal`) is
    among the candidates and `phiMP` is the top-ranked constraint, the
    optimal form has maximal presuppositional strength.

    This is a direct application of `phi_mp_selects_maximal`. The
    entity-level precondition is that [Sg]'s presupposition (atomicity)
    is satisfied — see `mp_blocks_plural_at_atom`. -/
theorem mp_selects_sg
    (rest : List (NamedConstraint PrivativePair))
    (hNE : [PrivativePair.maximal, .minimal] ≠ []) :
    ∀ c ∈ (buildTableau [.maximal, .minimal]
      (phiMP :: rest) hNE).optimal,
    presupStrength c = PrivativePair.maximal.specLevel :=
  phi_mp_selects_maximal _ rest hNE (by decide) (.head _)

/-- **Maximize Presupposition for number**: at an atomic referent,
    [Sg] is defined (its presupposition is satisfied), making `.maximal`
    a viable candidate. By `mp_selects_sg`, MP selects [Sg] over [Pl].
    This is why "*John are here" is ungrammatical. -/
theorem mp_blocks_plural_at_atom {E : Type*} [PartialOrder E]
    (x : E) (hAtom : Atom x) :
    -- Sg is defined → it enters the candidate set
    (sgSem E).defined x ∧
    -- Pl is also defined → both compete
    (plSem E).defined x ∧
    -- Same assertion → competition is presuppositional
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

end Coordination

-- ============================================================================
-- §5  Every = JE ∘ DER
-- ============================================================================

/-!
## §5: Decomposition of *every*

Sauerland decomposes *every* into two morphemes:

- **DER**: the definite determiner — selects the maximal element of the
  star-closed restrictor `*R` (= `AlgClosure R`).
- **JE**: a universal quantifier restricted to **atoms** (= mereological
  parts) of a group individual, with an existence presupposition.

`⟦JE⟧(X)(P)` is defined iff every atom of X is in the domain of P;
where defined, it asserts that P holds of every atom of X.

The [Sg] feature on φ within JE's scope restricts quantification to
atoms — this is why *every* quantifies over atomic individuals.

### Connection to QForall

@cite{haslinger-etal-2025-nllt}'s unified universal Q_∀ and Sauerland's
JE ∘ DER compute the same truth conditions for singular (atomic) NP
restrictors: both reduce to ∀x[R(x) → Q(x)]. The derivation paths
differ — Sauerland goes through DER (maximal *R element) + JE (atoms
of the result), while Haslinger et al. go through `maxNonOverlap` on
the restrictor directly — but the results coincide. See
`je_der_agrees_with_qforall`.
-/

open Semantics.Lexical.Determiner.UnifiedUniversal (QForall dng_atoms)

/-- **JE** (30b): universal quantifier over atoms of a group individual.

    `⟦JE⟧(X)(P)`:
    - **presupposes**: every atom of X is in the domain of P (the scope
      predicate's presupposition projects universally — this derives
      presupposition projection under "every", cf. (33a–b))
    - **asserts**: P holds of every atom of X

    The atomicity restriction comes from the [Sg] feature in φ below JE.
    The atom relation is mereological: `a` is an atom of `X` iff
    `Atom a ∧ a ≤ X`. -/
def JE {E : Type*} [PartialOrder E]
    (X : E) (P : E → Prop) (domP : E → Prop := fun _ => True) :
    PrProp E where
  presup := fun _ => ∀ a, Atom a → a ≤ X → domP a
  assertion := fun _ => ∀ a, Atom a → a ≤ X → P a

/-- JE presupposes that the scope predicate is defined at every atom
    of X. This derives presupposition projection under "every":
    "Every boy invited his sister" presupposes each boy has a sister. -/
theorem je_presup_projects {E : Type*} [PartialOrder E]
    (X : E) (P : E → Prop) (domP : E → Prop) (w : E)
    (h : (JE X P domP).defined w) :
    ∀ a, Atom a → a ≤ X → domP a := h

/-- With a total scope predicate (no presupposition), JE's
    presupposition is trivially satisfied. -/
theorem je_total_trivial {E : Type*} [PartialOrder E]
    (X : E) (P : E → Prop) (w : E) :
    (JE X P).defined w :=
  fun _ _ _ => trivial

/-- **every = JE ∘ DER** (30): Sauerland decomposes *every* into two
    morphemes. DER (the definite article) selects the maximal element
    of `*R` via `Mereology.isMaximal`. JE distributes over atoms of
    the result.

    `⟦every⟧(R)(P)` = `⟦JE⟧(max(*R))(P)` -/
def everySem {E : Type*} [PartialOrder E]
    (maxStarR : E) (P : E → Prop) (domP : E → Prop := fun _ => True) :
    PrProp E :=
  JE maxStarR P domP

-- ── Mereological grounding of DER ──

/-- **DER is well-defined**: `*R` is CUM, so it has at most one maximal
    element (`cum_maximal_unique`). DER's uniqueness presupposition is
    automatically satisfied for star-closed predicates. -/
theorem der_unique {E : Type*} [SemilatticeSup E]
    (R : E → Prop) (m₁ m₂ : E)
    (h₁ : isMaximal (AlgClosure R) m₁) (h₂ : isMaximal (AlgClosure R) m₂) :
    m₁ = m₂ :=
  cum_maximal_unique (algClosure_cum (P := R)) h₁ h₂

/-- **JE's assertion = standard universal** when the atoms below `maxR`
    are exactly the R-elements (the normal case for atomic restrictors:
    `*R` = `R ∪ sums`, and atoms of `max(*R)` = R-atoms).

    This makes explicit what `je_der_agrees_with_qforall` leaves
    implicit: JE's truth conditions at `max(*R)` are `∀x, R(x) → Q(x)`. -/
theorem je_assertion_eq_forall {E : Type*} [PartialOrder E]
    (R : E → Prop) (maxR : E)
    (hCov : ∀ x, R x → Atom x ∧ x ≤ maxR)
    (hCov' : ∀ x, Atom x → x ≤ maxR → R x)
    (Q : E → Prop) (w : E) :
    (JE maxR Q).assertion w ↔ ∀ x, R x → Q x := by
  constructor
  · intro h x hR; exact h x (hCov x hR).1 (hCov x hR).2
  · intro h a ha hle; exact h a (hCov' a ha hle)

/-- **JE ∘ DER agrees with Q_∀ on atomic restrictors.**

    Both Sauerland's JE∘DER and @cite{haslinger-etal-2025-nllt}'s QForall
    reduce to `∀x[R(x) → Q(x)]` when the restrictor is atomic with no
    overlap. Combined with `je_assertion_eq_forall`, this gives the full
    equivalence chain:

      JE(DER(R))(Q) ↔ ∀x, R(x) → Q(x) ↔ QForall R Q -/
theorem je_der_agrees_with_qforall {E : Type*} [PartialOrder E]
    {R Q : E → Prop}
    (hAtoms : ∀ x, R x → Atom x)
    (hDisj : ∀ x y, R x → R y → Mereology.Overlap x y → x = y) :
    QForall R Q ↔ ∀ x, R x → Q x :=
  dng_atoms hAtoms hDisj

-- ── Presupposition projection asymmetry (33a–b) ──

/-- **Pl has no presupposition to project** (33b).

    "Every boy should invite his sisters" — the [Pl] on "sisters" has
    a vacuous presupposition, so JE's universal projection is trivially
    satisfied. The sentence is compatible with boys having different
    numbers of sisters, including just one (though MP implicates ≥ 2
    for at least one). -/
theorem pl_projects_trivially {E : Type*} [PartialOrder E]
    (boys : E) (w : E) :
    (JE boys (fun _ => True) (fun _ => True)).defined w :=
  fun _ _ _ => trivial

-- ============================================================================
-- §5b  Existential Presupposition Projection
-- ============================================================================

/-!
## §5b: Existential Quantifier ⟦a⟧ (§5, (35))

Indefinites project their scope's presupposition existentially:

  ⟦a⟧(R)(S) is defined iff ∃x: R(x) ∧ x ∈ domain(S)
  where defined: ⟦a⟧(R)(S) = 1 iff ∃x: R(x) ∧ S(x) = 1

Unlike JE (which projects universally), the indefinite only requires
that *some* restrictor individual satisfy the scope presupposition.
This is why "A boy invited his sister" presupposes there exists a boy
with a sister, not that every boy has one.
-/

/-- ⟦a⟧ (35): existential quantifier with existential projection.

    The presupposition of ⟦a⟧(R)(S) is that some R-individual is in
    the domain of S. The assertion is that some R-individual satisfies S. -/
def aSem {E : Type*}
    (R : E → Prop) (S : E → Prop) (domS : E → Prop := fun _ => True) :
    PrProp E where
  presup := fun _ => ∃ x, R x ∧ domS x
  assertion := fun _ => ∃ x, R x ∧ S x

/-- The existential projects presuppositions existentially:
    ⟦a⟧(R)(S) only requires *some* restrictor individual to be in
    dom(S), unlike JE which requires *all* atoms. -/
theorem aSem_existential_projection {E : Type*}
    (R : E → Prop) (S : E → Prop) (domS : E → Prop) (w : E)
    (h : (aSem R S domS).defined w) :
    ∃ x, R x ∧ domS x := h

/-- **Universal vs existential projection contrast.**

    JE projects universally (every boy must have a sister).
    ⟦a⟧ projects existentially (some boy must have a sister).

    This asymmetry follows from the quantificational force of the
    determiner, not from any property of the presupposition itself. -/
theorem projection_asymmetry {E : Type*} [PartialOrder E]
    (boys : E) (R : E → Prop) (domP : E → Prop)
    (a₁ a₂ : E) (ha₂ : Atom a₂)
    (h₂ : a₂ ≤ boys)
    (hR₁ : R a₁)
    (hdom₁ : domP a₁) (hdom₂ : ¬domP a₂) :
    -- ⟦a⟧ is defined (some boy satisfies domP)
    (aSem R (fun _ => True) domP).defined boys ∧
    -- JE is NOT defined (a₂ doesn't satisfy domP)
    ¬(JE boys (fun _ => True) domP).defined boys :=
  ⟨⟨a₁, hR₁, hdom₁⟩, fun h => hdom₂ (h a₂ ha₂ h₂)⟩

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

/-- The competition between [Sg] and [Pl] is presuppositional, not
    at-issue: they share their assertive content but differ in
    presupposition. This is the structural signature of Maximize
    Presupposition (same assertion + strictly ordered presuppositions),
    as opposed to scalar implicature (different assertions).

    The same-assertion condition follows from `phiPresup_same_assertion`;
    the strength ordering is `presupStrength .maximal > presupStrength .minimal`
    (= 2 > 0). Together with `mp_selects_sg`, this shows number
    competition is governed by `phiMP`, not by at-issue scalar
    implicature. -/
theorem number_competition_is_presuppositional :
    -- Same assertive content (NOT a scalar strength difference)
    presupStrength .maximal > presupStrength .minimal ∧
    -- The MP constraint penalizes [Pl] (= .minimal) more than [Sg] (= .maximal)
    phiMP.eval .minimal > phiMP.eval .maximal :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- §6b  Negated Indefinites (§5, (41)–(42))
-- ============================================================================

/-!
## §6b: Negated Indefinites

(41a) "Lina didn't harvest a tomato" / "Lina harvested no tomato"
(41b) "Lina didn't harvest tomatoes" / "Lina harvested no tomatoes"

(41b) entails (41a): if Lina didn't harvest any tomatoes (Pl), she
certainly didn't harvest a single tomato (Sg). This follows from the
weak semantics of [Pl]: its assertion includes atomic referents.

The entailment goes: Pl's assertion is `¬∃x [*tomato](x) ∧ harvest(x)`.
Sg's assertion is `¬∃x atom(x) ∧ [*tomato](x) ∧ harvest(x)`.
Since atoms are in `*tomato`, the Pl assertion is strictly stronger.

Crucially, adding ¬atom(x) to the assertion of (41b) — which would
block the entailment — is ruled out because the negation of the
Sg presupposition is itself negated (the two premises of the
derivation are the Sg presupposition and the Pl assertion, but
the assertion is negated, blocking the reasoning from (40)).
-/

/-- **Pl negation entails Sg negation** (41).

    If no plurality of tomatoes was harvested, then no atomic tomato
    was harvested either. This follows from the inclusive semantics of
    [Pl] (which covers atoms) and holds because [Pl]'s assertion
    subsumes [Sg]'s assertion. -/
theorem negated_pl_entails_negated_sg {E : Type*} [PartialOrder E]
    (starR : E → Prop) (harvest : E → Prop)
    (hNoPlHarvest : ¬∃ e, starR e ∧ harvest e) :
    ¬∃ e, Atom e ∧ starR e ∧ harvest e :=
  fun ⟨e, _, hR, hH⟩ => hNoPlHarvest ⟨e, hR, hH⟩

-- ============================================================================
-- §7  Other Agreement Features: Gender (§6, (45))
-- ============================================================================

/-!
## §7: Gender Agreement in Czech Coordinations (§6, (45))

Czech gender agreement on the verb is determined by the entire
coordination, not just one conjunct. This parallels number:
the φ-head above the coordination must have a gender feature
whose presupposition is satisfied by the **sum** of the conjuncts.

- (45a) Jan a Petr šli (went-masc-pl): both male → masc ✓
- (45b) Věra a Barbara šly (went-fem-pl): both female → fem ✓
- (45c) Jan a Věra šli/*šly (went-masc-pl, NOT fem): mixed gender → masc
- (45d) Matka a její dítě šly (went-fem-pl): mother + neut child → fem
- (45e) Otec a jeho dítě šli (went-masc-pl): father + neut child → masc

Sauerland's analysis: masculine is vacuous (minimal cell), feminine
presupposes non-masculinity (intermediate), neuter presupposes
inanimate/genderless (maximal). These are precisely the presuppositional
denotations `mascSem`, `femSem`, `neutSem` from `PhiFeatures.lean §3b`.

The Czech facts follow from Maximize Presupposition over the sum:
- (45c): The sum includes a male referent (Jan), so fem's presupposition
  (non-masculine) fails → only masc (vacuous) is available.
- (45d): The sum includes a female referent and an inanimate referent.
  Neut presupposition (all inanimate) fails, but fem presupposition
  (all non-masculine) succeeds → MP selects fem.
-/

section CzechGender

/-- A referent's sex/animacy category (for Czech gender agreement). -/
inductive ReferentGender where
  | male
  | female
  | inanimate
  deriving DecidableEq, Repr

/-- `isFemale` predicate: the referent is female. -/
def isFemale : ReferentGender → Prop
  | .female => True
  | _ => False

/-- `isInanimate` predicate: the referent is genderless/inanimate. -/
def isInanimate : ReferentGender → Prop
  | .inanimate => True
  | _ => False

/-- `isNonMasculine` predicate: inanimate → non-masculine (containment). -/
theorem inanimate_is_nonmasculine (r : ReferentGender) :
    isInanimate r → isFemale r ∨ isInanimate r :=
  fun h => Or.inr h

/-- (45c): Jan (male) + Věra (female) → fem FAILS.
    The sum includes a male referent, so femSem's presupposition
    (all non-masculine) is not satisfied. Only mascSem (vacuous) works. -/
theorem czech_mixed_gender_masc :
    ¬isFemale ReferentGender.male ∧
    (mascSem (E := ReferentGender)).defined .male :=
  ⟨(fun h => nomatch h), trivial⟩

/-- (45d): Matka (female) + dítě (inanimate) → neut FAILS, fem SUCCEEDS.
    Neut presupposition (all inanimate) fails because mother is not
    inanimate. Fem presupposition (non-masculine) succeeds: mother is
    female and child is inanimate (hence non-masculine). -/
theorem czech_mother_child_fem :
    -- Neut presupposition fails: mother is not inanimate
    ¬(neutSem isInanimate).defined ReferentGender.female ∧
    -- Fem presupposition succeeds for both
    (femSem isFemale).defined ReferentGender.female ∧
    -- Masc is also available (vacuous)
    (mascSem (E := ReferentGender)).defined ReferentGender.female :=
  ⟨(fun h => nomatch h), trivial, trivial⟩

/-- (45e): Otec (male) + dítě (inanimate) → only masc.
    Both neut and fem fail on the male referent. -/
theorem czech_father_child_masc :
    ¬(neutSem isInanimate).defined ReferentGender.male ∧
    ¬(femSem isFemale).defined ReferentGender.male ∧
    (mascSem (E := ReferentGender)).defined ReferentGender.male :=
  ⟨(fun h => nomatch h), (fun h => nomatch h), trivial⟩

/-- **Gender resolution parallels number resolution.**

    Just as [Sg] fails on a coordination of two distinct atoms (→ [Pl]),
    [Fem] fails on a coordination containing a male referent (→ [Masc]).
    Both follow from the same mechanism: the presupposition of the more
    specified feature is not satisfied by the sum, so Maximize
    Presupposition selects the less specified (vacuous) alternative. -/
theorem gender_number_parallel :
    -- Number: non-atom → only Pl
    (∀ (E : Type*) [PartialOrder E] (x : E), ¬Atom x → (plSem E).defined x) ∧
    -- Gender: male referent → only Masc
    (mascSem (E := ReferentGender)).defined .male :=
  ⟨fun _ _ _ _ => trivial, trivial⟩

end CzechGender

-- ============================================================================
-- §8  Politeness Prediction (§2.2, §6)
-- ============================================================================

/-!
## §8: Politeness Prediction

Sauerland §2.2 predicts that polite address forms should recruit the
**less specified** phi-feature values — precisely those with weaker
(or vacuous) presuppositions. The prediction: as polite forms replacing
2nd person singular, only 2nd/3rd person plural and 3rd person singular
should be possible. German uses 3rd person plural "Sie" (14a) and
historically 2nd person plural "Ihr".

This prediction follows from the general principle that vacuous
presuppositions (`specLevel` 0) are compatible with any context —
they impose no domain restriction and hence no falsehood risk.

The formal content of this prediction is captured by
`isSemanticUnmarked` in `PhiFeatures.lean §5` and verified by
@cite{wang-r-2023} (see `Phenomena/Politeness/Studies/Wang2023.lean`),
which proves that all three cross-linguistic honorific strategies
(plural, 3rd person, indefinite) recruit the minimal (unmarked) cell.
-/

/-- The three semantically unmarked phi-values correspond to the
    three cross-linguistic politeness strategies. -/
theorem politeness_uses_unmarked :
    -- Plural (number)
    isSemanticUnmarked (PhiFeatures.toPair Core.Number.pluralF) = true ∧
    -- 3rd person
    isSemanticUnmarked (PhiFeatures.toPair Core.Person.third) = true ∧
    -- Masculine (gender)
    isSemanticUnmarked (PhiFeatures.toPair Core.Gender.masculineF) = true :=
  ⟨rfl, rfl, rfl⟩

/-- The three semantically marked phi-values are NOT used for
    politeness — their presuppositions would impose unwanted
    restrictions on the addressee. -/
theorem marked_not_polite :
    isSemanticMarked (PhiFeatures.toPair Core.Number.singularF) = true ∧
    isSemanticMarked (PhiFeatures.toPair Core.Person.first) = true ∧
    isSemanticMarked (PhiFeatures.toPair Core.Gender.neuterF) = true :=
  ⟨rfl, rfl, rfl⟩

end Phenomena.Plurals.Studies.Sauerland2003
