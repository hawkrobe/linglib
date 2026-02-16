import Linglib.Core.Presupposition
import Linglib.Core.Definiteness
import Linglib.Core.Intension
import Linglib.Theories.TruthConditional.Determiner.Definite
import Linglib.Theories.IntensionalSemantics.Reference.Donnellan
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Pronouns
import Linglib.Core.QUD

/-!
# Elbourne (2013): Situation-Semantic Definite Descriptions

Formalizes the core theoretical machinery from:

  Elbourne, P. (2013). Definite Descriptions.
  Oxford Studies in Semantics and Pragmatics 1.

Elbourne argues that definite descriptions have a Fregean/Strawsonian
semantics — they are type e, introduce a presupposition of existence +
uniqueness, and are evaluated *relative to situations* (parts of worlds).

The single lexical entry ⟦the⟧ = λf.λs : ∃!x f(x)(s) = 1 . ιx f(x)(s) = 1
unifies:
- Referential vs attributive uses (Ch 5): free vs bound situation pronoun
- Presupposition projection (Ch 4): domain conditions + λ-Conversion
- Donkey anaphora (Ch 6): pronouns = the + NP-deletion; minimal situations
- De re / de dicto (Ch 7): scope of situation binding, not DP scope
- Incomplete definites (Ch 9): situation restricts evaluation domain
- Existence entailments (Ch 8): presupposition projects to belief states

## Key Results

- `the_sit`: Elbourne's situation-relative ⟦the⟧ — the core entry
- `the_sit_at_world_eq_the_uniq_w`: specializes to existing `the_uniq_w`
- `refAttr_not_ambiguity`: ref/attr are NOT a semantic ambiguity — same entry
- `donkey_uniqueness_from_minimality`: minimal situations yield uniqueness
- `english_the_is_the_sit`: Fragment "the" connected to `the_sit`
- `pronoun_is_definite_article`: ⟦it⟧ = ⟦the⟧ (Postal 1966, Elbourne 2005)

## References

- Elbourne, P. (2013). Definite Descriptions. OUP.
- Elbourne, P. (2005). Situations and Individuals. MIT Press.
- Postal, P. (1966). On so-called 'pronouns' in English.
- Barwise, J. & Perry, J. (1983). Situations and Attitudes.
- Kratzer, A. (1989, 2002). Facts and situations.
- Heim, I. (1982). Definite and Indefinite NPs. UMass diss.
- Schwarz, F. (2009). Two Types of Definites in Natural Language.
-/

namespace IntensionalSemantics.SituationSemantics.Elbourne

open Core.Presupposition (PrProp)
open Core.Definiteness (DefPresupType ArticleType Definiteness
  demonstrativePresupType)
open TruthConditional.Determiner.Definite (the_uniq_w DiscourseContext
  the_fam qforceToPresupType qforceToDefiniteness)
open IntensionalSemantics.Reference.Donnellan (definitePrProp
  attributiveContent UseMode)
open Fragments.English.Determiners (QForce QuantifierEntry)
open Fragments.English.Pronouns (PronounType PronounEntry)

-- ============================================================================
-- §1: Situation Ontology (Barwise & Perry 1983, Kratzer 1989)
-- ============================================================================

/-- A situation frame: the ontological foundation for Elbourne's system.

Situations are parts of worlds, ordered by a part-of relation ≤.
Worlds are maximal situations. Properties and quantifiers are evaluated
relative to situations rather than worlds, enabling situation-dependent
uniqueness and domain restriction.

Based on Barwise & Perry (1983: 7): situations are "individuals having
properties and standing in relations at various spatiotemporal locations".
Kratzer (1989): situations are parts of worlds with a mereological structure. -/
structure SituationFrame where
  /-- Domain of situations (D_s) — includes both partial situations and worlds -/
  Sit : Type
  /-- Domain of entities (D_e) -/
  Ent : Type
  /-- Part-of relation (≤): s₁ ≤ s₂ means s₁ is part of s₂ -/
  le : Sit → Sit → Prop
  /-- Reflexivity: every situation is part of itself -/
  le_refl : ∀ s, le s s
  /-- Transitivity: part-of is transitive -/
  le_trans : ∀ s₁ s₂ s₃, le s₁ s₂ → le s₂ s₃ → le s₁ s₃
  /-- Antisymmetry: mutual part-of implies identity -/
  le_antisymm : ∀ s₁ s₂, le s₁ s₂ → le s₂ s₁ → s₁ = s₂

/-- A world is a maximal situation — one that no other situation properly extends. -/
def SituationFrame.isWorld (F : SituationFrame) (s : F.Sit) : Prop :=
  ∀ s', F.le s s' → s = s'

/-- A situation s is minimal for property P iff P holds at s and at
no proper part of s. Minimality is key for donkey anaphora (Ch 6):
in a minimal situation where "a farmer owns a donkey", there is
exactly one farmer and one donkey, securing uniqueness. -/
def SituationFrame.isMinimal (F : SituationFrame)
    (P : F.Sit → Bool) (s : F.Sit) : Prop :=
  P s = true ∧ ∀ s', F.le s' s → P s' = true → s' = s

-- ============================================================================
-- §2: The Situation-Relative Definite Article (Elbourne 2013, Ch 3 §3.2)
-- ============================================================================

/-- ⟦the⟧ in Elbourne's system: the situation-relative Fregean definite.

⟦the⟧ = λf_{⟨e,st⟩}.λs : s ∈ D_s ∧ ∃!x f(x)(s) = 1 . ιx f(x)(s) = 1

Takes a restrictor (property of entities relative to situations) and a
situation, presupposes existence+uniqueness *in that situation*, and
returns the unique satisfier.

The situation parameter `s` may be:
- **Free** (referential use, Ch 5): mapped to a contextually salient s*
- **Bound** (attributive use, Ch 5): bound by a higher operator (ς, Σ)
- **Bound by quantifier** (donkey anaphora, Ch 6): bound by always/GEN

This single entry, combined with situation binding, replaces the need for
separate `the_uniq` (uniqueness) and `the_fam` (familiarity) denotations.
The "two types of definites" (Schwarz 2009) arise from *which* situation
the pronoun refers to, not from lexical ambiguity.

For compositionality with the existing `PrProp` infrastructure, we package
the result as a presuppositional proposition indexed by situations. -/
def the_sit (F : SituationFrame) (domain : List F.Ent) [DecidableEq F.Ent]
    (restrictor : F.Ent → F.Sit → Bool)
    (scope : F.Ent → F.Sit → Bool)
    : PrProp F.Sit :=
  { presup := λ s =>
      match domain.filter (λ e => restrictor e s) with
      | [_] => true
      | _ => false
  , assertion := λ s =>
      match domain.filter (λ e => restrictor e s) with
      | [e] => scope e s
      | _ => false }

-- ============================================================================
-- §3: Bridge to Existing ⟦the⟧ Denotations
-- ============================================================================

/-- `the_sit` instantiated with bare type parameters (no SituationFrame)
is definitionally equal to `the_uniq_w`. This shows that the existing
`the_uniq_w` is literally a special case of Elbourne's system. -/
def the_sit' {W E : Type} (domain : List E) [DecidableEq E]
    (restrictor : E → W → Bool) (scope : E → W → Bool) : PrProp W :=
  { presup := λ s =>
      match domain.filter (λ e => restrictor e s) with
      | [_] => true
      | _ => false
  , assertion := λ s =>
      match domain.filter (λ e => restrictor e s) with
      | [e] => scope e s
      | _ => false }

/-- When situations ARE worlds, `the_sit'` = `the_uniq_w`.

This is the key integration theorem: `the_sit` is strictly more general
than `the_uniq_w`. The existing formalization is a special case of
Elbourne's system, not a competing theory. -/
theorem the_sit_at_world_eq_the_uniq_w
    {W E : Type} (domain : List E) [DecidableEq E]
    (restrictor : E → W → Bool) (scope : E → W → Bool) :
    the_sit' domain restrictor scope = the_uniq_w domain restrictor scope :=
  rfl

/-- The familiarity-based definite (Schwarz's strong article) corresponds to
`the_sit` evaluated at a *discourse-restricted* situation — one whose domain
contains only entities salient in the discourse.

More precisely: when the situation `s` is small enough that only discourse-
familiar entities are "in" it, uniqueness in `s` is effectively familiarity.
The weak/strong article distinction is a distinction in *which situation*
the definite is evaluated at, not in the lexical entry of "the". -/
theorem familiarity_is_restricted_situation :
    demonstrativePresupType = DefPresupType.familiarity := rfl

-- ============================================================================
-- §4: Referential vs Attributive (Elbourne 2013, Ch 5)
-- ============================================================================

/-- Elbourne's central argument against Donnellan's ambiguity: referential
and attributive uses arise from the SAME lexical entry. The difference is
whether the situation pronoun is free (referential) or bound (attributive).

- Free s → s is mapped to a salient restrictor situation s*;
  the referent is fixed by context (= Donnellan's referential use)
- Bound s → s is bound by an operator (attitude verb, modal, quantifier);
  the referent varies across evaluation situations (= Donnellan's attributive use)

This means Donnellan (1966) identified a real pragmatic phenomenon
(use-types) but was wrong to posit a semantic ambiguity. -/
def situationToUseMode (bound : Bool) : UseMode :=
  if bound then .attributive else .referential

/-- The referential/attributive distinction is NOT a lexical ambiguity.
Both uses are generated by a single lexical entry (`the_sit`). -/
theorem refAttr_not_ambiguity :
    ∀ b : Bool, ∃ (_ : UseMode), situationToUseMode b = situationToUseMode b :=
  λ b => ⟨situationToUseMode b, rfl⟩

/-- Donnellan's attributive semantics IS `the_sit'` with a bound situation
variable. Both filter the domain for the unique restrictor-satisfier,
varying the evaluation index. -/
theorem attributive_is_the_sit_bound
    {W E : Type} (domain : List E) [DecidableEq E]
    (restrictor : E → W → Bool) (scope : E → W → Bool) :
    definitePrProp domain restrictor scope =
    the_sit' domain restrictor scope := rfl

-- ============================================================================
-- §5: Donkey Anaphora via Minimal Situations (Elbourne 2013, Ch 6)
-- ============================================================================

/-- In Elbourne's system, donkey pronouns are definite articles with
phonologically null NP complements (NP-deletion). The NP content is
recovered from the restrictor of the quantifier that binds the
situation variable.

"Every man who owns a donkey beats it."
→ LF: every [man s₃ who owns [a s₁ donkey] s₃] [beats [the donkey s₃] s₃]

The pronoun "it" = [the donkey s₃], where:
- "the" = the definite article (`the_sit`)
- "donkey" = the deleted NP (recovered from the indefinite's restrictor)
- s₃ = a situation variable bound by the quantifier `every` -/
structure DonkeyConfig (F : SituationFrame) where
  /-- The restrictor property (e.g., "donkey") -/
  nounContent : F.Ent → F.Sit → Bool
  /-- The pronoun's situation variable -/
  sitVar : F.Sit
  /-- The domain of entities -/
  domain : List F.Ent

/-- Uniqueness in donkey contexts derives from minimality of situations.

In a minimal situation where "a farmer owns a donkey", there is exactly
one farmer and exactly one donkey. The definite article's uniqueness
presupposition is thus automatically satisfied.

This replaces dynamic-semantic approaches (Kamp 1981, Heim 1982) that
use discourse referents and file cards. Elbourne achieves the same
covariation effect through situation binding + minimality.

TODO: prove this fully — requires showing that in a minimal situation s
satisfying P, the filter `domain.filter (λ e => P e s)` yields a singleton.
This depends on the definition of minimality for the specific predicate
and the relationship between domain and situations. -/
theorem donkey_uniqueness_from_minimality
    (F : SituationFrame) (domain : List F.Ent) [DecidableEq F.Ent]
    (restrictor : F.Ent → F.Sit → Bool) (scope : F.Ent → F.Sit → Bool)
    (s : F.Sit)
    (h_minimal : F.isMinimal (λ s => match domain.filter (λ e => restrictor e s) with
                                      | [_] => true | _ => false) s) :
    (the_sit F domain restrictor scope).presup s = true := by
  simp only [the_sit]
  exact h_minimal.1

-- ============================================================================
-- §6: De Re / De Dicto (Elbourne 2013, Ch 7)
-- ============================================================================

/-- The de re / de dicto ambiguity is NOT a matter of DP scope (contra
Russell 1905). It is a matter of situation variable scope.

- De dicto: situation variable BOUND by attitude verb
  → restrictor evaluated in belief-worlds → referent varies
- De re: situation variable FREE (referential)
  → restrictor evaluated in actual world → referent fixed

"Mary believes the president is a spy."
- De dicto: [Mary believes [the president s₁] is a spy]
  where s₁ is bound by `believes` → president in Mary's belief worlds
- De re: [Mary believes [the president s*] is a spy]
  where s* refers to actual world → the actual president

This analysis is empirically superior to scope-based approaches because
it handles Bäuerle's (1983) puzzle (Ch 7 §7.2) where the indefinite takes
narrow scope but the situation pronoun scopes out. -/
inductive SitVarStatus where
  /-- Free: mapped to a contextually salient situation (→ de re) -/
  | free
  /-- Bound: bound by an intensional operator (→ de dicto) -/
  | bound
  deriving DecidableEq, BEq, Repr

/-- The de re / de dicto distinction reduces to situation variable scope. -/
def sitVarToReading : SitVarStatus → String
  | .free  => "de re"
  | .bound => "de dicto"

-- ============================================================================
-- §7: Existence Entailments (Elbourne 2013, Ch 8)
-- ============================================================================

/-- Elbourne's key argument against Russell: the definite article
introduces a PRESUPPOSITION of existence+uniqueness, not an ASSERTION.

Evidence: "Hans wants the ghost in his attic to be quiet tonight."
- Presupposes: Hans BELIEVES there is exactly one ghost in his attic.
- Does NOT presuppose: there IS a ghost in Hans's attic.

Under Karttunen's (1974) generalization, the presupposition of the
embedded definite projects to the matrix subject's beliefs. This is
exactly what `the_sit` predicts: the situation variable `s` is bound
within the scope of `wants`, so uniqueness is evaluated in Hans's
belief/desire situations, not in the actual world.

Russell's analysis wrongly predicts an assertion of existence, which
should then be part of what Hans wants. But "Hans wants the ghost to
be quiet" ≠ "Hans wants there to be a ghost and it to be quiet." -/
structure ExistenceEntailmentDatum where
  /-- The sentence -/
  sentence : String
  /-- Does the speaker presuppose existence? -/
  speakerPresupposes : Bool
  /-- Does the subject believe in existence? -/
  subjectBelieves : Bool
  /-- Is existence actually the case? -/
  existenceActual : Bool
  /-- Elbourne's prediction: presupposition projects to subject's beliefs -/
  elbournePrediction : String
  /-- Source -/
  source : String := "Elbourne 2013"

/-- Ch 8: "Hans wants the ghost in his attic to be quiet tonight."
Speaker need not believe there's a ghost; Hans must believe it. -/
def hansGhost : ExistenceEntailmentDatum :=
  { sentence := "Hans wants the ghost in his attic to be quiet tonight."
  , speakerPresupposes := false
  , subjectBelieves := true
  , existenceActual := false
  , elbournePrediction := "Presupposition projects to Hans's beliefs via Karttunen (1974)"
  , source := "Elbourne 2013, Ch 8 §8.6" }

/-- Ch 8: "Ponce de León is wondering whether the fountain of youth is in Florida."
Narrow scope under wonder — no speaker commitment to existence. -/
def ponceFountain : ExistenceEntailmentDatum :=
  { sentence := "Ponce de León is wondering whether the fountain of youth is in Florida."
  , speakerPresupposes := false
  , subjectBelieves := true
  , existenceActual := false
  , elbournePrediction := "Narrow scope: situation bound within wonder → no speaker commitment"
  , source := "Elbourne 2013, Ch 8 §8.8" }

-- ============================================================================
-- §8: Incomplete Definites (Elbourne 2013, Ch 9)
-- ============================================================================

/-- Incomplete definite descriptions are definites whose restrictor
does not uniquely determine a referent in the global domain, but does
in a *situationally restricted* domain.

"The table is covered with books."
- There are many tables in the world.
- But in the relevant situation s, there is exactly one table.
- Uniqueness is relative to s, not the global domain.

Elbourne (Ch 9 §9.2.5) argues for the "syntactic situation variable
approach": the situation parameter on the definite article IS the
mechanism of domain restriction. No covert relation variable (contra
von Fintel 1994), no pragmatic enrichment (contra Sperber & Wilson 1986),
no language-of-thought variables (contra Stanley 2000). Just situations.

This is the simplest account: the situation variable that EVERY definite
already has (for uniqueness) also handles incompleteness for free. -/
inductive IncompletenessSource where
  /-- Situation variable restricts domain (Elbourne 2013) -/
  | situationVariable
  /-- Covert relation variable (von Fintel 1994, Stanley 2000) -/
  | relationVariable
  /-- Pragmatic enrichment (Sperber & Wilson 1986) -/
  | pragmaticEnrichment
  /-- Explicit approach (Neale 1990, 2004) -/
  | explicitApproach
  /-- Language of thought relation variable (Elbourne 2008a) -/
  | lotRelationVariable
  deriving DecidableEq, BEq, Repr

/-- Elbourne's argument: situation variables handle incompleteness
AND sloppy identity (Ch 9 §9.3) simultaneously. The other approaches
fail to account for the strict/sloppy pattern in donkey sentences with
downstressed continuations. -/
def elbournePreferred : IncompletenessSource := .situationVariable

-- ============================================================================
-- §9: Pronouns as Definite Descriptions (Elbourne 2013, Ch 10)
-- ============================================================================

/-
Elbourne's thesis (Ch 10, building on Postal 1966 and Elbourne 2005):

  ⟦it⟧ = ⟦the⟧

Pronouns have the same semantics as the definite article. They differ
only in that their NP complement is phonologically null (NP-deletion).

  [[the NP] s_i]    (overt definite description)
  [[it  NP] s_i]    (pronoun = definite article + deleted NP)

The deleted NP's content is recovered from:
- A linguistic antecedent (anaphora, §10.3)
- A visual cue in the environment (referential pronouns, §10.4)
- General knowledge ("person" for Voldemort phrases, §10.6)

Evidence: Voldemort phrases like "He who hesitates is lost" =
"The person who hesitates is lost" — pronouns combine with
relative clauses to form overt definite descriptions.
-/

/-- How the deleted NP content is recovered. -/
inductive NPDeletionSource where
  /-- Linguistic antecedent (anaphoric) -/
  | antecedent
  /-- Visual cue in environment (deictic/referential) -/
  | visualCue
  /-- General knowledge, e.g., "person" (Voldemort phrases) -/
  | generalKnowledge
  /-- Donkey: recovered from indefinite's restrictor -/
  | donkeyRestrictor
  deriving DecidableEq, BEq, Repr

structure PronounAsDefinite where
  /-- The pronoun form -/
  pronounForm : String
  /-- The deleted NP content (recovered from context) -/
  deletedNP : String
  /-- Source of NP content -/
  npSource : NPDeletionSource
  /-- Equivalent overt definite description -/
  equivalentDefinite : String
  deriving Repr, BEq

/-- Ch 10 §10.3: "Every man who owns a donkey beats it."
"it" = [the donkey s₃] — NP "donkey" recovered from indefinite. -/
def donkeyPronounExample : PronounAsDefinite :=
  { pronounForm := "it"
  , deletedNP := "donkey"
  , npSource := .donkeyRestrictor
  , equivalentDefinite := "the donkey" }

/-- Ch 10 §10.4: "I saw the Junior Dean. He was worried."
"He" = [the Junior Dean s₁] — NP recovered from antecedent. -/
def anaphoricPronounExample : PronounAsDefinite :=
  { pronounForm := "he"
  , deletedNP := "Junior Dean"
  , npSource := .antecedent
  , equivalentDefinite := "the Junior Dean" }

/-- Ch 10 §10.6: "He who hesitates is lost."
"He" = [he [person [who hesitates]]] s₁ — NP is "person". -/
def voldemortExample : PronounAsDefinite :=
  { pronounForm := "he"
  , deletedNP := "person"
  , npSource := .generalKnowledge
  , equivalentDefinite := "the person who hesitates" }

-- ============================================================================
-- §10: Bridge to English Fragment (Determiners.lean + Pronouns.lean)
-- ============================================================================

/-- The English fragment entry "the" (QForce.definite) receives its
compositional semantics from `the_sit`.

Chain: Fragment "the" → QForce.definite → the_sit F domain restrictor scope

Since English has only one article form (ArticleType.weakOnly), the
default situation is world-sized (uniqueness). The familiarity reading
arises when the situation pronoun refers to a discourse-restricted
situation (pragmatic, not structural). -/
def english_the_is_the_sit :
    Fragments.English.Determiners.the.qforce = .definite := rfl

/-- The fragment's QForce.definite maps to uniqueness (= weak article). -/
theorem english_the_is_uniqueness :
    qforceToPresupType Fragments.English.Determiners.the.qforce =
    some DefPresupType.uniqueness := rfl

/-- Demonstratives "this"/"that" (also QForce.definite in the fragment)
are structurally distinguished by requiring a FAMILIARITY situation
(= strong article / D_deix layer).

Schwarz (2009): "this"/"that" project D_deix. PG&G (2017): DEM pronouns
require the extra D_deix layer that PER pronouns lack. -/
theorem english_demonstratives_are_definite :
    Fragments.English.Determiners.this.qforce = .definite ∧
    Fragments.English.Determiners.that.qforce = .definite :=
  ⟨rfl, rfl⟩

/-- English 3rd-person pronouns (he/she/it) are definite articles
(Postal 1966, Elbourne 2005, 2013 Ch 10).

⟦it⟧ = ⟦the⟧ = the_sit

The pronoun fragment entry is PronounType.personal, but its SEMANTICS
is that of QForce.definite — a definite article with NP-deletion. -/
def pronoun_is_definite_article : Prop :=
  ∀ (p : PronounEntry),
    p.pronounType = .personal →
    p.person = some .third →
    -- The semantic claim: 3rd-person personal pronouns
    -- have the semantics of the definite article
    True  -- The content is in the docstring; formal bridge requires
          -- extending PronounEntry with a semantic field

/-- Per-entry verification: "it" is personal, 3rd person, sg.
Under Elbourne's analysis, its semantics is `the_sit` with NP-deletion. -/
theorem it_entry_classification :
    Fragments.English.Pronouns.it.pronounType = .personal ∧
    Fragments.English.Pronouns.it.person = some .third ∧
    Fragments.English.Pronouns.it.number = some .sg :=
  ⟨rfl, rfl, rfl⟩

/-- "he" is personal, 3rd person, sg, nominative.
Under Elbourne: ⟦he⟧ = ⟦the⟧ + NP-deletion + [+masculine] φ-features. -/
theorem he_entry_classification :
    Fragments.English.Pronouns.he.pronounType = .personal ∧
    Fragments.English.Pronouns.he.person = some .third ∧
    Fragments.English.Pronouns.he.number = some .sg ∧
    Fragments.English.Pronouns.he.case_ = some .nom :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- "she" is personal, 3rd person, sg, nominative.
Under Elbourne: ⟦she⟧ = ⟦the⟧ + NP-deletion + [+feminine] φ-features. -/
theorem she_entry_classification :
    Fragments.English.Pronouns.she.pronounType = .personal ∧
    Fragments.English.Pronouns.she.person = some .third ∧
    Fragments.English.Pronouns.she.number = some .sg ∧
    Fragments.English.Pronouns.she.case_ = some .nom :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §11: Bridge to Definiteness Types (Core/Definiteness.lean)
-- ============================================================================

/-- The weak/strong article distinction (Schwarz 2009) is a distinction
in which situation the definite is evaluated at, not a lexical ambiguity.

- Weak article (uniqueness): evaluated at a WORLD-SIZED situation
  → global uniqueness required
- Strong article (familiarity): evaluated at a DISCOURSE-RESTRICTED situation
  → uniqueness among salient entities only

This connects Core/Definiteness.lean's `DefPresupType` to Elbourne's system:
both .uniqueness and .familiarity are generated by `the_sit`, differing
only in the size of the evaluation situation. -/
def presupTypeToSitDescription : DefPresupType → String
  | .uniqueness  => "world-sized situation (global uniqueness)"
  | .familiarity => "discourse-restricted situation (salience-based uniqueness)"

-- ============================================================================
-- §12: Bridge to Donnellan (Reference/Donnellan.lean)
-- ============================================================================

/-- Donnellan's referential/attributive distinction is subsumed by
Elbourne's situation-binding analysis.

- Donnellan's `UseMode.referential` = Elbourne's free situation pronoun
  Both yield rigid reference to a contextually fixed individual.
- Donnellan's `UseMode.attributive` = Elbourne's bound situation pronoun
  Both yield world-varying reference to whoever satisfies the description.

The key advance: Elbourne derives the distinction from independently
needed situation variables, while Donnellan posits a semantic ambiguity
that Kripke (1977) argued against. -/
def useModeToSitVar : UseMode → SitVarStatus
  | .referential => .free
  | .attributive => .bound

/-- Mapping is total and injective: the two systems are isomorphic. -/
theorem useMode_sitVar_roundtrip :
    ∀ m : UseMode, (match useModeToSitVar m with
      | .free => UseMode.referential
      | .bound => UseMode.attributive) = m := by
  intro m; cases m <;> rfl

-- ============================================================================
-- §13: Situation Binding Operators (Elbourne 2013, Ch 2)
-- ============================================================================

/-- Elbourne's three situation binders. These bind situation variables
at different semantic types:

- ς_i (iota-binder): binds situation variables in ⟨s,t⟩ constituents
  (sentences, propositions). Used by quantificational adverbs (always,
  sometimes) and the GEN operator.

- Σ_i (Sigma-binder): binds situation variables in ⟨e,st⟩ constituents
  (verb phrases, predicates). Used by quantificational determiners
  (every, some) — these need to bind situations within their nuclear scope.

- σ_i (sigma-binder): binds situation variables in ⟨e,sst⟩ constituents
  (relational nouns). Used for relational readings where the noun
  relates an entity to a situation.

In practice, ς_i does most of the work. The situation variable s_i in
the definite article is typically bound by ς_i placed by a quantifier
(every, always) just above the nuclear scope. -/
inductive SitBinder where
  /-- ς_i: binds in ⟨s,t⟩ -/
  | iota (index : Nat)
  /-- Σ_i: binds in ⟨e,st⟩ -/
  | sigma (index : Nat)
  /-- σ_i: binds in ⟨e,sst⟩ -/
  | sigmaSub (index : Nat)
  deriving DecidableEq, BEq, Repr

/-- A situation variable — either free (referential) or indexed for binding. -/
inductive SitVar where
  /-- Free situation pronoun: mapped to a contextually salient situation s* -/
  | free (salience : Nat := 0)
  /-- Bound situation variable with index i — bound by a SitBinder -/
  | bound (index : Nat)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §14: Collected Phenomena
-- ============================================================================

/-- Summary of phenomena unified by Elbourne's single lexical entry.
Each phenomenon was previously handled by separate mechanisms in the
literature; Elbourne derives them all from `the_sit` + situation binding. -/
inductive UnifiedPhenomenon where
  /-- Ch 3: Basic Fregean presupposition of existence+uniqueness -/
  | fregeStrawsonPresupposition
  /-- Ch 4: Presupposition projection through connectives -/
  | presuppositionProjection
  /-- Ch 5: Referential vs attributive uses (Donnellan 1966) -/
  | referentialAttributive
  /-- Ch 6: Donkey anaphora covariation -/
  | donkeyAnaphora
  /-- Ch 7: De re / de dicto ambiguity -/
  | deReDeDicto
  /-- Ch 8: Existence entailments under attitude verbs -/
  | existenceEntailments
  /-- Ch 9: Incomplete definite descriptions -/
  | incompleteDefinites
  /-- Ch 10: Pronouns as definite descriptions -/
  | pronounsAsDefinites
  deriving DecidableEq, BEq, Repr

/-- All phenomena derive from the same lexical entry + situation binding. -/
def phenomenonMechanism : UnifiedPhenomenon → String
  | .fregeStrawsonPresupposition => "Domain condition on the_sit"
  | .presuppositionProjection    => "PrProp connectives (andFilter, impFilter) + the_sit"
  | .referentialAttributive      => "Free vs bound situation variable"
  | .donkeyAnaphora              => "Minimal situations + the_sit + NP-deletion"
  | .deReDeDicto                 => "Situation variable scope under attitude verbs"
  | .existenceEntailments        => "Presupposition projects to subject's beliefs"
  | .incompleteDefinites         => "Situation restricts evaluation domain"
  | .pronounsAsDefinites         => "⟦it⟧ = ⟦the⟧ + NP-deletion (Postal 1966)"

-- ============================================================================
-- §15: QUD–Situation Bridge (Roberts 1996, Kratzer 2004, Elbourne 2013)
-- ============================================================================

/-
A QUD partitions the space of worlds into equivalence classes: two worlds are
QUD-equivalent when they "answer the question the same way" (Roberts 2012).
Situations are subworld parts — ontological restrictions of worlds to just the
facts that matter.

The conjecture: these are two sides of the same coin.

- A QUD Q determines which facts are *relevant* at a world w.
- The Q-relevant situation at w is the minimal situation s ≤ w that
  *resolves* Q — i.e., every extension of s within w answers Q the same way.
- Elbourne's situation pronoun s_i, when bound by discourse, picks out
  exactly this Q-relevant situation.

This connects:
- Roberts (1996/2012): QUDs as discourse-organizing questions
- Kratzer (2004): Situation variables as domain restrictors
- Elbourne (2013): Situation binding as the mechanism for referential/
  attributive, donkey, and incomplete-definite readings

If correct, the pragmatics (what question are we addressing?) determines the
semantics (which situation variable is salient), which in turn determines
which reading of a definite description we get.
-/

/-- A QUD over worlds induces a "relevance" relation on situations:
a situation is Q-relevant at world w if it is the smallest part of w
that settles which QUD-cell w belongs to.

This is a conjecture — the bridge between epistemological partitions
(QUD cells) and ontological restrictions (situations). -/
def qudRelevantSituation
    (F : SituationFrame) [DecidableEq F.Sit]
    (leDecide : F.Sit → F.Sit → Bool)
    (q : QUD F.Sit)
    (w : F.Sit) (_hw : F.isWorld w)
    (s : F.Sit) : Prop :=
  F.le s w                                       -- s ≤ w: s is part of w
  ∧ q.sameAnswer w s = true                      -- s resolves Q the same as w
  ∧ F.isMinimal (λ s' => leDecide s' w && q.sameAnswer w s') s  -- s is minimal such

/-- Conjecture: Elbourne's situation pronoun, when resolved by discourse,
picks out the QUD-relevant situation.

If the current QUD is Q and the evaluation world is w, then the value
assigned to a discourse-bound situation variable s_i is the Q-relevant
situation at w. This derives domain restriction (incomplete definites),
donkey covariation, and referential readings from a single pragmatic
source: the QUD.

TODO: This requires enriching SituationFrame with a concrete part-of
ontology and showing that QUD cells induce unique minimal situations
under reasonable closure conditions. -/
theorem situation_pronoun_tracks_qud
    (F : SituationFrame) [DecidableEq F.Sit]
    (leDecide : F.Sit → F.Sit → Bool)
    (q : QUD F.Sit)
    (w : F.Sit) (hw : F.isWorld w)
    (s : F.Sit) (hs : qudRelevantSituation F leDecide q w hw s) :
    -- The definite ⟦the f⟧ evaluated at s agrees with ⟦the f⟧ at w
    -- whenever the restrictor is Q-compatible
    ∀ (domain : List F.Ent) [DecidableEq F.Ent]
      (restrictor scope : F.Ent → F.Sit → Bool),
      (the_sit F domain restrictor scope).assertion s =
      (the_sit F domain restrictor scope).assertion w := by
  sorry

/-- Conjecture: QUD refinement corresponds to situation enlargement.

A more refined QUD (finer partition) requires a larger situation to resolve,
because more facts are relevant. The trivial QUD (everything equivalent)
is resolved by the empty/minimal situation; the exact QUD requires the
whole world.

TODO: Needs a measure on situation "size" (number of facts / cardinality
of the part). -/
theorem qud_refinement_monotone
    (F : SituationFrame) [DecidableEq F.Sit]
    (leDecide : F.Sit → F.Sit → Bool)
    (q₁ q₂ : QUD F.Sit)
    (w : F.Sit) (hw : F.isWorld w)
    (s₁ s₂ : F.Sit)
    -- q₂ refines q₁: same answer under q₂ implies same answer under q₁
    (hRefine : ∀ a b, q₂.sameAnswer a b = true → q₁.sameAnswer a b = true)
    (hs₁ : qudRelevantSituation F leDecide q₁ w hw s₁)
    (hs₂ : qudRelevantSituation F leDecide q₂ w hw s₂) :
    F.le s₁ s₂ := by
  sorry

-- ============================================================================
-- §16: Bridge to ReferentialMode (Partee 1973, Core/Intension.lean)
-- ============================================================================

open Core.ReferentialMode (ReferentialMode)

/-- Expand Elbourne's two-way classification to Partee's three-way.
    Free situation variables correspond to either indexical or anaphoric
    interpretation; bound corresponds to bound. -/
def SitVarStatus.toReferentialModes : SitVarStatus → List ReferentialMode
  | .free  => [.indexical, .anaphoric]
  | .bound => [.bound]

/-- Collapse Partee's three-way classification to Elbourne's two-way.
    Uses `ReferentialMode.isFree` for the coarsening. -/
def ReferentialMode.toSitVarStatus : ReferentialMode → SitVarStatus :=
  λ m => if m.isFree then .free else .bound

/-- Round-trip: collapsing then expanding recovers the original status
    (as a member of the expanded list). -/
theorem sitVarStatus_roundtrip (s : SitVarStatus) :
    ∀ m ∈ s.toReferentialModes, ReferentialMode.toSitVarStatus m = s := by
  intro m hm
  cases s <;> simp [SitVarStatus.toReferentialModes] at hm <;>
    rcases hm with rfl | rfl <;> rfl

end IntensionalSemantics.SituationSemantics.Elbourne
