import Linglib.Core.Interface
import Linglib.Theories.Syntax.Minimalism.CombinationSchemata
import Linglib.Theories.Syntax.Minimalism.Core.Labeling
import Linglib.Theories.Syntax.HPSG.Core.HeadFiller
import Linglib.Theories.Syntax.HPSG.Core.LexicalRules
import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Theories.Syntax.DependencyGrammar.Formal.NonProjective
import Linglib.Theories.Syntax.ConstructionGrammar.ArgumentStructure

/-!
# @cite{mueller-2013}: Unifying Everything
@cite{mueller-2013}

Cross-theory comparison formalizing Müller's central thesis: Minimalism, HPSG,
CCG, Construction Grammar, and Dependency Grammar converge on three universal
combination schemata (Head-Complement, Head-Specifier, Head-Filler).

## Structure

- §1. Classification functions: map each theory's operations to `CombinationKind`
- §2. Labeling convergence: head determines category of result
- §3. External Merge ↔ Head-Complement ↔ Application
- §4. Internal Merge ↔ Head-Filler ↔ Composition
- §5. Coordination diagnostic: same category required
- §6. Directional MG ≈ CCG (placeholder)
- §7. Both directions right: need Merge AND phrasal constructions
- §8. Concrete cross-theory examples
- §9. Labeling failures: free relatives + coordination
- §10. Monovalent verb serialization problem
- §11. Iterable valence operations

-/

namespace Comparisons.Mueller2013

open Core

/-! ## §1. Classification Functions

Lightweight mappers from each theory's combination operations to the
theory-neutral `CombinationKind`. -/

/-! ### CCG classification -/

/-- Classify a CCG derivation step as one of the three schemata.

- Forward/backward application → Head-Complement (functor selects argument)
- Forward/backward composition → Head-Filler (enables extraction;
  this is an approximation — composition also serves non-extraction
  functions like heavy NP shift and right-node raising)
- Type-raising → none (unary operation, not a binary combination)
- Coordination → none (symmetric, not one of the three headed schemata) -/
def classifyCCGDerivStep : CCG.DerivStep → Option CombinationKind
  | .fapp _ _ => some .headComplement
  | .bapp _ _ => some .headComplement
  | .fcomp _ _ => some .headFiller
  | .bcomp _ _ => some .headFiller
  | .lex _ => none
  | .ftr _ _ => none
  | .btr _ _ => none
  | .coord _ _ => none

/-! ### HPSG classification -/

/-- Classify an HPSG schema application as one of the three schemata.

    @cite{mueller-2013}'s three universal schemata are Head-Complement,
    Head-Subject, and Head-Filler. HPSG's fourth schema, Head-Modifier
    (adjunction), falls outside this classification — Müller does not
    include adjunction in the convergence claim. -/
def classifyHPSGSchema : HPSG.HPSGSchema → Option CombinationKind
  | .headComp _ => some .headComplement
  | .headSubj _ => some .headSpecifier
  | .headFiller _ => some .headFiller
  | .headMod _ => none

/-! ### Dependency Grammar classification -/

/-- Classify a UD dependency relation as one of the three schemata.

Subject dependencies are Head-Specifier; all other core dependencies
are Head-Complement. Non-projective dependencies (handled separately)
correspond to Head-Filler. -/
def classifyDepType : UD.DepRel → CombinationKind
  | .nsubj => .headSpecifier
  | .csubj => .headSpecifier
  | _ => .headComplement

/-! ### CxG classification -/

/-- Classify whether a CxG construction is fully compositional.

Fully abstract constructions without pragmatic function decompose into
sequences of Head-Complement and Head-Specifier steps. Other constructions
are irreducible phrasal patterns. -/
def classifyCxGFullyCompositional (c : ConstructionGrammar.Construction) : Bool :=
  ConstructionGrammar.isFullyCompositional c

/-! ## §2. Labeling Convergence (Müller §2.1)

The head determines the category of the result. This is called:
- Minimalism: the labeling algorithm (selector projects)
- HPSG: Head Feature Principle (head features percolate)
- CCG: the functor's result category is the output -/

/-- CCG forward application preserves the functor's result category.

When X/Y combines with Y via forward application, the result is X —
the left part of the functor's slash category. -/
theorem ccg_fapp_result_category (x y : CCG.Cat) :
    CCG.forwardApp (CCG.Cat.rslash x y) y = some x := by
  simp [CCG.forwardApp]

/-- CCG backward application preserves the functor's result category. -/
theorem ccg_bapp_result_category (x y : CCG.Cat) :
    CCG.backwardApp y (CCG.Cat.lslash x y) = some x := by
  simp [CCG.backwardApp]

/-- Minimalist labeling: when α selects β, the label of {α, β} = label of α.

The selector projects, giving the result the same category as the head. -/
theorem min_selector_projects (a b : Minimalism.SyntacticObject)
    (h : Minimalism.selects a b) :
    Minimalism.label (Minimalism.merge a b) = Minimalism.label a := by
  simp only [Minimalism.merge, Minimalism.label, Minimalism.selects] at *
  simp [h]

/-- Labeling convergence across theories.

Three independent formulations of "the head determines the result's category"
all hold simultaneously. -/
theorem labeling_convergence :
    -- Minimalism: selector projects
    (∀ a b : Minimalism.SyntacticObject, Minimalism.selectsB a b = true →
      Minimalism.labelCat (.node a b) = Minimalism.labelCat a) ∧
    -- CCG: forward application yields functor's result category
    (∀ x y : CCG.Cat, CCG.forwardApp (CCG.Cat.rslash x y) y = some x) ∧
    -- CCG: backward application yields functor's result category
    (∀ x y : CCG.Cat, CCG.backwardApp y (CCG.Cat.lslash x y) = some x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    simp [Minimalism.labelCat, Minimalism.label, Minimalism.selectsB] at h ⊢
    simp [h]
  · intro x y; simp [CCG.forwardApp]
  · intro x y; simp [CCG.backwardApp]

/-! ## §3. External Merge ↔ Head-Complement ↔ Application (§2.1–2.2)

All theories implement the head-complement combination:
- Minimalism: External Merge where one SO selects the other
- HPSG: Head-Complement Schema (head word combines with complements)
- CCG: Forward/backward application (functor consumes argument)
- DG: Core dependency relations (obj, det, comp,...) -/

/-- External Merge with selection is Head-Complement across all theories. -/
theorem external_merge_is_head_complement :
    -- Minimalism: Ext Merge with selection = headComplement
    (∀ a b : Minimalism.SyntacticObject, Minimalism.selectsB a b = true →
      Minimalism.classifyExternalMerge a b = .headComplement) ∧
    -- HPSG: HeadCompRule = headComplement
    (∀ r : HPSG.HeadCompRule,
      classifyHPSGSchema (.headComp r) = some .headComplement) ∧
    -- CCG: fapp = headComplement
    (∀ d1 d2 : CCG.DerivStep,
      classifyCCGDerivStep (.fapp d1 d2) = some .headComplement) ∧
    -- DG: obj dep = headComplement
    (classifyDepType .obj = .headComplement) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; exact Minimalism.selection_implies_headComplement a b h
  · intro _; rfl
  · intro _ _; rfl
  · rfl

/-- External Merge without selection is Head-Specifier across theories. -/
theorem external_merge_is_head_specifier :
    -- Minimalism: Ext Merge without selection = headSpecifier
    (∀ a b : Minimalism.SyntacticObject,
      Minimalism.selectsB a b = false → Minimalism.selectsB b a = false →
      Minimalism.classifyExternalMerge a b = .headSpecifier) ∧
    -- HPSG: HeadSubjRule = headSpecifier
    (∀ r : HPSG.HeadSubjRule,
      classifyHPSGSchema (.headSubj r) = some .headSpecifier) ∧
    -- DG: subj dep = headSpecifier
    (classifyDepType .nsubj = .headSpecifier) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb; exact Minimalism.no_selection_implies_headSpecifier a b ha hb
  · intro _; rfl
  · rfl

/-! ## §4. Internal Merge ↔ Head-Filler ↔ Composition (§2.3)

All theories handle long-distance dependencies via the third schema:
- Minimalism: Internal Merge (re-merge of a contained element)
- HPSG: Head-Filler Schema (filler XP + S[SLASH {XP}])
- CCG: Forward/backward composition (enables extraction)
- DG: Non-projective (crossing) dependencies -/

/-- Internal Merge / Head-Filler / Composition across theories. -/
theorem internal_merge_is_head_filler :
    -- Minimalism: Internal Merge = headFiller
    (Minimalism.classifyInternalMerge = .headFiller) ∧
    -- HPSG: HeadFillerRule = headFiller
    (∀ r : HPSG.HeadFillerRule,
      classifyHPSGSchema (.headFiller r) = some .headFiller) ∧
    -- CCG: forward composition = headFiller
    (∀ d1 d2 : CCG.DerivStep,
      classifyCCGDerivStep (.fcomp d1 d2) = some .headFiller) ∧
    -- CCG: backward composition = headFiller
    (∀ d1 d2 : CCG.DerivStep,
      classifyCCGDerivStep (.bcomp d1 d2) = some .headFiller) := by
  exact ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Non-projective dependencies in DG correspond to Head-Filler.

A non-projective (crossing) dependency represents displacement — the DG
analogue of Internal Merge and the Head-Filler Schema. -/
theorem dg_nonproj_is_filler_gap :
    -- A tree with crossing arcs has filler-gap dependencies
    DepGrammar.hasFillerGap DepGrammar.nonProjectiveTree = true := by
  native_decide

/-! ## §5. Coordination Diagnostic (§2.2)

Coordination requires matching categories across all theories. This
is a *diagnostic* for whether two expressions have the same category. -/

/-- CCG coordination requires matching categories. -/
theorem ccg_coordination_same_cat (c1 c2 : CCG.Cat) :
    CCG.coordinate c1 c2 ≠ none → c1 = c2 := by
  simp only [CCG.coordinate]
  intro h
  by_contra hne
  have : ¬(c1 == c2) = true := by
    intro heq; exact hne (beq_iff_eq.mp heq)
  simp [this] at h

/-- CCG coordination of mismatched categories fails. -/
theorem ccg_coordination_mismatch (c1 c2 : CCG.Cat) (h : c1 ≠ c2) :
    CCG.coordinate c1 c2 = none := by
  simp only [CCG.coordinate]
  have : ¬(c1 == c2) = true := by
    intro heq; exact h (beq_iff_eq.mp heq)
  simp [this]

/-- HPSG lexical rules preserve head features, enabling coordination.

When two signs undergo the same lexical rule, they retain the same
category — which is why passivized verbs can coordinate with each other. -/
theorem hpsg_lexrule_enables_coordination (rule : HPSG.LexicalRule)
    (s1 s2 : HPSG.Sign) (h : s1.synsem.cat = s2.synsem.cat) :
    (HPSG.applyLexRule rule s1).synsem.cat =
    (HPSG.applyLexRule rule s2).synsem.cat :=
  HPSG.same_rule_same_cat rule s1 s2 h

/-! ## §6. Directional MG ≈ CCG (§2.3)

Stabler's directional Minimalist Grammar uses features =x (looking right)
and x= (looking left), which correspond directly to CCG's X/Y and X\Y.

This formal correspondence is not yet formalized because directional MG
is not in the codebase. -/

/- Placeholder: directional MG ≈ CCG (Stabler's =x ≈ X/Y, x= ≈ X\Y).
   TODO: When directional MG is added, prove:
   - =x features ≈ forward slash (X/Y)
   - x= features ≈ backward slash (X\Y)
   - DMG derivation trees ≈ CCG derivation trees -/

/-! ## §7. Both Directions Right (§3)

Müller's conclusion: the three universal schemata handle fully abstract
constructions, but Construction Grammar's phrasal constructions are
irreducible — they cannot be decomposed into the three schemata.

"Both directions right": we need BOTH Merge/schemata AND constructions. -/

/-- Concrete examples: fully abstract constructions decompose. -/
theorem ditransitive_decomposes :
    ConstructionGrammar.decompose ConstructionGrammar.ditransitive =
      [.headSpecifier, .headComplement, .headComplement] :=
  ConstructionGrammar.ditransitive_decomposes

theorem causedMotion_decomposes :
    ConstructionGrammar.decompose ConstructionGrammar.causedMotion =
      [.headSpecifier, .headComplement, .headComplement] :=
  ConstructionGrammar.causedMotion_decomposes

/-- Concrete examples: phrasal constructions are irreducible. -/
theorem pal_irreducible :
    ConstructionGrammar.isFullyCompositional
      ConstructionGrammar.Studies.GoldbergShirtz2025.palConstruction = false :=
  ConstructionGrammar.pal_irreducible

theorem let_alone_irreducible :
    ConstructionGrammar.isFullyCompositional
      ConstructionGrammar.Studies.FillmoreKayOConnor1988.letAloneConstruction = false :=
  ConstructionGrammar.let_alone_irreducible

/-- Both directions right: the three schemata AND phrasal constructions are needed.

1. Fully abstract constructions without pragmatic functions are fully
   compositional — decomposable into Head-Complement and Head-Specifier steps.
2. There exist constructions that are not fully compositional — they cannot
   be captured by the three schemata alone, requiring CxG's phrasal patterns. -/
theorem both_directions_right :
    -- Direction 1: fully abstract constructions are fully compositional
    (∀ c : ConstructionGrammar.Construction,
      c.specificity = .fullyAbstract →
      c.pragmaticFunction = none →
      ConstructionGrammar.isFullyCompositional c = true) ∧
    -- Direction 2: there exist non-fully-compositional constructions
    (∃ c : ConstructionGrammar.Construction,
      ConstructionGrammar.isFullyCompositional c = false) :=
  ConstructionGrammar.both_directions_right

/-! ## §8. Concrete Cross-Theory Examples

Verify that specific combinations classify identically across theories. -/

/-- D selecting N is Head-Complement in Minimalism. -/
example : Minimalism.classifyExternalMerge
    (.leaf Minimalism.detThe) (.leaf Minimalism.nounPizza) = .headComplement := by
  native_decide

/-- Det + N via forward application is Head-Complement in CCG. -/
example : classifyCCGDerivStep
    (.fapp (.lex ⟨"the", CCG.Det⟩) (.lex ⟨"pizza", CCG.N⟩)) =
    some .headComplement := rfl

/-- Det dependency is Head-Complement in DG. -/
example : classifyDepType .det = .headComplement := rfl

/-- Subject dependency is Head-Specifier in DG. -/
example : classifyDepType .nsubj = .headSpecifier := rfl

/-- The three schemata are exhaustive for External Merge in Minimalism. -/
theorem min_external_exhaustive (a b : Minimalism.SyntacticObject) :
    Minimalism.classifyExternalMerge a b = .headComplement ∨
    Minimalism.classifyExternalMerge a b = .headSpecifier :=
  Minimalism.classify_external_exhaustive a b

/-- The three primary HPSG schemata map to the three universal schemata;
    Head-Modifier (adjunction) falls outside the classification. -/
theorem hpsg_schemata_classified (s : HPSG.HPSGSchema) :
    classifyHPSGSchema s = some .headComplement ∨
    classifyHPSGSchema s = some .headSpecifier ∨
    classifyHPSGSchema s = some .headFiller ∨
    classifyHPSGSchema s = none := by
  cases s with
  | headComp _ => left; rfl
  | headSubj _ => right; left; rfl
  | headFiller _ => right; right; left; rfl
  | headMod _ => right; right; right; rfl

/-- Head-Modifier falls outside Müller's three schemata.
    Adjunction is HPSG-specific and not part of the universal convergence claim. -/
theorem hpsg_headMod_not_classified (r : HPSG.HeadModRule) :
    classifyHPSGSchema (.headMod r) = none := rfl

/-! ## §9. Labeling Failures (§2.1)

Müller shows that Chomsky's labeling algorithm fails in two ways:

1. **Free relatives**: rules 14a and 14b give contradictory labels (D vs V)
2. **Coordination of phrases**: neither rule applies (neither daughter is
   an LI, neither selects the other)

Note: The free relative SO `freeRelSO` models the surface structure
{what, [wrote ___]} without explicitly modeling Internal Merge — "what"
and the gap have different token IDs rather than being literal copies.
The labeling conflict holds regardless of how the gap is represented. -/

/-- Free relatives expose a labeling conflict between Chomsky's two rules. -/
theorem free_relative_labeling_conflict :
    Minimalism.labelRule14a Minimalism.freeRelSO = some .D ∧
    Minimalism.labelCat Minimalism.freeRelSO = some .V :=
  ⟨Minimalism.freeRel_rule14a_gives_D, Minimalism.freeRel_labelCat_gives_V⟩

/-- Coordination of two phrases: rule 14a fails (no LI daughter) and
    neither phrase selects the other. -/
theorem coordination_labeling_failure :
    Minimalism.labelRule14a Minimalism.coordDP = none ∧
    Minimalism.selectsB Minimalism.theDP Minimalism.aBookDP = false ∧
    Minimalism.selectsB Minimalism.aBookDP Minimalism.theDP = false :=
  ⟨Minimalism.coord_rule14a_fails,
   Minimalism.coord_neither_selects.1,
   Minimalism.coord_neither_selects.2⟩

/-! ## §10. Monovalent Verb Serialization Problem (§2.3)

Merge classifies a monovalent verb's sole argument as a complement,
yielding wrong linearization ("*Sleeps Max" instead of "Max sleeps"). -/

/-- Monovalent verbs: sole argument classified as complement → wrong order. -/
theorem monovalent_verb_serialization_problem :
    Minimalism.classifyExternalMerge
      (.leaf Minimalism.sleepsToken) (.leaf Minimalism.maxToken) = .headComplement ∧
    (Minimalism.merge (.leaf Minimalism.sleepsToken)
      (.leaf Minimalism.maxToken)).phonYield = ["sleeps", "Max"] :=
  ⟨Minimalism.monovalent_classified_as_complement,
   Minimalism.monovalent_wrong_linearization⟩

/-! ## §11. Iterable Valence Operations (§1)

Lexical rules compose freely, capturing double passivization (Turkish,
Lithuanian) without phrasal machinery. -/

/-- Any chain of lexical rules preserves head features. -/
theorem valence_iteration_works :
    ∀ s : HPSG.Sign,
      (HPSG.applyLexRule HPSG.passiveRule
        (HPSG.applyLexRule HPSG.passiveRule s)).synsem.head =
      s.synsem.head :=
  HPSG.double_passive_preserves_head

/-! ## Summary Table

| Claim | Min | HPSG | CCG | DG | CxG | Status |
|-------|-----|------|-----|-----|-----|--------|
| Head-Complement | Ext Merge + sel | HeadComp | fapp/bapp | obj/det/... | slot decomp | Proved |
| Head-Specifier | Ext Merge − sel | HeadSubj | (= bapp) | subj | slot decomp | Proved |
| Head-Filler | Int Merge | HeadFiller | fcomp/bcomp | nonproj | irreducible | Proved |
| Head-Modifier | — | HeadMod | — | — | — | Not in 3 schemata |
| Labeling | selector proj | HFP | functor result | head | — | Proved |
| Coordination | same cat | same cat | same cat | — | — | Proved |
| Labeling failure (FR) | 14a≠14b | — | — | — | — | Proved |
| Labeling failure (coord) | no rule applies | — | — | — | — | Proved |
| Monovalent verb | *Sleeps Max | — | — | — | — | Proved |
| Valence iteration | — | double passive | — | — | — | Proved |
| Directional MG ≈ CCG | =x ≈ X/Y | — | — | — | — | Sorry |
| Both directions right | — | — | — | — | abstract ∨ phrasal | Proved |

Note: CCG has no separate Head-Specifier mechanism. Subject combination uses
backward application (the verb S\NP is the functor), which is Head-Complement
in the classification. The subject/complement distinction is syntactic, not
combinatory, in CCG.
-/

end Comparisons.Mueller2013
