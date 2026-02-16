/-!
# Definiteness: Types and Classifications

Framework-agnostic vocabulary for definiteness phenomena. These types classify
definite descriptions, article systems, and presupposition types without
committing to any particular semantic theory.

The organizing principle is `DefPresupType` (.uniqueness | .familiarity) —
every other type in this module is a dimension that maps into this binary
distinction: article morphology, pragmatic use type, bridging relation, etc.

Used by:
- `Theories/Semantics.Montague/Determiner/Definite.lean` (denotations: ⟦the⟧)
- `Phenomena/Anaphora/PronounTypology.lean` (cross-linguistic article data)
- `Phenomena/Anaphora/Bridging.lean` (bridging presupposition types)

## References

- Schwarz, F. (2009). Two Types of Definites in Natural Language. UMass diss.
- Schwarz, F. (2013). Two Kinds of Definites Cross-linguistically. L&L Compass 7(10).
- Hawkins, J. (1978). Definiteness and Indefiniteness. Croom Helm.
- Heim, I. (1982). The Semantics of Definite and Indefinite NPs. UMass diss.
- Patel-Grosz, P. & B. Grosz (2017). Revisiting Pronominal Typology. LI 48(2).
- Donnellan, K. (1966). Reference and Definite Descriptions. Phil. Review.
-/

namespace Core.Definiteness

-- ============================================================================
-- §1: The Core Binary Distinction
-- ============================================================================

/-- The two presupposition types underlying definite descriptions.

Schwarz (2009): these correspond to two morphologically distinct articles
in languages like German, Fering, Lakhota, and Akan. Every classification
in this module ultimately maps into this binary type. -/
inductive DefPresupType where
  | uniqueness   -- Russell/Frege/Strawson: ∃!x. φ(x)
  | familiarity  -- Heim/Kamp: x is discourse-familiar
  deriving DecidableEq, BEq, Repr

/-- Demonstratives (this/that) project D_deix — the familiarity/strong-article
layer. Schwarz (2013) §5.5 and PG&G (2017). -/
def demonstrativePresupType : DefPresupType := .familiarity

-- ============================================================================
-- §2: Article Types (Schwarz 2009)
-- ============================================================================

/-- Schwarz (2009): article type in the D-domain.

Schwarz argues for two structurally distinct definite articles:
- Weak: situational uniqueness
- Strong: anaphoric familiarity

PG&G (2017) build on this: ArticleType predicts D-layer count and
whether DEM pronouns exist. -/
inductive ArticleType where
  | none_         -- No articles (Japanese, Korean, Czech, etc.)
  | weakOnly      -- Weak articles only (e.g., Kutchi Gujarati, French)
  | weakAndStrong -- Both weak and strong articles (e.g., German, Bavarian)
  deriving DecidableEq, BEq, Repr

/-- Which presupposition types a language's article system makes available. -/
def articleTypeToAvailablePresup : ArticleType → List DefPresupType
  | .none_         => []                            -- No articles
  | .weakOnly      => [.uniqueness]                 -- Only uniqueness (or ambiguous)
  | .weakAndStrong => [.uniqueness, .familiarity]   -- Both explicitly

/-- Languages with two article forms have both presupposition types available.
This is PG&G's structural claim translated to semantics: 2 D-layers = 2
presupposition types. -/
theorem two_layers_two_presup_types :
    (articleTypeToAvailablePresup .weakAndStrong).length = 2 := rfl

/-- Languages with one article form have one presupposition type
(modulo ambiguity). -/
theorem one_layer_one_presup_type :
    (articleTypeToAvailablePresup .weakOnly).length = 1 := rfl

-- ============================================================================
-- §3: Definite Use Types (Hawkins 1978 / Schwarz 2013)
-- ============================================================================

/-- Hawkins' (1978) four use types for definite descriptions.
Schwarz (2013) shows these map systematically onto weak vs strong articles. -/
inductive DefiniteUseType where
  | anaphoric          -- Antecedent in prior discourse (strong article)
  | immediateSituation -- Referent present in utterance situation (weak article)
  | largerSituation    -- Unique in larger context, e.g., "the king" (weak article)
  | bridging           -- Related to antecedent via relation (split: see BridgingSubtype)
  deriving DecidableEq, BEq, Repr

/-- Map definite use type to presupposition type (Schwarz 2013 §3.1).

Anaphoric uses require the strong article (familiarity); situational uses
require the weak article (uniqueness). -/
def useTypeToPresupType : DefiniteUseType → DefPresupType
  | .anaphoric          => .familiarity   -- Strong article: discourse-familiar
  | .immediateSituation => .uniqueness    -- Weak article: situationally unique
  | .largerSituation    => .uniqueness    -- Weak article: contextually unique
  | .bridging           => .uniqueness    -- Default weak (relational bridging overrides)

-- ============================================================================
-- §4: Bridging Subtypes (Schwarz 2013 §3.2)
-- ============================================================================

/-- Bridging subtypes (Schwarz 2013 §3.2).
German and Fering show that bridging splits across the two article forms:
- Part-whole bridging → weak article (situational uniqueness)
- Relational bridging → strong article (anaphoric link)

Schwarz's "producer bridging" (e.g., "the play ... the author") is the
prototypical case of relational bridging. -/
inductive BridgingSubtype where
  | partWhole   -- "the fridge ... the crisper" (weak: situational uniqueness)
  | relational  -- "the play ... the author" (strong: anaphoric relation)
  deriving DecidableEq, BEq, Repr

/-- Map bridging subtype to presupposition type (Schwarz 2013 §3.2). -/
def bridgingPresupType : BridgingSubtype → DefPresupType
  | .partWhole  => .uniqueness   -- weak: "the village ... the tower"
  | .relational => .familiarity  -- strong: "the play ... the author"

-- ============================================================================
-- §5: Weak Article Strategy (Schwarz 2013 §4)
-- ============================================================================

/-- How a language expresses the weak/strong article contrast.

Schwarz (2013) surveys languages along two dimensions:
- How many overt article forms? (0, 1, or 2)
- What expresses weak-article definites? (bare nominal, overt article, etc.) -/
inductive WeakArticleStrategy where
  | bareNominal    -- No overt form; bare noun = weak definite (Akan, Mauritian Creole)
  | overtArticle   -- Distinct overt weak article (German contracted, Fering A-form)
  | sameAsStrong   -- Single form for both (Haitian Creole `la`)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §6: The Indefinite–Definite Contrast
-- ============================================================================

/-- The fundamental semantic contrast between indefinite and definite:

- **Indefinite** (some/a): existential quantification, no presupposition
  on prior discourse. Introduces a NEW discourse referent.
- **Definite** (the): presupposes existence (+ uniqueness or familiarity).
  Retrieves an EXISTING referent.

Heim (1982): indefinites are novel, definites are familiar.
This is the dynamic semantics version of the ∃/ι contrast. -/
inductive Definiteness where
  | indefinite  -- ∃: introduces new dref, no presupposition
  | definite    -- ι/familiar: retrieves existing dref, presupposes availability
  deriving DecidableEq, BEq, Repr

/-- Definiteness is a binary contrast. -/
theorem definite_indefinite_exhaustive :
    ∀ d : Definiteness, d = .indefinite ∨ d = .definite := by
  intro d; cases d <;> simp

end Core.Definiteness
