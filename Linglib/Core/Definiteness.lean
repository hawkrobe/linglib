/-!
# Definiteness: Types and Classifications
@cite{donnellan-1966} @cite{hawkins-1978} @cite{heim-1982} @cite{patel-grosz-grosz-2017} @cite{schwarz-2009} @cite{schwarz-2013}

Framework-agnostic vocabulary for definiteness phenomena. These types classify
definite descriptions, article systems, and presupposition types without
committing to any particular semantic theory.

The organizing principle is `DefPresupType` (.uniqueness |.familiarity) —
every other type in this module is a dimension that maps into this binary
distinction: article morphology, pragmatic use type, bridging relation, etc.

Used by:
- `Theories/Semantics.Montague/Determiner/Definite.lean` (denotations: ⟦the⟧)
- `Phenomena/Anaphora/PronounTypology.lean` (cross-linguistic article data)
- `Phenomena/Anaphora/Bridging.lean` (bridging presupposition types)

-/

namespace Core.Definiteness

-- ============================================================================
-- §1: The Core Binary Distinction
-- ============================================================================

/-- The two presupposition types underlying definite descriptions.

@cite{schwarz-2009}: these correspond to two morphologically distinct articles
in languages like German, Fering, Lakhota, and Akan. Every classification
in this module ultimately maps into this binary type. -/
inductive DefPresupType where
  | uniqueness   -- Russell/Frege/Strawson: ∃!x. φ(x)
  | familiarity  -- Heim/Kamp: x is discourse-familiar
  deriving DecidableEq, Repr

/-- Demonstratives (this/that) project D_deix — the familiarity/strong-article
layer. @cite{schwarz-2013} §5.5 and @cite{patel-grosz-grosz-2017}. -/
def demonstrativePresupType : DefPresupType := .familiarity

-- ============================================================================
-- §2: Article Types (@cite{schwarz-2009})
-- ============================================================================

/-- @cite{schwarz-2009}: article type in the D-domain.

Schwarz argues for two structurally distinct definite articles:
- Weak: situational uniqueness
- Strong: anaphoric familiarity

@cite{patel-grosz-grosz-2017} build on this: ArticleType predicts D-layer count and
whether DEM pronouns exist. -/
inductive ArticleType where
  | none_         -- No articles (Japanese, Korean, Czech, etc.)
  | weakOnly      -- Weak articles only (e.g., Kutchi Gujarati, French)
  | weakAndStrong -- Both weak and strong articles (e.g., German, Bavarian)
  deriving DecidableEq, Repr

/-- Which presupposition types are **morphologically distinguished** by a
language's article system. This tracks overt marking, not semantic
availability: a language with no articles (`.none_`) morphologically
distinguishes zero presupposition types, but may still *express* both
uniqueness and familiarity via covert type-shifting (e.g., Shan bare
nouns; @cite{moroney-2021}). Semantic availability of presupposition
types is determined by the blocking principle and type-shift hierarchy
(@cite{dayal-2004}), not by article inventory alone. -/
def articleTypeToDistinguishedPresup : ArticleType → List DefPresupType
  | .none_         => []                            -- No articles: no morphological signal
  | .weakOnly      => [.uniqueness]                 -- One form: uniqueness (or ambiguous)
  | .weakAndStrong => [.uniqueness, .familiarity]   -- Two forms: both explicitly marked

/-- Languages with two article forms morphologically distinguish both
presupposition types. This is @cite{patel-grosz-grosz-2017}'s structural
claim: 2 D-layers = 2 morphologically distinct presupposition signals. -/
theorem two_forms_two_distinguished :
    (articleTypeToDistinguishedPresup .weakAndStrong).length = 2 := rfl

/-- Languages with one article form morphologically distinguish one
presupposition type (modulo ambiguity). -/
theorem one_form_one_distinguished :
    (articleTypeToDistinguishedPresup .weakOnly).length = 1 := rfl

-- ============================================================================
-- §3: Definite Use Types (@cite{hawkins-1978} / @cite{schwarz-2013})
-- ============================================================================

/-- @cite{hawkins-1978}'s four use types for definite descriptions.
@cite{schwarz-2013} shows these map systematically onto weak vs strong articles. -/
inductive DefiniteUseType where
  | anaphoric          -- Antecedent in prior discourse (strong article)
  | immediateSituation -- Referent present in utterance situation (weak article)
  | largerSituation    -- Unique in larger context, e.g., "the king" (weak article)
  | bridging           -- Related to antecedent via relation (split: see BridgingSubtype)
  | donkey             -- Donkey anaphora: variable bound by c-commanding quantifier.
                       -- German: strong article (*von dem*); Thai/Mandarin: demonstrative.
                       -- @cite{schwarz-2009} §3: donkey pronouns pattern with anaphoric
                       -- uses (familiarity), not uniqueness uses.
  deriving DecidableEq, Repr

/-- Map definite use type to presupposition type (@cite{schwarz-2013} §3.1).

Anaphoric uses require the strong article (familiarity); situational uses
require the weak article (uniqueness). -/
def useTypeToPresupType : DefiniteUseType → DefPresupType
  | .anaphoric          => .familiarity   -- Strong article: discourse-familiar
  | .immediateSituation => .uniqueness    -- Weak article: situationally unique
  | .largerSituation    => .uniqueness    -- Weak article: contextually unique
  | .bridging           => .uniqueness    -- Default weak (relational bridging overrides)
  | .donkey             => .familiarity   -- Strong article: donkey anaphora patterns
                                          -- with familiarity (@cite{schwarz-2009} §3)

-- ============================================================================
-- §4: Bridging Subtypes (@cite{schwarz-2013} §3.2)
-- ============================================================================

/-- Bridging subtypes (@cite{schwarz-2013} §3.2).
German and Fering show that bridging splits across the two article forms:
- Part-whole bridging → weak article (situational uniqueness)
- Relational bridging → strong article (anaphoric link)

Schwarz's "producer bridging" (e.g., "the play... the author") is the
prototypical case of relational bridging. -/
inductive BridgingSubtype where
  | partWhole   -- "the fridge ... the crisper" (weak: situational uniqueness)
  | relational  -- "the play ... the author" (strong: anaphoric relation)
  deriving DecidableEq, Repr

/-- Map bridging subtype to presupposition type (@cite{schwarz-2013} §3.2). -/
def bridgingPresupType : BridgingSubtype → DefPresupType
  | .partWhole  => .uniqueness   -- weak: "the village ... the tower"
  | .relational => .familiarity  -- strong: "the play ... the author"

-- ============================================================================
-- §5: Weak Article Strategy (@cite{schwarz-2013} §4)
-- ============================================================================

/-- How a language expresses the weak/strong article contrast.

@cite{schwarz-2013} surveys languages along two dimensions:
- How many overt article forms? (0, 1, or 2)
- What expresses weak-article definites? (bare nominal, overt article, etc.) -/
inductive WeakArticleStrategy where
  | bareNominal    -- No overt form; bare noun = weak definite (Mauritian Creole).
                   -- Akan also uses this strategy, though Akan bare NPs have
                   -- context-dependent readings: definite for globally unique
                   -- referents (*ewia* 'sun'), indefinite/∃ otherwise.
                   -- See @cite{owusu-2022}, @cite{philipp-2022}.
  | overtArticle   -- Distinct overt weak article (German contracted, Fering A-form)
  | sameAsStrong   -- Single form for both (Haitian Creole `la`)
  deriving DecidableEq, Repr

-- ============================================================================
-- §6: The Indefinite–Definite Contrast
-- ============================================================================

/-- The fundamental semantic contrast between indefinite and definite:

- **Indefinite** (some/a): existential quantification, no presupposition
  on prior discourse. Introduces a NEW discourse referent.
- **Definite** (the): presupposes existence (+ uniqueness or familiarity).
  Retrieves an EXISTING referent.

@cite{heim-1982}: indefinites are novel, definites are familiar.
This is the dynamic semantics version of the ∃/ι contrast. -/
inductive Definiteness where
  | indefinite  -- ∃: introduces new dref, no presupposition
  | definite    -- ι/familiar: retrieves existing dref, presupposes availability
  deriving DecidableEq, Repr

/-- Definiteness is a binary contrast. -/
theorem definite_indefinite_exhaustive :
    ∀ d : Definiteness, d = .indefinite ∨ d = .definite := by
  intro d; cases d <;> simp

-- ============================================================================
-- §7: Definiteness Marking Typology (@cite{jenks-2018} / @cite{moroney-2021})
-- ============================================================================

/-- Cross-linguistic strategy for marking definiteness, following
@cite{jenks-2018}'s typology extended by @cite{moroney-2021} with the
`.unmarked` category.

The original @cite{jenks-2018} typology had four cells (2×2:
both-marked × same/different + one-marked × unique/anaphoric), but
"one-marked, unique" was unattested. @cite{moroney-2021} adds a fifth:
neither type is obligatorily marked, yet both are expressible via bare
nouns. This captures Shan, Serbian, and Kannada.

This is strictly finer than `ArticleType`: `.generallyMarked` and
`.markedAnaphoric` both map to `ArticleType.weakOnly`, so `ArticleType`
collapses a real distinction. -/
inductive DefMarkingStrategy where
  /-- Both unique and anaphoric definiteness are marked with the same form.
      Languages: English (*the*), Cantonese. -/
  | generallyMarked
  /-- Unique and anaphoric definiteness are marked with different forms.
      Languages: German (weak/strong articles), Lakhota. -/
  | bipartite
  /-- Only anaphoric definiteness is obligatorily marked (via demonstrative).
      Unique definiteness is expressed with bare nouns.
      Languages: Mandarin, Akan, Wu. -/
  | markedAnaphoric
  /-- Neither type is obligatorily marked. Bare nouns can express both
      unique and anaphoric definiteness. Demonstrative-noun phrases are
      optional in anaphoric contexts.
      Languages: Shan, Serbian, Kannada. NEW in @cite{moroney-2021}. -/
  | unmarked
  deriving DecidableEq, Repr

/-- Language-specific definiteness parameters: the article inventory and
what each form expresses. This is the input from which `DefMarkingStrategy`
is derivable — rather than stipulating the strategy directly, we derive it
from the language's overt forms and which type-shifts they block.

@cite{moroney-2021} Tables 4.6–4.9: the blocking principle + article
inventory jointly determine the marking strategy. -/
structure DefMarkingParams where
  /-- Does the language have an overt form for unique definiteness? -/
  hasUniqueForm : Bool
  /-- Does the language have an overt form for anaphoric definiteness? -/
  hasAnaphoricForm : Bool
  /-- If both forms exist, are they the same form? -/
  sameForm : Bool := false
  deriving Repr, DecidableEq

/-- Derive the marking strategy from language-specific parameters.

This replaces stipulated classification: instead of manually classifying
each language, we derive its classification from observable properties
(article inventory). -/
def deriveStrategy : DefMarkingParams → DefMarkingStrategy
  | ⟨true, true, true⟩   => .generallyMarked
  | ⟨true, true, false⟩  => .bipartite
  | ⟨false, true, _⟩     => .markedAnaphoric
  | ⟨true, false, _⟩     => .generallyMarked
  | ⟨false, false, _⟩    => .unmarked

/-- Map marking strategy to `ArticleType`. Lossy: `.generallyMarked`
and `.markedAnaphoric` both map to `.weakOnly`. -/
def strategyToArticleType : DefMarkingStrategy → ArticleType
  | .generallyMarked  => .weakOnly
  | .bipartite        => .weakAndStrong
  | .markedAnaphoric  => .weakOnly
  | .unmarked         => .none_

/-- The marking strategy typology is finer than `ArticleType`:
`.generallyMarked` and `.markedAnaphoric` both map to `.weakOnly`,
so `ArticleType` cannot distinguish them. -/
theorem strategy_finer_than_articleType :
    strategyToArticleType .generallyMarked =
    strategyToArticleType .markedAnaphoric ∧
    DefMarkingStrategy.generallyMarked ≠ .markedAnaphoric :=
  ⟨rfl, by decide⟩

end Core.Definiteness
