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
-- §6: Definite Description Structure
-- ============================================================================

/-- A definite description is characterized by two predicates:

1. **restrictor** P: the NP-internal content ("dog", "book", "man drinking
   a martini"). This is what the definite description is "about."

2. **presupFilter** Q: the discourse-linking content (anaphoric index,
   familiarity condition). This is what connects the description to
   prior discourse or the utterance situation.

The presupposition of a definite description is: ∃!x ∈ domain. P(x) ∧ Q(x).
The assertion is: S(that unique x).

The @cite{schwarz-2009} weak/strong distinction reduces to the triviality
of Q:
- **Weak article** (uniqueness): Q = λ _ => true — no discourse-linking
  requirement. The description succeeds by situational uniqueness alone.
- **Strong article** (familiarity): Q is a non-trivial anaphoric predicate.
  The description succeeds only for discourse-familiar entities.

@cite{moroney-2021} Def 508: ι^x P Q = ιx[P(x) ∧ Q(x)] is the general
form; standard ι P = ι^x P (λ _ => true) is the special case. -/
structure DefiniteDesc (E : Type) where
  /-- NP-internal content: the restrictor predicate -/
  restrictor : E → Bool
  /-- Discourse-linking content: the presupposition filter.
      Trivial (λ _ => true) for uniqueness; non-trivial for familiarity. -/
  presupFilter : E → Bool

/-- Construct a uniqueness-based (weak, ι) definite description.
The presupposition filter is vacuous — any entity in the domain
that satisfies the restrictor is a candidate. -/
def DefiniteDesc.unique {E : Type} (restrictor : E → Bool) : DefiniteDesc E :=
  ⟨restrictor, λ _ => true⟩

/-- Construct an anaphoric (strong, ι^x) definite description.
The presupposition filter Q further restricts candidates to
discourse-familiar entities. -/
def DefiniteDesc.anaphoric {E : Type}
    (restrictor : E → Bool) (anaphoricQ : E → Bool) : DefiniteDesc E :=
  ⟨restrictor, anaphoricQ⟩

/-- A uniqueness description is an anaphoric description with trivial Q. -/
theorem DefiniteDesc.unique_eq_anaphoric_trivial {E : Type}
    (restrictor : E → Bool) :
    DefiniteDesc.unique restrictor =
    DefiniteDesc.anaphoric restrictor (λ _ => true) := rfl

-- ============================================================================
-- §7: The Indefinite–Definite Contrast
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

end Core.Definiteness
