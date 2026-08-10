/-!
# Definiteness classifications

Framework-agnostic vocabulary for definiteness phenomena: types classifying
definite descriptions, article systems, and presupposition types without
committing to a particular semantic theory.

The organizing principle is `DefPresupType` — [schwarz-2009]'s binary between
uniqueness and familiarity presuppositions. Every other type here is a
dimension that maps into that distinction: description kinds
(`DescriptionKind`), article inventories (`ArticleType`,
[patel-grosz-grosz-2017]), [hawkins-1978]'s definite use types
(`DefiniteUseType`, refined by [schwarz-2013]), bridging subtypes
(`BridgingSubtype`), and marking typology (`DefMarkingStrategy`,
[jenks-2018] extended by [moroney-2021]). The [heim-1982]
novelty/familiarity contrast appears as the binary `Definiteness`. The
denotational layer lives in `Semantics/Definiteness/Basic.lean` and
`Semantics/Definiteness/Description.lean`.
-/

namespace Semantics.Definiteness

/-! ### The core binary distinction -/

/-- The two presupposition types underlying definite descriptions.

[schwarz-2009]: these correspond to two morphologically distinct articles
in languages like German, Fering, Lakhota, and Akan. Every classification
in this module ultimately maps into this binary type. -/
inductive DefPresupType where
  | uniqueness   -- Russell/Frege/Strawson: ∃!x. φ(x)
  | familiarity  -- Heim/Kamp: x is discourse-familiar
  deriving DecidableEq, Repr

/-- Demonstratives (this/that) project D_deix — the familiarity/strong-article
layer. [schwarz-2013] §5.5 and [patel-grosz-grosz-2017]. -/
def demonstrativePresupType : DefPresupType := .familiarity

/-! ### Description kinds -/

/-- The kinds of nominal description an inventory can realize — the Frame-free
skeleton of `Semantics.Definiteness.Description` (one case per constructor,
payload erased). Inventory questions (realization, marking typology) depend
only on this kind, so they are stated over it rather than over the
entity/index-parameterized `Description`. -/
inductive DescriptionKind where
  | bare
  | indefinite
  | unique
  | anaphoric
  | demonstrative
  | possessive
  deriving DecidableEq, Repr

/-- The description kind realizing a [schwarz-2009] article strength: the weak
article (uniqueness) realizes `unique`, the strong article (familiarity)
realizes `anaphoric`. The Frame-free counterpart of
`Semantics.Definiteness.Description.ofPresupType`. -/
def DefPresupType.toKind : DefPresupType → DescriptionKind
  | .uniqueness  => .unique
  | .familiarity => .anaphoric

namespace DescriptionKind

/-- The kind is a definite description (in the broad sense — uniqueness,
familiarity, demonstrative, or possessive). -/
def IsDefinite : DescriptionKind → Prop
  | .bare | .indefinite => False
  | .unique | .anaphoric | .demonstrative | .possessive => True

instance : DecidablePred IsDefinite := fun k => by
  cases k <;> unfold IsDefinite <;> infer_instance

/-- The kind requires a discourse antecedent: anaphoric and demonstrative do;
unique, possessive, bare, and indefinite do not. -/
def IsAnaphoric : DescriptionKind → Prop
  | .anaphoric | .demonstrative => True
  | _ => False

instance : DecidablePred IsAnaphoric := fun k => by
  cases k <;> unfold IsAnaphoric <;> infer_instance

/-- The kind binds a structural situation pronoun: Coppock–Beaver uniqueness
and demonstratives do (resource situation for maximality and the deictic
check); the other kinds do not. -/
def UsesSituationPronoun : DescriptionKind → Prop
  | .unique | .demonstrative => True
  | _ => False

instance : DecidablePred UsesSituationPronoun := fun k => by
  cases k <;> unfold UsesSituationPronoun <;> infer_instance

/-- The [schwarz-2009]–[schwarz-2013] presupposition type a kind expresses,
where applicable. Bare and indefinite return `none` because they are not (in
themselves) definites. -/
def presupType : DescriptionKind → Option DefPresupType
  | .bare | .indefinite         => none
  | .unique | .possessive       => some .uniqueness
  | .anaphoric | .demonstrative => some .familiarity

/-- Definites are exactly the kinds with a presupposition type. -/
theorem isDefinite_iff_presupType_isSome (k : DescriptionKind) :
    k.IsDefinite ↔ k.presupType.isSome = true := by
  cases k <;> simp [IsDefinite, presupType]

/-- Anaphoric kinds all carry the familiarity presupposition type. -/
theorem IsAnaphoric.presupType_familiarity {k : DescriptionKind}
    (h : k.IsAnaphoric) : k.presupType = some .familiarity := by
  cases k <;> simp_all [IsAnaphoric, presupType]

/-- `toKind` recovers its strength through `presupType`: the round-trip of
`DefPresupType.toKind`. -/
theorem presupType_toKind (p : DefPresupType) :
    p.toKind.presupType = some p := by
  cases p <;> rfl

end DescriptionKind

/-! ### Article types -/

/-- [schwarz-2009]: article type in the D-domain.

Schwarz argues for two structurally distinct definite articles:
- Weak: situational uniqueness
- Strong: anaphoric familiarity

[patel-grosz-grosz-2017] build on this: ArticleType predicts D-layer count and
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
nouns; [moroney-2021]). Semantic availability of presupposition
types is determined by the blocking principle and type-shift hierarchy
([dayal-2004]), not by article inventory alone. -/
def articleTypeToDistinguishedPresup : ArticleType → List DefPresupType
  | .none_         => []                            -- No articles: no morphological signal
  | .weakOnly      => [.uniqueness]                 -- One form: uniqueness (or ambiguous)
  | .weakAndStrong => [.uniqueness, .familiarity]   -- Two forms: both explicitly marked

/-- Languages with two article forms morphologically distinguish both
presupposition types. This is [patel-grosz-grosz-2017]'s structural
claim: 2 D-layers = 2 morphologically distinct presupposition signals. -/
theorem two_forms_two_distinguished :
    (articleTypeToDistinguishedPresup .weakAndStrong).length = 2 := rfl

/-- Languages with one article form morphologically distinguish one
presupposition type (modulo ambiguity). -/
theorem one_form_one_distinguished :
    (articleTypeToDistinguishedPresup .weakOnly).length = 1 := rfl

/-! ### Definite use types -/

/-- [hawkins-1978]'s four use types for definite descriptions.
[schwarz-2013] shows these map systematically onto weak vs strong articles. -/
inductive DefiniteUseType where
  | anaphoric          -- Antecedent in prior discourse (strong article)
  | immediateSituation -- Referent present in utterance situation (weak article)
  | largerSituation    -- Unique in larger context, e.g., "the king" (weak article)
  | bridging           -- Related to antecedent via relation (split: see BridgingSubtype)
  | donkey             -- Donkey anaphora: variable bound by c-commanding quantifier.
                       -- German: strong article (*von dem*); Thai/Mandarin: demonstrative.
                       -- [schwarz-2009] §3: donkey pronouns pattern with anaphoric
                       -- uses (familiarity), not uniqueness uses.
  deriving DecidableEq, Repr

/-- Map definite use type to presupposition type ([schwarz-2013] §3.1).

Anaphoric uses require the strong article (familiarity); situational uses
require the weak article (uniqueness). -/
def useTypeToPresupType : DefiniteUseType → DefPresupType
  | .anaphoric          => .familiarity   -- Strong article: discourse-familiar
  | .immediateSituation => .uniqueness    -- Weak article: situationally unique
  | .largerSituation    => .uniqueness    -- Weak article: contextually unique
  | .bridging           => .uniqueness    -- Default weak (relational bridging overrides)
  | .donkey             => .familiarity   -- Strong article: donkey anaphora patterns
                                          -- with familiarity ([schwarz-2009] §3)

/-! ### Bridging subtypes -/

/-- Bridging subtypes ([schwarz-2013] §3.2).
German and Fering show that bridging splits across the two article forms:
- Part-whole bridging → weak article (situational uniqueness)
- Relational bridging → strong article (anaphoric link)

Schwarz's "producer bridging" (e.g., "the play... the author") is the
prototypical case of relational bridging. -/
inductive BridgingSubtype where
  | partWhole   -- "the fridge ... the crisper" (weak: situational uniqueness)
  | relational  -- "the play ... the author" (strong: anaphoric relation)
  deriving DecidableEq, Repr

/-- Map bridging subtype to presupposition type ([schwarz-2013] §3.2). -/
def bridgingPresupType : BridgingSubtype → DefPresupType
  | .partWhole  => .uniqueness   -- weak: "the village ... the tower"
  | .relational => .familiarity  -- strong: "the play ... the author"

/-! ### Weak article strategies -/

/-- How a language expresses the weak/strong article contrast.

[schwarz-2013] surveys languages along two dimensions:
- How many overt article forms? (0, 1, or 2)
- What expresses weak-article definites? (bare nominal, overt article, etc.) -/
inductive WeakArticleStrategy where
  | bareNominal    -- No overt form; bare noun = weak definite (Mauritian Creole).
                   -- Akan also uses this strategy, though Akan bare NPs have
                   -- context-dependent readings: definite for globally unique
                   -- referents (*ewia* 'sun'), indefinite/∃ otherwise.
                   -- See [owusu-2022], [philipp-2022].
  | overtArticle   -- Distinct overt weak article (German contracted, Fering A-form)
  | sameAsStrong   -- Single form for both (Haitian Creole `la`)
  deriving DecidableEq, Repr

/-! ### The indefinite–definite contrast -/

/-- The fundamental semantic contrast between indefinite and definite:

- **Indefinite** (some/a): existential quantification, no presupposition
  on prior discourse. Introduces a NEW discourse referent.
- **Definite** (the): presupposes existence (+ uniqueness or familiarity).
  Retrieves an EXISTING referent.

[heim-1982]: indefinites are novel, definites are familiar.
This is the dynamic semantics version of the ∃/ι contrast. -/
inductive Definiteness where
  | indefinite  -- ∃: introduces new dref, no presupposition
  | definite    -- ι/familiar: retrieves existing dref, presupposes availability
  deriving DecidableEq, Repr

/-- Definiteness is a binary contrast. -/
theorem definite_indefinite_exhaustive :
    ∀ d : Definiteness, d = .indefinite ∨ d = .definite := by
  intro d; cases d <;> simp

/-! ### Definiteness marking typology -/

/-- Cross-linguistic strategy for marking definiteness, following
[jenks-2018]'s typology extended by [moroney-2021] with the
`.unmarked` category.

The original [jenks-2018] typology had four cells (2×2:
both-marked × same/different + one-marked × unique/anaphoric), but
"one-marked, unique" was unattested. [moroney-2021] adds a fifth:
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
      Languages: Shan, Serbian, Kannada. NEW in [moroney-2021]. -/
  | unmarked
  deriving DecidableEq, Repr

/-- Map marking strategy to `ArticleType`. Lossy: `.generallyMarked`
and `.markedAnaphoric` both map to `.weakOnly`.

Per-language strategy values are *not* stipulated here — they are derived
from each language's declared determiner set via `Determiner.Inventory.markingStrategy`.
This function records only the cross-typology coarsening relation (Moroney's
4-cell strategy → Schwarz's 3-cell `ArticleType`). -/
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

end Semantics.Definiteness
