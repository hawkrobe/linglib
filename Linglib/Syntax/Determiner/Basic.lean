import Linglib.Features.Definiteness
import Linglib.Features.Deixis
import Linglib.Features.Number.Basic

/-!
# Determiner

The determiner (D head) as a lexical object, following the standard determiner
taxonomy: `Article`, `DemonstrativeDeterminer`, `Quantifier`, and `Possessive` each
`extends` the base `Determiner`. The base carries only what is universal to all
determiners — a surface `form`; each specialization adds its own structure.

A language's determiner inventory is a `List Determiner.Entry` (a heterogeneous
collection of the four kinds) declared in its Fragment — there is no per-language
wrapper record. The [moroney-2021] definiteness-marking typology
(`DefMarkingStrategy`) is *derived* from that list by `markingStrategy`, not
stipulated: a language's Moroney cell is a theorem about its declared
determiners, checked by `decide`.

Because `Article` records its `exponent`, a classifier-phrase definite and a
dedicated-article definite are both `Article`s differing only there, so a
classifier language declares a definite *and* an indefinite `Article`
symmetrically — the contested "is [Clf-N] a definite marker" question is
localized to a single declaration.

## Main declarations

* `Determiner` — the base D-head record (just `form`).
* `Article`, `DemonstrativeDeterminer`, `Quantifier`, `Possessive` — the four
  specializations.
* `Determiner.Entry` — a determiner occurrence in a language's inventory.
* `Determiner.markingStrategy` — derives the [moroney-2021] 4-cell typology
  from a declared `List Determiner.Entry`.

## Implementation notes

An `Article`'s admissible [schwarz-2009] strengths are `Article.presupTypes`
(Frame-free, read off `uses`); its denotation is `Article.toDescriptions`
(`Semantics/Definiteness/DeterminerLicensing.lean`, Frame-aware) — the set of `Description`s
those strengths admit via `Description.ofPresupType`, so a syncretic article like
English *the* denotes *both* the weak and the strong description.
(`Semantics/Quantification`), and the `Possessive` possession relation remain
deferred; `Quantifier`/`Possessive` are declared but not fleshed out beyond `form`.
This file stays the Frame-free lexical/typological layer.
-/

open Features.Definiteness
  (DefPresupType DefiniteUseType DefMarkingStrategy Definiteness ArticleType
   useTypeToPresupType strategyToArticleType)

namespace Determiner

/-- How an article is morphosyntactically realized. Analysis-neutral: the
distinction between a dedicated article morpheme and a classifier/numeral/
demonstrative construction is recorded here, not used to decide whether the form
"counts" as marking definiteness — that is the `uses` field's job. -/
inductive Exponent where
  /-- A dedicated article morpheme (English *the*/*a*, German *der*/*ein*). -/
  | dedicatedMorpheme
  /-- A bare classifier phrase (Cantonese [Clf-N] definite). -/
  | classifierPhrase
  /-- A numeral-classifier phrase (Cantonese [jat-Clf-N] indefinite). -/
  | numeralClassifier
  /-- A demonstrative form doing definite duty (Mandarin *na* anaphoric). -/
  | demonstrativeForm
  /-- A bare noun whose reading is fixed by covert type-shift. -/
  | bareNoun
  deriving DecidableEq, Repr

end Determiner

/-- The base determiner (D head): only what is universal to every determiner —
a surface form. Specializations (`Article`, `DemonstrativeDeterminer`, `Quantifier`,
`Possessive`) `extends` this. -/
structure Determiner where
  /-- Surface form (a representative morpheme or construction label). -/
  form : String
  deriving DecidableEq, Repr

/-- An article: the definite/indefinite determiner. `uses` is the definite
use-types it obligatorily expones (empty for indefinites). -/
structure Article extends Determiner where
  /-- Definite or indefinite. -/
  definiteness : Definiteness
  /-- How the article is realized. -/
  exponent : Determiner.Exponent
  /-- The definite use-types this article obligatorily expones. -/
  uses : List DefiniteUseType := []
  deriving DecidableEq, Repr

/-- A demonstrative determiner (*this*/*that* book). `definiteUses` is nonempty iff the
demonstrative is the *obligatory* exponent of some definite use (Mandarin anaphoric); for a
plain demonstrative that merely *can* be used deictically it is empty. The determiner carrier of
the word-class-neutral `Demonstrative` deixis capability, sharing it with `DemonstrativePronoun`. -/
structure DemonstrativeDeterminer extends Determiner where
  /-- Deictic feature (proximal/medial/distal/unspecified). -/
  deictic : Features.Deixis.Feature
  /-- Definite use-types this demonstrative obligatorily expones. -/
  definiteUses : List DefiniteUseType := []
  deriving DecidableEq, Repr

/-- The demonstrative determiner exposes its `deictic` field as the `Demonstrative` capability,
    shared word-class-neutrally with `DemonstrativePronoun`. -/
instance : Demonstrative DemonstrativeDeterminer := ⟨DemonstrativeDeterminer.deictic⟩

/-- A quantificational determiner (every/some/most/no), marked like a `Pronoun`: a
decidable lexical record carrying only what the *meaning leaves open* — the morphosyntactic
idiosyncrasies on which synonymous determiners diverge. Its denotation is a generalized
quantifier (`Semantics/Quantification`) supplied *externally* (the entry carries no `GQ`,
exactly as `Pronoun` carries no referent); everything the meaning *fixes* — force, class,
monotonicity, strength, conservativity — is a theorem about that denotation, not a field. -/
structure Quantifier extends Determiner where
  /-- Selectional number: the grammatical number the determiner combines with
      (*every* → singular, *all*/*most* → plural; `none` = number-neutral). Not fixed by the
      GQ — *every* and *all* can share a denotation yet differ here. -/
  numberRestriction : Option Number := none
  /-- Selects mass NPs? (*much*/*all* do; *every*/*both* don't.) Likewise not fixed by the GQ. -/
  selectsMass : Bool := false
  deriving DecidableEq, Repr

/-- A possessive determiner (my/your/the boy's). Its denotation is definiteness
via a possession relation; deferred. -/
structure Possessive extends Determiner
  deriving DecidableEq, Repr

namespace Determiner

/-- A determiner occurrence in a language's inventory: one of the four kinds,
carrying its typed payload. -/
inductive Entry where
  | article (a : Article)
  | demonstrative (d : DemonstrativeDeterminer)
  | quantifier (q : Quantifier)
  | possessive (p : Possessive)
  deriving DecidableEq, Repr

/-- The definite use-types a determiner occurrence obligatorily expones. Only
definite articles and (obligatory) demonstratives contribute; indefinite
articles, quantifiers, and possessives expone none. -/
def Entry.definiteUses : Entry → List DefiniteUseType
  | .article a      => a.uses
  | .demonstrative d => d.definiteUses
  | .quantifier _   => []
  | .possessive _   => []

/-! ### Deriving the Moroney typology from a declared determiner set -/

/-- The declared set obligatorily marks presupposition type `p` — some
determiner expones a definite use whose presupposition is `p`. -/
def MarksPresup (ds : List Entry) (p : DefPresupType) : Prop :=
  ∃ e ∈ ds, ∃ u ∈ e.definiteUses, useTypeToPresupType u = p

instance (ds : List Entry) (p : DefPresupType) : Decidable (MarksPresup ds p) := by
  unfold MarksPresup; infer_instance

/-- Some single determiner is the exponent of *both* presupposition types
(English *the*). Distinguishes `.generallyMarked` (one form covers both) from
`.bipartite` (German weak vs strong). -/
def IsSyncretic (ds : List Entry) : Prop :=
  ∃ e ∈ ds, (∃ u ∈ e.definiteUses, useTypeToPresupType u = .uniqueness)
          ∧ (∃ u ∈ e.definiteUses, useTypeToPresupType u = .familiarity)

instance (ds : List Entry) : Decidable (IsSyncretic ds) := by
  unfold IsSyncretic; infer_instance

/-- Derive the [moroney-2021] four-cell definiteness-marking typology from a
declared determiner set. Stored nowhere — a language's cell is a theorem about
its `List Determiner.Entry`. Reproduces the decision table of the former
boolean article inventory:

- uniqueness marked, familiarity marked, by one form → `.generallyMarked`
- uniqueness marked, familiarity marked, by distinct forms → `.bipartite`
- uniqueness marked, familiarity unmarked → `.generallyMarked`
- uniqueness unmarked, familiarity marked (e.g. via demonstrative) → `.markedAnaphoric`
- neither marked → `.unmarked`
-/
def markingStrategy (ds : List Entry) : DefMarkingStrategy :=
  if MarksPresup ds .uniqueness then
    if MarksPresup ds .familiarity then
      if IsSyncretic ds then .generallyMarked else .bipartite
    else .generallyMarked
  else if MarksPresup ds .familiarity then .markedAnaphoric else .unmarked

/-- Derived Schwarz/Patel-Grosz–Grosz 3-cell `ArticleType` classification. Lossy:
`.generallyMarked` and `.markedAnaphoric` both collapse to `.weakOnly`, as
`strategyToArticleType` documents. -/
def articleType (ds : List Entry) : ArticleType :=
  strategyToArticleType (markingStrategy ds)

/-! ### Kind predicates over an inventory (for licensing) -/

/-- The occurrence is an indefinite article. -/
def Entry.IsIndefiniteArticle : Entry → Prop
  | .article a => a.definiteness = .indefinite
  | _          => False

instance : DecidablePred Entry.IsIndefiniteArticle := fun e => by
  cases e <;> unfold Entry.IsIndefiniteArticle <;> infer_instance

/-- The occurrence is a demonstrative. -/
def Entry.IsDemonstrative : Entry → Prop
  | .demonstrative _ => True
  | _                => False

instance : DecidablePred Entry.IsDemonstrative := fun e => by
  cases e <;> unfold Entry.IsDemonstrative <;> infer_instance

/-- The occurrence is a possessive. -/
def Entry.IsPossessive : Entry → Prop
  | .possessive _ => True
  | _             => False

instance : DecidablePred Entry.IsPossessive := fun e => by
  cases e <;> unfold Entry.IsPossessive <;> infer_instance

/-! ### Cell coverage: the derivation reproduces all four Moroney cells -/

/-- English: one definite article covering both presupposition types + an
indefinite article → `.generallyMarked`. -/
example : markingStrategy
    [ .article { form := "the", definiteness := .definite, exponent := .dedicatedMorpheme,
                 uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] },
      .article { form := "a", definiteness := .indefinite, exponent := .dedicatedMorpheme } ]
    = .generallyMarked := by decide

/-- German: distinct weak (uniqueness) and strong (familiarity) definite
articles → `.bipartite`. -/
example : markingStrategy
    [ .article { form := "der/weak", definiteness := .definite, exponent := .dedicatedMorpheme,
                 uses := [.immediateSituation, .largerSituation] },
      .article { form := "der/strong", definiteness := .definite, exponent := .dedicatedMorpheme,
                 uses := [.anaphoric, .donkey] },
      .article { form := "ein", definiteness := .indefinite, exponent := .dedicatedMorpheme } ]
    = .bipartite := by decide

/-- Mandarin: the demonstrative expones anaphoric definites; uniqueness is bare
(no determiner) → `.markedAnaphoric`. -/
example : markingStrategy
    [ .demonstrative { form := "na", deictic := .distal, definiteUses := [.anaphoric] } ]
    = .markedAnaphoric := by decide

/-- Cantonese: one classifier-phrase definite article covering both uses + a
numeral-classifier indefinite article → `.generallyMarked`. The indefinite is a
first-class `Article`, so the old `hasIndefinite := False` asymmetry is gone. -/
example : markingStrategy
    [ .article { form := "Clf-N", definiteness := .definite, exponent := .classifierPhrase,
                 uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] },
      .article { form := "jat-Clf-N", definiteness := .indefinite, exponent := .numeralClassifier } ]
    = .generallyMarked := by decide

/-- Shan: the demonstrative is optional — it expones nothing obligatorily →
`.unmarked`. (Contrast Mandarin, where it obligatorily expones the anaphoric
use.) -/
example : markingStrategy
    [ .demonstrative { form := "naaj/nan", deictic := .proximal, definiteUses := [] } ]
    = .unmarked := by decide

end Determiner

/-! ### Admissible article strengths

The [schwarz-2009] presupposition types an article *can* express — its
admissible readings, read off `uses`. A syncretic article (English *the*) admits
both; a weak- or strong-only article admits one. The image of these under
`Description.ofPresupType` is the article's set of possible denotations
(`Article.toDescriptions`, in `DeterminerLicensing.lean`). -/

/-- The [schwarz-2009] strengths an article admits, read off its `uses` (as a
list — `DefPresupType` is binary, so its content is the membership-closure). -/
def Article.presupTypes (a : Article) : List DefPresupType :=
  a.uses.map useTypeToPresupType

/-- An article admits strength `p` iff a one-article inventory containing it marks
`p` — the single-article case of `Determiner.MarksPresup`. -/
theorem Article.mem_presupTypes_iff_marksPresup (a : Article) (p : DefPresupType) :
    p ∈ a.presupTypes ↔ Determiner.MarksPresup [.article a] p := by
  unfold Article.presupTypes Determiner.MarksPresup
  rw [List.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨.article a, List.mem_singleton_self _, u, hu, rfl⟩
  · rintro ⟨e, he, u, hu, rfl⟩
    rw [List.mem_singleton] at he
    subst he
    exact ⟨u, hu, rfl⟩
