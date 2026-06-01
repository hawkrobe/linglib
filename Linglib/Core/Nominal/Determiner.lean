import Linglib.Features.Definiteness
import Linglib.Features.Deixis

/-!
# Determiner

The determiner (D head) as a lexical object, following the standard determiner
taxonomy: `Article`, `Demonstrative`, `Quantifier`, and `Possessive` each
`extends` the base `Determiner`. The base carries only what is universal to all
determiners — a surface `form`; each specialization adds its own structure.

A language's determiner inventory is a `List Determiner.Entry` (a heterogeneous
collection of the four kinds) declared in its Fragment — there is no per-language
wrapper record. The @cite{moroney-2021} definiteness-marking typology
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
* `Article`, `Demonstrative`, `Quantifier`, `Possessive` — the four
  specializations.
* `Determiner.Entry` — a determiner occurrence in a language's inventory.
* `Determiner.markingStrategy` — derives the @cite{moroney-2021} 4-cell typology
  from a declared `List Determiner.Entry`.

## Implementation notes

The semantic side — `Article.denote`, `Demonstrative.denote`, the `Quantifier`
denotation as a generalized quantifier (`Core/Logic/Quantification`), the
`Possessive` possession relation — is deferred to the migration of the
nominal-description substrate; this file is the Frame-free lexical and
typological layer only. `Quantifier` and `Possessive` are therefore declared but
not yet fleshed out beyond the shared `form`.
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
a surface form. Specializations (`Article`, `Demonstrative`, `Quantifier`,
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

/-- A demonstrative (this/that). `definiteUses` is nonempty iff the demonstrative
is the *obligatory* exponent of some definite use (Mandarin anaphoric); for a
plain demonstrative that merely *can* be used deictically it is empty. -/
structure Demonstrative extends Determiner where
  /-- Deictic feature (proximal/medial/distal/unspecified). -/
  deictic : Features.Deixis.Feature
  /-- Definite use-types this demonstrative obligatorily expones. -/
  definiteUses : List DefiniteUseType := []
  deriving DecidableEq, Repr

/-- A quantificational determiner (every/some/most/no). Its denotation is a
generalized quantifier (`Core/Logic/Quantification`); deferred. -/
structure Quantifier extends Determiner
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
  | demonstrative (d : Demonstrative)
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

/-- Derive the @cite{moroney-2021} four-cell definiteness-marking typology from a
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
