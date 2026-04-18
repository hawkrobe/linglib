import Linglib.Core.Nominal.Description
import Linglib.Core.Definiteness

/-!
# Article Inventory: Surface Forms → Derived Typology
@cite{schwarz-2009} @cite{schwarz-2013} @cite{patel-grosz-grosz-2017}
@cite{moroney-2021} @cite{jenks-2018}

A language's surface inventory of nominal forms (indefinite article, unique
article, anaphoric article, demonstrative, possessive, plus the syncretism
between unique and anaphoric forms) is a richer object than the
`DefMarkingStrategy` typology cells of @cite{moroney-2021} or the
`ArticleType` cells of @cite{schwarz-2009}. The latter are *derivable* from
the former.

`ArticleInventory` is the **single source of truth** for per-language
definiteness data. Per-language strategy/article-type assignments are not
stipulated separately — they are computed from the inventory:

- `licensesKind` — does this inventory have the form a particular
  `NominalKind` constructor needs?
- `toMarkingStrategy` — Moroney 4-cell typology
- `toArticleType` — Schwarz/Patel-Grosz–Grosz 3-cell coarse classification

Bare nominals are always licensed (every language allows bare nouns at some
level — the question is only what readings they admit, which is a matter of
the type-shift hierarchy, not the article inventory).
-/

namespace Core.Nominal

open Core.IntensionalLogic
open Core.Definiteness

-- The structure is declared before `open Core.IntensionalLogic.Variables`
-- because that namespace introduces a `g[n ↦ x]` notation whose `[`
-- conflicts with structure instance-field syntax `[name : Type]`.

-- ════════════════════════════════════════════════════════════════
-- § The Inventory Structure
-- ════════════════════════════════════════════════════════════════

/-- The morphological inventory of nominal forms a language has.

Each field is a `Prop` recording whether the language has an overt form
of the named kind, with a `[Decidable]` instance field so values are
computable. `uniqueAnaphoricSyncretism` records whether `hasUniqueArticle`
and `hasAnaphoricArticle` are realized by the *same* form (English `the`)
or *different* forms (German weak vs strong). When either article is
missing the syncretism flag is uninformative; only `(hasUniqueArticle ∧
hasAnaphoricArticle)` makes the distinction load-bearing. -/
structure ArticleInventory where
  /-- An overt indefinite article (English *a/an*, German *ein-*). -/
  hasIndefinite : Prop
  /-- An overt article for uniqueness/situational definites (German weak,
      English *the*). -/
  hasUniqueArticle : Prop
  /-- An overt article for anaphoric/familiarity definites (German strong,
      English *the*). -/
  hasAnaphoricArticle : Prop
  /-- If both unique and anaphoric articles exist, are they the same form
      (English *the*) or distinct (German weak vs strong)? -/
  uniqueAnaphoricSyncretism : Prop := False
  /-- An overt demonstrative paradigm (English *this/that*; almost
      universal). -/
  hasDemonstrative : Prop
  /-- An overt possessive paradigm (English *my/your*, German *mein-*). -/
  hasPossessive : Prop
  [decHasIndefinite : Decidable hasIndefinite]
  [decHasUniqueArticle : Decidable hasUniqueArticle]
  [decHasAnaphoricArticle : Decidable hasAnaphoricArticle]
  [decUniqueAnaphoricSyncretism : Decidable uniqueAnaphoricSyncretism]
  [decHasDemonstrative : Decidable hasDemonstrative]
  [decHasPossessive : Decidable hasPossessive]

attribute [instance] ArticleInventory.decHasIndefinite
  ArticleInventory.decHasUniqueArticle
  ArticleInventory.decHasAnaphoricArticle
  ArticleInventory.decUniqueAnaphoricSyncretism
  ArticleInventory.decHasDemonstrative
  ArticleInventory.decHasPossessive

-- Now safe to open Variables — structure is already declared.
open Core.IntensionalLogic.Variables

-- ════════════════════════════════════════════════════════════════
-- § Constructor-Level Licensing
-- ════════════════════════════════════════════════════════════════

namespace ArticleInventory

/-- Does this inventory have the surface form needed to realize the given
    `NominalKind` constructor? Bare and `unique` are licensed by
    *availability of the form*; `anaphoric` may be expressed either by a
    distinct anaphoric article (German strong) or by the syncretic article
    (English *the*); demonstratives and possessives need their respective
    paradigms.

    This is not a *grammaticality* claim about every NP — it is a claim
    about morphological availability of the licensing form. -/
def licensesKind {F : Frame} (inv : ArticleInventory) : NominalKind F → Prop
  | .bare _              => True
  | .indefinite _        => inv.hasIndefinite
  | .unique _ _          => inv.hasUniqueArticle
  | .anaphoric _ _       =>
      inv.hasAnaphoricArticle ∨
        (inv.hasUniqueArticle ∧ inv.uniqueAnaphoricSyncretism)
  | .demonstrative ..    => inv.hasDemonstrative
  | .possessive ..       => inv.hasPossessive

instance decLicensesKind {F : Frame} (inv : ArticleInventory) :
    (k : NominalKind F) → Decidable (inv.licensesKind k)
  | .bare _              => isTrue trivial
  | .indefinite _        => inv.decHasIndefinite
  | .unique _ _          => inv.decHasUniqueArticle
  | .anaphoric _ _       =>
      @instDecidableOr _ _ inv.decHasAnaphoricArticle
        (@instDecidableAnd _ _ inv.decHasUniqueArticle
          inv.decUniqueAnaphoricSyncretism)
  | .demonstrative ..    => inv.decHasDemonstrative
  | .possessive ..       => inv.decHasPossessive

/-- Bare nominals are universally licensed by the inventory. -/
@[simp] theorem licensesKind_bare {F : Frame}
    (inv : ArticleInventory) (R : DenotGS F .et) :
    inv.licensesKind (.bare R) := trivial

-- ════════════════════════════════════════════════════════════════
-- § Derivation of Typology Cells
-- ════════════════════════════════════════════════════════════════

/-- Compute Moroney's 4-cell strategy directly from the inventory bools.

    - both forms, syncretic → `.generallyMarked` (English *the*)
    - both forms, distinct → `.bipartite` (German weak vs strong)
    - only anaphoric form → `.markedAnaphoric` (Mandarin/Thai dem)
    - only unique form → `.generallyMarked` (the unique form covers both)
    - neither form → `.unmarked` (Shan, Serbian, Kannada bare)
-/
def toMarkingStrategy (inv : ArticleInventory) : DefMarkingStrategy :=
  if inv.hasUniqueArticle then
    if inv.hasAnaphoricArticle then
      if inv.uniqueAnaphoricSyncretism then .generallyMarked else .bipartite
    else .generallyMarked
  else
    if inv.hasAnaphoricArticle then .markedAnaphoric else .unmarked

/-- Derived classification into the Schwarz/Patel-Grosz–Grosz 3-cell
    `ArticleType` typology. Lossy: collapses `.generallyMarked` and
    `.markedAnaphoric` to `.weakOnly`, as `Core.Definiteness`
    `strategyToArticleType` already documents. -/
def toArticleType (inv : ArticleInventory) : ArticleType :=
  strategyToArticleType inv.toMarkingStrategy

/-- The inventory-derived `ArticleType` agrees with the
    `strategyToArticleType` collapse of the inventory-derived strategy. By
    definition. -/
theorem toArticleType_eq_strategyToArticleType (inv : ArticleInventory) :
    inv.toArticleType = strategyToArticleType inv.toMarkingStrategy := rfl

end ArticleInventory

end Core.Nominal
