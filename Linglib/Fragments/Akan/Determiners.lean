import Linglib.Syntax.Category.Determiner.Basic

/-!
# Akan determiner inventory

Textbook-consensus types for the Akan (Kwa, Niger-Congo) determiner
system, with no analytical denotations. The inventory is uncontroversial
across the Akan literature ([amfo-2010], [arkoh-matthewson-2013],
[owusu-2022] Ch 2–3). The strong definite *nó* marks anaphoric reference,
uniqueness definites are bare nominals, and *bí* marks indefinites;
covarying (donkey) uses of *nó* are unreported in [schwarz-2013] §4.1.1.
Paper-specific denotations ([schwarz-2013] strong-DEF, [bombi-2018]
weak-DEF, [owusu-2022] skolem-CF for *bí*, etc.) live in Studies files
that consume these entries.

## Main declarations

* `Akan.Determiners.inventory` — the declared inventory, deriving the
  `.markedAnaphoric` Moroney cell.
* `Akan.Determiners.Definite` — bare NP vs. *nó* (the DEF marker).
* `Akan.Determiners.Indefinite` — bare NP vs. *bí* (the INDEF marker).

## Implementation notes

The Akan DEF marker *nó* occurs both nominally and clausally
([owusu-2022] Ch 4); only the nominal use is typed here.
Bare NPs appear under both definiteness values ([owusu-2022] Ch 2 on
definite bare nouns; App. A on bare-noun kind/indefinite readings) —
the `bare` constructor is shared between the two inductives to reflect
this.
-/

namespace Akan.Determiners

/-- The declared Akan determiners are the strong definite *nó* and the
    indefinite *bí*; uniqueness definites are bare. -/
def inventory : Determiner.Inventory :=
  [ .article { form := "nó", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric] },
    .article { form := "bí", definiteness := .indefinite, exponent := .dedicatedMorpheme } ]

/-- Akan derives the `.markedAnaphoric` Moroney cell. -/
theorem marking : inventory.markingStrategy = .markedAnaphoric := by decide

/-- Akan adnominal definiteness contrast ([owusu-2022] Ch 2). -/
inductive Definite where
  /-- Bare NP — definiteness inferred from context. -/
  | bare
  /-- *nó* — postnominal DEF marker. Cross-categorial: also occurs on
      VPs and TPs ([arkoh-matthewson-2013], [owusu-2022] Ch 4). -/
  | no
  deriving DecidableEq, Repr

/-- Akan adnominal indefiniteness contrast ([owusu-2022] Ch 3). -/
inductive Indefinite where
  /-- Bare NP — indefiniteness inferred from context. -/
  | bare
  /-- *bí* — postnominal INDEF marker. -/
  | bi
  deriving DecidableEq, Repr

end Akan.Determiners
