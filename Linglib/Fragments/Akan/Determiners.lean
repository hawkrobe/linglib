/-!
# Akan determiner inventory

Textbook-consensus types for the Akan (Kwa, Niger-Congo) determiner
system, with no analytical denotations. The inventory is uncontroversial
across the Akan literature (Christaller 1875, Boadi 1974, @cite{amfo-2010},
@cite{arkoh-matthewson-2013}, @cite{owusu-2022} Ch 1–2). Paper-specific
denotations (Schwarz 2013 strong-DEF, @cite{bombi-2018} weak-DEF,
@cite{owusu-2022} skolem-CF for *bí*, etc.) live in Studies files that
consume these entries.

## Main declarations

* `Fragments.Akan.Determiners.Definite` — bare NP vs. *nó* (the DEF marker).
* `Fragments.Akan.Determiners.Indefinite` — bare NP vs. *bí* (the INDEF marker).

## Implementation notes

The Akan DEF marker *nó* occurs both nominally and clausally
(@cite{owusu-2022} Ch 4); only the nominal use is typed here.
Bare NPs appear under both definiteness values
(@cite{owusu-2022} App. A) — the `bare` constructor is shared between
the two inductives to reflect this.
-/

namespace Fragments.Akan.Determiners

/-- Akan adnominal definiteness contrast (@cite{owusu-2022} Ch 2). -/
inductive Definite where
  /-- Bare NP — definiteness inferred from context. -/
  | bare
  /-- *nó* — postnominal DEF marker. Cross-categorial: also occurs on
      VPs and TPs (@cite{arkoh-matthewson-2013}, @cite{owusu-2022} Ch 4). -/
  | no
  deriving DecidableEq, Repr

/-- Akan adnominal indefiniteness contrast (@cite{owusu-2022} Ch 3). -/
inductive Indefinite where
  /-- Bare NP — indefiniteness inferred from context. -/
  | bare
  /-- *bí* — postnominal INDEF marker. -/
  | bi
  deriving DecidableEq, Repr

end Fragments.Akan.Determiners
