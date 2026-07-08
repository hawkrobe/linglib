import Linglib.Syntax.Category.Determiner.Basic

/-!
# French Determiners and Quantifiers
[jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]

A small lexicon of French determiners and quantifiers, structured to
parallel `English.Determiners` so that the two can be compared directly
in cross-linguistic studies. The genuinely quantificational words are
`Syntax.Determiner.Quantifier` records (marked like a `Pronoun`, carrying
only the morphosyntax synonyms diverge on); the definite/indefinite
articles (*les*, *un*) are `Article`s. Only `form` and language-specific
feature combinations differ from English.

This fragment is the minimum needed by `Studies/JereticEtAl2025.lean`. The
notable gap relative to English: French has no lexical dual universal
quantifier (no counterpart of `both`). The expression *les deux* is the
nearest equivalent and is encoded here as a `Quantifier` with
`numberRestriction := some .dual`, marking that — unlike *tous*, which is
plural-restricted — it realizes the dual core concept
(`JereticEtAl2025.CoreConcept.Id.dual`).
-/

namespace French.Determiners

/-! ## Quantificational determiners

Marked `Quantifier` records: `form`, the selectional `numberRestriction`
(root `Number`), and `selectsMass`. -/

/-- *tous* — universal, plural. The French universal of [chemla-2007]'s
puzzle: anti-dual despite the lack of any French *both*. The paper's
analysis: anti-duality is implicated via competition with the indirect
alternative *les deux* (`les_deux`). -/
def tous : Quantifier :=
  { form := "tous"
  , numberRestriction := some .plural
  , selectsMass := true }

/-- *chaque* — universal, singular distributive (≈ English *each*). -/
def chaque : Quantifier :=
  { form := "chaque"
  , numberRestriction := some .singular }

/-- *aucun* — negative, singular. NOT anti-dual: French has no
expression simple enough to act as an indirect alternative
(*aucun des deux* and *ni l'un ni l'autre* are both more complex).
See JereticEtAl2025 §5.2. -/
def aucun : Quantifier :=
  { form := "aucun"
  , numberRestriction := some .singular }

/-- *les deux* — definite dual ('the two'). The pronounceable
expression that serves as an indirect alternative for the unpronounceable
*tous les NP.dual* (paper Fig. 1 + §4.1). Restricted to dual domains;
marked here as a `Quantifier` so its dual `numberRestriction` is
readable (the dual core-concept witness), paralleling English *both*. -/
def les_deux : Quantifier :=
  { form := "les deux"
  , numberRestriction := some .dual }

/-- *quelques* — existential, plural. -/
def quelques : Quantifier :=
  { form := "quelques"
  , numberRestriction := some .plural }

/-- *un* — indefinite article, singular. -/
def un : Article :=
  { form := "un"
  , definiteness := .indefinite
  , exponent := .dedicatedMorpheme }

/-- *les* — definite plural article. -/
def les : Article :=
  { form := "les"
  , definiteness := .definite
  , exponent := .dedicatedMorpheme
  , uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] }

/-- *toujours* — universal temporal ('always'). Parallel to English
`always` (which decomposes as *all*+*ways*); JereticEtAl2025 §5.4
contrasts: English *always* is anti-dual via competition with
*both times*; French *toujours*, despite morphological decomposition
*tous*+*jours*, is NOT anti-dual because *les deux fois* ('the two
times') is more complex than *toujours*. -/
def toujours : Quantifier :=
  { form := "toujours"
  , numberRestriction := some .plural }

/-- All French quantifier entries (definite articles *les*/*un* excluded). -/
def allQuantifiers : List Quantifier :=
  [tous, chaque, aucun, les_deux, quelques, toujours]

/-- All French article entries. -/
def allArticles : List Article := [un, les]

end French.Determiners
