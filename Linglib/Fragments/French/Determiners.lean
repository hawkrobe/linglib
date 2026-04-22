import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.Quantification.Lexicon

/-!
# French Determiners and Quantifiers
@cite{jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025}

A small lexicon of French determiners and quantifiers, structured to
parallel `Fragments.English.Determiners` so that the two can be
compared directly in cross-linguistic studies. The shape `QuantifierEntry`
is reused; only `form` and language-specific feature combinations
differ.

This fragment is the minimum needed by
`Phenomena/Presupposition/Studies/JereticEtAl2025.lean`. The notable
gap relative to English: French has no lexical dual universal
quantifier (no counterpart of `both`). The expression `les deux` is the
nearest equivalent and is encoded here, with `numberRestriction := some
.du`, marking that — unlike `tous`, which is plural-restricted — it
realizes the dual core concept (`Core.CoreConcept.Id.dual`).
-/

namespace Fragments.French.Determiners

open Theories.Semantics.Quantification.Lexicon
  (QuantifierEntry QForce Monotonicity Strength)

/-- *tous* — universal, plural. The French universal of @cite{chemla-2007}'s
puzzle: anti-dual despite the lack of any French *both*. The paper's
analysis: anti-duality is implicated via competition with the indirect
alternative *les deux* (`les_deux`). -/
def tous : QuantifierEntry :=
  { form := "tous"
  , qforce := .universal
  , numberRestriction := some .pl
  , allowsMass := true
  , monotonicity := .increasing
  , strength := .strong
  , gqtThreshold := 1
  , ptPrototype := 1
  , ptSpread := 1
  }

/-- *chaque* — universal, singular distributive (≈ English *each*). -/
def chaque : QuantifierEntry :=
  { form := "chaque"
  , qforce := .universal
  , numberRestriction := some .sg
  , monotonicity := .increasing
  , strength := .strong
  , gqtThreshold := 1
  , ptPrototype := 1
  , ptSpread := 1
  }

/-- *aucun* — negative, singular. NOT anti-dual: French has no
expression simple enough to act as an indirect alternative
(*aucun des deux* and *ni l'un ni l'autre* are both more complex).
See JereticEtAl2025 §5.2. -/
def aucun : QuantifierEntry :=
  { form := "aucun"
  , qforce := .negative
  , numberRestriction := some .sg
  , monotonicity := .decreasing
  , strength := .strong
  , gqtThreshold := 0
  , ptPrototype := 0
  , ptSpread := 1
  }

/-- *les deux* — definite dual ('the two'). The pronounceable
expression that serves as an indirect alternative for the unpronounceable
*tous les NP.dual* (paper Fig. 1 + §4.1). Restricted to dual domains. -/
def les_deux : QuantifierEntry :=
  { form := "les deux"
  , qforce := .definite
  , numberRestriction := some .du
  , monotonicity := .nonMonotone
  , strength := .strong
  }

/-- *quelques* — existential, plural. -/
def quelques : QuantifierEntry :=
  { form := "quelques"
  , qforce := .existential
  , numberRestriction := some .pl
  , monotonicity := .increasing
  , gqtThreshold := 0
  , ptPrototype := 1/3
  , ptSpread := 3
  }

/-- *un* — existential, singular. -/
def un : QuantifierEntry :=
  { form := "un"
  , qforce := .existential
  , numberRestriction := some .sg
  }

/-- *les* — definite plural article. -/
def les : QuantifierEntry :=
  { form := "les"
  , qforce := .definite
  , numberRestriction := some .pl
  , allowsMass := true
  , strength := .strong
  }

/-- *toujours* — universal temporal ('always'). Parallel to English
`always` (which decomposes as *all*+*ways*); JereticEtAl2025 §5.4
contrasts: English *always* is anti-dual via competition with
*both times*; French *toujours*, despite morphological decomposition
*tous*+*jours*, is NOT anti-dual because *les deux fois* ('the two
times') is more complex than *toujours*. -/
def toujours : QuantifierEntry :=
  { form := "toujours"
  , qforce := .universal
  , numberRestriction := some .pl
  , monotonicity := .increasing
  , strength := .strong
  , gqtThreshold := 1
  , ptPrototype := 1
  , ptSpread := 1
  }

/-- All French quantifier entries. -/
def allQuantifiers : List QuantifierEntry :=
  [tous, chaque, aucun, les_deux, quelques, un, les, toujours]

end Fragments.French.Determiners
