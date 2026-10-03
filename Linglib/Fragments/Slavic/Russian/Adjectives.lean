module

public import Linglib.Syntax.Category.Adjective.Basic

/-!
# Russian adjectives

Each entry records the morphological comparative (*suš-e*, *luč-še*) and the periphrastic
superlative, *samyj* 'most' with the positive. A literary morphological superlative such as
*nai-xud-š-ij* 'worst' exists beside the periphrasis ([bobaljik-2012] §3.3.3) and is not entered.
Since *samyj* embeds the positive, a suppletive comparative root does not recur in the superlative,
and the root pattern of *xoroš-ij – luč-še – samyj xoroš-ij* is ABA.

Forms are in scientific transliteration. A consonant mutation before *-e* (*sux-oj – suš-e*,
*prost-oj – prošč-e*) is phonological and leaves the root pattern AAA.

## References

* [bobaljik-2012]
-/

@[expose] public section

namespace Russian.Adjectives

/-! ### Regular adjectives -/

/-- *sux-oj – suš-e – samyj sux-oj* 'dry'. -/
def suxoj : Adjective :=
  { form := "suxoj", script := some "сухой"
  , comparison :=
      { formComp := "suše", formSuper := "samyj suxoj", superlativeStrategy := .periphrastic } }

/-- *prost-oj – prošč-e – samyj prost-oj* 'simple'. -/
def prostoj : Adjective :=
  { form := "prostoj", script := some "простой"
  , comparison :=
      { formComp := "prošče", formSuper := "samyj prostoj"
      , superlativeStrategy := .periphrastic } }

/-! ### Suppletive adjectives -/

/-- *xoroš-ij – luč-še – samyj xoroš-ij* 'good'. *Samyj luč-š-ij* also occurs, which
[bobaljik-2012] takes to be a vestigial morphological superlative reinforced by *samyj*. -/
def xoroshij : Adjective :=
  { form := "xorošij", script := some "хороший"
  , comparison :=
      { formComp := "lučše", formSuper := "samyj xorošij", superlativeStrategy := .periphrastic
      , suppletion := Morphology.Paradigm.aba } }

/-- *plox-oj – xuž-e – samyj plox-oj* 'bad', with the comparative root *xud-* mutated before
*-e*. -/
def ploxoj : Adjective :=
  { form := "ploxoj", script := some "плохой"
  , comparison :=
      { formComp := "xuže", formSuper := "samyj ploxoj", superlativeStrategy := .periphrastic
      , suppletion := Morphology.Paradigm.aba } }

/-! ### Inventory -/

/-- Every entry of the fragment. -/
def allEntries : List Adjective := [suxoj, prostoj, xoroshij, ploxoj]

end Russian.Adjectives
