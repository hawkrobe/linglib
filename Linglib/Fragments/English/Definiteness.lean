import Linglib.Syntax.Category.Determiner.Basic

/-!
# English Definiteness Fragment
[schwarz-2009] [schwarz-2013] [moroney-2021]

English uses a single syncretic definite article *the* for both uniqueness
and anaphoric definiteness, an indefinite *a/an*, demonstratives *this/that*,
and possessives *my/your/...*. Under the [moroney-2021] typology this
is the `.generallyMarked` strategy: a single form covers all
[schwarz-2009] use types.
-/

namespace English.Definiteness

/-- English: the syncretic definite article *the* (one form for both unique and
    anaphoric uses), indefinite *a/an*, demonstratives *this/that*, possessives. -/
def determiners : List Determiner.Entry :=
  [ .article { form := "the", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] },
    .article { form := "a", definiteness := .indefinite, exponent := .dedicatedMorpheme },
    .demonstrative { form := "that", deictic := .distal },
    .possessive { form := "my" } ]

/-- English's inventory derives the `.generallyMarked` Moroney cell. -/
theorem marking : Determiner.markingStrategy determiners = .generallyMarked := by decide

end English.Definiteness
