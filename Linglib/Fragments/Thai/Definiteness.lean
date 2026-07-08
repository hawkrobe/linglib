import Linglib.Syntax.Category.Determiner.Basic

/-!
# Thai Definiteness Fragment
[jenks-2015] [moroney-2021]

Thai patterns with Mandarin on the [moroney-2021] typology: bare nouns
serve uniqueness contexts and demonstratives carry the anaphoric load —
no overt indefinite or unique article. Possessives are productive. Under
the [moroney-2021] typology this is the `.markedAnaphoric` strategy.
-/

namespace Thai.Definiteness

/-- Thai [jenks-2015]: same definite-marking pattern as Mandarin — the
    demonstrative (*nán* 'that') obligatorily expones anaphoric definites;
    uniqueness is bare; possessives via *khɔ̌ɔng*. -/
def determiners : List Determiner.Entry :=
  [ .demonstrative { form := "nan", deictic := .distal, definiteUses := [.anaphoric] },
    .possessive { form := "khong" } ]

/-- Thai's inventory derives the `.markedAnaphoric` Moroney cell — same cell as
    Mandarin (same definite-marking pattern). -/
theorem marking : Determiner.markingStrategy determiners = .markedAnaphoric := by decide

end Thai.Definiteness
