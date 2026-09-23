module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Brazilian Portuguese verbs
[palmieri-2024]

Brazilian Portuguese verbs with lexical reciprocal entries alongside their
transitive alternates ([palmieri-2024], Appendix A): the reciprocal
reading emerges without *se* in the language's Table 2.2 environments.
Membership in `BrazilianPortuguese.Reciprocals.lexicalReciprocals` carries the
reciprocal marking; the entries here are ordinary verb entries.
-/

@[expose] public section

namespace BrazilianPortuguese.Verbs

/-- *abraçar* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abracar : Verb where
  form := "abraçar"
  frames := [ArgumentFrame.np]

/-- *beijar* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def beijar : Verb where
  form := "beijar"
  frames := [ArgumentFrame.np]

/-- *casar* 'marry' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def casar : Verb where
  form := "casar"
  frames := [ArgumentFrame.np]

/-- *consultar* 'consult/confer' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def consultar : Verb where
  form := "consultar"
  frames := [ArgumentFrame.np]

/-- *cumprimentar* 'greet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def cumprimentar : Verb where
  form := "cumprimentar"
  frames := [ArgumentFrame.np]

/-- *encontrar* 'meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def encontrar : Verb where
  form := "encontrar"
  frames := [ArgumentFrame.np]

/-- *namorar* 'date, be partners' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def namorar : Verb where
  form := "namorar"
  frames := [ArgumentFrame.np]

end BrazilianPortuguese.Verbs
