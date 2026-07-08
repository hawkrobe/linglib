import Linglib.Semantics.Verb.Basic

/-!
# Brazilian Portuguese Predicate Lexicon Fragment
[palmieri-2024]

Brazilian Portuguese verbs with lexical reciprocal entries alongside their
transitive alternates ([palmieri-2024], Appendix A): the reciprocal
reading emerges without *se* in the language's Table 2.2 environments.
Membership in `BrazilianPortuguese.Reciprocals.lexicalReciprocals` carries the
reciprocal marking; the entries here are ordinary verb entries.
-/

namespace BrazilianPortuguese.Predicates

/-- *abraçar* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abracar : Verb where
  form := "abraçar"
  frames := [Frame.np]

/-- *beijar* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def beijar : Verb where
  form := "beijar"
  frames := [Frame.np]

/-- *casar* 'marry' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def casar : Verb where
  form := "casar"
  frames := [Frame.np]

/-- *consultar* 'consult/confer' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def consultar : Verb where
  form := "consultar"
  frames := [Frame.np]

/-- *cumprimentar* 'greet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def cumprimentar : Verb where
  form := "cumprimentar"
  frames := [Frame.np]

/-- *encontrar* 'meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def encontrar : Verb where
  form := "encontrar"
  frames := [Frame.np]

/-- *namorar* 'date, be partners' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def namorar : Verb where
  form := "namorar"
  frames := [Frame.np]

end BrazilianPortuguese.Predicates
