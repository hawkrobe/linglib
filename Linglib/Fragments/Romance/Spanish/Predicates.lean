import Linglib.Semantics.Verb.Basic

/-!
# Spanish Predicate Lexicon Fragment
[palmieri-2024]

Spanish verbs with lexical reciprocal entries alongside their
transitive alternates ([palmieri-2024], Appendix A): the reciprocal
reading emerges without *se* in the language's Table 2.2 environments.
Membership in `Spanish.Reciprocals.lexicalReciprocals` carries the
reciprocal marking; the entries here are ordinary verb entries.
-/

namespace Spanish.Predicates

/-- *abrazar* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abrazar : Verb where
  form := "abrazar"
  frames := [Frame.np]

/-- *acurrucar* 'cuddle' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def acurrucar : Verb where
  form := "acurrucar"
  frames := [Frame.np]

/-- *besar* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def besar : Verb where
  form := "besar"
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

/-- *cruzar* 'run into, meet accidentally' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def cruzar : Verb where
  form := "cruzar"
  frames := [Frame.np]

/-- *dejar* 'leave/break up' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def dejar : Verb where
  form := "dejar"
  frames := [Frame.np]

/-- *encontrar* 'find/meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def encontrar : Verb where
  form := "encontrar"
  frames := [Frame.np]

end Spanish.Predicates
