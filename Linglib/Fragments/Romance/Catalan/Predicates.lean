import Linglib.Semantics.Verb.Basic

/-!
# Catalan Predicate Lexicon Fragment
[palmieri-2024]

Catalan verbs with lexical reciprocal entries alongside their
transitive alternates ([palmieri-2024], Appendix A): the reciprocal
reading emerges without *se* in the language's Table 2.2 environments.
Membership in `Catalan.Reciprocals.lexicalReciprocals` carries the
reciprocal marking; the entries here are ordinary verb entries.
-/

namespace Catalan.Predicates

/-- *abraçar* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abracar : Verb where
  form := "abraçar"
  frames := [Frame.np]

/-- *casar* 'marry' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def casar : Verb where
  form := "casar"
  frames := [Frame.np]

/-- *deixar* 'leave/break up' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def deixar : Verb where
  form := "deixar"
  frames := [Frame.np]

/-- *petonejar* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def petonejar : Verb where
  form := "petonejar"
  frames := [Frame.np]

/-- *topar* 'run into, meet accidentally' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def topar : Verb where
  form := "topar"
  frames := [Frame.np]

/-- *trobar* 'find/meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def trobar : Verb where
  form := "trobar"
  frames := [Frame.np]

end Catalan.Predicates
