module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Catalan verbs
[palmieri-2024]

Catalan verbs with lexical reciprocal entries alongside their
transitive alternates ([palmieri-2024], Appendix A): the reciprocal
reading emerges without *se* in the language's Table 2.2 environments.
Membership in `Catalan.Reciprocals.lexicalReciprocals` carries the
reciprocal marking; the entries here are ordinary verb entries.
-/

@[expose] public section

namespace Catalan.Verbs

/-- *abraçar* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abracar : Verb where
  form := "abraçar"
  valency := .ofFrame ArgumentFrame.np

/-- *casar* 'marry' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def casar : Verb where
  form := "casar"
  valency := .ofFrame ArgumentFrame.np

/-- *deixar* 'leave/break up' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def deixar : Verb where
  form := "deixar"
  valency := .ofFrame ArgumentFrame.np

/-- *petonejar* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def petonejar : Verb where
  form := "petonejar"
  valency := .ofFrame ArgumentFrame.np

/-- *topar* 'run into, meet accidentally' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def topar : Verb where
  form := "topar"
  valency := .ofFrame ArgumentFrame.np

/-- *trobar* 'find/meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def trobar : Verb where
  form := "trobar"
  valency := .ofFrame ArgumentFrame.np

end Catalan.Verbs
