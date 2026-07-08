import Linglib.Semantics.Verb.Basic

/-!
# Italian Predicate Lexicon Fragment
[palmieri-2024]

Italian verbs with lexical reciprocal entries alongside their
transitive alternates ([palmieri-2024], Appendix A): the reciprocal
reading emerges without *se* in the language's Table 2.2 environments.
Membership in `Italian.Reciprocals.lexicalReciprocals` carries the
reciprocal marking; the entries here are ordinary verb entries.
-/

namespace Italian.Predicates

/-- *abbracciare* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abbracciare : Verb where
  form := "abbracciare"
  frames := [Frame.np]

/-- *baciare* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def baciare : Verb where
  form := "baciare"
  frames := [Frame.np]

/-- *coccolare* 'cuddle' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def coccolare : Verb where
  form := "coccolare"
  frames := [Frame.np]

/-- *conoscere* 'know (of)' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def conoscere : Verb where
  form := "conoscere"
  frames := [Frame.np]

/-- *consultare* 'consult/confer' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def consultare : Verb where
  form := "consultare"
  frames := [Frame.np]

/-- *frequentare* 'date' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def frequentare : Verb where
  form := "frequentare"
  frames := [Frame.np]

/-- *incontrare* 'meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def incontrare : Verb where
  form := "incontrare"
  frames := [Frame.np]

/-- *incrociare* 'run into, meet accidentally' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def incrociare : Verb where
  form := "incrociare"
  frames := [Frame.np]

/-- *lasciare* 'leave/break up' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def lasciare : Verb where
  form := "lasciare"
  frames := [Frame.np]

/-- *sposare* 'marry' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def sposare : Verb where
  form := "sposare"
  frames := [Frame.np]

/-- *trovare* 'find/meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def trovare : Verb where
  form := "trovare"
  frames := [Frame.np]

/-- *vedere* 'see/meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def vedere : Verb where
  form := "vedere"
  frames := [Frame.np]

end Italian.Predicates
