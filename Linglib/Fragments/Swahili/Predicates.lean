import Linglib.Syntax.Category.Verb.Basic

/-!
# Swahili Predicate Lexicon Fragment
[palmieri-2024]

Swahili *-an-* verbs with lexicalized reciprocal entries and their
binary bases ([palmieri-2024], Appendix C). The reciprocal verbs are
diagnosed as lexical by singular predication (modal embedding,
habituality) and affix ordering; some bases drift semantically
(*pambana* 'fight' < *pamba* 'decorate'), and *jibizana* has no binary
base at all (\**jibiza*).
-/

namespace Swahili.Predicates

/-! ### Lexical reciprocal verbs -/

/-- *achana* 'break up, divorce' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def achana : Verb where
  form := "achana"
  frames := [ArgumentFrame.intransitive]

/-- *gawana* 'share' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def gawana : Verb where
  form := "gawana"
  frames := [ArgumentFrame.intransitive]

/-- *gombana* 'quarrel' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def gombana : Verb where
  form := "gombana"
  frames := [ArgumentFrame.intransitive]

/-- *gongana* 'collide' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def gongana : Verb where
  form := "gongana"
  frames := [ArgumentFrame.intransitive]

/-- *jibizana* 'discuss, talk, dialogue' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def jibizana : Verb where
  form := "jibizana"
  frames := [ArgumentFrame.intransitive]

/-- *pambana* 'fight, be in conflict' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def pambana : Verb where
  form := "pambana"
  frames := [ArgumentFrame.intransitive]

/-- *patana* 'agree' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def patana : Verb where
  form := "patana"
  frames := [ArgumentFrame.intransitive]

/-- *pigana* 'fight' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def pigana : Verb where
  form := "pigana"
  frames := [ArgumentFrame.intransitive]

/-- *shindana* 'compete' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def shindana : Verb where
  form := "shindana"
  frames := [ArgumentFrame.intransitive]

/-! ### Binary bases -/

/-- *acha* 'leave, abandon' — binary base ([palmieri-2024], Appendix C). -/
def acha : Verb where
  form := "acha"
  frames := [ArgumentFrame.np]

/-- *gawa* 'distribute' — binary base ([palmieri-2024], Appendix C). -/
def gawa : Verb where
  form := "gawa"
  frames := [ArgumentFrame.np]

/-- *gomba* 'argue with' — binary base ([palmieri-2024], Appendix C). -/
def gomba : Verb where
  form := "gomba"
  frames := [ArgumentFrame.np]

/-- *gonga* 'crash against' — binary base ([palmieri-2024], Appendix C). -/
def gonga : Verb where
  form := "gonga"
  frames := [ArgumentFrame.np]

/-- *pamba* 'decorate' — binary base ([palmieri-2024], Appendix C). -/
def pamba : Verb where
  form := "pamba"
  frames := [ArgumentFrame.np]

/-- *pata* 'find' — binary base ([palmieri-2024], Appendix C). -/
def pata : Verb where
  form := "pata"
  frames := [ArgumentFrame.np]

/-- *piga* 'hit' — binary base ([palmieri-2024], Appendix C). -/
def piga : Verb where
  form := "piga"
  frames := [ArgumentFrame.np]

/-- *shinda* 'defeat' — binary base ([palmieri-2024], Appendix C). -/
def shinda : Verb where
  form := "shinda"
  frames := [ArgumentFrame.np]

end Swahili.Predicates
