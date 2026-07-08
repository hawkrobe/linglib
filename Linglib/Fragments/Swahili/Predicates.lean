import Linglib.Semantics.Verb.Basic

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
  frames := []

/-- *gawana* 'share' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def gawana : Verb where
  form := "gawana"
  frames := []

/-- *gombana* 'quarrel' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def gombana : Verb where
  form := "gombana"
  frames := []

/-- *gongana* 'collide' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def gongana : Verb where
  form := "gongana"
  frames := []

/-- *jibizana* 'discuss, talk, dialogue' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def jibizana : Verb where
  form := "jibizana"
  frames := []

/-- *pambana* 'fight, be in conflict' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def pambana : Verb where
  form := "pambana"
  frames := []

/-- *patana* 'agree' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def patana : Verb where
  form := "patana"
  frames := []

/-- *pigana* 'fight' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def pigana : Verb where
  form := "pigana"
  frames := []

/-- *shindana* 'compete' — lexical reciprocal ([palmieri-2024], Appendix C). -/
def shindana : Verb where
  form := "shindana"
  frames := []

/-! ### Binary bases -/

/-- *acha* 'leave, abandon' — binary base ([palmieri-2024], Appendix C). -/
def acha : Verb where
  form := "acha"
  frames := [Frame.np]

/-- *gawa* 'distribute' — binary base ([palmieri-2024], Appendix C). -/
def gawa : Verb where
  form := "gawa"
  frames := [Frame.np]

/-- *gomba* 'argue with' — binary base ([palmieri-2024], Appendix C). -/
def gomba : Verb where
  form := "gomba"
  frames := [Frame.np]

/-- *gonga* 'crash against' — binary base ([palmieri-2024], Appendix C). -/
def gonga : Verb where
  form := "gonga"
  frames := [Frame.np]

/-- *pamba* 'decorate' — binary base ([palmieri-2024], Appendix C). -/
def pamba : Verb where
  form := "pamba"
  frames := [Frame.np]

/-- *pata* 'find' — binary base ([palmieri-2024], Appendix C). -/
def pata : Verb where
  form := "pata"
  frames := [Frame.np]

/-- *piga* 'hit' — binary base ([palmieri-2024], Appendix C). -/
def piga : Verb where
  form := "piga"
  frames := [Frame.np]

/-- *shinda* 'defeat' — binary base ([palmieri-2024], Appendix C). -/
def shinda : Verb where
  form := "shinda"
  frames := [Frame.np]

end Swahili.Predicates
