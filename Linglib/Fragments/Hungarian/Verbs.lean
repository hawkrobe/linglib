module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Hungarian verbs

This file defines the Hungarian matrix predicates of Egressy's study of sequence of tense, the
perception, cognition, psychological and communication verbs that embed a finite *hogy*-clause:
*lát* 'see', *hall* 'hear', *álmodik* 'dream', *gondol* 'think', *hisz* 'believe', *aggaszt*
'worry', *mond* 'say', *rikolt* 'shout' and *morog* 'growl'. A Hungarian verb agrees with the
definiteness of its object as well as with its subject, in the definite or the indefinite
objective conjugation of the reference grammar, so a clausal complement with the accusative
expletive *azt* takes the definite form, *tudta* 'knew it'. Whether the complement reports
speech or not is a property of the clause and not of the verb, as Egressy shows with *hall*
and *morog*, so the entries carry no clause type.

## Main definitions

* `Hungarian.Verbs.verbs`: the entries.

## References

* [egressy-2026]
* [kenesei-vago-fenyvesi-1998]
* [kiss-2002]
-/

@[expose] public section

namespace Hungarian.Verbs

open ArgumentStructure

/-- *lát* 'see', a perception verb. -/
def lat : Verb := { form := "lát", frames := [ArgumentFrame.finiteClause] }

/-- *hall* 'hear', a perception verb that embeds a perceived event or a heard report alike. -/
def hall : Verb := { form := "hall", frames := [ArgumentFrame.finiteClause] }

/-- *álmodik* 'dream'. -/
def almodik : Verb := { form := "álmodik", frames := [ArgumentFrame.finiteClause] }

/-- *gondol* 'think'. -/
def gondol : Verb := { form := "gondol", frames := [ArgumentFrame.finiteClause] }

/-- *hisz* 'believe'. -/
def hisz : Verb := { form := "hisz", frames := [ArgumentFrame.finiteClause] }

/-- *aggaszt* 'worry', a psychological verb whose clause is its subject. -/
def aggaszt : Verb := { form := "aggaszt", frames := [ArgumentFrame.finiteClause] }

/-- *mond* 'say'. -/
def mond : Verb :=
  { form := "mond", frames := [ArgumentFrame.finiteClause], speechActVerb := true }

/-- *rikolt* 'shout', a manner-of-speaking verb. -/
def rikolt : Verb :=
  { form := "rikolt", frames := [ArgumentFrame.finiteClause], speechActVerb := true }

/-- *morog* 'growl', a manner-of-speaking verb that also takes a reason adjunct. -/
def morog : Verb :=
  { form := "morog", frames := [ArgumentFrame.finiteClause], speechActVerb := true }

/-- The entries. -/
def verbs : List Verb := [lat, hall, almodik, gondol, hisz, aggaszt, mond, rikolt, morog]

end Hungarian.Verbs
