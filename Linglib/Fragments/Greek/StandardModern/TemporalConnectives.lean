module

public import Linglib.Semantics.Tense.Connective

/-!
# Greek temporal connectives

Lexical entries for the Modern Greek temporal connectives: *prin* 'before', whose complement is a
*na*-subjunctive, *afou* 'after' and *otan* 'when' with indicative complements, the durative
*mexri* 'until', and *para monon*, literally 'but only', the scalar polarity item that serves as
the punctual *until* under negation and *xoris* 'without' ([giannakidou-2002], the paper's
(36)–(42)). Greek thus lexicalizes [karttunen-1974]'s two *until*s, which English leaves to one
word. That *para monon* needs an antiveridical licenser is the paper's classification and lives
in its study.

## References

* [giannakidou-2002]
* [karttunen-1974]
-/

@[expose] public section

namespace Greek.StandardModern.TemporalConnectives

open Tense

/-- *prin* (πριν) 'before', with a *na*-subjunctive complement: *efije prin na erthi o Janis*
'she left before Janis came'. -/
def prin : Connective where
  form := "prin"
  relation := .before
  mood := some .subjunctive

/-- *afou* (αφού) 'after', with an indicative complement: *efije afou irthe o Janis* 'she left
after Janis came'. -/
def afou : Connective where
  form := "afou"
  relation := .after
  mood := some .indicative

/-- *otan* (όταν) 'when', with an indicative complement: *efije otan irthe o Janis* 'she left when
Janis came'. -/
def otan : Connective where
  form := "otan"
  relation := .when_
  mood := some .indicative

/-- *mexri* (μέχρι), the durative 'until': *i prigipisa kimotane mexri ta mesanixta* 'the
princess was sleeping until midnight'. -/
def mexri : Connective := { form := "mexri", relation := .until_ }

/-- *para monon* (παρά μόνον), literally 'but only', the punctual 'until' of a negated clause:
*i prigipisa dhen eftase para monon ta mesanixta* 'the princess did not arrive until midnight'.
-/
def paraMonon : Connective where
  form := "para monon"
  relation := .until_
  punctual := True

end Greek.StandardModern.TemporalConnectives
