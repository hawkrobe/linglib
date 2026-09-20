import Linglib.Syntax.Category.Verb.Basic
import Linglib.Syntax.Clause.Complementation

/-!
# Cantonese complement-taking verbs

Cantonese complement-taking verbs as `Verb`s with their character and their [noonan-2007] class:
the desideratives *soeng* 'want' and *daasyun* 'intend', the manipulatives *hyun* 'urge', *bik*
'force' and *giu* 'ask', the attitude verb *seon* 'believe', the utterance verb *gong* 'say'
and the factive *geidak* 'remember' [matthews-yip-1994]. The size of the complement each
selects, and the scope of an *again*-element across it, are the analysis of [liu-yip-2026] and
live in `Studies/LiuYip2026.lean`.

## References

* [matthews-yip-1994]
* [noonan-2007]
* [liu-yip-2026]
-/

namespace Cantonese.Verbs

open ArgumentStructure

/-- A Cantonese verb: the cross-linguistic core with the jyutping as citation form, plus its
characters and its complement-taking predicate class. -/
structure Verb extends _root_.Verb where
  /-- The characters. -/
  hanzi : String
  /-- The complement-taking predicate class. -/
  predicateClass : Complement.PredicateClass

/-- *soeng* 想 'want'. -/
def soeng : Verb :=
  { form := "soeng2", hanzi := "想", predicateClass := .desiderative,
    frames := [ArgumentFrame.infinitival],
    passivizable := false, opaqueContext := true,
    attitude := some (.preferential (.degreeComparison .positive)) }

/-- *hyun* 勸 'urge'. -/
def hyun : Verb :=
  { form := "hyun3", hanzi := "勸", predicateClass := .manipulative,
    frames := [ArgumentFrame.infinitival] }

/-- *bik* 逼 'force'. -/
def bik : Verb :=
  { form := "bik1", hanzi := "逼", predicateClass := .manipulative,
    frames := [ArgumentFrame.infinitival] }

/-- *giu* 叫 'ask, tell'. -/
def giu : Verb :=
  { form := "giu3", hanzi := "叫", predicateClass := .manipulative,
    frames := [ArgumentFrame.infinitival] }

/-- *daasyun* 打算 'intend, plan'. -/
def daasyun : Verb :=
  { form := "daa2syun3", hanzi := "打算", predicateClass := .desiderative,
    frames := [ArgumentFrame.infinitival], passivizable := false, opaqueContext := true,
    attitude := some (.preferential (.degreeComparison .positive)) }

/-- *seon* 信 'believe'. -/
def seon : Verb :=
  { form := "seon3", hanzi := "信", predicateClass := .propAttitude,
    frames := [ArgumentFrame.finiteClause],
    passivizable := false, opaqueContext := true, attitude := some (.doxastic .veridical) }

/-- *gong* 講 'say'. -/
def gong : Verb :=
  { form := "gong2", hanzi := "講", predicateClass := .utterance,
    frames := [ArgumentFrame.finiteClause],
    speechActVerb := true }

/-- *geidak* 記得 'remember', a factive. -/
def geidak : Verb :=
  { form := "gei3dak1", hanzi := "記得", predicateClass := .knowledge,
    frames := [ArgumentFrame.finiteClause],
    passivizable := false, factivity := some .semi }

/-- The verbs. -/
def all : List Verb := [soeng, hyun, bik, giu, daasyun, seon, gong, geidak]

end Cantonese.Verbs
