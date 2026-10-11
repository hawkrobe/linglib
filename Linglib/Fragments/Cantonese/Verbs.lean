module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Clause.Complementation

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

@[expose] public section

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
  { morphs := [.root "soeng2"], hanzi := "想", predicateClass := .desiderative,
    valency := .ofFrame ArgumentFrame.infinitival,
    passivizable := false, opaqueContext := true,
    attitude := some (.preferential .positive true) }

/-- *hyun* 勸 'urge'. -/
def hyun : Verb :=
  { morphs := [.root "hyun3"], hanzi := "勸", predicateClass := .manipulative,
    valency := .ofFrame ArgumentFrame.infinitival }

/-- *bik* 逼 'force'. -/
def bik : Verb :=
  { morphs := [.root "bik1"], hanzi := "逼", predicateClass := .manipulative,
    valency := .ofFrame ArgumentFrame.infinitival }

/-- *giu* 叫 'ask, tell'. -/
def giu : Verb :=
  { morphs := [.root "giu3"], hanzi := "叫", predicateClass := .manipulative,
    valency := .ofFrame ArgumentFrame.infinitival }

/-- *daasyun* 打算 'intend, plan'. -/
def daasyun : Verb :=
  { morphs := [.root "daa2syun3"], hanzi := "打算", predicateClass := .desiderative,
    valency := .ofFrame ArgumentFrame.infinitival, passivizable := false, opaqueContext := true,
    attitude := some (.preferential .positive true) }

/-- *seon* 信 'believe'. -/
def seon : Verb :=
  { morphs := [.root "seon3"], hanzi := "信", predicateClass := .propAttitude,
    valency := .ofFrame ArgumentFrame.finiteClause,
    passivizable := false, opaqueContext := true, attitude := some (.doxastic .veridical) }

/-- *gong* 講 'say'. -/
def gong : Verb :=
  { morphs := [.root "gong2"], hanzi := "講", predicateClass := .utterance,
    valency := .ofFrame ArgumentFrame.finiteClause,
    speechActVerb := true }

/-- *geidak* 記得 'remember', a factive. -/
def geidak : Verb :=
  { morphs := [.root "gei3dak1"], hanzi := "記得", predicateClass := .knowledge,
    valency := .ofFrame ArgumentFrame.finiteClause,
    passivizable := false, factivity := some .semi }

/-- The verbs. -/
def all : List Verb := [soeng, hyun, bik, giu, daasyun, seon, gong, geidak]

end Cantonese.Verbs
