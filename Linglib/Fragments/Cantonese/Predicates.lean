import Linglib.Syntax.Clause.Complementation

/-!
# Cantonese complement-taking predicates

Cantonese complement-taking predicates with their [noonan-2007] class: the desideratives
*soeng* 'want' and *daasyun* 'intend', the manipulatives *hyun* 'urge', *bik* 'force' and *giu*
'ask', the attitude verb *seon* 'believe', the utterance verb *gong* 'say' and the factive
*geidak* 'remember' [matthews-yip-1994]. The size of the complement each selects, and the
scope of an *again*-element across it, are the analysis of [liu-yip-2026] and live in
`Studies/LiuYip2026.lean`.

## References

* [matthews-yip-1994]
* [noonan-2007]
* [liu-yip-2026]
-/

namespace Cantonese.Predicates

/-- A Cantonese complement-taking predicate: its jyutping, its character, its gloss and its
[noonan-2007] class. -/
structure CTPEntry where
  /-- The jyutping form with tone numbers. -/
  jyutping : String
  /-- The characters. -/
  hanzi : String
  /-- The gloss. -/
  gloss : String
  /-- The complement-taking predicate class. -/
  ctpClass : CTPClass
  deriving Repr, DecidableEq

/-- *soeng* 想 'want'. -/
def soeng : CTPEntry :=
  { jyutping := "soeng2", hanzi := "想", gloss := "want", ctpClass := .desiderative }

/-- *hyun* 勸 'urge'. -/
def hyun : CTPEntry :=
  { jyutping := "hyun3", hanzi := "勸", gloss := "urge", ctpClass := .manipulative }

/-- *bik* 逼 'force'. -/
def bik : CTPEntry :=
  { jyutping := "bik1", hanzi := "逼", gloss := "force", ctpClass := .manipulative }

/-- *giu* 叫 'ask, tell'. -/
def giu : CTPEntry :=
  { jyutping := "giu3", hanzi := "叫", gloss := "ask, tell", ctpClass := .manipulative }

/-- *daasyun* 打算 'intend, plan'. -/
def daasyun : CTPEntry :=
  { jyutping := "daa2syun3", hanzi := "打算", gloss := "intend, plan", ctpClass := .desiderative }

/-- *seon* 信 'believe'. -/
def seon : CTPEntry :=
  { jyutping := "seon3", hanzi := "信", gloss := "believe", ctpClass := .propAttitude }

/-- *gong* 講 'say'. -/
def gong : CTPEntry :=
  { jyutping := "gong2", hanzi := "講", gloss := "say", ctpClass := .utterance }

/-- *geidak* 記得 'remember'. -/
def geidak : CTPEntry :=
  { jyutping := "gei3dak1", hanzi := "記得", gloss := "remember", ctpClass := .knowledge }

/-- The predicates. -/
def all : List CTPEntry := [soeng, hyun, bik, giu, daasyun, seon, gong, geidak]

end Cantonese.Predicates
