import Linglib.Syntax.Category.Verb.Basic

/-!
# Mandarin verbs

The Mandarin clause-embedding predicates the studies of Qing and Uegaki, of Glass, of Wang and
of Liu and Yip consume: the preferential attitudes *qidai* 'look forward to', *danxin* 'worry',
*xiwang* 'hope' and *haipa* 'fear', the doxastic *yiwei* 'think, wrongly' and *renwei*
'think', the factives *zhidao* 'know' and *houhui* 'regret', the inchoative *kaishi* 'start',
and the control and causative predicates *xiang* 'want', *rang* 'let', *xiangxin*
'believe', *quan* 'urge', *bi* 'force', *dasuan* 'plan' and *shefa* 'try'. Mandarin is
isolating, so a verb carries no inflectional fields beyond the root entry.

## Main definitions

* `Mandarin.Verb`: a Mandarin verb, the root `Verb` with no inflectional fields.
* `Mandarin.verbs`: the inventory of the entries.

## References

* [glass-2025]
* [qing-uegaki-2025]
* [wang-2025]
* [liu-yip-2026]
-/

namespace Mandarin

open ArgumentStructure

/-- A Mandarin verb is the cross-linguistic core with no inflectional fields, Mandarin being
isolating. -/
structure Verb extends _root_.Verb where
  deriving BEq

/-- 期待 *qīdài* 'look forward to' is a positive preferential attitude that takes questions. -/
def qidai : Verb := {
  form := "qidai"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.relevanceBased .positive)) }

/-- 担心 *dānxīn* 'worry' is a negative preferential attitude. -/
def danxin : Verb := {
  form := "danxin"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased) }

/-- 希望 *xīwàng* 'hope' is a positive preferential attitude that takes no questions. -/
def xiwang : Verb := {
  form := "xiwang"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 害怕 *hàipà* 'fear' is a negative preferential attitude that takes questions. -/
def haipa : Verb := {
  form := "haipa"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative)) }

/-- 以为 *yǐwéi* 'be under the impression that' is a nonveridical doxastic attitude. -/
def yiwei : Verb := {
  form := "yiwei"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-- 认为 *rènwéi* 'think, hold the view that' is the neutral nonveridical doxastic verb. -/
def renwei : Verb := {
  form := "renwei"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-- 知道 *zhīdào* 'know', presupposing its complement and asserting belief in it; *rènwéi* is
its non-factive counterpart. -/
def zhidao : Verb := {
  form := "zhidao"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  passivizable := false
  opaqueContext := true
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi }

/-- 后悔 *hòuhuǐ* 'regret', the emotive factive. -/
def houhui : Verb := {
  form := "houhui"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  projectionBehavior := some .hole
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full }

/-- 开始 *kāishǐ* 'start', presupposing that the action or state was not under way before. -/
def kaishi : Verb := {
  form := "kaishi"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  phasal := some .inception }

/-! ### Control and causative predicates

The entries record the surface form and whether the complement is finite. The sizes and the
dynamicity of the complements each predicate selects are the analysis of Liu and Yip and live in
`Studies/LiuYip2026.lean`. -/

/-- 想 *xiǎng* 'want' is a desiderative verb with a nonfinite complement. -/
def xiang : Verb := {
  form := "xiang"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 让 *ràng* 'let' is a manipulative verb with a nonfinite complement. -/
def rang : Verb := {
  form := "rang"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := false }

/-- 相信 *xiāngxìn* 'believe' is a propositional attitude verb with a finite complement. -/
def xiangxin : Verb := {
  form := "xiangxin"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .veridical) }

/-- 劝 *quàn* 'urge' is a manipulative verb with a nonfinite complement. -/
def quan : Verb := {
  form := "quan"
  frames := [ArgumentFrame.infinitival]
  passivizable := true
  opaqueContext := false }

/-- 逼 *bī* 'force' is a manipulative verb with a nonfinite complement. -/
def bi : Verb := {
  form := "bi"
  frames := [ArgumentFrame.infinitival]
  passivizable := true
  opaqueContext := false }

/-- 打算 *dǎsuàn* 'plan' is a desiderative verb with a nonfinite complement. -/
def dasuan : Verb := {
  form := "dasuan"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 设法 *shèfǎ* 'try' is an achievement verb with a nonfinite complement. -/
def shefa : Verb := {
  form := "shefa"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := false }

/-- The verb inventory. -/
def verbs : List Verb :=
  [qidai, danxin, xiwang, haipa, yiwei, renwei, zhidao, houhui, kaishi,
   xiang, rang, xiangxin, quan, bi, dasuan, shefa]

end Mandarin
