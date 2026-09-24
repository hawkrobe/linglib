module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Mandarin verbs

The Mandarin clause-embedding predicates the studies of Qing and Uegaki, of Glass, of Wang and
of Liu and Yip consume: the preferential attitudes *qīdài* 'look forward to', *dānxīn* 'worry',
*xīwàng* 'hope' and *hàipà* 'fear', the doxastic *yǐwéi* 'think, wrongly' and *rènwéi*
'think', the factives *zhīdào* 'know' and *hòuhuǐ* 'regret', the inchoative *kāishǐ* 'start',
and the control and causative predicates *xiǎng* 'want', *ràng* 'let', *xiāngxìn*
'believe', *quàn* 'urge', *bī* 'force', *dǎsuàn* 'plan' and *shèfǎ* 'try'. Mandarin is
isolating, so a verb carries no inflectional fields; an entry adds its characters to the root
entry, whose form is the pinyin.

## Main definitions

* `Mandarin.Verb`: a Mandarin verb, the root `Verb` with its characters.
* `Mandarin.verbs`: the inventory of the entries.

## References

* [glass-2025]
* [qing-uegaki-2025]
* [wang-2025]
* [liu-yip-2026]
-/

@[expose] public section

namespace Mandarin

open ArgumentStructure

/-- A Mandarin verb: the cross-linguistic core with the pinyin as citation form, plus its
characters. Mandarin being isolating, the verb has no inflectional fields. -/
structure Verb extends _root_.Verb where
  /-- The characters. -/
  hanzi : String
  deriving BEq

/-- 期待 *qīdài* 'look forward to' is a positive preferential attitude that takes questions. -/
def qidai : Verb := {
  form := "qīdài"
  hanzi := "期待"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.relevanceBased .positive)) }

/-- 担心 *dānxīn* 'worry' is a negative preferential attitude. -/
def danxin : Verb := {
  form := "dānxīn"
  hanzi := "担心"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased) }

/-- 希望 *xīwàng* 'hope' is a positive preferential attitude that takes no questions. -/
def xiwang : Verb := {
  form := "xīwàng"
  hanzi := "希望"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 害怕 *hàipà* 'fear' is a negative preferential attitude that takes questions. -/
def haipa : Verb := {
  form := "hàipà"
  hanzi := "害怕"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative)) }

/-- 以为 *yǐwéi* 'be under the impression that' is a nonveridical doxastic attitude. -/
def yiwei : Verb := {
  form := "yǐwéi"
  hanzi := "以为"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-- 认为 *rènwéi* 'think, hold the view that' is the neutral nonveridical doxastic verb. -/
def renwei : Verb := {
  form := "rènwéi"
  hanzi := "认为"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-- 知道 *zhīdào* 'know', presupposing its complement and asserting belief in it; *rènwéi* is
its non-factive counterpart. -/
def zhidao : Verb := {
  form := "zhīdào"
  hanzi := "知道"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  passivizable := false
  opaqueContext := true
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi }

/-- 后悔 *hòuhuǐ* 'regret', the emotive factive. -/
def houhui : Verb := {
  form := "hòuhuǐ"
  hanzi := "后悔"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  projectionBehavior := some .hole
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full }

/-- 开始 *kāishǐ* 'start', presupposing that the action or state was not under way before. -/
def kaishi : Verb := {
  form := "kāishǐ"
  hanzi := "开始"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  phasal := some .inception }

/-! ### Control and causative predicates

The entries record the surface form and whether the complement is finite. The sizes and the
dynamicity of the complements each predicate selects are the analysis of Liu and Yip and live in
`Studies/LiuYip2026.lean`. -/

/-- 想 *xiǎng* 'want' is a desiderative verb with a nonfinite complement. -/
def xiang : Verb := {
  form := "xiǎng"
  hanzi := "想"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 让 *ràng* 'let' is a manipulative verb with a nonfinite complement. -/
def rang : Verb := {
  form := "ràng"
  hanzi := "让"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := false }

/-- 相信 *xiāngxìn* 'believe' is a propositional attitude verb with a finite complement. -/
def xiangxin : Verb := {
  form := "xiāngxìn"
  hanzi := "相信"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .veridical) }

/-- 劝 *quàn* 'urge' is a manipulative verb with a nonfinite complement. -/
def quan : Verb := {
  form := "quàn"
  hanzi := "劝"
  frames := [ArgumentFrame.infinitival]
  passivizable := true
  opaqueContext := false }

/-- 逼 *bī* 'force' is a manipulative verb with a nonfinite complement. -/
def bi : Verb := {
  form := "bī"
  hanzi := "逼"
  frames := [ArgumentFrame.infinitival]
  passivizable := true
  opaqueContext := false }

/-- 打算 *dǎsuàn* 'plan' is a desiderative verb with a nonfinite complement. -/
def dasuan : Verb := {
  form := "dǎsuàn"
  hanzi := "打算"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 设法 *shèfǎ* 'try' is an achievement verb with a nonfinite complement. -/
def shefa : Verb := {
  form := "shèfǎ"
  hanzi := "设法"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := false }

/-- The verb inventory. -/
def verbs : List Verb :=
  [qidai, danxin, xiwang, haipa, yiwei, renwei, zhidao, houhui, kaishi,
   xiang, rang, xiangxin, quan, bi, dasuan, shefa]

end Mandarin
