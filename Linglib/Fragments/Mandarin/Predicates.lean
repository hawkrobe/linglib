import Linglib.Syntax.Category.Verb.Basic

/-!
# Mandarin predicates

The Mandarin clause-embedding predicates the studies of Qing and Uegaki, of Glass and of Liu
and Yip consume: the preferential attitudes *qidai* 'look forward to', *danxin* 'worry',
*xiwang* 'hope' and *haipa* 'fear', the doxastic *yiwei* 'think, wrongly' and *renwei*
'think', and the control and causative predicates *xiang* 'want', *rang* 'let', *xiangxin*
'believe', *quan* 'urge', *bi* 'force', *dasuan* 'plan' and *shefa* 'try'. Mandarin is
isolating, so a verb carries no inflectional fields beyond the root entry.

## Main definitions

* `Mandarin.Verb` — a Mandarin verb, the root `Verb`
* `Mandarin.verbs` — the inventory

## References

* [glass-2025]
* [qing-uegaki-2025]
-/

namespace Mandarin

open ArgumentStructure

/-- A Mandarin verb: the cross-linguistic core with no inflectional fields, Mandarin being
isolating. -/
structure Verb extends _root_.Verb where
  deriving Repr, BEq

/-- 期待 "qidai" — look forward to (Class 1: positive, non-C-distributive, takes questions). -/
def qidai : Verb := {
  form := "qidai"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.relevanceBased .positive)) }

/-- 担心 "danxin" — worry (Class 1: negative, non-C-distributive). -/
def danxin : Verb := {
  form := "danxin"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased) }

/-- 希望 "xiwang" — hope (Class 3: positive, C-distributive, anti-rogative). -/
def xiwang : Verb := {
  form := "xiwang"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 害怕 "haipa" — fear (Class 2: negative, C-distributive, takes questions). -/
def haipa : Verb := {
  form := "haipa"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative)) }

/-- 以为 "yǐwéi" — be under the impression that.

A nonveridical doxastic attitude. [glass-2025] analyzes its weak
contrafactive postsupposition (◇¬p, not derivable from veridicality alone);
that paper-specific apparatus lives in `Glass2025`, not on this entry. -/
def yiwei : Verb := {
  form := "yiwei"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-- 认为 "rènwéi" — think, hold the view that: the neutral nonveridical doxastic verb. -/
def renwei : Verb := {
  form := "renwei"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-! ### Complement-taking predicates of [liu-yip-2026]

Surface form and finite versus nonfinite complement selection only; the sizes and the
dynamicity of the complements each predicate selects are the analysis of [liu-yip-2026] and live
in `Studies/LiuYip2026.lean`. -/

/-- 想 *xiang* 'want' — desiderative; nonfinite-taking. [liu-yip-2026]. -/
def xiang : Verb := {
  form := "xiang"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 让 *rang* 'let' — manipulative; nonfinite-taking. [liu-yip-2026]. -/
def rang : Verb := {
  form := "rang"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := false }

/-- 相信 *xiangxin* 'believe' — propositional attitude; finite-taking
    (CP-only). [liu-yip-2026]. -/
def xiangxin : Verb := {
  form := "xiangxin"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .veridical) }

/-- 劝 *quan* 'urge' — manipulative; nonfinite-taking. [liu-yip-2026]. -/
def quan : Verb := {
  form := "quan"
  frames := [ArgumentFrame.infinitival]
  passivizable := true
  opaqueContext := false }

/-- 逼 *bi* 'force' — manipulative; nonfinite-taking [liu-yip-2026]. -/
def bi : Verb := {
  form := "bi"
  frames := [ArgumentFrame.infinitival]
  passivizable := true
  opaqueContext := false }

/-- 打算 *dasuan* 'plan' — desiderative; nonfinite-taking [liu-yip-2026]. -/
def dasuan : Verb := {
  form := "dasuan"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 设法 *shefa* 'try' — achievement; nonfinite-taking [liu-yip-2026]. -/
def shefa : Verb := {
  form := "shefa"
  frames := [ArgumentFrame.infinitival]
  passivizable := false
  opaqueContext := false }

def verbs : List Verb :=
  [qidai, danxin, xiwang, haipa, yiwei, renwei,
   xiang, rang, xiangxin, quan, bi, dasuan, shefa]


end Mandarin
