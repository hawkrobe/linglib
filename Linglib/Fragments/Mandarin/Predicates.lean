import Linglib.Semantics.Attitudes.Preferential
import Linglib.Semantics.Verb.Basic

/-!
# Mandarin Predicate Lexicon Fragment
@cite{qing-uegaki-2025} @cite{glass-2025}

Mandarin predicates relevant to @cite{qing-uegaki-2025}. Properties like
C-distributivity and NVP class are DERIVED from the `attitude` field.
-/

namespace Mandarin.Predicates

open Semantics.Lexical
open Semantics.Attitudes.Preferential (AttitudeValence NVPClass)

/-- Mandarin verb entry: extends VerbCore with no inflectional morphology
    (Mandarin is an isolating language). -/
structure MandarinVerbEntry extends VerbCore where
  deriving Repr, BEq

/-- Smart constructor: sets only the citation form (no inflection). -/
def MandarinVerbEntry.mk' (core : VerbCore) : MandarinVerbEntry :=
  { toVerbCore := core }

/-- 期待 "qidai" — look forward to (Class 1: positive, non-C-distributive, takes questions). -/
def qidai : MandarinVerbEntry := .mk' {
  form := "qidai"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.relevanceBased .positive)) }

/-- 担心 "danxin" — worry (Class 1: negative, non-C-distributive). -/
def danxin : MandarinVerbEntry := .mk' {
  form := "danxin"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased) }

/-- 希望 "xiwang" — hope (Class 3: positive, C-distributive, anti-rogative). -/
def xiwang : MandarinVerbEntry := .mk' {
  form := "xiwang"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 害怕 "haipa" — fear (Class 2: negative, C-distributive, takes questions). -/
def haipa : MandarinVerbEntry := .mk' {
  form := "haipa"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative)) }

/-- 以为 "yǐwéi" — be under the impression that.

A nonveridical doxastic attitude. @cite{glass-2025} analyzes its weak
contrafactive postsupposition (◇¬p, not derivable from veridicality alone);
that paper-specific apparatus lives in `Glass2025`, not on this entry. -/
def yiwei : MandarinVerbEntry := .mk' {
  form := "yiwei"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical) }

/-! ## Liu & Yip 2026 complement-taking predicates

Seven additional Mandarin CTPs cited by @cite{liu-yip-2026} (lists in (18)
and (19)) for the *you*-skipping pattern. Theory-light: only consensus
typology — surface form, finite vs nonfinite complement selection, and
@cite{noonan-2007} `CTPClass`. The [+D] / [-D] selectional refinement
within nonfinite TPs (Lin & Liu 2009) is theory-laden and lives in
`Studies/LiuYip2026.lean` as a Studies-side
projection per the audit's "derive don't stipulate" discipline. -/

/-- 想 *xiang* 'want' — desiderative; nonfinite-taking. Liu & Yip 2026 (18). -/
def xiang : MandarinVerbEntry := .mk' {
  form := "xiang"
  complementType := .infinitival
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 让 *rang* 'let' — manipulative; nonfinite-taking. Liu & Yip 2026 (18). -/
def rang : MandarinVerbEntry := .mk' {
  form := "rang"
  complementType := .infinitival
  passivizable := false
  opaqueContext := false }

/-- 相信 *xiangxin* 'believe' — propositional attitude; finite-taking
    (CP-only). Liu & Yip 2026 (19) — blocks *you*-skipping. -/
def xiangxin : MandarinVerbEntry := .mk' {
  form := "xiangxin"
  complementType := .finiteClause
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .veridical) }

/-- 劝 *quan* 'urge' — manipulative; nonfinite-taking. Liu & Yip 2026 (18). -/
def quan : MandarinVerbEntry := .mk' {
  form := "quan"
  complementType := .infinitival
  passivizable := true
  opaqueContext := false }

/-- 逼 *bi* 'force' — manipulative; nonfinite-taking. Liu & Yip 2026 (18)
    (listed as *bi(po)*). -/
def bi : MandarinVerbEntry := .mk' {
  form := "bi"
  complementType := .infinitival
  passivizable := true
  opaqueContext := false }

/-- 打算 *dasuan* 'plan' — desiderative; nonfinite-taking. Liu & Yip 2026
    (18). Liu & Yip Appendix A discusses *dasuan*'s ambiguity between
    Type II (TP) and Type III (vP) selection. -/
def dasuan : MandarinVerbEntry := .mk' {
  form := "dasuan"
  complementType := .infinitival
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- 设法 *shefa* 'try' — achievement; nonfinite-taking. Liu & Yip 2026 (18).
    @cite{noonan-2007} classifies 'try' under the achievement CTP class. -/
def shefa : MandarinVerbEntry := .mk' {
  form := "shefa"
  complementType := .infinitival
  passivizable := false
  opaqueContext := false }

def allVerbs : List MandarinVerbEntry :=
  [qidai, danxin, xiwang, haipa, yiwei,
   xiang, rang, xiangxin, quan, bi, dasuan, shefa]

def lookup (form : String) : Option MandarinVerbEntry :=
  allVerbs.find? (·.form == form)

/-! ## Drift sentries on the Liu&Yip2026 cohort -/

/-- The seven Liu & Yip 2026 predicates split into 6 nonfinite-takers
    (allow *you*-skipping per (18)) and 1 finite-taker (blocks it per (19)). -/
theorem liuyip_partition :
    [xiang, rang, quan, bi, dasuan, shefa].all
      (·.complementType = .infinitival) = true ∧
    xiangxin.complementType = .finiteClause := by
  refine ⟨?_, rfl⟩
  decide

end Mandarin.Predicates
