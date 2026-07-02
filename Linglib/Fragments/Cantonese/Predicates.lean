import Linglib.Features.Complementation

/-!
# Cantonese Complement-Taking Predicates
[matthews-yip-1994] [liu-yip-2026]

Theory-light inventory of Cantonese complement-taking predicates (CTPs)
relevant to the Liu & Yip 2026 analysis. Each entry records consensus
metadata: surface form, Noonan CTP class, and which complement sizes the
predicate is reported to take per Liu & Yip 2026 §5–6 (Lists in (79) and (80)).

The size labels (`vP`, `tP`, `cP`) are exposed through a small enum local to
this file rather than imported from `Syntax/Minimalist/`, because
the size-classification is a *consensus typological* observation that any
theory of Cantonese clausal complementation must respect, not an analytical
projection. The Minimalist-internal `ComplementSize` substrate is consumed
by the Studies file, not by the Fragment.
-/

namespace Cantonese.Predicates

/-- The size of the complement clause a Cantonese predicate selects, per
    [liu-yip-2026] §5–6's classification: vP (Aspect Restructuring,
    Type III), tP (nonfinite without Aspect Restructuring, Type II), or
    cP (finite, Type I). A predicate may select more than one size. -/
inductive ComplementSizeLabel where
  | vP
  | tP
  | cP
  deriving DecidableEq, Repr

/-- A Cantonese complement-taking predicate. -/
structure CTPEntry where
  jyutping : String
  hanzi : String
  gloss : String
  ctpClass : CTPClass
  /-- Sizes this predicate is attested to take per [liu-yip-2026]. -/
  selects : List ComplementSizeLabel
  notes : String := ""
  deriving Repr

/-! ## Predicates allowing -faan's exceptional wide scope (per Liu&Yip2026 (79))

These are nonfinite-clause-takers; they license -faan-lowering across their
embedded vP. Liu & Yip's (79) lists: bik, ceng, daasyun, gaiwaak, gam, giu,
hang, hoici, hoji, hyun, paai, soeng, zeonbei. -/

/-- 想 *soeng* 'want' — desiderative; selects vP (per Liu&Yip2026 §5–6). -/
def soeng : CTPEntry :=
  { jyutping := "soeng2", hanzi := "想", gloss := "want"
  , ctpClass := .desiderative, selects := [.vP] }

/-- 勸 *hyun* 'urge' — manipulative; selects vP. -/
def hyun : CTPEntry :=
  { jyutping := "hyun3", hanzi := "勸", gloss := "urge"
  , ctpClass := .manipulative, selects := [.vP] }

/-- 逼 *bik* 'force' — manipulative; selects vP. -/
def bik : CTPEntry :=
  { jyutping := "bik1", hanzi := "逼", gloss := "force"
  , ctpClass := .manipulative, selects := [.vP] }

/-- 叫 *giu* 'ask, tell' — manipulative; selects vP. -/
def giu : CTPEntry :=
  { jyutping := "giu3", hanzi := "叫", gloss := "ask, tell"
  , ctpClass := .manipulative, selects := [.vP] }

/-- 打算 *daasyun* 'intend, plan' — desiderative; selects vP. -/
def daasyun : CTPEntry :=
  { jyutping := "daa2syun3", hanzi := "打算", gloss := "intend, plan"
  , ctpClass := .desiderative, selects := [.vP] }

/-! ## Predicates blocking -faan's exceptional wide scope (per Liu&Yip2026 (80))

These are finite-clause (CP) takers. Liu & Yip's (80) lists: geidak, gong,
honang, jingwai, (so-eng)seon, syunbou. -/

/-- 信 *seon* 'believe' — propositional attitude; selects cP only.
    Same family as Mandarin *xiangxin*. Per Liu & Yip 2026 (78), -faan
    cannot take wide scope across an embedded *seon* clause. -/
def seon : CTPEntry :=
  { jyutping := "seon3", hanzi := "信", gloss := "believe"
  , ctpClass := .propAttitude, selects := [.cP] }

/-- 講 *gong* 'say' — utterance; selects cP only. -/
def gong : CTPEntry :=
  { jyutping := "gong2", hanzi := "講", gloss := "say"
  , ctpClass := .utterance, selects := [.cP] }

/-- 記得 *geidak* 'remember' — knowledge / cognitive factive; selects cP
    only per Liu & Yip 2026 (80). -/
def geidak : CTPEntry :=
  { jyutping := "gei3dak1", hanzi := "記得", gloss := "remember"
  , ctpClass := .knowledge, selects := [.cP] }

def all : List CTPEntry :=
  [soeng, hyun, bik, giu, daasyun, seon, gong, geidak]

/-- Drift sentry: 8-predicate inventory matches the verbs explicitly
    mentioned in `Studies/LiuYip2026.lean` consumption. -/
theorem all_membership :
    all.map (·.jyutping) =
      ["soeng2", "hyun3", "bik1", "giu3", "daa2syun3",
       "seon3", "gong2", "gei3dak1"] := by decide

/-- vP-takers (allow -faan-lowering) and cP-takers (block it) form
    a partition of the inventory. Liu & Yip 2026 (79)/(80) classification. -/
theorem partition_vP_cP :
    (all.filter (·.selects = [.vP])).length = 5 ∧
    (all.filter (·.selects = [.cP])).length = 3 := by decide

end Cantonese.Predicates
