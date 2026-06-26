import Linglib.Syntax.Minimalist.Verbal.Aspect

/-!
# Cantonese Resultative / Phase Complements
[matthews-yip-1994] [cheung-2007] [yip-k-f-2025]
[liu-yip-2026] App. B (127), Table 6

Cantonese inner-aspectual postverbal elements catalogued by
[yip-k-f-2025] and reproduced in [liu-yip-2026] Appendix B (127).
The audit on Liu & Yip 2026's integration flagged that these elements were
entirely absent from linglib at that point; this file fills the gap with a
theory-light per-morpheme inventory paralleling Mandarin's
`Fragments/Mandarin/Resultatives.lean` phase-complement entries.

Distinguishing the resultative-verbal-complements (RVCs) from the
phase complements proper requires the three diagnostics of Liu & Yip
Appendix B Table 6: perfective suffixation, *-dak* / *-m-* infixation,
and following an RVC. We commit only the morphological/phonological
data; the diagnostic-based classification lives in the Studies file.
-/

namespace Cantonese.ResultativeComplements

open Minimalist (AspFlavor AspHead)

/-- A Cantonese inner-aspectual postverbal element. -/
structure InnerAspMarker where
  jyutping : String        -- jyutping with tone number
  hanzi : String           -- Chinese character (when standardized)
  gloss : String           -- short English gloss
  example_ : String        -- representative V+marker example
  notes : String := ""
  deriving Repr

/-! ## Inventory per [liu-yip-2026] Appendix B (127a–m) -/

/-- *-dim6* 掂 'all right'. e.g. *gaau2-dim6* 'finished, settled'. -/
def dim : InnerAspMarker :=
  { jyutping := "-dim6", hanzi := "掂", gloss := "all right"
  , example_ := "gaau2-dim6 (finished, settled)" }

/-- *-dou2* 倒 'arrive'. e.g. *wan2-dou2* 'found'. -/
def dou : InnerAspMarker :=
  { jyutping := "-dou2", hanzi := "倒", gloss := "arrive"
  , example_ := "wan2-dou2 (found)" }

/-- *-gin3* 見 'see'. e.g. *teng1-gin3* 'hear'. -/
def gin : InnerAspMarker :=
  { jyutping := "-gin3", hanzi := "見", gloss := "see"
  , example_ := "teng1-gin3 (hear)" }

/-- *-hei2* 起 (lit. 'lift'). e.g. *waak6-hei2* 'finished drawing'. -/
def hei : InnerAspMarker :=
  { jyutping := "-hei2", hanzi := "起", gloss := "lift / finish"
  , example_ := "waak6-hei2 (finished drawing)" }

/-- *-hou2* 好 'good'. e.g. *zou6-hou2* 'being done'. -/
def hou : InnerAspMarker :=
  { jyutping := "-hou2", hanzi := "好", gloss := "good"
  , example_ := "zou6-hou2 (being done)" }

/-- *-jyun4* 完 'finish'. e.g. *sik6-jyun4* 'finished eating'. -/
def jyun : InnerAspMarker :=
  { jyutping := "-jyun4", hanzi := "完", gloss := "finish"
  , example_ := "sik6-jyun4 (finished eating)" }

/-- *-seng4* 成 'succeed'. e.g. *joek3-seng4* 'succeeded in making
    an appointment'. -/
def seng : InnerAspMarker :=
  { jyutping := "-seng4", hanzi := "成", gloss := "succeed"
  , example_ := "joek3-seng4 (succeeded in making an appointment)" }

/-- *-zoek6* 著 'on target'. e.g. *fan3-zoek6* 'slept'. -/
def zoek : InnerAspMarker :=
  { jyutping := "-zoek6", hanzi := "著", gloss := "on target"
  , example_ := "fan3-zoek6 (slept)" }

/-- *-lok6* 落 'finish, fall'. e.g. *zyu2-lok6* 'taught way back then'. -/
def lok : InnerAspMarker :=
  { jyutping := "-lok6", hanzi := "落", gloss := "finish (a long time ago)"
  , example_ := "zyu2-lok6 (taught way back then)" }

/-- *-ding6* 定 'in advance'. e.g. *zyu2-ding6* 'cooked in advance'.
    Per [wong-shing-kit-2018]. -/
def ding : InnerAspMarker :=
  { jyutping := "-ding6", hanzi := "定", gloss := "in advance"
  , example_ := "zyu2-ding6 (cooked in advance)" }

/-- *-can1* 親 'adversative'. e.g. *daa2-can1* 'injure by hitting'.
    Per [sio-2020]. -/
def can : InnerAspMarker :=
  { jyutping := "-can1", hanzi := "親", gloss := "adversative"
  , example_ := "daa2-can1 (injure by hitting)" }

/-- *-zyu6* 住 'hold'. Continuative use. e.g. *kam2-zyu6* 'cover still'. -/
def zyu : InnerAspMarker :=
  { jyutping := "-zyu6", hanzi := "住", gloss := "hold (continuative)"
  , example_ := "kam2-zyu6 (cover still)" }

/-- *-sat6* 實 'firm'. e.g. *mong6-sat6* 'keep looking'. -/
def sat : InnerAspMarker :=
  { jyutping := "-sat6", hanzi := "實", gloss := "firm"
  , example_ := "mong6-sat6 (keep looking)" }

def all : List InnerAspMarker :=
  [dim, dou, gin, hei, hou, jyun, seng, zoek, lok, ding, can, zyu, sat]

/-- Drift sentry: 13 inner-aspectual elements per [liu-yip-2026]
    Appendix B (127a–m). -/
theorem all_count : all.length = 13 := by decide

/-- All entries are inner-aspectual, projecting to `AspFlavor.inner`. -/
def InnerAspMarker.toAspHead (_ : InnerAspMarker) : AspHead :=
  { flavor := .inner, selectsDynamicity := none }

theorem all_inner :
    ∀ m ∈ all, (m.toAspHead).flavor = .inner := by
  intro m _; rfl

end Cantonese.ResultativeComplements
