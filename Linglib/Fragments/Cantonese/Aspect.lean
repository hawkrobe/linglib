import Linglib.Syntax.Minimalist.Verbal.Aspect

/-!
# Cantonese Aspect Markers
[matthews-yip-1994] [cheung-1972] [cheung-2007] [yip-k-f-2025]
[liu-yip-2026] App. B (127)

Cantonese (ISO `yue`, Sinitic) postverbal aspect markers, organized along the
inner / outer split (Travis 2010, MacDonald 2008, Sybesma 2017): outer markers
sit above vP and host viewpoint distinctions; inner markers sit inside vP and
host Aktionsart-derived distinctions (notably the rich inventory of phase
complements catalogued by [yip-k-f-2025] and reproduced in
[liu-yip-2026] Appendix B).

This file commits the lexical data; the analytical positioning of -faan as
outer-aspect-associated (and -gwo as inner-aspect-associated) is per Liu &
Yip 2026's analysis and lives in
`Studies/LiuYip2026.lean`.
-/

namespace Cantonese.Aspect

open Minimalist (AspFlavor AspHead)

/-- A Cantonese aspect-marker lexical entry. Theory-light: surface form, gloss,
    a rough Aktionsart classification (perfective / experiential / progressive /
    continuative / repetitive), the cartographic AspFlavor it conventionally
    associates with (per the inner / outer split), and a pointer to the
    canonical citation. -/
structure AspectMarker where
  form : String          -- jyutping
  hanzi : String         -- Chinese character
  gloss : String         -- short gloss
  flavor : AspFlavor     -- outer (above vP) or inner (within vP)
  semantic : String      -- coarse semantic label
  notes : String := ""
  deriving Repr

/-! ## Outer-aspect markers (canonically associate with AspP_outer above vP) -/

/-- *-zo* 咗 — perfective, postverbal suffix (Cantonese counterpart of Mandarin
    *-le*). Outer aspect per [yip-k-f-2025]. -/
def zo : AspectMarker :=
  { form := "-zo", hanzi := "咗", gloss := "PFV"
  , flavor := .outer, semantic := "perfective" }

/-- *-gan* 緊 — progressive, postverbal suffix. Outer aspect (viewpoint).
    Cantonese counterpart of Mandarin *zhengzai* / *zai* (the progressive,
    not the again-element). -/
def gan : AspectMarker :=
  { form := "-gan", hanzi := "緊", gloss := "PROG"
  , flavor := .outer, semantic := "progressive" }

/-- *-faan* 返 — repetitive / restorative aspect, postverbal suffix.
    Liu & Yip 2026 §5–6 analyse it as AspP_outer-associated; its exceptional
    wide scope across nonfinite vPs is the headline Cantonese case study. -/
def faan : AspectMarker :=
  { form := "-faan", hanzi := "返", gloss := "again"
  , flavor := .outer, semantic := "repetitive"
  , notes := "Liu&Yip2026: associates with matrix AspP_outer via Agree" }

/-! ## Inner-aspect markers (canonically associate with AspP_inner within vP) -/

/-- *-gwo* 過 — experiential aspect, postverbal suffix (Cantonese counterpart of
    Mandarin *-guo*). [liu-yip-2026] §5 analyse the *repetitive*-flavored
    *-gwo* as AspP_inner-associated, distinct from the experiential reading.
    The entry here records the lexical form; the dual analysis lives in
    `LiuYip2026.lean`. -/
def gwo : AspectMarker :=
  { form := "-gwo", hanzi := "過", gloss := "EXP/again"
  , flavor := .inner, semantic := "experiential / repetitive"
  , notes := "Liu&Yip2026: repetitive use is AspP_inner; no scope lowering" }

/-- *-zyu* 住 — continuative / durative postverbal suffix. Per
    [matthews-yip-1994]: ngo5 zo6-zyu6 'I am sitting'. Inner aspect. -/
def zyu : AspectMarker :=
  { form := "-zyu", hanzi := "住", gloss := "CONT"
  , flavor := .inner, semantic := "continuative" }

/-! ## Inventory + drift sentry -/

def all : List AspectMarker := [zo, gan, faan, gwo, zyu]

/-- Drift sentry: this fragment covers the five aspect markers above. -/
theorem all_membership :
    all.map (·.form) = ["-zo", "-gan", "-faan", "-gwo", "-zyu"] := by decide

/-- *-faan* and *-zo* and *-gan* are outer-aspect; *-gwo* and *-zyu* are
    inner-aspect. -/
theorem flavor_partition :
    faan.flavor = .outer ∧ zo.flavor = .outer ∧ gan.flavor = .outer ∧
    gwo.flavor = .inner ∧ zyu.flavor = .inner := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Bridge to AspHead substrate

Each AspectMarker projects to an `AspHead`. *-faan* is the only entry that
gets a probe-bearing AspHead (it is the head that triggers Liu & Yip's
agreement-across-clause-boundary mechanism); the others are bare. *-faan*'s
AspHead has `selectsDynamicity = none` because Liu & Yip 2026 (their footnote
on (78), citing data with stative *jau* 'have') note that *-faan* does NOT
require a dynamic complement, in contrast with Mandarin *you* (which does). -/

def AspectMarker.toAspHead (m : AspectMarker) : AspHead :=
  match m.flavor with
  | .outer => { flavor := .outer, selectsDynamicity := none }
  | .inner => { flavor := .inner, selectsDynamicity := none }

theorem faan_is_outer : faan.toAspHead.flavor = .outer := rfl
theorem gwo_is_inner : gwo.toAspHead.flavor = .inner := rfl

/-- Liu & Yip 2026's audit-flagged claim: *-faan* does NOT carry a `[+D]`
    selectional restriction (it composes with stative *jau* 'have'). Encoded
    by leaving `selectsDynamicity = none` on its AspHead. -/
theorem faan_no_dynamicity_requirement :
    faan.toAspHead.selectsDynamicity = none := rfl

end Cantonese.Aspect
