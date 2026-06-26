import Linglib.Syntax.Negation

/-! # Italian Negation Fragment
[haspelmath-2013] [dryer-2013-wals] [zanuttini-1997] [cinque-1999]

Italian sentential negation: the standard preverbal negation particle *non*
and its packaging as a `NegationSystem`. The marker is a free particle
in preverbal position; WALS Ch 143A classifies Italian as `.negv`.
Italian object clitics attach between *non* and the verb (*non lo vedo*,
not **lo non vedo*) — the canonical syntactic analysis is
[zanuttini-1997]'s NegP cartography, refined by [cinque-1999]'s
adverb hierarchy.

## Sibling files

Italian negation is distributed across three coordinated files. This file
holds the operator (the marker + system) and the EN trigger inventory.
The other axes:

- `Fragments/Italian/PolarityItems.lean` — lexical reactives: n-words
  (*nessuno*, *niente*, *mai*, *neanche/nemmeno/neppure*), the formal NPI
  *alcuno*, the emphatic reinforcer *mica*, the FCIs *qualsiasi/qualunque*.
  The operator/lexical-reactive split is documented in
  `Core/Lexical/NegMarker.lean`.
- the EN trigger inventory (this file, below) — the eight [jin-koenig-2021]
  trigger classes attested for Italian, with their lexical triggers.
  Distinct axis from standard sentential negation. The finer
  construction-level weak/strong classification of Italian EN
  environments ([greco-2020] Tables 1–2) lives in `Studies/Greco2020.lean`.
- `Fragments/Italian/PolarityMarking.lean` — sentence-level polarity
  strategies (emphatic affirmation, focus particles).

Bias-conditioned *non₂* (the non-truth-functional comparative *non* of
[napoli-nespor-1976]) surfaces obliquely via the `pur` and `affatto`
entries in `PolarityItems.lean`.
-/

namespace Italian.Negation

open Syntax.Negation

/-- *non* — Italian's standard preverbal negation particle.
    `Non ho visto nessuno` 'NEG have seen nobody' = "I didn't see anyone".
    A free word, not a clitic; syntactically immediately preverbal. -/
def non : NegMarkerEntry :=
  { form := "non"
  , morphemeType := .particle
  , position := .preverbal }

/-- The Italian negation system: a single preverbal particle.
    The Fragment-side joint consumed by `Studies/Dryer2013Negation.lean`.
    WALS classifications are pulled from `Data/WALS/Features/F112A.lean`
    et al. via `NegationSystem.ofISO` — never hand-encoded. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "ita" [non]

/-! ## Expletive Negation
[jin-koenig-2021]

The eight EN trigger classes attested for Italian in [jin-koenig-2021]'s
722-language survey (Table 3, Italic row), each with its lexical trigger.
Unlike French — whose grammaticalized EN marker is bare *ne*, distinct
from standard *ne...pas* — Italian uses the standard negator *non* for
every EN environment, so EN and standard negation are string-identical
([greco-2020] exploits exactly this ambiguity for Snegs).

Note the cross-Romance contrast visible in the survey: Italian's row has
DOUBT (*dubitare*) but, unlike French, no FEAR class.
-/

/-- EN trigger-negator pairings from [jin-koenig-2021] Table 3
    (Italic section). -/
def enTriggerNegators : List ENTriggerNegator :=
  [ { triggerClass := "BEFORE", triggerForm := "prima che"
    , enNegatorForm := "non" }
  , { triggerClass := "DOUBT", triggerForm := "dubitare"
    , enNegatorForm := "non" }
  , { triggerClass := "HARDLY", triggerForm := "appena"
    , enNegatorForm := "non" }
  , { triggerClass := "NEARLY", triggerForm := "per poco"
    , enNegatorForm := "non" }
  , { triggerClass := "THAN", triggerForm := "di quanto"
    , enNegatorForm := "non" }
  , { triggerClass := "UNLESS", triggerForm := "a meno che"
    , enNegatorForm := "non" }
  , { triggerClass := "UNTIL", triggerForm := "finché, fino a"
    , enNegatorForm := "non" }
    -- J&K Table 3 prints the WITHOUT trigger as "senza que" (a typo
    -- carried from their source, per their fn. 5); *senza che* is the
    -- Italian form.
  , { triggerClass := "WITHOUT", triggerForm := "senza che"
    , enNegatorForm := "non" } ]

/-- Every Italian EN environment uses the standard negator: the EN
    negator form coincides with the `non` marker entry. -/
theorem en_negator_is_standard :
    enTriggerNegators.all (·.enNegatorForm == non.form) = true := by decide

/-- Italian negation profile (WALS Ch 112-115 + Greco/JinKoenig fields). -/
def negationProfile : Syntax.Negation.NegationProfile :=
  { language := "Italian"
  , iso := "ita"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .mixed
  , negMarkers := ["non"]
  , negIsHead := some true
  , enAttested := some true }

end Italian.Negation
