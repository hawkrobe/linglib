import Linglib.Semantics.Tense.Evidential

/-!
# Korean Evidential Fragment
[cumming-2026]

Paradigm entries for Korean tense-evidential morphology from [cumming-2026],
paradigm tables (18) (-te) and (19) (-ney). Korean is notable for morphologically encoding
evidential perspective independently of utterance perspective.

## -te vs -ney

Both markers distinguish retrospective/contemporaneous/prospective EP, but
their UP constraints differ:
- **-te**: UP is always T < S (past-shifted)
- **-ney**: UP tracks speech-time more tightly (T < S, T = S, S < T)

This EP/UP factorization is verified in `Studies/Cumming2026.lean`.

-/

namespace Korean.Evidentials

open Tense.Evidential

-- ════════════════════════════════════════════════════
-- § 1. Korean -te (table (18))
-- ════════════════════════════════════════════════════

/-- Korean -te PAST: T < A (strict downstream), T < S (past). -/
def tePast : TAMEEntry where
  label := "-te PAST"
  ep := .strictDownstream
  up := .past

/-- Korean -te PRESENT: T = A (contemporaneous), T < S (past). -/
def tePresent : TAMEEntry where
  label := "-te PRES"
  ep := .contemporaneous
  up := .past

/-- Korean -te FUTURE: A < T (prospective). -/
def teFuture : TAMEEntry where
  label := "-te FUT"
  ep := .prospective
  up := .unconstrained

-- ════════════════════════════════════════════════════
-- § 2. Korean -ney (table (19))
-- ════════════════════════════════════════════════════

/-- Korean -ney PAST: T < A (strict downstream), T < S (past). -/
def neyPast : TAMEEntry where
  label := "-ney PAST"
  ep := .strictDownstream
  up := .past

/-- Korean -ney PRESENT: T = A (contemporaneous), T = S (present). -/
def neyPresent : TAMEEntry where
  label := "-ney PRES"
  ep := .contemporaneous
  up := .present

/-- Korean -ney FUTURE: A < T (prospective), S < T (future). -/
def neyFuture : TAMEEntry where
  label := "-ney FUT"
  ep := .prospective
  up := .future

-- ════════════════════════════════════════════════════
-- § 3. Collections
-- ════════════════════════════════════════════════════

/-- All Korean -te entries. -/
def teEntries : List TAMEEntry :=
  [tePast, tePresent, teFuture]

/-- All Korean -ney entries. -/
def neyEntries : List TAMEEntry :=
  [neyPast, neyPresent, neyFuture]

/-- All Korean evidential entries. -/
def allEntries : List TAMEEntry :=
  teEntries ++ neyEntries

end Korean.Evidentials
