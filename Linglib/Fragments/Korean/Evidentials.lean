import Linglib.Theories.Semantics.Tense.Evidential

/-!
# Korean Evidential Fragment (Cumming 2026)

Paradigm entries for Korean tense-evidential morphology from Cumming (2026),
Tables 18 (-te) and 19 (-ney). Korean is notable for morphologically encoding
evidential perspective independently of utterance perspective.

## -te vs -ney

Both markers distinguish retrospective/contemporaneous/prospective EP, but
their UP constraints differ:
- **-te**: UP is always T < S (past-shifted)
- **-ney**: UP tracks speech-time more tightly (T < S, T = S, S < T)

This EP/UP factorization is verified in `Phenomena/Cumming2026/Bridge.lean`.

## References

- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175. Tables 18, 19.
-/

namespace Fragments.Korean.Evidentials

open Semantics.Tense.Evidential

-- ════════════════════════════════════════════════════
-- § 1. Korean -te (Table 18)
-- ════════════════════════════════════════════════════

/-- Korean -te PAST: T < A (strict downstream), T < S (past). -/
def tePast : TenseEvidentialParadigm where
  label := "-te PAST"
  ep := .strictDownstream
  up := .past

/-- Korean -te PRESENT: T = A (contemporaneous), T < S (past). -/
def tePresent : TenseEvidentialParadigm where
  label := "-te PRES"
  ep := .contemporaneous
  up := .past

/-- Korean -te FUTURE: A < T (prospective). -/
def teFuture : TenseEvidentialParadigm where
  label := "-te FUT"
  ep := .prospective
  up := .unconstrained

-- ════════════════════════════════════════════════════
-- § 2. Korean -ney (Table 19)
-- ════════════════════════════════════════════════════

/-- Korean -ney PAST: T < A (strict downstream), T < S (past). -/
def neyPast : TenseEvidentialParadigm where
  label := "-ney PAST"
  ep := .strictDownstream
  up := .past

/-- Korean -ney PRESENT: T = A (contemporaneous), T = S (present). -/
def neyPresent : TenseEvidentialParadigm where
  label := "-ney PRES"
  ep := .contemporaneous
  up := .present

/-- Korean -ney FUTURE: A < T (prospective), S < T (future). -/
def neyFuture : TenseEvidentialParadigm where
  label := "-ney FUT"
  ep := .prospective
  up := .future

-- ════════════════════════════════════════════════════
-- § 3. Collections
-- ════════════════════════════════════════════════════

/-- All Korean -te entries. -/
def teEntries : List TenseEvidentialParadigm :=
  [tePast, tePresent, teFuture]

/-- All Korean -ney entries. -/
def neyEntries : List TenseEvidentialParadigm :=
  [neyPast, neyPresent, neyFuture]

/-- All Korean evidential entries. -/
def allEntries : List TenseEvidentialParadigm :=
  teEntries ++ neyEntries

end Fragments.Korean.Evidentials
