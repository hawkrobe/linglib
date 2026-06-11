import Linglib.Data.Examples.Schema
import Linglib.Semantics.Tense.Reichenbach
import Linglib.Data.Examples.ArreguiKusumoto1998

/-!
# [arregui-kusumoto-1998]: Tense in Temporal Adjunct Clauses
[arregui-kusumoto-1998] [ogihara-sharvit-2012]

Arregui & Kusumoto (SALT VIII, 1998) argue that tense in temporal
adjunct clauses (TACs) is **not** semantically in the scope of the
matrix tense. They reject the relative-tense analysis of Ogihara (1994,
1996) on the basis of:

- Japanese when-clauses with past tense (ex 8) are episodic and
  acceptable, contradicting a relative-tense prediction of clash with
  `toki` ('when').
- Polish before- or after-clauses pattern with English (past + past), but
  Polish lacks the SOT rule — so the English pattern can't be a
  SOT-deletion effect.
- Geis-style ambiguities (ex 14) in English when-, before-, after-clauses
  indicate a relative-clause structure where the embedded tense is
  evaluated independently with the speech time as its reference.

A&K propose: English and Polish TACs are relative-clause-like (absolute
tenses); Japanese before- or after-clauses involve direct TP-selection by
the temporal connective (no relative-clause structure); Japanese
when-clauses are absolute (like English when). The past-vs-present
contrast in Japanese TACs is **quantificational** (episodic vs
habitual), not temporal — present tense is a temporal variable bound
by adverbs of quantification.

## Empirical anchors (verified vs PDF)

- (1) "Bernhard said that Junko was sick" — English SOT context-setter.
- (5a/b) Japanese before+past * vs before+present OK.
- (6a/b) Japanese after+past OK vs after+present *.
- (7a/b) English Elliott/Eva with both past+past tense.
- (8) "Junko was in her room when Satoshi came" — Japanese when+past
  (episodic), the counterexample to Ogihara's relative tense.
- (9) "...whenever Satoshi came" — Japanese when+present (habitual).
- (14) "I encountered Satoshi in Amherst when you said he had left"
  — Geis ambiguity.
- (18a/b) "I watered the plant before/after it died" — before/after
  veridicality contrast.

## Scope of the Reichenbach frames below

A&K's English-side anchor example is **Elliott left before Eva came**
(ex 7a); frames are named `elliottLeft` / `evaCame` accordingly.

The (R,E)-frames only capture temporal ordering between two past
events. A&K's actual contribution — the relative-clause analysis of
English/Polish TACs vs direct TP-selection in Japanese, plus the
past/present quantificational contrast — is not encodable in
(S,P,R,E) and lives in the JSON above + the verified Geis-ambiguity
example.

-/

namespace ArreguiKusumoto1998

open Data.Examples (LinguisticExample)

-- ════════════════════════════════════════════════════════════════
-- § Reichenbach frames (illustrative; named for A&K ex 7a Elliott/Eva)
-- ════════════════════════════════════════════════════════════════

/-! These frames represent A&K example (7a) — `Elliott left before Eva
    came`. The (R,E)-frame only encodes the temporal ordering between
    the two past events; A&K's actual claims about TAC structure
    (relative-clause vs direct TP-selection) and the
    episodic/habitual quantificational contrast are not encoded in
    Reichenbach frames. The JSON above carries those facts. -/

/-- Adjunct clause "before Eva came" — Eva's coming event.
    Past tense; in A&K's analysis, this past tense in English is
    interpreted absolutely (with speech time as reference), unlike
    the Ogihara relative-tense story. -/
def evaCame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- absolute: P = S
  referenceTime := -3
  eventTime := -3

/-- Matrix clause "Elliott left" — Elliott's leaving event.
    Past tense; absolute perspective. -/
def elliottLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2


-- ════════════════════════════════════════════════════════════════
-- § Per-datum verifications
-- ════════════════════════════════════════════════════════════════

/-- `before`-ordering: the adjunct event precedes the matrix event.
    This is the structural consequence of `before` in the temporal
    connective, not of any tense composition. -/
theorem evaCame_before_elliottLeft :
    evaCame.eventTime < elliottLeft.eventTime := by decide

end ArreguiKusumoto1998
