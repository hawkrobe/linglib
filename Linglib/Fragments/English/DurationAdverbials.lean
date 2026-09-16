import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Tense.TemporalAdverbials
import Linglib.Semantics.Polarity.Item

/-!
# English duration adverbials

Lexical entries for the English duration adverbials, which take a measure phrase and measure an
interval rather than ordering two times: telic *in three hours*, atelic *for three hours*, the
postposition *three days ago*, and the negative polarity item *in years*, which measures the gap
from the last witnessing event to the right edge of the perfect time span. The schema records the
surface form, the sub-class, the Vendler class the adverbial selects ([vendler-1957]), the
[iatridou-anagnostopoulou-izvorski-2001] durative or inclusive classification, and the polarity
and licensing requirements. Paper-specific apparatus, such as [rouillard-2026]'s labels or the
domain-widening profile of [iatridou-zeijlstra-2021], lives in the study that uses it.

## References

* [iatridou-anagnostopoulou-izvorski-2001]
* [vendler-1957]
* [zwarts-1998]
-/

namespace English.DurationAdverbials

open Aspect
open Tense.TemporalAdverbials (AdverbialType)
open Polarity

/-- The sub-classes of duration adverbial: measuring a telic event from onset to telos, measuring
an atelic event, a deictic offset into the past, and the gap since the last witnessing event under
negation and the perfect. -/
inductive DurationKind where
  | telicCompletion
  | atelicDurative
  | pastOffset
  | npiGap
  deriving DecidableEq, Repr, Inhabited

/-- A duration adverbial. -/
structure DurationExprEntry where
  /-- The surface form. -/
  form : String
  /-- The sub-class. -/
  kind : DurationKind
  /-- Whether the adverbial follows its measure phrase, as *ago* does. -/
  isPostposition : Prop := False
  /-- The aspectual class the adverbial selects at the VP it modifies, if any. -/
  vendlerSelection : Option Telicity := none
  /-- The [iatridou-anagnostopoulou-izvorski-2001] classification: durative adverbials pin the
  left boundary of the perfect time span, inclusive ones leave it free. -/
  iaiClassification : Option AdverbialType := none
  /-- Whether the adverbial is itself a polarity-sensitive item. -/
  polaritySensitive : Prop := False
  /-- The minimum [zwarts-1998] strength of a licensing environment, for a polarity item. -/
  npiLicensor : Option Polarity.DEStrength := none
  /-- Whether the adverbial requires the perfect. -/
  requiresPerfect : Prop := False
  /-- Whether the adverbial requires negation. -/
  requiresNegation : Prop := False

/-- Telic *in three days*: *Mary wrote a paper in three days*. Selects telic VPs; inclusive. -/
def inTelic : DurationExprEntry :=
  { form := "in"
    kind := .telicCompletion
    vendlerSelection := some .telic
    iaiClassification := some .inclusive }

/-- *in years*: *Mary hasn't been sick in years*. A strong polarity item that requires the perfect
and negation; durative. The same preposition as `inTelic`, told apart by position and licensing
environment. -/
def inGap : DurationExprEntry :=
  { form := "in"
    kind := .npiGap
    iaiClassification := some .durative
    polaritySensitive := True
    npiLicensor := some .antiAdditive
    requiresPerfect := True
    requiresNegation := True }

/-- *for three hours*: *Mary was sick for three hours*. Selects atelic VPs; durative with the
perfect. -/
def forDur : DurationExprEntry :=
  { form := "for"
    kind := .atelicDurative
    vendlerSelection := some .atelic
    iaiClassification := some .durative }

/-- *three days ago*, the postposition locating an event a measured duration before the utterance
time. -/
def ago : DurationExprEntry :=
  { form := "ago"
    kind := .pastOffset
    isPostposition := True }

end English.DurationAdverbials
