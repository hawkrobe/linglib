import Linglib.Semantics.Tense.Connective

/-!
# Dutch temporal connectives

Lexical entries for the Dutch *until* words: the durative *tot*, which does not combine with
negation, and *pas* 'only then', the positive polarity item that takes the place of a punctual
*until* and contributes *not before* without a negation ([giannakidou-2002], the paper's (47);
[karttunen-1974] on the parallel German *erst*).

## References

* [giannakidou-2002]
* [karttunen-1974]
-/

namespace Dutch.TemporalConnectives

open Tense

/-- *tot*, the durative 'until': *Marie wachtte tot 9 uur* 'Marie waited until nine'. -/
def tot : Connective := { form := "tot", relation := .until_ }

/-- *pas* 'only then', the punctual 'until' of a positive clause: *Marie kwam pas om 9 uur aan*
'Marie only arrived at nine'. -/
def pas : Connective where
  form := "pas"
  relation := .until_
  punctual := True

end Dutch.TemporalConnectives
