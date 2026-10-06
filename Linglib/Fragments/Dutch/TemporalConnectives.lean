module

public import Linglib.Semantics.Tense.Connective

/-!
# Dutch temporal connectives

Lexical entries for the Dutch *until* words: the durative *tot*, which does not combine with
negation, and *pas* 'only then', the positive polarity item that takes the place of a punctual
*until* and contributes *not before* without a negation, by Giannakidou's (47). Karttunen treats
the parallel German *erst* alike.

## References

* [giannakidou-2002]
* [karttunen-1974]
-/

@[expose] public section

namespace Dutch.TemporalConnectives

open Tense

/-- *tot* is the durative 'until', *Marie wachtte tot 9 uur* 'Marie waited until nine'. -/
def tot : Connective := { form := "tot", relation := .until_ }

/-- *pas* 'only then' is the punctual 'until' of a positive clause, *Marie kwam pas om 9 uur aan*
'Marie only arrived at nine'. -/
def pas : Connective := { form := "pas", relation := .until_ }

end Dutch.TemporalConnectives
