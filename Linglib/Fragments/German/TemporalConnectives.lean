module

public import Linglib.Semantics.Tense.Connective

/-!
# German temporal connectives

Lexical entries for the German *until* words of Karttunen's chart (37): the durative *bis*, which
has no punctual negative-polarity use with a phrase (his footnote records an incipient one before
a clause), and *erst* 'only then', the positive polarity item that carries the punctual *until*'s
presupposition of lateness (his (38)). Giannakidou finds Dutch *tot* and *pas* patterning the same
way.

## References

* [karttunen-1974]
* [giannakidou-2002]
-/

@[expose] public section

namespace German.TemporalConnectives

open Tense

/-- *bis* is the durative 'until', as in *die Prinzessin schlief bis 9 Uhr* 'the princess slept
until nine'. -/
def bis : Connective := { form := "bis", relation := .until_ }

/-- *erst* 'only then' is the punctual 'until' of a positive clause, as in *die Prinzessin wachte
erst um 9 Uhr auf* 'the princess did not wake up until nine', which entails a waking at nine and
does not combine with negation. -/
def erst : Connective := { form := "erst", relation := .until_ }

end German.TemporalConnectives
