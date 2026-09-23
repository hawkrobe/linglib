module

public import Linglib.Semantics.Tense.Connective

/-!
# German temporal connectives

Lexical entries for the German *until* words of [karttunen-1974]'s chart (37): the durative *bis*,
which has no punctual negative-polarity use with a phrase (the paper's footnote records an
incipient one before a clause), and *erst* 'only then', the positive polarity item that carries the
punctual *until*'s presupposition of lateness (the paper's (38)). Dutch *tot* and *pas* pattern the
same way ([giannakidou-2002]).

## References

* [karttunen-1974]
* [giannakidou-2002]
-/

@[expose] public section

namespace German.TemporalConnectives

open Tense

/-- *bis*, the durative 'until': *die Prinzessin schlief bis 9 Uhr* 'the princess slept until
nine'. -/
def bis : Connective := { form := "bis", relation := .until_ }

/-- *erst* 'only then', the punctual 'until' of a positive clause: *die Prinzessin wachte erst um
9 Uhr auf* 'the princess did not wake up until nine', which entails a waking at nine and does not
combine with negation. -/
def erst : Connective where
  form := "erst"
  relation := .until_
  punctual := True

end German.TemporalConnectives
