import Linglib.Semantics.Tense.Connective

/-!
# Icelandic temporal connectives

Lexical entries for the Icelandic *until* words, which lexicalize [karttunen-1974]'s two
*until*s without overt aspect on the verb ([giannakidou-2002], the paper's (43)–(46), from
Gunnar Hansson): the durative *(þangað) til*, and *fyrr en*, literally 'earlier than', the
punctual *until* that needs the negation *ekki*.

## References

* [giannakidou-2002]
* [karttunen-1974]
-/

namespace Icelandic.TemporalConnectives

open Tense

/-- *(þangað) til*, the durative 'until': *prinsessan svaf þangað til klukkan fimm* 'the princess
slept until five'. -/
def thangadTil : Connective := { form := "þangað til", relation := .until_ }

/-- *fyrr en* 'earlier than', the punctual 'until' of a negated clause: *prinsessan kom ekki fyrr
en klukkan fimm* 'the princess did not arrive until five'. -/
def fyrrEn : Connective where
  form := "fyrr en"
  relation := .until_
  punctual := True

end Icelandic.TemporalConnectives
