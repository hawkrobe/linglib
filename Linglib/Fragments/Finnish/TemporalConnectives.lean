import Linglib.Semantics.Tense.Connective

/-!
# Finnish temporal connectives

Lexical entries for the Finnish temporal connectives: *ennen* and *ennen kuin* 'before',
*jälkeen* 'after', *kun* 'when' with its compounds *sillä aikaa kun* 'while', *aina kun*
'whenever' and *heti kun* 'as soon as', and the durative *kunnes* 'until'. Finnish separates
[karttunen-1974]'s two *until*s: *kunnes* is the durative one, and the punctual one is the
negated *ennen kuin*, whose form is that of *before*.

## References

* [heinamaki-1974]
* [karttunen-1974]
-/

namespace Finnish.TemporalConnectives

open Tense

/-- *ennen* 'before', the preposition. -/
def ennen : Connective := { form := "ennen", relation := .before }

/-- *ennen kuin* 'before', literally 'before than', the conjunction; negated, it is the punctual
*until*. -/
def ennenKuin : Connective := { form := "ennen kuin", relation := .before }

/-- *jälkeen* 'after'. -/
def jälkeen : Connective := { form := "jälkeen", relation := .after }

/-- *kun* 'when'. -/
def kun : Connective := { form := "kun", relation := .when_ }

/-- *sillä aikaa kun* 'while', literally 'in that time when'. -/
def silläAikaaKun : Connective := { form := "sillä aikaa kun", relation := .while_ }

/-- *aina kun* 'whenever', literally 'always when'. -/
def ainaKun : Connective := { form := "aina kun", relation := .whenever }

/-- *heti kun* 'as soon as', literally 'immediately when'. -/
def hetiKun : Connective := { form := "heti kun", relation := .after }

/-- *kunnes*, the durative 'until'. -/
def kunnes : Connective := { form := "kunnes", relation := .until_ }

end Finnish.TemporalConnectives
