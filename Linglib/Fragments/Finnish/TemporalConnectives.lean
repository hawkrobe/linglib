import Linglib.Semantics.Tense.Connective

/-!
# Finnish temporal connectives

Lexical entries for the Finnish temporal connectives: *ennen* and *ennen kuin* 'before',
*jälkeen* 'after', *kun* 'when' with its compounds *sillä aikaa kun* 'while', *aina kun*
'whenever' and *heti kun* 'as soon as', the durative *kunnes* and *saakka* 'until', and *vasta*
'only then'. Finnish separates [karttunen-1974]'s two *until*s and, uniquely in the paper's
sample, has both polarities of the punctual one: the negated *ennen kuin*, whose form is that of
*before*, and the positive polarity item *vasta*, the twin of German *erst* (the paper's (37) and
(39)).

## References

* [heinamaki-1974]
* [karttunen-1974]
-/

namespace Finnish.TemporalConnectives

open Tense

/-- *ennen* 'before', the preposition. -/
def ennen : Connective := { form := "ennen", relation := .before }

/-- *ennen kuin* 'before', literally 'before than', the conjunction; negated, it is the punctual
*until* of *prinsessa ei herännyt ennen kuin yhdeksältä* 'the princess did not wake up until
nine'. -/
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

/-- *kunnes*, the durative 'until', the conjunction. -/
def kunnes : Connective := { form := "kunnes", relation := .until_ }

/-- *saakka*, the durative 'until', the postposition. -/
def saakka : Connective := { form := "saakka", relation := .until_ }

/-- *vasta* 'only then', the punctual 'until' of a positive clause: *prinsessa heräsi vasta
yhdeksältä* 'the princess did not wake up until nine', with the same commitment to a waking at
nine and the same suggestion of lateness as the negated *ennen kuin*. -/
def vasta : Connective where
  form := "vasta"
  relation := .until_
  punctual := True

end Finnish.TemporalConnectives
