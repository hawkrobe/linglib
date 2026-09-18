import Linglib.Semantics.Tense.Perspective

/-!
# Hebrew temporal deictic adverbs

Modern Hebrew *az* 'then' is the distal temporal deictic adverb, referring to a past or future
time away from the deictic centre. The examples are those of [tsilia-zhao-2026].

## References

* [tsilia-zhao-2026]
-/

namespace Hebrew.TemporalDeictic

open Semantics

open Tense

/-- *az* (אז) 'then', a time before or after the deictic centre: *lifney alpayim šana, Yosef
xašav še Miriam ahava oto az* 'Two thousand years ago Yosef believed that Miriam loved him
then'. -/
def az : DeicticAdverb := { form := "az", cell := ⟦present⟧ᶜ }

end Hebrew.TemporalDeictic
