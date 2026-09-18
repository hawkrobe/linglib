import Linglib.Syntax.Category.Verb.Tense

/-!
# English tense forms

This file lists the tense forms of English. The English verb has two synthetic tense forms, the
simple present and the simple past. The progressive forms put the present participle under
*be*, as in *is building* and *was building*, and the perfect forms put the past participle
under *have*, as in *has built* and *had built*.

## References

* [kratzer-1998]
-/

namespace English

/-- English has the simple, the progressive and the perfect forms of the present and of the
past. -/
def tenseForms : List Tense.Form :=
  [.simplePresent, .simplePast, .presentProgressive, .pastProgressive, .presentPerfect,
    .pastPerfect]

end English
