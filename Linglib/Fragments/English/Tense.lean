import Linglib.Syntax.Category.Verb.Tense

/-!
# English tense forms

This file lists the tense forms of English. The English verb has two synthetic tense forms, the
simple present and the simple past. The progressive forms put the present participle under *be*,
as in *is building* and *was building*, and the perfect forms put the past participle under
*have*, as in *has built* and *had built*.

## References

* [kratzer-1998]
-/

namespace English.Tense

/-- The simple present is the synthetic present, as *builds*. -/
def simplePresent : Tense.Form := { name := "simple present", finite := .Pres }

/-- The simple past is the synthetic past, as *built*. -/
def simplePast : Tense.Form := { name := "simple past", finite := .Past }

/-- The present progressive puts the present participle under present *be*, as *is building*. -/
def presentProgressive : Tense.Form :=
  { name := "present progressive", finite := .Pres, nonfinite := [.presentParticiple] }

/-- The past progressive puts the present participle under past *be*, as *was building*. -/
def pastProgressive : Tense.Form :=
  { name := "past progressive", finite := .Past, nonfinite := [.presentParticiple] }

/-- The present perfect puts the past participle under present *have*, as *has built*. -/
def presentPerfect : Tense.Form :=
  { name := "present perfect", finite := .Pres, nonfinite := [.pastParticiple] }

/-- The past perfect puts the past participle under past *have*, as *had built*. -/
def pastPerfect : Tense.Form :=
  { name := "past perfect", finite := .Past, nonfinite := [.pastParticiple] }

/-- English has these tense forms. -/
def forms : List Tense.Form :=
  [simplePresent, simplePast, presentProgressive, pastProgressive, presentPerfect, pastPerfect]

end English.Tense
