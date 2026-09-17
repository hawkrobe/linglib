import Linglib.Syntax.Category.Verb.Defs
import Linglib.Semantics.Root.Defs

/-! # Verb entry — lookup and root

The entry-level readers of a verb: lookup by citation form and sense, the root's content, and
the argument profiles with their Levin-class fallback. The semantic classifications of an
entry live with their theories, each under the `Verb` namespace: factivity and trigger status
in `Semantics/Presupposition/Verb.lean`, the attitude in `Semantics/Attitudes/Verb.lean`,
causatives in `Semantics/Causation/Verb.lean`, and unaccusativity in
`Semantics/ArgumentStructure/Verb.lean`.

## References

* [spalek-mcnally-2026]
* [levin-1993]
* [dowty-1991]
-/

open ArgumentStructure

namespace Verb

/-- The subject's entailment profile, the entry's own or else the one its Levin classes agree
on ([levin-1993], [dowty-1991]). -/
def subjectProfile? (v : Verb) : Option EntailmentProfile :=
  v.subjectEntailments <|> LevinClass.commonProfile LevinClass.subjectProfile v.levinClasses

/-- The object's entailment profile, the entry's own or else the one its Levin classes agree
on. -/
def objectProfile? (v : Verb) : Option EntailmentProfile :=
  v.objectEntailments <|> LevinClass.commonProfile LevinClass.objectProfile v.levinClasses

/-- The verb's within-class root content ([spalek-mcnally-2026]). -/
def rootContent (v : Verb) : Semantics.Root.Content := v.root.content

/-- The entry with the given citation form and sense, if the list has one. -/
def find? (verbs : List Verb) (form : String) (tag : SenseTag := .default) : Option Verb :=
  verbs.find? fun v ↦ v.form == form && v.senseTag == tag

end Verb
