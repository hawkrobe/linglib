import Linglib.Syntax.Category.Verb.Defs
import Linglib.Semantics.Root.Defs

/-! # Verb entry — lookup and root

The entry-level readers of a verb: lookup by citation form and sense and the root's
content. The semantic classifications of an
entry live with their theories, each under the `Verb` namespace: factivity and trigger status
in `Semantics/Presupposition/Verb.lean`, the attitude in `Semantics/Attitudes/Verb.lean`,
causatives in `Semantics/Causation/Verb.lean`, and unaccusativity in
`Semantics/ArgumentStructure/Unaccusativity.lean`.

## References

* [spalek-mcnally-2026]
-/

open ArgumentStructure

namespace Verb

/-- The verb's within-class root content ([spalek-mcnally-2026]). -/
def rootContent (v : Verb) : Semantics.Root.Content := v.root.content

/-- The entry with the given citation form and sense, if the list has one. -/
def find? (verbs : List Verb) (form : String) (tag : SenseTag := .default) : Option Verb :=
  verbs.find? fun v ↦ v.form == form && v.senseTag == tag

end Verb
