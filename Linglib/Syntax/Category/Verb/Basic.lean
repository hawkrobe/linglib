module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Semantics.Root.Defs
public import Linglib.Syntax.Category.Adposition.Spatial

/-! # Verb entry — lookup and root

The entry-level readers of a verb: lookup by citation form and sense, the root's content, and
the argument profiles with their Levin-class fallback, and the predicate a verb forms with a
path phrase (`Verb.withPath`). The semantic classifications of an
entry live with their theories, each under the `Verb` namespace: factivity and trigger status
in `Semantics/Presupposition/Verb.lean`, the attitude in `Semantics/Attitudes/Verb.lean`, and
unaccusativity in `Semantics/ArgumentStructure/Unaccusativity.lean`.

## References

* [spalek-mcnally-2026]
* [levin-1993]
* [dowty-1991]
* [levin-hovav-1995]
* [zwarts-2005]
-/

@[expose] public section

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

/-! ### Path phrases -/

section withPath

variable {v : Verb} {p : Adposition.SpatialReading}

/-- The predicate a verb forms with a path phrase of reading `p`. A directional phrase that the
verb selects as a complement gives the theme's path its direction, the directed motion use of a
verb of manner of motion ([levin-hovav-1995] p. 185), and a bounded one an endpoint, which makes
the predicate telic ([zwarts-2005]). A locative phrase, and a phrase the verb does not select, an
adjunct, leave the verb as it is: *correre* 'run' has a directed motion use in Italian but
*nuotare* 'swim' has none. -/
def withPath (v : Verb) (p : Adposition.SpatialReading) : Verb :=
  if p.direction = .place ∨ ¬ v.TakesSpatial then v else
    { v with
      direction := some p.direction
      vendlerClass := if p.IsBounded then v.vendlerClass.map (·.telicize) else v.vendlerClass }

@[simp] theorem withPath_of_direction_eq_place (h : p.direction = .place) : v.withPath p = v := by
  simp [withPath, h]

@[simp] theorem withPath_of_not_takesSpatial (h : ¬ v.TakesSpatial) : v.withPath p = v := by
  simp [withPath, h]

@[simp] theorem direction_withPath (hv : v.TakesSpatial) (h : p.direction ≠ .place) :
    (v.withPath p).direction = some p.direction := by
  simp [withPath, hv, h]

@[simp] theorem vendlerClass_withPath (hv : v.TakesSpatial) (h : p.direction ≠ .place) :
    (v.withPath p).vendlerClass =
      if p.IsBounded then v.vendlerClass.map (·.telicize) else v.vendlerClass := by
  simp [withPath, hv, h]

end withPath

end Verb
