import Linglib.Fragments.English.Pronouns
import Linglib.Semantics.Reference.PronounDenotation

/-!
# Büring 2012 — pronouns as φ-presupposing variables
[buring-2012]

[buring-2012]'s handbook survey of pronoun semantics makes several claims
this file states as theorems about the *unified* pronoun denotation
(`PersonalPronoun.denote` / `PersonalPronoun.phiPresup`) applied to the English
Fragment's lexical entries (`English.Pronouns`) — not about a local
re-implementation. This is the "theory-hub denotation as study-file constraint":
the object the rest of the codebase attributes to pronouns is the object these
theorems are about.

* A pronoun denotes the assignment value `g i` — the variable lookup
  (`interpPronoun`). Free, anaphoric, and deictic uses share this selector.
* Its φ-features are *presuppositions* on the resolved referent: a feminine
  pronoun is undefined of a non-feminine referent (agreement-as-presupposition,
  not assertion).
* A *bound* pronoun has the *same* denotation as a free one — binding is
  supplied externally by an assignment update, not by a distinct lexical entry
  (Büring's §3 thesis; the continuation rendering is `Semantics.Reference.Binding`).

A fourth theorem records the [arnold-2026] contrast that motivates the
English `epicene` paradigm: *they* carries no gender presupposition, so it is
defined of a referent of any gender — exactly where *she* is undefined.

## Main results

* `she_denotes_assignment_value` — the selector is the variable lookup `g i`.
* `she_undefined_of_non_female` — the φ-feature presupposition (negative test).
* `she_bound_reading` — external binding (assignment update) returns the binder.
* `they_defined_regardless_of_gender` — epicene *they* imposes no gender presup.
-/

set_option autoImplicit false

namespace Buring2012

open English.Pronouns (she they)
open Core (Assignment)
open Core.Logic.Intensional.Variables (interpPronoun)

variable {E : Type} [PartialOrder E]
  (g : Assignment E) (i : ℕ) (spk adr : E)
  (isFemale isInanimate : E → Prop)

/-- A pronoun denotes the assignment value `g i`: its selector is the canonical
variable lookup `interpPronoun i`, by construction. Büring's assignment-lookup
denotation — the same selector for free, anaphoric, and deictic uses. -/
theorem she_denotes_assignment_value :
    (she.denote i spk adr isFemale isInanimate).selector g ⟨⟩
      = some (interpPronoun (E := E) (W := PUnit) i g) := rfl

/-- φ-features as presupposition: *she* is undefined of a non-female referent.
The feminine feature does not *assert* femaleness of `g i` — it *presupposes*
it, so the whole denotation lacks a defined value when the referent is not
female. -/
theorem she_undefined_of_non_female (scope : E → PUnit → Prop)
    (h : ¬ isFemale (g i)) :
    ¬ ((she.denote i spk adr isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ :=
  fun hp => h hp.1.2.2

/-- A bound pronoun has the same denotation as a free one: binding is the
external assignment update `Function.update g i b`, and the *unchanged* selector then
returns the binder `b`. Büring §3 — there is no separate "bound pronoun"
lexeme; the lexical entry is identical, binding lives in the assignment. -/
theorem she_bound_reading (b : E) :
    (she.denote i spk adr isFemale isInanimate).selector (Function.update g i b) ⟨⟩
      = some b := by
  simp only [PersonalPronoun.denote, interpPronoun, Function.update_self]

/-- Epicene *they* ([arnold-2026]) carries no gender presupposition: its
denotation is defined of a referent regardless of gender — the structural
correlate of *they*'s gender-neutrality, and the direct contrast with
`she_undefined_of_non_female`. -/
theorem they_defined_regardless_of_gender (scope : E → PUnit → Prop) :
    ((they.denote i spk adr isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ := by
  refine ⟨⟨trivial, trivial, trivial⟩, ?_⟩
  rfl

end Buring2012
