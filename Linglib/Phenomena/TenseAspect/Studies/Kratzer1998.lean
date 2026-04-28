import Linglib.Theories.Semantics.Tense.SOT.Decomposition

/-!
# @cite{kratzer-1998}: More Structural Analogies between Pronouns and Tenses
@cite{kratzer-1998} @cite{partee-1973} @cite{klein-1994}

@cite{kratzer-1998}'s SALT VIII paper extends @cite{partee-1973}'s
tense–pronoun analogy in three directions: aspect-decomposition of
English simple past, SOT deletion, and zero forms with locality. The
substrate machinery is at `Theories/Semantics/Tense/SOT/Decomposition.lean`
(deletion mechanism + Kratzer-named lexical entries used by Fragments);
this study file is the paper-anchored cross-reference for Phase F
bridge theorems (Kratzer ↔ Ogihara on past-tense ambiguity, Kratzer ↔
Sharvit on simultaneous mechanism, Kratzer ↔ Klecha on the modal-base
explanation).

## Architectural note

The `kratzerEnglishPast` / `kratzerGermanPreterit` / `kratzerZeroTense`
lexical entries live at the Theories layer (Decomposition.lean)
because `Fragments/{English,German,Italian}/Tense.lean` consume them
via the `Fragments → Theories` import direction. CLAUDE.md's
"Fragments imports Theories, not Phenomena" discipline forces the
substrate placement; this Studies file collects the paper-anchored
cross-paper claims and (in Phase F) bridge theorems that don't need to
be Fragment-visible.

-/

namespace Phenomena.TenseAspect.Studies.Kratzer1998

open Semantics.Tense.SOT.Decomposition

/-! ### Cross-paper bridge theorems (Phase F)

The contrast theorems with Ogihara, Sharvit, von Stechow, Klecha are
intentionally not yet landed; substrate is ready (`applyDeletion`,
`sotDeletionApplicable`, the kratzer-named lexical entries are all
exported from `Tense/SOT/Decomposition.lean`). The current scope is
the file rename + paper-anchor docstring. -/

end Phenomena.TenseAspect.Studies.Kratzer1998
