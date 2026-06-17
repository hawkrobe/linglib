import Linglib.Semantics.Tense.SOT.Decomposition
import Linglib.Fragments.English.Tense
import Linglib.Fragments.German.Tense
import Linglib.Data.Examples.Schema
import Linglib.Semantics.Tense.Pronoun
import Linglib.Data.Examples.Kratzer1998

/-!
# [kratzer-1998]: More Structural Analogies between Pronouns and Tenses
[kratzer-1998] [partee-1973] [klein-1994] [abusch-1988]
[abusch-1997] [ogihara-1989]

[kratzer-1998]'s SALT VIII paper extends [partee-1973]'s
tense–pronoun analogy in three directions: an aspect-based decomposition
of English simple past, SOT deletion via zero tenses, and zero forms with
locality constraints. The substrate machinery (deletion mechanism +
Kratzer-named lexical entries used by Fragments) is at
`Semantics/Tense/SOT/Decomposition.lean`; this study file
collects the paper-anchored cross-references and the empirical chain
theorems connecting Fragments → Theory → Data → Empirical judgments.

## Architectural note

The `kratzerEnglishPast` / `kratzerGermanPreterit` / `kratzerZeroTense`
lexical entries live at the Theories layer
(`Tense/SOT/Decomposition.lean`) because
`Fragments/{English,German,Italian}/Tense.lean` consume them via the
`Fragments → Theories` import direction. The "Fragments import
Theories, never Studies" layering discipline forces the substrate
placement; this Studies file collects the paper-anchored cross-paper
claims and bridge theorems that don't need to be Fragment-visible.

## Section 7 decomposition (English simple past = perfect + present)

The cornerstone empirical contrast (`[kratzer-1998]` Section 7,
ex (40), p. 16) is the English/German out-of-the-blue diagnostic:
English simple past is acceptable as a deictic past tense (`(40a)`
"Who built this Church? Borromini built this church."); the German
simple past (Präteritum) is deviant in the same context (`(40b)`);
the German present perfect (Perfekt) fills the deictic slot
(`(40c)`). Kratzer concludes: "Since the simple past in English can
be used in out of the blue utterances describing past events, it
must be a way of spelling out perfect aspect and present tense
together" (p. 18).

The empirical data live as `Examples.ex40a`/`ex40b`/`ex40c` in the
generated block below, with `Examples.all` exposing the full Kratzer98
example list. The chain theorems below verify that the Fragment entries'
`canBeDeictic` predictions agree with each example's empirical
judgment.

-/

open Time

namespace Kratzer1998

open Tense.SOT.Decomposition
open Tense
open Data.Examples (LinguisticExample)

/-! ### Fragment ↔ Example agreement: deictic-vs-anaphoric tense

The chain Fragment → Example replaces the previous Fragment → frame →
datum chain (which was a six-conjunct `rfl` tower over hand-stipulated
Reichenbach integers). The empirical anchor is now the
`LinguisticExample.judgment` field of the corresponding Kratzer98
numbered example, which is verifiable from the paper itself.

Predictions tested:
- `kratzerSimplePast.canBeDeictic = true` ↔ `Examples.ex40a.judgment = .acceptable`
  (English simple past, out of the blue).
- `kratzerPreterit.canBeDeictic = false` ↔ `Examples.ex40b.judgment = .ungrammatical`
  (German Präteritum, out of the blue).
- `kratzerPerfekt.canBeDeictic = true` ↔ `Examples.ex40c.judgment = .acceptable`
  (German Perfekt, out of the blue). -/

section KratzerChain

open English.Tense (kratzerSimplePast)
open German.Tense (kratzerPreterit kratzerPerfekt)
open Features (Judgment)

/-- **English simple past = perfect + present.** Per Kratzer §7
    (p. 18), the English simple past decomposes as PRESENT-tense head
    over PERFECT aspect. The Fragment-level encoding (`constraint =
    .present` + `hasPerfect = true`) is verified directly in
    `Fragments/English/Tense.lean`; this theorem isolates the bridge
    claim that needs both Fragment-side and Example-side facts: the
    Fragment encoding predicts deictic usability, and Kratzer's
    out-of-the-blue example (40a) ("Who built this Church?…") is
    `.acceptable`. -/
theorem english_simple_past_chain :
    kratzerSimplePast.tensePronoun.constraint = Tense.present ∧
    kratzerSimplePast.hasPerfect = true ∧
    Examples.ex40a.judgment = Judgment.acceptable :=
  ⟨rfl, rfl, rfl⟩

/-- **German Preterit = genuine past pronoun.** Per Kratzer §7
    (ex (40b), p. 16): the German Präteritum requires a contextually
    salient past time, behaving like an anaphoric pronoun. The Fragment
    encodes this as `kratzerPreterit.tensePronoun.constraint = .past`
    + `hasPerfect = false`; the empirical anchor is `Examples.ex40b`
    (deviant out of the blue, star per Kratzer). -/
theorem german_preterit_chain :
    kratzerPreterit.tensePronoun.constraint = Tense.past ∧
    kratzerPreterit.hasPerfect = false ∧
    Examples.ex40b.judgment = Judgment.ungrammatical :=
  ⟨rfl, rfl, rfl⟩

/-- **German Perfekt = perfect + present** (same decomposition as
    English simple past). Per Kratzer §7 (ex (40c), p. 16): the Perfekt
    fills the deictic-past slot that the Preterit cannot. The chain
    asserts BOTH the empirical agreement on (40c) AND the cross-Fragment
    parallelism (Perfekt's tense head + perfect-aspect coincide with
    `kratzerSimplePast`'s), which is the substantive content of "same
    decomposition." -/
theorem german_perfekt_chain :
    kratzerPerfekt.tensePronoun.constraint = Tense.present ∧
    kratzerPerfekt.hasPerfect = true ∧
    Examples.ex40c.judgment = Judgment.acceptable ∧
    kratzerPerfekt.tensePronoun.constraint =
      kratzerSimplePast.tensePronoun.constraint ∧
    kratzerPerfekt.hasPerfect = kratzerSimplePast.hasPerfect :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Zero tense surface properties.** Per Kratzer §4 (p. 10–11):
    English has two indexical tenses (present, past) and a zero tense.
    The substrate lemmas `zero_tense_is_present` and `zero_tense_overtness`
    in `Tense/SOT/Decomposition.lean` carry the underlying claims; this
    theorem just binds them locally for cross-reference. -/
theorem zero_tense_chain :
    (kratzerZeroTense 1).constraint = Tense.present ∧
    Overtness.fromBinding (kratzerZeroTense 1).mode true = .zero :=
  ⟨zero_tense_is_present 1, zero_tense_overtness 1⟩

end KratzerChain

/-! ### Agreement with Ogihara on the simultaneous cell -/

/-- Kratzer's SOT deletion and [ogihara-1996]'s zero-tense binding build
    the **same embedded frame**: deletion yields exactly the
    `simultaneousFrame` whose embedded event time is the matrix event time,
    and that frame is PRESENT relative to the shifted perspective. The two
    accounts provably agree on the core past-under-past simultaneous cell;
    they differ in mechanism (deletion of a genuine PAST vs a bound zero
    PRESENT — see `Tense.SOT.Ambiguity.PastReading` for the typed
    mechanism-level divergence). -/
theorem deletion_agrees_with_zero_tense_binding {Time : Type*}
    (m : ReichenbachFrame Time) :
    applyDeletion m = Tense.simultaneousFrame m m.eventTime ∧
    (applyDeletion m).isPresent :=
  ⟨applyDeletion_eq_simultaneousFrame m, kratzer_derives_simultaneous m⟩

/-! ### Cross-paper bridge theorems (Phase F)

The contrast theorems with Ogihara, Sharvit, von Stechow, Klecha are
intentionally not yet landed; substrate is ready (`applyDeletion`,
`sotDeletionApplicable`, the kratzer-named lexical entries are all
exported from `Tense/SOT/Decomposition.lean`). -/

end Kratzer1998
