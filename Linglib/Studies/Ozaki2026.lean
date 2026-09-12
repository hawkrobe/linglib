import Linglib.Data.Examples.Ozaki2026
import Linglib.Syntax.Case.Dependent
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Fragments.Japanese.Predicates
import Linglib.Fragments.Japanese.Passive

/-!
# Ozaki (2026): Japanese Accusative/Ablative Alternation Verbs Are Unaccusative

This file formalizes the argument of [ozaki-2026] that the Japanese verbs of departure whose
source argument is marked either accusative *o* or ablative *kara*, *hanareru* 'leave' and
*deru* 'exit', project one dyadic unaccusative structure under both markings. The source is
an argument whatever its marking, since it elides under an overt adjunct, the argumenthood
diagnostic of [funakoshi-2016], and scrambles long-distance, that of [saito-1985]; and the
verbs project no thematic Voice ([kratzer-1996]) under either marking, since their passive
is the indirect passive, the direct passive with *niyotte* being ungrammatical, and the
accusative wh-adjunct *nani-o* 'why' of [kurafuji-1997] is unavailable, as with
unaccusatives. Each diagnostic returns the same verdict for both markings (`verdict`,
`judgment_eq_verdict`, `diagnostics_both_markings`). The alternation is then a matter of case
assignment: *kara* is a lexical ablative assigned by an optional postposition, and *o* is the
dependent accusative assigned to a caseless noun phrase c-commanded by another, which the
ablative bleeds (`acc_variant`, `abl_variant`, `accusative_without_voice`).

## Implementation notes

The examples are the generated rows of `Data/Examples/Ozaki2026`, the (9), (13), and (26)
pairs split into an accusative and an ablative row. The case algorithm is the one-domain
dependent-case assignment of `Syntax/Case/Dependent`, and the absence of thematic Voice is the
non-thematic Voice head of `Syntax/Minimalist/Verbal/Voice`, which the Japanese Fragment records
for both verbs and from which it derives their unaccusativity.

## References

* [ozaki-2026]
* [funakoshi-2016]
* [saito-1985]
* [kurafuji-1997]
* [kratzer-1996]
-/

namespace Ozaki2026

open Data.Examples Ozaki2026.Examples Case Minimalist.Voice

/-! ### The diagnostics -/

/-- The diagnostic an example applies. -/
def diagnostic (e : LinguisticExample) : Option String := e.feature? "diagnostic"

/-- The marking of the source in an example. -/
def marking (e : LinguisticExample) : Option String := e.feature? "marking"

/-- The verdict the argument assigns to each diagnostic: the alternation, the argumenthood
diagnostics, and the indirect passive succeed, the direct passive and the wh-adjunct fail. -/
def verdict : Option String → Judgment
  | some "direct_passive" | some "nani_o" => .unacceptable
  | _ => .acceptable

/-- Every example's judgment is its diagnostic's verdict: the marking of the source plays no
role. -/
theorem judgment_eq_verdict : ∀ e ∈ Examples.all, e.judgment = verdict (diagnostic e) := by decide

/-- Both markings are attested with each marking-sensitive diagnostic: the source elides and
scrambles, and the wh-adjunct is out, under accusative and under ablative alike. -/
theorem diagnostics_both_markings :
    ∀ m ∈ ["acc", "abl"],
      (∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "ellipsis" ∧
        e.judgment = .acceptable) ∧
      (∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "scrambling" ∧
        e.judgment = .acceptable) ∧
      ∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "nani_o" ∧
        e.judgment = .unacceptable := by
  decide

/-- The Fragment records both verbs with non-thematic Voice, from which their unaccusativity
is derived, and as non-passivizable. -/
theorem alternation_verbs_unaccusative :
    ∀ v ∈ [Japanese.Predicates.hanareru, Japanese.Predicates.deru],
      v.voiceType = some .nonThematic ∧ v.toVerb.derivedUnaccusative = true ∧
        v.passivizable = false := by
  decide

/-- The direct passive requires thematic Voice, which the non-thematic head does not
provide: (20) is out. -/
theorem direct_passive_requires_voice :
    Japanese.Passive.PassiveType.requiresThematicVoice .direct = true ∧
      ¬ anticausative.AssignsTheta :=
  ⟨rfl, by decide⟩

/-! ### Case assignment (§3) -/

/-- The accusative variant (28): leaver and source are caseless noun phrases in the one
Spell-Out domain, the leaver c-commanding the source. -/
def accVariant : List NP := [⟨"leaver", none⟩, ⟨"source", none⟩]

/-- The ablative variant (29): the postposition has valued the source ablative. -/
def ablVariant : List NP := [⟨"leaver", none⟩, ⟨"source", some .abl⟩]

/-- In the accusative variant the source receives dependent accusative by (27) and the
leaver unmarked nominative. -/
theorem acc_variant :
    getCaseOf "source" (assignCases .accusative accVariant) = some .acc ∧
      getMechanismOf "source" (assignCases .accusative accVariant) = some .dependent ∧
      getCaseOf "leaver" (assignCases .accusative accVariant) = some .nom ∧
      getMechanismOf "leaver" (assignCases .accusative accVariant) = some .unmarked := by
  decide

/-- In the ablative variant the lexical ablative bleeds dependent accusative, and the leaver
is unaffected. -/
theorem abl_variant :
    getCaseOf "source" (assignCases .accusative ablVariant) = some .abl ∧
      getMechanismOf "source" (assignCases .accusative ablVariant) = some .lexical ∧
      getCaseOf "leaver" (assignCases .accusative ablVariant) = some .nom ∧
      getMechanismOf "leaver" (assignCases .accusative ablVariant) = some .unmarked := by
  decide

/-- Accusative without thematic Voice: the non-thematic head assigns no θ-role, and the
source's accusative is configurational rather than assigned by a functional head. -/
theorem accusative_without_voice :
    ¬ anticausative.AssignsTheta ∧
      getMechanismOf "source" (assignCases .accusative accVariant) = some .dependent := by
  decide

end Ozaki2026
