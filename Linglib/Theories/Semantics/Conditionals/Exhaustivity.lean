import Mathlib.Data.Set.Basic
import Linglib.Theories.Semantics.Exhaustification.Operators.Basic

/-!
# Conditional Perfection via Answer-Level Exhaustification
@cite{cornulier-1983} @cite{evcen-bale-barner-2026} @cite{groenendijk-stokhof-1984} @cite{von-fintel-2001} @cite{geis-zwicky-1971}

Formalizes the connection between conditional perfection and speech-act level
exhaustification, following @cite{von-fintel-2001} "Conditional strengthening."

## Key Insight

Propositional-level exhaustification of the material conditional does NOT yield
perfection: `EXH(¬A∨C, {¬B∨C}) = (¬A∨C) ∧ B ∧ ¬C` — a specific world, not
`¬A→¬C`. Instead, conditional perfection arises from **answer-level**
exhaustification: the answer "A causes C" is exhaustified against the
alternative "B causes C," yielding "only A causes C." Combined with a coverage
assumption (every C-event has some trigger), this entails `¬A→¬C`.

This is @cite{von-fintel-2001}'s reconstruction of @cite{cornulier-1983}: when the QUD
asks for sufficient conditions for C (antecedent-focus), the conditional answer
triggers exhaustification over alternative antecedents. @cite{evcen-bale-barner-2026} experimentally validate this prediction.

-/

namespace Semantics.Conditionals.Exhaustivity

open Exhaustification

/-! ### Answer-level alternatives

A conditional perfection scenario is parameterized by a family of potential
triggers (antecedents) `causes : ι → Set W` saying which worlds each trigger
is active at, plus a salience filter `triggers : Set ι` recording which
triggers are contextually available. The key QUD is "which trigger causes
C?" and the answer "trigger t causes C" is the proposition `causes t`. Its
alternatives are `causes t'` for each other salient `t'`.

This models @cite{von-fintel-2001}'s analysis: the relevant alternatives
are not propositional alternatives to the conditional, but alternative
*answers* to the question "under which conditions does C hold?" -/

/-- The set of alternative answers competing with "trigger `t` causes C":
`{causes t' | t' ∈ triggers, t' ≠ t}`. The answer for `t` itself is
excluded — these are the answers that compete with it under exhaustification. -/
def answerAlternatives {ι W : Type*} (causes : ι → Set W) (triggers : Set ι)
    (t : ι) : Set (Set W) :=
  causes '' (triggers \ {t})

@[simp] theorem mem_answerAlternatives {ι W : Type*}
    {causes : ι → Set W} {triggers : Set ι} {t : ι} {p : Set W} :
    p ∈ answerAlternatives causes triggers t ↔
      ∃ t' ∈ triggers, t' ≠ t ∧ causes t' = p := by
  simp only [answerAlternatives, Set.mem_image, Set.mem_diff,
             Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨t', ⟨ht'_mem, ht'_ne⟩, heq⟩; exact ⟨t', ht'_mem, ht'_ne, heq⟩
  · rintro ⟨t', ht'_mem, ht'_ne, heq⟩; exact ⟨t', ⟨ht'_mem, ht'_ne⟩, heq⟩

/-! ### Connection to `exhIE` -/

/-- The exhaustified answer: assert "trigger `t` causes C" and innocently
exclude all alternative triggers.

This is `exhIE` from @cite{spector-2016} applied at the **answer level** rather
than the propositional level — the key move that makes exhaustification yield
perfection rather than a contradictory specific world.

At the propositional level, `EXH(¬A∨C, {¬B∨C})` gives `A ∧ B ∧ ¬C`.
At the answer level, `EXH("A causes C", {"B causes C"})` gives
"A causes C and B does not cause C" — which with coverage yields perfection. -/
def exhaustifiedAnswer {ι W : Type*} (causes : ι → Set W) (triggers : Set ι)
    (t : ι) : Set W :=
  exhIE (answerAlternatives causes triggers t) (causes t)

/-! ### General perfection theorem -/

/-- **Conditional perfection from exclusion and coverage.**

If:
- trigger `t` requires precondition `p` (t-worlds are p-worlds),
- all other triggers are excluded (exhaustification),
- every C-event has some trigger (coverage/closure),

then `¬p → ¬C`.

This is the core logical step underlying @cite{von-fintel-2001}'s analysis:
exhaustification provides exclusion (only t causes C), the QUD-driven
coverage assumption closes the gap to perfection (every C has a cause,
the only cause requires p, so ¬p → ¬C).

The proof is purely structural (no `sorry`, no `native_decide`). -/
theorem perfection_from_exclusion_and_coverage
    {ι W : Type*}
    (causes : ι → Set W) (triggers : Set ι)
    (t : ι)
    (p C : Set W)
    (h_t_requires_p : ∀ w, causes t w → p w)
    (h_exclusion : ∀ t' ∈ triggers, t' ≠ t → ∀ w, ¬causes t' w)
    (h_coverage : ∀ w, C w → ∃ t' ∈ triggers, causes t' w)
    (w : W) (hnp : ¬p w) : ¬C w := by
  intro hC
  obtain ⟨t', ht'_mem, ht'_causes⟩ := h_coverage w hC
  have hne : t' ≠ t := by
    intro heq; subst heq
    exact hnp (h_t_requires_p w ht'_causes)
  exact h_exclusion t' ht'_mem hne w ht'_causes

/-! ### Connecting exhaustification to perfection -/

/-- **Exhaustification excludes innocently excludable alternatives.**

If the exhaustified answer holds at world `w` and alternative trigger `t'`
is innocently excludable (its negation belongs to every MC-set), then
`t'` does not cause C at `w`.

This is the key connecting lemma: it bridges `exhIE` to the
exclusion hypothesis in `perfection_from_exclusion_and_coverage`. Without it,
`exhaustifiedAnswer` and the perfection theorem are disconnected definitions. -/
theorem exhaustifiedAnswer_excludes
    {ι W : Type*} (causes : ι → Set W) (triggers : Set ι)
    (t t' : ι) (w : W)
    (h_exh : exhaustifiedAnswer causes triggers t w)
    (h_ie : IsInnocentlyExcludable
              (answerAlternatives causes triggers t) (causes t) (causes t'))
    : ¬causes t' w :=
  h_exh _ h_ie.2

/-- **Full prediction chain: exhaustification → perfection.**

This is the genuine dependency chain from theory to prediction:

1. `exhaustifiedAnswer causes triggers t w` holds (speaker asserts under
   antecedent-focus QUD)
2. All alternative triggers are innocently excludable (`h_all_ie`)
3. Every C-event has some trigger (`h_coverage`)
4. Trigger `t` requires precondition `p` (`h_t_requires_p`)
5. Therefore: `¬p w → ¬C w`

Steps 1–2 yield local exclusion at `w` (via `exhaustifiedAnswer_excludes`).
Step 3 is the coverage/closure assumption driven by the QUD.
The conclusion follows by `perfection_from_exclusion_and_coverage`.

This theorem closes the gap between the exhaustification mechanism (`exhIE`)
and the perfection result. Without it, the theory has two disconnected pieces:
the definition of exhaustified answers and the perfection theorem, with no
proof that the former provides the exclusion the latter requires. -/
theorem exhaustification_yields_perfection
    {ι W : Type*} (causes : ι → Set W) (triggers : Set ι)
    (t : ι) (p C : Set W) (w : W)
    (h_t_requires_p : ∀ w, causes t w → p w)
    (h_all_ie : ∀ t' ∈ triggers, t' ≠ t →
      IsInnocentlyExcludable
        (answerAlternatives causes triggers t) (causes t) (causes t'))
    (h_coverage : C w → ∃ t' ∈ triggers, causes t' w)
    (h_exh : exhaustifiedAnswer causes triggers t w)
    (hnp : ¬p w) : ¬C w := by
  intro hC
  obtain ⟨t', ht'_mem, ht'_causes⟩ := h_coverage hC
  by_cases hne : t' = t
  · subst hne; exact hnp (h_t_requires_p w ht'_causes)
  · exact absurd ht'_causes
      (exhaustifiedAnswer_excludes causes triggers t t' w h_exh
        (h_all_ie t' ht'_mem hne))

end Semantics.Conditionals.Exhaustivity
