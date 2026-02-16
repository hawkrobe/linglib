import Linglib.Theories.Semantics.Tense.Compositional
import Linglib.Theories.Semantics.Reference.KaplanLD
import Linglib.Theories.Semantics.Intensional.Situations.Elbourne
import Linglib.Core.Intension

/-!
# Tenses and Pronouns: Partee's Structural Analogy

Formalizes Partee (1973): tenses in English exhibit the same three-way
interpretive ambiguity as pronouns — indexical, anaphoric, and bound-variable
— and share the same formal mechanisms (assignment functions, variable
lookup, lambda abstraction).

The unifying type for all five views of tense is `Core.Tense.TensePronoun`
(Abusch 1997): a variable index + a presupposed temporal constraint + a
binding mode + an eval time index (Klecha 2016). The bridges in this file —
`referential_past_decomposition`, `indexical_tense_matches_opNow`,
`toSitVarStatus` — are projections of `TensePronoun` onto specific
theoretical vocabularies.

For the full tense theory comparison (Abusch, Von Stechow, Kratzer,
Ogihara, Klecha, Deal, Sharvit, Zeijlstra, Wurmbrand), see
`Comparisons/TenseTheories.lean` and `Theories/Semantics.Intensional/Tense/`.

## The Analogy

| Mode      | Pronouns                     | Tenses                              |
|-----------|------------------------------|-------------------------------------|
| Indexical | "I" → agent of context       | present → speech time               |
| Anaphoric | "he" → salient individual    | past → salient narrative time       |
| Bound     | "his" in ∀x...his...         | tense in "whenever...is..."         |

Partee's main argument against Prior's tense-as-operator view: "I didn't
turn off the stove" with past tense does NOT mean "at SOME past time I
didn't turn off the stove" (trivially true). It means "at THAT specific
time (when I left) I didn't turn off the stove." Tenses refer; they
don't quantify.

## Structural Parallel to Variables.lean

The definitions here are the temporal counterparts of H&K (1998) entity
variable infrastructure in `Semantics.Montague.Variables`. Both are
instantiations of the generic `Core.VarAssignment` infrastructure:

| Generic (Core.VarAssignment)     | Entity (Variables.lean)    | Temporal (this file)      |
|----------------------------------|---------------------------|---------------------------|
| `VarAssignment D` (ℕ → D)       | `Assignment m` (ℕ → Ent)  | `TemporalAssignment Time` |
| `lookupVar n g = g(n)`           | `interpPronoun n g`       | `interpTense n g`         |
| `updateVar g n d`                | `Assignment.update g n x` | `updateTemporal g n t`    |
| `varLambdaAbs n body`            | `lambdaAbsG n body`       | `temporalLambdaAbs n body`|

The algebraic structure is identical: Partee's insight is that the SAME
referential mechanism operates over different domains.

## References

- Partee, B. (1973). Some structural analogies between tenses and pronouns
  in English. *The Journal of Philosophy* 70(18): 601–609.
- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
  *SALT VIII*.
- Abusch, D. (1997). Sequence of tense and temporal de re.
- Kaplan, D. (1989). Demonstratives.
- Elbourne, P. (2013). Definite Descriptions. OUP.
-/

namespace Comparisons.Partee1973

open Semantics.Tense (TenseInterpretation TemporalAssignment
  interpTense temporalLambdaAbs updateTemporal situationToTemporal PAST SitProp)
open Semantics.Reference.KaplanLD (opNow)
open Semantics.Intensional.Situations.Elbourne (SitVarStatus)
open Core.Time (Situation)
open Core.ReferentialMode (ReferentialMode)


-- ════════════════════════════════════════════════════════════════
-- § 3. Indexical Tense = Kaplan's Now
-- ════════════════════════════════════════════════════════════════

/-! Partee: indexical tenses are anchored to utterance time, just as "I"
is anchored to the speaker. Kaplan's `opNow cT φ` evaluates φ at context
time cT — this IS the indexical tense interpretation.

    Kaplan `pronI` : character = λc. rigid(c.agent) — "I" → speaker
    Temporal parallel :       character = λc. rigid(c.time) — present → speech time -/

/-- An indexically interpreted tense is equivalent to Kaplan's Now:
    both fix the temporal coordinate to a context-given value,
    ignoring the circumstance evaluation time. -/
theorem indexical_tense_matches_opNow {W T : Type*}
    (cT : T) (φ : W → T → Prop) (w : W) (t : T) :
    opNow cT φ w t = φ w cT := rfl


-- ════════════════════════════════════════════════════════════════
-- § 4. Partee → Elbourne: TenseInterpretation → SitVarStatus
-- ════════════════════════════════════════════════════════════════

/-! Elbourne (2013) generalizes Partee from times to situations (world–time
pairs). His `SitVarStatus` (free/bound) collapses Partee's three-way
distinction: indexical and anaphoric tenses both have FREE variables,
differing only in how the free variable is pragmatically resolved
(utterance context vs. discourse salience). -/

/-- Map Partee's three-way classification to Elbourne's two-way.
    Indexical and anaphoric → free; bound → bound.
    Uses `ReferentialMode.isFree` for the coarsening. -/
def toSitVarStatus : TenseInterpretation → SitVarStatus
  | t => if t.isFree then .free else .bound

/-- Surjective: Partee's classification is at least as fine as Elbourne's. -/
theorem toSitVarStatus_surjective :
    ∀ s : SitVarStatus, ∃ t : TenseInterpretation, toSitVarStatus t = s := by
  intro s; cases s
  · exact ⟨.indexical, rfl⟩
  · exact ⟨.bound, rfl⟩

/-- Not injective: indexical ≠ anaphoric but both map to free.
    The indexical/anaphoric distinction is a pragmatic refinement
    invisible to Elbourne's structural semantics. -/
theorem toSitVarStatus_not_injective :
    ReferentialMode.indexical ≠ ReferentialMode.anaphoric ∧
    toSitVarStatus .indexical = toSitVarStatus .anaphoric :=
  ⟨nofun, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § 6. Partee vs Prior
-- ════════════════════════════════════════════════════════════════

/-! The codebase contains both perspectives on tense:

**Prior (1967)**: `PAST P s s' := s.time < s'.time ∧ P s`. Tense is an
operator that constrains temporal relations — existential quantification
over past times.

**Partee (1973)**: `interpTense n g = g n`. Tense is a variable that
refers to a specific contextual time.

Partee's argument: "I didn't turn off the stove" under Prior's analysis
gives `∃t < now. ¬turn_off(stove, t)` — trivially true, since there are
always past times when you weren't turning off the stove. The intended
reading is `¬turn_off(stove, t_i)` where `t_i` is a specific time (when
you left the house). Only the referential analysis captures this.

The Priorean operators `PAST`/`PRES`/`FUT` in `Tense/Basic.lean` remain
useful for modeling tense in isolation. The referential analysis here
is needed for discourse anaphora and binding. -/

/-- Partee's stove example: "I didn't turn off the stove."

    Past tense introduces a temporal variable resolved to a specific
    contextually salient time. The negation scopes OVER the temporal
    reference, giving ¬P(t_i) rather than Prior's ∃t.¬P(t). -/
def parteeStoveExample {Time : Type*} (turnedOff : Time → Bool)
    (g : TemporalAssignment Time) (n : ℕ) : Bool :=
  !turnedOff (interpTense n g)

/-- Partee's narrative example: "He turned the corner. He saw a house."

    Both past tenses refer to the same (or closely related) narrative time
    — temporal anaphora. Under the referential analysis, both clauses
    evaluate at g(n) for the same discourse-salient temporal variable n.
    Anaphoric tenses corefer with a previously established temporal
    referent, just as anaphoric pronouns corefer with a previously
    established individual. -/
def narrativeAnaphora {Time : Type*} (P Q : Time → Bool)
    (g : TemporalAssignment Time) (n : ℕ) : Bool :=
  P (interpTense n g) && Q (interpTense n g)


-- ════════════════════════════════════════════════════════════════
-- § 7. Referential ↔ Priorean Bridge (Ogihara 1989)
-- ════════════════════════════════════════════════════════════════

/-! The Priorean operators `PAST`/`PRES`/`FUT` in `Tense/Basic.lean` and the
referential analysis (`interpTense`, `temporalLambdaAbs`) are not competitors
but complementary layers. Ogihara (1989) §2.3: tense is a variable (picks a
time) that must satisfy a temporal presupposition (the picked time is
past/present/future). The following theorems make this reconciliation formal. -/

/-- The Priorean PAST operator, applied at a referentially-determined time g(n),
    decomposes into the conjunction of (1) the referential time precedes the
    speech situation and (2) the predicate holds at the referential time.

    This is the formal reconciliation: the referential analysis (Partee) picks
    the TIME; the operator analysis (Prior) imposes the CONSTRAINT. They are
    not competitors but complementary layers.

    Ogihara (1989) §2.3: tense is a variable (picks a time) that must satisfy
    a temporal presupposition (the picked time is past/present/future). -/
theorem referential_past_decomposition {W Time : Type*} [LT Time]
    (P : SitProp W Time) (g : TemporalAssignment Time) (n : ℕ)
    (w : W) (speechTime : Time) :
    PAST P ⟨w, interpTense n g⟩ ⟨w, speechTime⟩ ↔
    (g n < speechTime ∧ P ⟨w, g n⟩) := by rfl

/-- Bound tense under attitude embedding: the binder (attitude verb) fills
    the temporal variable, yielding the simultaneous reading.

    `temporalLambdaAbs n body g t` = `body (g[n ↦ t])`: the body is
    evaluated with variable n set to binder time t. The tense variable
    no longer refers independently — it receives the attitude's event time. -/
theorem bound_tense_receives_attitude_time {Time α : Type*}
    (body : TemporalAssignment Time → α) (g : TemporalAssignment Time)
    (n : ℕ) (attitudeEventTime : Time) :
    temporalLambdaAbs n body g attitudeEventTime =
    body (updateTemporal g n attitudeEventTime) := by rfl


end Comparisons.Partee1973
