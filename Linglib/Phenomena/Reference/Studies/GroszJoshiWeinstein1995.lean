import Linglib.Theories.Discourse.Centering.Basic
import Linglib.Theories.Discourse.Centering.Transition
import Linglib.Theories.Discourse.Centering.Rule1
import Linglib.Theories.Discourse.Centering.Rule2
import Linglib.Theories.Discourse.Centering.Instances.GrammaticalRole
import Linglib.Core.Discourse.Accessibility
import Linglib.Phenomena.Reference.Studies.Sidner1983
import Linglib.Phenomena.Reference.Studies.Ariel2001
import Linglib.Phenomena.Reference.Studies.KehlerRohde2013
import Linglib.Phenomena.Reference.Studies.KwonLee2026

/-!
# @cite{grosz-joshi-weinstein-1995}: Centering Theory
@cite{kameyama-1986} @cite{gordon-grosz-gilliom-1993} @cite{kehler-rohde-2013} @cite{sidner-1983}

Centering: A Framework for Modeling the Local Coherence of Discourse.
*Computational Linguistics* 21(2): 203–225.

Each utterance has a set of forward-looking centers `Cf` (ranked by
grammatical role: subject > object > other) and at most one
backward-looking center `Cb` (the highest-ranked Cf element of the
previous utterance that is also realized in the current one). Three
transition types — `continuation`, `retaining`, `shifting` — classify
adjacent-utterance pairs by whether the Cb is preserved and whether
that Cb is the most-highly-ranked Cf.

Two normative rules govern coherent discourse: **Rule 1**
(pronominalization constraint — if any Cf element is pronominalized
in the next utterance, the Cb must be); **Rule 2** (transition
preference — continuations preferred over retentions, retentions
over shifts).

The key empirical contrast is between Discourses 1 and 2 (§ 4 below):
same propositional content, different transition pattern, different
perceived coherence. The framework predicts the difference.

This file consumes the substrate types and operators from
`Theories/Discourse/Centering/{Defs,Basic,Transition,Rule1,Rule2}.lean`
plus the `GrammaticalRole` Cf-ranker instance from
`Instances/GrammaticalRole.lean`. Per linglib's import-don't-restipulate
discipline, no Centering primitives are redefined here — the file's
contribution is the empirical-example anchor for the substrate plus
the §8 comparison with @cite{sidner-1983}.
-/

set_option autoImplicit false

namespace GroszJoshiWeinstein1995

open Discourse.Centering

/-! Throughout, examples use `String` entities for readability and
    `Utterance String GrammaticalRole` from the substrate. -/

/-- Utterance abbreviation specialized to the GJW use case
    (`String` entities, grammatical-role-ranked Cf). -/
abbrev Utt : Type := Utterance String GrammaticalRole

-- ════════════════════════════════════════════════════
-- § 1. Discourse 1 vs Discourse 2: the coherence contrast (paper §2)
-- ════════════════════════════════════════════════════

namespace D1

/-- (1a) John went to his favorite music store to buy a piano. -/
def a : Utt :=
  ⟨[⟨"John", .subject, false⟩, ⟨"store", .object, false⟩,
    ⟨"piano", .other, false⟩]⟩

/-- (1b) He had frequented the store for many years. -/
def b : Utt :=
  ⟨[⟨"John", .subject, true⟩, ⟨"store", .object, false⟩]⟩

/-- (1c) He was excited that he could finally buy a piano. -/
def c : Utt :=
  ⟨[⟨"John", .subject, true⟩, ⟨"piano", .object, false⟩]⟩

/-- (1d) He arrived just as the store was closing for the day. -/
def d : Utt :=
  ⟨[⟨"John", .subject, true⟩, ⟨"store", .other, false⟩]⟩

end D1

namespace D2

/-- (2a) John went to his favorite music store to buy a piano. -/
def a : Utt :=
  ⟨[⟨"John", .subject, false⟩, ⟨"store", .object, false⟩,
    ⟨"piano", .other, false⟩]⟩

/-- (2b) It was a store John had frequented for many years. -/
def b : Utt :=
  ⟨[⟨"store", .subject, true⟩, ⟨"John", .object, false⟩]⟩

/-- (2c) He was excited that he could finally buy a piano. -/
def c : Utt :=
  ⟨[⟨"John", .subject, true⟩, ⟨"piano", .object, false⟩]⟩

/-- (2d) It was closing just as John arrived. -/
def d : Utt :=
  ⟨[⟨"store", .subject, true⟩, ⟨"John", .object, false⟩]⟩

end D2

/-! ### Per-pair transition predictions

    For each adjacent pair, the Cb (computed from the prior utterance)
    and the transition type follow from the substrate definitions. -/

/-- Discourse 1 (a→b): John continues as Cb. -/
theorem d1_a_to_b_cb : cb D1.a D1.b = some "John" := by decide

theorem d1_a_to_b_continuation :
    classifyTransitionExtended D1.a D1.b D1.b.cp none = .continuation := by decide

/-- Discourse 1 (b→c): John continues. -/
theorem d1_b_to_c_continuation :
    classifyTransitionExtended D1.b D1.c D1.c.cp (cb D1.a D1.b) = .continuation := by decide

/-- Discourse 1 (c→d): John continues. -/
theorem d1_c_to_d_continuation :
    classifyTransitionExtended D1.c D1.d D1.d.cp (cb D1.b D1.c) = .continuation := by decide

/-- Discourse 2 (a→b): the Cb is John (the only entity in `Cf(D2.a)`
    that is realized in `D2.b`), but `Cp(D2.b) = "store"` (not John),
    so this is a *retain* — already a less coherent transition than
    Discourse 1's continuation. -/
theorem d2_a_to_b_cb : cb D2.a D2.b = some "John" := by decide

theorem d2_a_to_b_retaining :
    classifyTransitionExtended D2.a D2.b D2.b.cp none = .retaining := by decide

/-- Discourse 2 (b→c): John re-emerges as Cb (it was object in D2.b);
    in D2.c, John is also `Cp` — so this would be a continuation.
    Rule 1 is also fine here. -/
theorem d2_b_to_c_cb : cb D2.b D2.c = some "John" := by decide

theorem d2_b_to_c_continuation :
    classifyTransitionExtended D2.b D2.c D2.c.cp (cb D2.a D2.b) = .continuation := by decide

/-- Discourse 2 (c→d): John remains Cb (was subject in D2.c, object
    in D2.d), but `Cp(D2.d) = "store"`. RETAIN, not continuation. -/
theorem d2_c_to_d_retaining :
    classifyTransitionExtended D2.c D2.d D2.d.cp (cb D2.b D2.c) = .retaining := by decide

/-- **The coherence contrast (paper §2)**: Discourse 1's transition
    pattern is all continuations; Discourse 2's pattern is
    `retain, continue, retain` — a mix of weaker transitions. The sum
    of `Transition.rank`s is a coarse but theory-aligned coherence
    measure. -/
def d1_score : Nat :=
  Transition.continuation.rank + Transition.continuation.rank
    + Transition.continuation.rank
def d2_score : Nat :=
  Transition.retaining.rank + Transition.continuation.rank
    + Transition.retaining.rank

theorem discourse1_more_coherent_than_discourse2 : d1_score > d2_score := by decide

-- ════════════════════════════════════════════════════
-- § 2. Discourse 15: Rule 1 violation
-- ════════════════════════════════════════════════════

namespace D15

/-- (15a) He has been acting quite odd. (Cb = John, presumed in segment.) -/
def a : Utt := ⟨[⟨"John", .subject, true⟩]⟩

/-- (15b) He called up Mike yesterday. (Cb = John, "He" = John.) -/
def b : Utt :=
  ⟨[⟨"John", .subject, true⟩, ⟨"Mike", .object, false⟩]⟩

/-- (15c) John wanted to meet him urgently. (Cb = John, "him" = Mike.)
    The Cf member Mike is pronominalized but the Cb John is *not* —
    a Rule 1 violation. -/
def c : Utt :=
  ⟨[⟨"John", .subject, false⟩, ⟨"Mike", .object, true⟩]⟩

end D15

theorem d15_b_to_c_cb : cb D15.b D15.c = some "John" := by decide

/-- **Rule 1 violation**: in (15c), Mike is pronominalized but the Cb
    John is realized as a proper name. The paper's diagnosis. -/
theorem discourse15_violates_rule1 :
    ¬ Rule1GJW95 D15.b D15.c := by decide

/-- The (a→b) pair of the same discourse satisfies Rule 1 (the only
    Cf element from (a) is John, who is pronominalized in (b) — the Cb
    is also pronominalized). The violation is local to the (b→c) step. -/
theorem d15_a_to_b_satisfies_rule1 :
    Rule1GJW95 D15.a D15.b := by decide

-- ════════════════════════════════════════════════════
-- § 3. Discourses 7-10: Cf ranking + Rule 1 interaction
-- ════════════════════════════════════════════════════

/-! @cite{grosz-joshi-weinstein-1995} §5 examples (7)-(10). All four
    variants share utterances (a) and (b); they differ only in (c)'s
    realization choices. Variants (7) and (8) satisfy Rule 1; variants
    (9) and (10) violate it. The paper notes (10) is "completely
    unacceptable" and (9) is also degraded — both more so than (7) and
    (8) — because of the Rule 1 violations.

    Shared:
    > a. Susan gave Betsy a pet hamster.
    > b. She reminded her that such hamsters were quite shy. -/

namespace D7_10

/-- (a) Susan gave Betsy a pet hamster.  Cf = [Susan, Betsy, hamster]. -/
def a : Utt :=
  ⟨[⟨"Susan", .subject, false⟩, ⟨"Betsy", .object, false⟩,
    ⟨"hamster", .other, false⟩]⟩

/-- (b) She reminded her ...  "She" = Susan (subj), "her" = Betsy (obj). -/
def b : Utt :=
  ⟨[⟨"Susan", .subject, true⟩, ⟨"Betsy", .object, true⟩]⟩

/-- (7c) She asked Betsy whether she liked the gift. — "She" = Susan,
    Betsy as proper name (object). Cb = Susan, Cp = Susan ⇒ CONTINUE.
    Susan is pronominalized; Rule 1 satisfied. -/
def c7 : Utt :=
  ⟨[⟨"Susan", .subject, true⟩, ⟨"Betsy", .object, false⟩]⟩

/-- (8c) Betsy told her that she really liked the gift. — Betsy as
    proper name (subject), "her" = Susan. Cb = Susan (highest in Cf(b)
    realized in c), but Cp = Betsy ⇒ RETAIN. Susan as Cb pronominalized
    via "her"; Rule 1 satisfied. -/
def c8 : Utt :=
  ⟨[⟨"Betsy", .subject, false⟩, ⟨"Susan", .object, true⟩]⟩

/-- (9c) Susan asked her whether she liked the gift. — Susan as proper
    name (subject), "her" = Betsy. Cb = Susan, Cp = Susan ⇒ would be
    CONTINUE, but Betsy is pronominalized while Cb (Susan) is a proper
    name ⇒ Rule 1 VIOLATION. -/
def c9 : Utt :=
  ⟨[⟨"Susan", .subject, false⟩, ⟨"Betsy", .object, true⟩]⟩

/-- (10c) She told Susan that she really liked the gift. — "She" =
    Betsy (subj), Susan as proper name (obj). Cb = Susan (highest in
    Cf(b) realized in c). Cp = Betsy ⇒ RETAIN. Betsy is pronominalized
    while Cb (Susan) is a proper name ⇒ Rule 1 VIOLATION. -/
def c10 : Utt :=
  ⟨[⟨"Betsy", .subject, true⟩, ⟨"Susan", .object, false⟩]⟩

end D7_10

/-- All four (c) variants share Cb = Susan: Susan is the highest-ranked
    Cf(b) element realized in each (c). The choice of variant does not
    change *which* entity is the Cb — only how that Cb is realized. -/
theorem d7_to_10_share_cb :
    cb D7_10.b D7_10.c7  = some "Susan" ∧
    cb D7_10.b D7_10.c8  = some "Susan" ∧
    cb D7_10.b D7_10.c9  = some "Susan" ∧
    cb D7_10.b D7_10.c10 = some "Susan" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Variant 7 satisfies Rule 1 (Susan as Cb pronominalized). -/
theorem d7_satisfies_rule1 :
    Rule1GJW95 D7_10.b D7_10.c7 := by decide

/-- Variant 8 satisfies Rule 1 (Susan as Cb pronominalized via "her"). -/
theorem d8_satisfies_rule1 :
    Rule1GJW95 D7_10.b D7_10.c8 := by decide

/-- **Variant 9 violates Rule 1**: Betsy is pronominalized but Cb
    (Susan) is realized as a proper name. -/
theorem d9_violates_rule1 :
    ¬ Rule1GJW95 D7_10.b D7_10.c9 := by decide

/-- **Variant 10 violates Rule 1**: Betsy is pronominalized but Cb
    (Susan) is realized as a proper name. The paper calls this case
    "completely unacceptable". -/
theorem d10_violates_rule1 :
    ¬ Rule1GJW95 D7_10.b D7_10.c10 := by decide

/-- The Rule-1 split (`d7,8 OK` vs `d9,10 violate`) tracks the paper's
    acceptability ordering: variants 7 and 8 are acceptable, 9 and 10
    are degraded. The framework predicts this directly from Rule 1
    plus the subject>object Cf ranking. -/
theorem rule1_distinguishes_variants_7_8_from_9_10 :
    (Rule1GJW95 D7_10.b D7_10.c7 ∧ Rule1GJW95 D7_10.b D7_10.c8) ∧
    (¬ Rule1GJW95 D7_10.b D7_10.c9 ∧ ¬ Rule1GJW95 D7_10.b D7_10.c10) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 4. Discourse 20: full CONTINUE / RETAIN / SHIFT pattern
-- ════════════════════════════════════════════════════

namespace D20

/-- (20a) John has been having a lot of trouble arranging his vacation. -/
def a : Utt := ⟨[⟨"John", .subject, false⟩]⟩

/-- (20b) He cannot find anyone to take over his responsibilities. -/
def b : Utt := ⟨[⟨"John", .subject, true⟩]⟩

/-- (20c) He called up Mike yesterday. -/
def c : Utt :=
  ⟨[⟨"John", .subject, true⟩, ⟨"Mike", .object, false⟩]⟩

/-- (20d) Mike has annoyed him a lot recently. -/
def d : Utt :=
  ⟨[⟨"Mike", .subject, false⟩, ⟨"John", .object, true⟩]⟩

/-- (20e) He called John at 5 AM on Friday last week. -/
def e : Utt :=
  ⟨[⟨"Mike", .subject, true⟩, ⟨"John", .object, false⟩]⟩

end D20

/-- The paper-stipulated transition labels b→c, c→d, d→e:
    CONTINUE, RETAIN, SHIFT. -/
theorem discourse20_b_to_c_continuation :
    classifyTransitionExtended D20.b D20.c D20.c.cp (cb D20.a D20.b) = .continuation := by decide

theorem discourse20_c_to_d_retaining :
    classifyTransitionExtended D20.c D20.d D20.d.cp (cb D20.b D20.c) = .retaining := by decide

theorem discourse20_d_to_e_shifting :
    classifyTransitionExtended D20.d D20.e D20.e.cp (cb D20.c D20.d) = .shifting := by decide

/-- Rule 1 holds throughout Discourse 20 (the paper's claim). -/
theorem discourse20_rule1_a_b : Rule1GJW95 D20.a D20.b := by decide
theorem discourse20_rule1_b_c : Rule1GJW95 D20.b D20.c := by decide
theorem discourse20_rule1_c_d : Rule1GJW95 D20.c D20.d := by decide
theorem discourse20_rule1_d_e : Rule1GJW95 D20.d D20.e := by decide

-- ════════════════════════════════════════════════════
-- § 5. Bridge to @cite{kehler-rohde-2013} (Topichood)
-- ════════════════════════════════════════════════════

/-- Centering's "highest-ranked Cf element" — the `Cp` (preferred
    center) — corresponds to @cite{kehler-rohde-2013}'s **topichood**
    side of the Bayesian decomposition: the production component
    P(pronoun | referent) is conditioned on whether the referent is
    the topic. The Cp of an active-clause subject is precisely the
    `default_` topichood level in @cite{kehler-rohde-2013}'s scheme. -/
def cpTopichood : KehlerRohde2013.TopichoodLevel :=
  KehlerRohde2013.topichood .Act true

theorem cp_is_default_topichood : cpTopichood = .default_ := rfl

-- ════════════════════════════════════════════════════
-- § 6. Bridge to @cite{kwon-lee-2026} (Korean Pronouns)
-- ════════════════════════════════════════════════════

/-! @cite{kwon-lee-2026}'s Korean Exp 3 finding (null pronouns
    strongly prefer subject antecedents) is **predicted** by Centering
    Theory:

    1. Subject is the highest-ranked Cf element (Kameyama 1986).
    2. The subject of `U_n` typically becomes the Cb of `U_{n+1}`.
    3. By Rule 1, the Cb is preferentially realized by a pronoun.
    4. In Korean, the highest-accessibility marker (most preferred
       pronominal form) is the *null* pronoun (@cite{ariel-2001}).

    Composing: subject → Cb → pronoun → null in Korean.

    The derivation is anchored on a concrete two-utterance Korean
    continuation pattern: utterance (a) introduces a subject-marked
    referent; utterance (b) refers back to it with a null pronoun. -/

namespace KoreanContinuation

/-- (a) Mary often took Tom to the sea. — adapted from
    @cite{kwon-lee-2026} Exp 3 stimulus pattern. -/
def utt_a : Utt :=
  ⟨[⟨"Mary", .subject, false⟩, ⟨"Tom", .object, false⟩,
    ⟨"sea", .other, false⟩]⟩

/-- (b) [pro] achieved the dream of becoming a sea navigator.
    Korean null subject; the realization is pronominal (the empty
    category counts as pronominal in the Centering sense). -/
def utt_b_null : Utt :=
  ⟨[⟨"Mary", .subject, true⟩]⟩

end KoreanContinuation

/-- Step 1 of the derivation: in canonical Korean SVO, the Cb of the
    second utterance is the prior-utterance subject. -/
theorem korean_cb_is_prior_subject :
    cb KoreanContinuation.utt_a KoreanContinuation.utt_b_null = some "Mary" := by
  decide

/-- Step 2: realizing the Cb pronominally satisfies Rule 1
    (the null subject in Korean counts as pronominal). -/
theorem korean_null_realization_satisfies_rule1 :
    Rule1GJW95 KoreanContinuation.utt_a KoreanContinuation.utt_b_null := by
  decide

/-- Step 3: among Korean's three referential forms, the null pronoun is
    the most accessible (top of the Korean-form linear order, derived
    from `Ariel2001.AccessibilityLevel.rank` in `KwonLee2026`). -/
theorem korean_null_is_top_form :
    ∀ f : KwonLee2026.KoreanRefForm,
      f ≤ KwonLee2026.KoreanRefForm.nullPro := by
  intro f; cases f <;> decide

/-- **Centering predicts Korean's null-subject preference**: combining
    Rule 1 with Korean's accessibility-scale calibration. The 71%
    empirical subject bias for null pronouns (@cite{kwon-lee-2026} Exp
    3) is the predicted consequence of this composition. -/
theorem korean_subject_bias_for_null_exceeds_chance :
    KwonLee2026.exp3_pro.subjectPercent > 50 := by decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to @cite{ariel-2001} (Accessibility Marking)
-- ════════════════════════════════════════════════════

open Core.Discourse.Accessibility

/-- Centering's Cb (the "currently centered" entity) corresponds to a
    high-accessibility referent on @cite{ariel-2001}'s scale. Rule 1
    predicts that the Cb's realization should use a high-accessibility
    marker — typically a pronoun. -/
def cbExpectedAccessibility : AccessibilityLevel := .unstressedPron

theorem cb_marker_is_high_accessibility :
    cbExpectedAccessibility.rank ≥ AccessibilityLevel.shortDefDescription.rank := by
  decide

-- ════════════════════════════════════════════════════
-- § 8. Comparison with @cite{sidner-1983}: example (34)
-- ════════════════════════════════════════════════════

/-! This section mechanizes the Sidner-comparison the paper makes in
    its own §9 (p. 222), on the discourse:

    (34) a. I haven't seen Jeff for several days.
         b. Carl thinks he's studying for his exams,
         c. but I think he went to the Cape with Linda.

    GJW summarize Sidner's prediction: "On Sidner's account, Carl is
    the actor focus after (34b) and Jeff is the discourse focus.
    Because the actor focus is preferred as the referent of pronominal
    expressions, Carl is the leading candidate for the entity referred
    to by *he* in (34c)." Then: "On our account, Jeff is the C_b at
    (34b) and there is no problem."

    Both theories must commit to a referent for *he* in (34c). The
    formalization picks the one that is **coherence-preferred** under
    each theory:

    - Sidner: agent-position pronoun → actor focus (Carl). See
      `Sidner1983.resolvePronoun` and the focus-state computation in
      `Phenomena/Reference/Studies/Sidner1983.lean`.
    - GJW: pick the resolution that yields the higher-ranked Rule-2
      transition. With "he" = Jeff the Cb is preserved (Jeff → Jeff)
      but the matrix subject "I" becomes the new Cp, so this is a
      RETAIN. With "he" = Carl, the Cb shifts (Jeff → Carl), so this
      is a SHIFT. RETAIN outranks SHIFT under Rule 2, so GJW predict
      Jeff. -/

namespace D34

/-- (34a) I haven't seen Jeff for several days. -/
def a : Utt :=
  ⟨[⟨"speaker", .subject, true⟩, ⟨"Jeff", .object, false⟩]⟩

/-- (34b) Carl thinks he's studying for his exams. The matrix subject
    is Carl (full name); the embedded subject "he" co-specifies Jeff
    (continuing from 34a). -/
def b : Utt :=
  ⟨[⟨"Carl", .subject, false⟩, ⟨"Jeff", .other, true⟩]⟩

/-- (34c) under the resolution "he" = Jeff: continues the Cb. -/
def c_he_is_jeff : Utt :=
  ⟨[⟨"speaker", .subject, true⟩, ⟨"Jeff", .other, true⟩,
    ⟨"Cape", .other, false⟩, ⟨"Linda", .other, false⟩]⟩

/-- (34c) under the resolution "he" = Carl: shifts the Cb. -/
def c_he_is_carl : Utt :=
  ⟨[⟨"speaker", .subject, true⟩, ⟨"Carl", .other, true⟩,
    ⟨"Cape", .other, false⟩, ⟨"Linda", .other, false⟩]⟩

end D34

/-- Cb of (34b) given (34a) is Jeff — paper's own claim ("Jeff is the
    C_b at (34b)", §9 p. 222). -/
theorem d34_cb_b : cb D34.a D34.b = some "Jeff" := by decide

/-- Under the Jeff-resolution of (34c), the Cb continues as Jeff. -/
theorem d34_cb_c_jeff : cb D34.b D34.c_he_is_jeff = some "Jeff" := by decide

/-- Under the Carl-resolution of (34c), the Cb shifts to Carl. -/
theorem d34_cb_c_carl : cb D34.b D34.c_he_is_carl = some "Carl" := by decide

/-- Jeff-resolution: Cb stable (Jeff → Jeff), but the matrix "I"
    becomes the new Cp, so this is a RETAIN, not a CONTINUE. -/
theorem d34_jeff_retaining :
    classifyTransitionExtended D34.b D34.c_he_is_jeff D34.c_he_is_jeff.cp
      (cb D34.a D34.b) = .retaining := by decide

/-- Carl-resolution: Cb shifts from Jeff to Carl. -/
theorem d34_carl_shift :
    classifyTransitionExtended D34.b D34.c_he_is_carl D34.c_he_is_carl.cp
      (cb D34.a D34.b) = .shifting := by decide

/-- **GJW prediction for (34c)**: by Rule 2 (RETAIN outranks SHIFT
    here), the Jeff-resolution is preferred. Returns `Option String`:
    `none` if the candidate Rule-2 ranks coincide and the framework
    cannot adjudicate; otherwise `some "Jeff"` or `some "Carl"`.

    **Caveat about overclaim.** GJW themselves do not commit to a
    unique referent in §9 p. 222 — they only say "Jeff is the C_b at
    (34b) and there is no problem." Rule 2 in their paper is a
    constraint over *speaker production*, not an *interpreter
    resolution algorithm*. This function operationalizes "GJW's
    prediction" as "the resolution Rule 2 would prefer if a speaker
    had to choose between the two transitions"; it is closer to the
    Brennan-Friedman-Pollard 1987 resolution algorithm than to GJW
    1995 as published. The headline disagreement theorem is honest
    about this gap — see its docstring. -/
def gjwPredictedHe : Option String :=
  let jeffTrans := classifyTransitionExtended D34.b D34.c_he_is_jeff
                     D34.c_he_is_jeff.cp (cb D34.a D34.b)
  let carlTrans := classifyTransitionExtended D34.b D34.c_he_is_carl
                     D34.c_he_is_carl.cp (cb D34.a D34.b)
  if jeffTrans.rank > carlTrans.rank then some "Jeff"
  else if carlTrans.rank > jeffTrans.rank then some "Carl"
  else none

theorem gjw_prefers_jeff : gjwPredictedHe = some "Jeff" := by decide

/-- **The disagreement on what "he" in (34c) refers to.**

    Sidner's prediction (§5.2.6 step 3): agent-position pronoun →
    actor focus = Carl.

    GJW's Rule-2 preference (with the caveat above that GJW themselves
    don't claim uniqueness): RETAIN > SHIFT under Rule 2 ⇒ Jeff.

    Stated constructively (mathlib idiom): each side commits to a
    *named* prediction; the inequality follows by transparent
    `decide` from the witnesses. -/
theorem sidner_gjw_disagree_on_d34c :
    Sidner1983.D34.sidnerPredictedHe ≠ gjwPredictedHe := by
  rw [Sidner1983.D34.sidner_predicts_carl, gjw_prefers_jeff]
  decide

end GroszJoshiWeinstein1995
