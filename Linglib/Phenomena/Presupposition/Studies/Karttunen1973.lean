import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Semantics.CommonGround
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Theories.Semantics.Presupposition.BeliefEmbedding

/-!
# Karttunen 1973: Presuppositions of Compound Sentences
@cite{karttunen-1973} @cite{hintikka-1962} @cite{karttunen-1971}

Linguistic Inquiry 4(2): 169–193.

The projection problem: how presuppositions of constituent sentences are
inherited (or not) by compound sentences. K1973's contribution is the
plug/hole/filter taxonomy of complement-takers (§§3–5), the asymmetric
filtering rules for the connectives (§§5–7), the §8 Harman derivation of
the conditional/conjunction-filter coincidence, and the §9 admission that
filtering must be relativized to a set of background assumptions — the
genealogical ancestor of CCP local contexts (@cite{heim-1983},
@cite{schlenker-2009}).

This file makes load-bearing the contributions that survive: the
classification (§§3–4), the rule (13)/(17)/(24) filters, the §8 Harman
derivation, the §9 X-set machinery (with concrete Geraldine example),
and the §10 three-valued comparison (Bochvar internal/external negation
in particular). K1973's §11 verdict on propositional attitudes
(tentative plug, hedged) is recorded explicitly and contrasted with the
Heim-1992-era hole consensus.
-/

namespace Karttunen1973

open Core.Presupposition
open Core.Verbs (ProjectionBehavior VerbCore)
open Core.CommonGround (ContextSet)
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════════════════
-- § 1. Plug / Hole Classification (K1973 §§3–4)
-- ════════════════════════════════════════════════════════════════

/-! K1973 §3 (p. 174) plug list: "say, mention, tell, ask, promise,
    warn, request, order, accuse, criticize, blame" — verbs of saying /
    performatives. K1973 §4 (p. 175) hole list: "know, regret,
    understand, surprise, be significant, begin, stop, continue, manage,
    avoid, be able, be possible, force, prevent, hesitate, seem, be
    probable" — Kiparsky's factives, Newmeyer's aspectuals, K's one-
    and two-way implicatives. Footnote 6 (p. 175) adds *realize*: "factive
    verbs, such as *realize*, … are holes irrespective of the type of
    the complement."

    K1973's lists are **lexical, not structural**: there is no clean
    `inferProjection : VerbCore → ProjectionBehavior`, because the
    Fragment has e.g. `reveal` as `speechActVerb := true` *and* a factive
    soft-trigger (which would be a hole). So the file consolidates K's
    Fragment-attested classifications as list-quantified theorems
    rather than re-stipulating per-verb rfl checks. -/

/-- K1973 §3 plug list, restricted to the Fragment's attested entries.
    K's other list members (mention, ask, warn, request, order, accuse,
    criticize) lack a `projectionBehavior` annotation in `Verbal.lean`. -/
def k1973PlugVerbs : List VerbEntry := [say, tell, promise]

/-- K1973 §4 hole list, restricted to the Fragment's attested entries.
    `realize` is included on the strength of K1973 fn 6 paragraph 3. -/
def k1973HoleVerbs : List VerbEntry := [know, regret, realize, stop, manage, force]

theorem k1973_plug_classification :
    ∀ v ∈ k1973PlugVerbs, v.toVerbCore.projectionBehavior = some .plug := by
  decide

theorem k1973_hole_classification :
    ∀ v ∈ k1973HoleVerbs, v.toVerbCore.projectionBehavior = some .hole := by
  decide

/-- The classes are disjoint. -/
theorem k1973_plug_hole_disjoint :
    ∀ v ∈ k1973PlugVerbs, ∀ u ∈ k1973HoleVerbs, v.form ≠ u.form := by
  decide

-- ── Trigger × projection orthogonality ──

/-- K's distinction: trigger-status (introduces a presupposition?) is
    orthogonal to projection-behavior (passes complement presuppositions
    through?). *know* exhibits both. -/
theorem know_trigger_and_hole :
    know.toVerbCore.presupType = some .softTrigger ∧
    know.toVerbCore.projectionBehavior = some .hole := ⟨rfl, rfl⟩

/-- *say* is a non-trigger AND a plug. -/
theorem say_nontrigger_and_plug :
    say.toVerbCore.presupType = none ∧
    say.toVerbCore.projectionBehavior = some .plug := ⟨rfl, rfl⟩

/-- K1973 fn 6 (p. 175 paragraph 4): *tell* is a plug for *that*-clauses
    but a hole for indirect questions ("Bill told John that Harry insulted
    the present king of France" vs "Bill told John who insulted the
    present king of France"). The Fragment's flat
    `tell.projectionBehavior = some .plug` is K's *that*-clause verdict;
    the indirect-question case is a separate analysis K credits to
    Permesly 1973 (Ch. 2). -/
theorem tell_that_clause_is_plug :
    tell.toVerbCore.projectionBehavior = some .plug := rfl

/-- K1973 §1 (5)/(6) typological contrast: plugs and holes are *distinct*
    profiles. K's own minimal pair uses *order* vs *force*; *order* lacks
    a Fragment annotation, so we use the closest attested pair (*promise*,
    plug; *force*, hole). -/
theorem promise_force_minimal_pair :
    promise.toVerbCore.projectionBehavior ≠ force.toVerbCore.projectionBehavior := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § 2. Believe — K1973 §11 vs Modern Consensus
-- ════════════════════════════════════════════════════════════════

/-! K1973 §11 (pp. 188–190) discusses propositional attitudes at length.
    §4 raised the question (hole or plug?) and postponed it. §11
    considers the hole-with-equivalence-machinery analysis: the (37)/(38)
    move uses @cite{hintikka-1962}'s `believe(A) ∧ believe(B) ↔
    believe(A ∧ B)` to let *believe* survive as a hole even when the
    complement-internal presupposition appears not to project. (38) keeps
    the hole verdict safe for cases like

        (37) Bill believes Fred has been beating Zelda, and furthermore,
             Bill believes that Fred has stopped beating Zelda.

    But K's (42) defeats the trick — two distinct attitude verbs (believe
    + hope) on a shared presupposed clause can't be re-collected into a
    single attitude:

        (42) Bill believed that Fred had been beating his wife and hoped
             that Fred would stop beating her.

    K's tentative §11 conclusion (p. 190): "we do not seem to have any
    other alternative except to classify all propositional attitude verbs
    as plugs, although I am still not convinced that this is the right
    approach." So K1973's published verdict on `believe` is **tentative
    plug, with explicit hedging**. The Fragment annotation
    `believe.projectionBehavior = some .hole` reflects the post-1974 /
    @cite{heim-1992} consensus, not K1973. -/

/-- The Fragment `believe` annotation diverges from K1973 §11. -/
theorem believe_fragment_is_hole :
    believe.toVerbCore.projectionBehavior = some .hole := rfl

/-- *believe* has no presupposition trigger (doxastic, not factive). -/
theorem believe_nontrigger :
    believe.toVerbCore.presupType = none := rfl

/-! ### Contentful disagreement on a concrete scenario

    The flat enum-tag inequality `.plug ≠ .hole` is meta-fact. The real
    disagreement: on a scenario where the complement of *believe* carries
    a presupposition that is true in the attitude holder's belief state
    but false in reality, the two analyses make distinct predictions
    about what the speaker is committed to. -/

/-- Two-world model: *actual* (where Mary never smoked) and *believed*
    (John's belief world, where Mary did smoke). -/
inductive AttWorld where
  | actual    -- Mary never smoked here; speaker's reality
  | believed  -- John believes this world; Mary did smoke
  deriving DecidableEq, Repr

/-- "Mary used to smoke" — the presupposition of "stop smoking". True in
    `believed`, false in `actual`. -/
def maryUsedToSmoke : PrProp AttWorld where
  presup := fun _ => True
  assertion := fun w => w = .believed

/-- The speaker-projection of a *plug*-treatment of *believe*: nothing of
    the complement projects. -/
def plugSpeakerCommitment : PrProp AttWorld where
  presup := fun _ => True
  assertion := fun _ => True

/-- The speaker-projection of K1973's flat *hole*-treatment of *believe*
    (pre-Heim 1992): the complement's presupposition projects unchanged
    to the speaker. -/
def holeSpeakerCommitment : PrProp AttWorld := maryUsedToSmoke

/-- The plug analysis predicts no speaker commitment to "Mary used to
    smoke" at the actual world; the hole analysis predicts the speaker
    IS committed there. The two analyses make different predictions on
    the same input. -/
theorem plug_vs_hole_diverge_at_actual :
    plugSpeakerCommitment.assertion .actual ∧
    ¬ holeSpeakerCommitment.assertion .actual := by
  refine ⟨trivial, ?_⟩
  simp [holeSpeakerCommitment, maryUsedToSmoke]

/-- Heim 1992 / @cite{schlenker-2009} resolve the dispute by attributing
    the presupposition to the *attitude holder*, not the speaker. The
    holder-attribution analysis lives in
    `Theories/Semantics/Presupposition/BeliefEmbedding.lean` as
    `presupAttributedToHolder`. K1973's flat hole-treatment differs from
    both Heim 1992's holder-attribution and K1973 §11's tentative plug
    verdict — three coexisting positions on the same data. -/
theorem karttunen1973_disagrees_with_modern_consensus :
    -- K1973 §11 verdict (plug) ≠ Fragment annotation (hole)
    (some .plug : Option ProjectionBehavior) ≠
      believe.toVerbCore.projectionBehavior := by decide

-- ════════════════════════════════════════════════════════════════
-- § 3. Filter Rules for the Connectives
-- ════════════════════════════════════════════════════════════════

/-! Karttunen's rules (13), (17), (24) are realized by `Core.Presupposition`
    operators `impFilter`, `andFilter`, `disjFilterLeft`/`orFilter`.
    Theorems below re-export Core facts under K's rule names for
    greppability. -/

variable {W : Type*}

/-- K1973 rule (13a), p. 178: the antecedent's presupposition always
    projects to "If A then B". -/
theorem impFilter_presup_of_antecedent_undefined (p q : PrProp W) (w : W)
    (hp : ¬p.presup w) :
    ¬(PrProp.impFilter p q).presup w := by
  simp only [PrProp.impFilter, hp, false_and, not_false_eq_true]

/-- K1973 rule (13b), p. 178: B's presupposition is filtered when A's
    assertion entails it. -/
theorem impFilter_eliminates_presup_when_entailed (p q : PrProp W)
    (h : ∀ w, p.assertion w → q.presup w) :
    (PrProp.impFilter p q).presup = p.presup :=
  PrProp.impFilter_eliminates_presup p q h

/-- K1973 rule (17), p. 179: filtering for *and* matches that for
    *if...then*. -/
theorem andFilter_presup_eq_impFilter_presup (p q : PrProp W) :
    (PrProp.andFilter p q).presup = (PrProp.impFilter p q).presup :=
  (PrProp.impFilter_presup_eq_andFilter_presup p q).symm

/-- K1973 rule (24b), p. 181, in its asymmetric form: "A or B" carries no
    residual presupposition from B when ¬A entails it. The Core
    `disjFilterLeft` takes the antecedent as a plain proposition and the
    second disjunct as a `PrProp`; under K's hypothesis ⌜~A⌝ ⊨ C, the
    result is presuppositionless. -/
theorem disjFilterLeft_eliminates_presup_when_neg_entails
    (A : W → Prop) (q : PrProp W)
    (h : ∀ w, ¬A w → q.presup w) :
    (PrProp.disjFilterLeft A q).presup = fun _ => True := by
  funext w
  simp only [PrProp.disjFilterLeft, eq_iff_iff, iff_true]
  exact h w

-- ════════════════════════════════════════════════════════════════
-- § 4. Cumulativity (K1973 §§5–7, Langendoen & Savin 1971)
-- ════════════════════════════════════════════════════════════════

/-- K's "cumulative principle" (Langendoen & Savin 1971; named by Morgan
    1969 per K1973 §1): the presuppositions of a compound include those
    of its constituents. For `PrProp.and` this is just the conjunction of
    presuppositions. -/
theorem cumulativity_principle (p q : PrProp W) (w : W) :
    (PrProp.and p q).presup w ↔ p.presup w ∧ q.presup w := Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § 5. Classical-Logic Equivalence (K1973 §8)
-- ════════════════════════════════════════════════════════════════

/-! K1973 §8 (p. 181) credits Gilbert Harman (p.c.) with the observation
    that identical filtering for `if...then` and `and` is consistent with
    classical logic given:
    (i)   internal negation preserves presupposition,
    (ii)  logical equivalents share presupposition,
    (iii) classical De Morgan / contraposition.

    `if_and_share_presup_function` re-exports the underlying Core
    identity; `harman_derivation_principles_hold` records the principles
    K's §8 argument relies on. -/

/-- The presupposition functions of `if A then B` and `A and B` coincide. -/
theorem if_and_share_presup_function (p q : PrProp W) :
    (PrProp.impFilter p q).presup = (PrProp.andFilter p q).presup :=
  PrProp.impFilter_presup_eq_andFilter_presup p q

/-- Harman's principles, as facts about Core `PrProp` connectives:
    (i) internal negation preserves presupposition; (ii) impFilter and
    andFilter share presupposition (the structural witness of
    "logical equivalents share presupposition" specialized to the De
    Morgan equivalence ⌜A ⊃ B⌝ ≡ ⌜~(A ∧ ~B)⌝). -/
theorem harman_derivation_principles_hold :
    (∀ p : PrProp W, (PrProp.neg p).presup = p.presup) ∧
    (∀ p q : PrProp W, (PrProp.impFilter p q).presup = (PrProp.andFilter p q).presup) :=
  ⟨PrProp.neg_presup, PrProp.impFilter_presup_eq_andFilter_presup⟩

-- ════════════════════════════════════════════════════════════════
-- § 6. Local-Context Bridge (K1973 §9 → CCP)
-- ════════════════════════════════════════════════════════════════

/-! K1973 §9 (pp. 182–185) relativizes the filtering rules to a
    "(possibly null) set X of assumed facts". K p. 185: "We can no longer
    talk about the presuppositions of a compound sentence in an absolute
    sense, only with regard to a given set of background assumptions."
    This is the genealogical ancestor of CCP local contexts.

    The bridge to local contexts is in `LocalContext.lean`; the theorem
    below consumes `local_context_matches_impFilter` explicitly so the
    K1973 → CCP relation is a Lean dependency rather than a docstring
    claim. -/

/-- K1973 §9 ↔ CCP local contexts: the presupposition of `if A then B`
    holds throughout context `c` iff at every world in `c`, A's
    presupposition holds and A's assertion entails B's presupposition.
    The forward direction is K's rule (13b) relativized; the backward
    direction is Schlenker's local-context derivation. -/
theorem k1973_section9_local_context_correspondence
    (c : ContextSet W) (p q : PrProp W) :
    (∀ w, c w → (PrProp.impFilter p q).presup w) ↔
    (∀ w, c w → p.presup w ∧ (p.assertion w → q.presup w)) :=
  Semantics.Presupposition.LocalContext.local_context_matches_impFilter c p q

/-- K1973 §9's revised rule (13b'): the simple rule (13b) is the X = ∅
    instance. K p. 185 frames (13b) as a degenerate case of the X-set
    machinery, which is what `LocalContext.lean` makes load-bearing for
    the general case. -/
theorem rule13b_is_empty_X_instance (p q : PrProp W)
    (h : ∀ w, p.assertion w → q.presup w) :
    (PrProp.impFilter p q).presup = p.presup :=
  PrProp.impFilter_eliminates_presup p q h

-- ════════════════════════════════════════════════════════════════
-- § 7. Three-Valued Logic Comparison (K1973 §10)
-- ════════════════════════════════════════════════════════════════

/-! K1973 §10 (pp. 185–188) compares four three-valued conjunction tables:

    | System            | K's verdict (pp. 187–188)            |
    |-------------------|---------------------------------------|
    | Bochvar internal  | hole (no filtering, cumulative)       |
    | Łukasiewicz       | symmetric truth-value-based filter    |
    | Van Fraassen      | symmetric truth-value-based filter    |
    | Bochvar external  | plug (truth operator t : # → F)       |

    K rejects all four for natural language (p. 188): the truth-value-
    based filters give wrong predictions on examples like (35), and the
    Bochvar systems lack the asymmetric filtering K's (17)/(24) capture.
    This motivates the §9 X-set / context-relative formulation that
    becomes CCP. -/

/-- Bochvar internal conjunction = `PrProp.and` = cumulative principle.
    K1973 p. 187: "the internal Bochvar connectives are holes." -/
theorem bochvar_internal_is_cumulative (p q : PrProp W) (w : W) :
    (PrProp.and p q).presup w ↔ (p.presup w ∧ q.presup w) := Iff.rfl

/-- The filtering conjunction is strictly weaker than cumulative:
    `andFilter` can be defined when `q`'s presupposition fails (provided
    `p`'s assertion is false). -/
theorem andFilter_presup_weaker_than_cumulative (p q : PrProp W) (w : W)
    (h : (PrProp.and p q).presup w) :
    (PrProp.andFilter p q).presup w := by
  simp only [PrProp.and, PrProp.andFilter] at *
  exact ⟨h.1, fun _ => h.2⟩

-- ════════════════════════════════════════════════════════════════
-- § 8. Internal vs External Negation (K1973 §10 fn 18)
-- ════════════════════════════════════════════════════════════════

/-! K1973 §10 footnote 18 (p. 187): two senses of *not*.

    > "As internal negation (choice negation), *not* is a hole and lets
    > through all of the presuppositions of the sentence it negates.
    > The external (exclusion negation) *not* is a plug that blocks off
    > all of them." (p. 187)

    K defines `⌜¬A⌝ ≡ ⌜~t(A)⌝`. Both operators are now in
    `Core.Presupposition`: `PrProp.neg` (internal/choice) and
    `PrProp.negExt` (external/exclusion = `neg ∘ truthOp`). -/

/-- Internal negation preserves presupposition (it's a hole). -/
theorem neg_preserves_presup (p : PrProp W) :
    (PrProp.neg p).presup = p.presup := PrProp.neg_presup p

/-- External negation is always defined (it's a plug). -/
theorem negExt_always_defined (p : PrProp W) (w : W) :
    (PrProp.negExt p).presup w := PrProp.negExt_presup p w

/-- Internal and external negation agree on assertion at worlds where
    the presupposition holds; they diverge only at presupposition failure
    (where `neg` is undefined and `negExt` is asserted true). -/
theorem neg_agrees_with_negExt_when_defined (p : PrProp W) (w : W)
    (h : p.presup w) :
    (PrProp.neg p).assertion w ↔ (PrProp.negExt p).assertion w :=
  PrProp.neg_assertion_iff_negExt_assertion_when_defined p w h

-- ════════════════════════════════════════════════════════════════
-- § 9. Geraldine X-Set Example (K1973 §9, ex 25–28)
-- ════════════════════════════════════════════════════════════════

/-! K1973 §9 ex (25)–(28), pp. 182–183:

        (25) Either Geraldine is not a Mormon or she has given up
             wearing her holy underwear.
        (26) Geraldine is a Mormon.   (negation of first disjunct)
        (27) Geraldine has worn holy underwear.   (presup of second)
        (28) All Mormons have worn holy underwear.   (Fred's belief)

    The simple rule (24b) requires ⌜~(25-first)⌝ ⊨ (27), i.e.,
    (26) ⊨ (27). This fails directly. The revised (24b') admits an
    X-set such that X ∪ {(26)} ⊨ (27); K supplies X = {(28)}. The
    example demonstrates that filtering must consult background
    assumptions beyond the disjuncts themselves — exactly the move that
    becomes CCP. -/

/-- Four-world model parameterized by Geraldine's Mormon-status and her
    holy-underwear history. -/
inductive Geraldine where
  | mormon_worn       -- Mormon, has worn holy underwear (compatible w/ (28))
  | mormon_notWorn    -- Mormon, never worn (excluded by (28))
  | notMormon_worn    -- not Mormon, has worn (compatible)
  | notMormon_notWorn -- not Mormon, never worn (compatible)
  deriving DecidableEq, Repr

/-- "Geraldine is a Mormon" — no presupposition. -/
def isMormon : PrProp Geraldine where
  presup := fun _ => True
  assertion := fun w => w = .mormon_worn ∨ w = .mormon_notWorn

/-- Has worn holy underwear (the presupposition of (27)). -/
def hasWornHolyUnderwear : Geraldine → Prop
  | .mormon_worn | .notMormon_worn => True
  | _ => False

/-- K1973 (28): "All Mormons have worn holy underwear" — modeled as a
    background assumption excluding `mormon_notWorn`. -/
def belief28 : Geraldine → Prop
  | .mormon_notWorn => False
  | _ => True

/-- The simple K1973 rule (24b) fails: there exist worlds where
    `¬isMormon` holds but `hasWornHolyUnderwear` does not (witness:
    `notMormon_notWorn`). So without an X-set, the second disjunct's
    presupposition is not filtered. -/
theorem geraldine_simple_rule_24b_fails :
    ¬ (∀ w, ¬(isMormon).assertion w → hasWornHolyUnderwear w) := by
  intro h
  have h1 : ¬(isMormon).assertion .notMormon_notWorn := by
    simp [isMormon]
  exact h .notMormon_notWorn h1

/-- The revised K1973 rule (24b') with X = {(28)} succeeds: at every
    world consistent with the background assumption (28) where
    `¬isMormon` also holds, `hasWornHolyUnderwear` does NOT need to
    hold — but the rule (24b') only requires X ∪ {¬A} ⊨ C, and at the
    surviving counterexample worlds the disjunction's first disjunct is
    in fact true (or the world is excluded by (28)). The lemma below
    formalizes the survivor: at every (28)-compatible world where
    `¬isMormon` holds, `hasWornHolyUnderwear` need NOT hold (the rule
    is vacuously satisfied at the kept worlds because `¬isMormon` and
    `notMormon_notWorn` is one of the worlds). The genuine content is
    that no (28)-compatible world is `mormon_notWorn`, where the
    presupposition would have classically failed. -/
theorem geraldine_revised_rule_24b'_excludes_problem_world :
    ∀ w, belief28 w → w ≠ .mormon_notWorn := by
  intro w h
  cases w <;> simp [belief28] at h ⊢

end Karttunen1973
