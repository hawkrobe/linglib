import Linglib.Core.Discourse.Accessibility
import Linglib.Phenomena.Reference.Studies.Ariel2001
import Linglib.Phenomena.Reference.Studies.KehlerRohde2013
import Linglib.Phenomena.Reference.Studies.KwonLee2026

/-!
# @cite{grosz-joshi-weinstein-1995}: Centering Theory
@cite{kameyama-1986} @cite{gordon-grosz-gilliom-1993} @cite{kehler-rohde-2013}

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
-/

set_option autoImplicit false

namespace GroszJoshiWeinstein1995

-- ════════════════════════════════════════════════════
-- § 1. Grammatical Role
-- ════════════════════════════════════════════════════

/-- Grammatical role used to rank Cf elements (@cite{kameyama-1986},
    @cite{gordon-grosz-gilliom-1993}): SUBJECT > OBJECT > OTHER.

    @cite{grosz-joshi-weinstein-1995} §5 surveys the evidence (examples
    11–14) that grammatical role is the major determinant of Cf ranking
    in English. Earlier work (@cite{sidner-1979}) used thematic role;
    @cite{kameyama-1986} argued for grammatical role over thematic. -/
inductive GrammaticalRole where
  | subject
  | object
  | other
  deriving DecidableEq, Repr

@[simp] def GrammaticalRole.rank : GrammaticalRole → Nat
  | .subject => 2
  | .object  => 1
  | .other   => 0

instance : LinearOrder GrammaticalRole :=
  LinearOrder.lift' GrammaticalRole.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [GrammaticalRole.rank])

theorem subject_gt_object : (GrammaticalRole.subject : GrammaticalRole) > .object := by decide

theorem object_gt_other : (GrammaticalRole.object : GrammaticalRole) > .other := by decide

-- ════════════════════════════════════════════════════
-- § 2. Realization, Utterance, Cb, Cf
-- ════════════════════════════════════════════════════

/-- A single noun-phrase realization: which entity it refers to, what
    grammatical role it occupies, and whether the form is pronominal.

    Centering @cite{grosz-joshi-weinstein-1995} §3 uses a "realizes"
    relation that (in general) depends on the underlying semantic theory.
    This formalization uses a binary `realized` predicate (an entity is
    in the utterance or it isn't), corresponding to the paper's "directly
    realizes" plus the simplifying assumption that all contributing NPs
    are listed. Bridging/implicit realization is left for future work,
    mirroring the paper's own §7 discussion. -/
structure Realization (E : Type) where
  entity : E
  role : GrammaticalRole
  isPronoun : Bool
  deriving Repr

/-- An utterance, abstractly: a list of NP realizations. -/
structure Utterance (E : Type) where
  realizations : List (Realization E)
  deriving Repr

namespace Utterance
variable {E : Type} [DecidableEq E]

/-- An entity is **realized** in an utterance when some realization
    refers to it (@cite{grosz-joshi-weinstein-1995} §3). -/
def Realizes (u : Utterance E) (e : E) : Prop :=
  ∃ r ∈ u.realizations, r.entity = e

/-- Bool version of `Realizes`, used internally by `cb`'s `find?` and
    by the `Decidable` instance to keep `decide` proofs fast. -/
def realizesBool (u : Utterance E) (e : E) : Bool :=
  u.realizations.any (·.entity == e)

theorem realizes_iff_realizesBool (u : Utterance E) (e : E) :
    u.Realizes e ↔ u.realizesBool e = true := by
  unfold Realizes realizesBool
  simp [List.any_eq_true]

instance (u : Utterance E) (e : E) : Decidable (u.Realizes e) :=
  decidable_of_iff _ (realizes_iff_realizesBool u e).symm

/-- An entity is **pronominalized** in an utterance when some
    realization refers to it via a pronoun. -/
def Pronominalizes (u : Utterance E) (e : E) : Prop :=
  ∃ r ∈ u.realizations, r.entity = e ∧ r.isPronoun = true

/-- Bool version of `Pronominalizes`, used by the `Decidable` instance. -/
def pronominalizesBool (u : Utterance E) (e : E) : Bool :=
  u.realizations.any (fun r => r.entity == e && r.isPronoun)

theorem pronominalizes_iff_pronominalizesBool (u : Utterance E) (e : E) :
    u.Pronominalizes e ↔ u.pronominalizesBool e = true := by
  unfold Pronominalizes pronominalizesBool
  simp [List.any_eq_true]

instance (u : Utterance E) (e : E) : Decidable (u.Pronominalizes e) :=
  decidable_of_iff _ (pronominalizes_iff_pronominalizesBool u e).symm

/-- Forward-looking centers, ranked highest-first by grammatical role.
    Realized as a three-bucket concatenation (subject ++ object ++
    other) instead of `mergeSort` so the kernel can reduce `cf` for
    `decide` proofs of concrete examples. Within each bucket, order
    follows the original `realizations` list (i.e., textual order in
    the utterance). -/
def cf (u : Utterance E) : List E :=
  let bucket (r : GrammaticalRole) : List E :=
    (u.realizations.filter (·.role == r)).map (·.entity)
  bucket .subject ++ bucket .object ++ bucket .other

/-- The top-ranked Cf element (Cp, the "preferred center"). -/
def cp (u : Utterance E) : Option E := u.cf.head?

end Utterance

/-- Backward-looking center of `cur` with respect to the previous
    utterance `prev`: the highest-ranked element of `prev.cf` that is
    realized in `cur`. `none` if no such element exists.
    @cite{grosz-joshi-weinstein-1995} §3, "Locality of Cb" claim.

    The "A unique Cb" claim of the paper (each utterance has at most
    one backward-looking center) is enforced by the *type* `Option E`,
    not by a separate theorem. -/
def cb {E : Type} [DecidableEq E] (prev cur : Utterance E) : Option E :=
  prev.cf.find? cur.realizesBool

/-- **Locality of Cb** (@cite{grosz-joshi-weinstein-1995} §4, claim 5):
    when `cb prev cur` returns some entity, that entity is in
    `prev.cf` — i.e., the backward-looking center is strictly local,
    drawn only from the previous utterance's forward-looking centers,
    never from `Cf(U_{n-2})` or earlier. -/
theorem cb_mem_prev_cf {E : Type} [DecidableEq E]
    {prev cur : Utterance E} {e : E} (h : cb prev cur = some e) :
    e ∈ prev.cf :=
  List.mem_of_find?_eq_some h

-- ════════════════════════════════════════════════════
-- § 3. Transitions and Rules
-- ════════════════════════════════════════════════════

/-- Three transition types between U_n and U_{n+1}
    (@cite{grosz-joshi-weinstein-1995} §3):

    * **continuation**: `Cb(U_{n+1}) = Cb(U_n)` AND `Cb(U_{n+1})` is
      the most-highly-ranked element of `Cf(U_{n+1})`.
    * **retaining**: `Cb(U_{n+1}) = Cb(U_n)`, but is *not* the
      most-highly-ranked element of `Cf(U_{n+1})`.
    * **shifting**: `Cb(U_{n+1}) ≠ Cb(U_n)` (including the case where
      no Cb of U_{n+1} exists, by convention). -/
inductive Transition where
  | continuation
  | retaining
  | shifting
  deriving DecidableEq, Repr

/-- @cite{grosz-joshi-weinstein-1995} **Rule 2** preference order:
    continuation > retaining > shifting. -/
@[simp] def Transition.rank : Transition → Nat
  | .continuation => 2
  | .retaining    => 1
  | .shifting     => 0

instance : LinearOrder Transition :=
  LinearOrder.lift' Transition.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [Transition.rank])

theorem continuation_gt_retaining :
    (Transition.continuation : Transition) > .retaining := by decide

theorem retaining_gt_shifting :
    (Transition.retaining : Transition) > .shifting := by decide

/-- @cite{grosz-joshi-weinstein-1995} **Rule 2** is stated at the
    *pair-of-transitions* level: a pair `(t₁, t₂)` of consecutive
    transitions is preferred over a pair `(s₁, s₂)` when its constituent
    transitions are at least as preferred (and one is strictly more so).

    The paper specifies the canonical case: a pair of continuations is
    preferred over a pair of retentions, which is preferred over a pair
    of shifts. The general pair preference uses sum-of-ranks, the
    discriminating measure consistent with these specific claims (`min`
    is a coarser alternative). -/
def pairRank (t₁ t₂ : Transition) : Nat := t₁.rank + t₂.rank

theorem rule2_continuations_preferred_over_retentions :
    pairRank .continuation .continuation > pairRank .retaining .retaining := by decide

theorem rule2_retentions_preferred_over_shifts :
    pairRank .retaining .retaining > pairRank .shifting .shifting := by decide

theorem rule2_continuations_preferred_over_shifts :
    pairRank .continuation .continuation > pairRank .shifting .shifting := by decide

/-- Classify the transition between `prev` and `cur`, given `prev`'s
    own Cb (which depends on the utterance before it).

    For the segment-initial transition `prevCb = none`, follow the
    convention used by @cite{grosz-joshi-weinstein-1995} examples
    (1)/(20): treat as a continuation when `Cb = Cp` in `cur`, as a
    retaining otherwise. The paper does not formally classify this
    "establishment" transition, but the convention preserves the
    paper's intuitive coherence labels for Discourses 1 and 20. -/
def classifyTransition {E : Type} [DecidableEq E]
    (prev cur : Utterance E) (prevCb : Option E) : Transition :=
  match cb prev cur with
  | none => .shifting
  | some curCb =>
    match prevCb with
    | none =>
      if cur.cp = some curCb then .continuation else .retaining
    | some pcb =>
      if pcb = curCb then
        if cur.cp = some curCb then .continuation else .retaining
      else .shifting

/-- @cite{grosz-joshi-weinstein-1995} **Rule 1**: if any element of
    `Cf(U_n)` is realized by a pronoun in `U_{n+1}`, then `Cb(U_{n+1})`
    is realized by a pronoun also.

    Vacuously satisfied when no Cb exists. The constraint is
    *one-directional*: it says nothing about whether the Cb *must* be
    pronominalized when no other entity is — Rule 1 only constrains
    what happens when pronominalization is used at all. -/
def Rule1Holds {E : Type} [DecidableEq E]
    (prev cur : Utterance E) : Prop :=
  match cb prev cur with
  | none => True
  | some curCb =>
    (∃ e ∈ prev.cf, cur.Pronominalizes e) → cur.Pronominalizes curCb

instance {E : Type} [DecidableEq E] (prev cur : Utterance E) :
    Decidable (Rule1Holds prev cur) := by
  unfold Rule1Holds
  cases cb prev cur <;> infer_instance

-- ════════════════════════════════════════════════════
-- § 4. Discourse 1 vs Discourse 2: the coherence contrast
-- ════════════════════════════════════════════════════

/-! Concrete examples use `String` entities for readability. Each
    discourse names its individual utterances so per-pair theorems can
    refer to them directly without recursing through a list. -/

namespace D1

/-- (1a) John went to his favorite music store to buy a piano. -/
def a : Utterance String :=
  ⟨[⟨"John", .subject, false⟩, ⟨"store", .object, false⟩,
    ⟨"piano", .other, false⟩]⟩

/-- (1b) He had frequented the store for many years. -/
def b : Utterance String :=
  ⟨[⟨"John", .subject, true⟩, ⟨"store", .object, false⟩]⟩

/-- (1c) He was excited that he could finally buy a piano. -/
def c : Utterance String :=
  ⟨[⟨"John", .subject, true⟩, ⟨"piano", .object, false⟩]⟩

/-- (1d) He arrived just as the store was closing for the day. -/
def d : Utterance String :=
  ⟨[⟨"John", .subject, true⟩, ⟨"store", .other, false⟩]⟩

end D1

namespace D2

/-- (2a) John went to his favorite music store to buy a piano. -/
def a : Utterance String :=
  ⟨[⟨"John", .subject, false⟩, ⟨"store", .object, false⟩,
    ⟨"piano", .other, false⟩]⟩

/-- (2b) It was a store John had frequented for many years. -/
def b : Utterance String :=
  ⟨[⟨"store", .subject, true⟩, ⟨"John", .object, false⟩]⟩

/-- (2c) He was excited that he could finally buy a piano. -/
def c : Utterance String :=
  ⟨[⟨"John", .subject, true⟩, ⟨"piano", .object, false⟩]⟩

/-- (2d) It was closing just as John arrived. -/
def d : Utterance String :=
  ⟨[⟨"store", .subject, true⟩, ⟨"John", .object, false⟩]⟩

end D2

/-! ### Per-pair transition predictions

    For each adjacent pair, the Cb (computed from the prior utterance)
    and the transition type follow from the formal definitions. -/

/-- Discourse 1 (a→b): John continues as Cb. -/
theorem d1_a_to_b_cb : cb D1.a D1.b = some "John" := by decide

theorem d1_a_to_b_continuation :
    classifyTransition D1.a D1.b none = .continuation := by decide

/-- Discourse 1 (b→c): John continues. -/
theorem d1_b_to_c_continuation :
    classifyTransition D1.b D1.c (cb D1.a D1.b) = .continuation := by decide

/-- Discourse 1 (c→d): John continues. -/
theorem d1_c_to_d_continuation :
    classifyTransition D1.c D1.d (cb D1.b D1.c) = .continuation := by decide

/-- Discourse 2 (a→b): the Cb is John (the only entity in `Cf(D2.a)`
    that is realized in `D2.b`), but `Cp(D2.b) = "store"` (not John),
    so this is a *retain* — already a less coherent transition than
    Discourse 1's continuation. -/
theorem d2_a_to_b_cb : cb D2.a D2.b = some "John" := by decide

theorem d2_a_to_b_retaining :
    classifyTransition D2.a D2.b none = .retaining := by decide

/-- Discourse 2 (b→c): John re-emerges as Cb (it was object in D2.b);
    in D2.c, John is also `Cp` — so this would be a continuation.
    Rule 1 is also fine here. -/
theorem d2_b_to_c_cb : cb D2.b D2.c = some "John" := by decide

theorem d2_b_to_c_continuation :
    classifyTransition D2.b D2.c (cb D2.a D2.b) = .continuation := by decide

/-- Discourse 2 (c→d): John remains Cb (was subject in D2.c, object
    in D2.d), but `Cp(D2.d) = "store"`. RETAIN, not continuation. -/
theorem d2_c_to_d_retaining :
    classifyTransition D2.c D2.d (cb D2.b D2.c) = .retaining := by decide

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
-- § 5. Discourse 15: Rule 1 violation
-- ════════════════════════════════════════════════════

namespace D15

/-- (15a) He has been acting quite odd. (Cb = John, presumed in segment.) -/
def a : Utterance String := ⟨[⟨"John", .subject, true⟩]⟩

/-- (15b) He called up Mike yesterday. (Cb = John, "He" = John.) -/
def b : Utterance String :=
  ⟨[⟨"John", .subject, true⟩, ⟨"Mike", .object, false⟩]⟩

/-- (15c) John wanted to meet him urgently. (Cb = John, "him" = Mike.)
    The Cf member Mike is pronominalized but the Cb John is *not* —
    a Rule 1 violation. -/
def c : Utterance String :=
  ⟨[⟨"John", .subject, false⟩, ⟨"Mike", .object, true⟩]⟩

end D15

theorem d15_b_to_c_cb : cb D15.b D15.c = some "John" := by decide

/-- **Rule 1 violation**: in (15c), Mike is pronominalized but the Cb
    John is realized as a proper name. The paper's diagnosis. -/
theorem discourse15_violates_rule1 :
    ¬ Rule1Holds D15.b D15.c := by decide

/-- The (a→b) pair of the same discourse satisfies Rule 1 (the only
    Cf element from (a) is John, who is pronominalized in (b) — the Cb
    is also pronominalized). The violation is local to the (b→c) step. -/
theorem d15_a_to_b_satisfies_rule1 :
    Rule1Holds D15.a D15.b := by decide

-- ════════════════════════════════════════════════════
-- § 5b. Discourses 7-10: Cf ranking + Rule 1 interaction
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
def a : Utterance String :=
  ⟨[⟨"Susan", .subject, false⟩, ⟨"Betsy", .object, false⟩,
    ⟨"hamster", .other, false⟩]⟩

/-- (b) She reminded her ...  "She" = Susan (subj), "her" = Betsy (obj). -/
def b : Utterance String :=
  ⟨[⟨"Susan", .subject, true⟩, ⟨"Betsy", .object, true⟩]⟩

/-- (7c) She asked Betsy whether she liked the gift. — "She" = Susan,
    Betsy as proper name (object). Cb = Susan, Cp = Susan ⇒ CONTINUE.
    Susan is pronominalized; Rule 1 satisfied. -/
def c7 : Utterance String :=
  ⟨[⟨"Susan", .subject, true⟩, ⟨"Betsy", .object, false⟩]⟩

/-- (8c) Betsy told her that she really liked the gift. — Betsy as
    proper name (subject), "her" = Susan. Cb = Susan (highest in Cf(b)
    realized in c), but Cp = Betsy ⇒ RETAIN. Susan as Cb pronominalized
    via "her"; Rule 1 satisfied. -/
def c8 : Utterance String :=
  ⟨[⟨"Betsy", .subject, false⟩, ⟨"Susan", .object, true⟩]⟩

/-- (9c) Susan asked her whether she liked the gift. — Susan as proper
    name (subject), "her" = Betsy. Cb = Susan, Cp = Susan ⇒ would be
    CONTINUE, but Betsy is pronominalized while Cb (Susan) is a proper
    name ⇒ Rule 1 VIOLATION. -/
def c9 : Utterance String :=
  ⟨[⟨"Susan", .subject, false⟩, ⟨"Betsy", .object, true⟩]⟩

/-- (10c) She told Susan that she really liked the gift. — "She" =
    Betsy (subj), Susan as proper name (obj). Cb = Susan (highest in
    Cf(b) realized in c). Cp = Betsy ⇒ RETAIN. Betsy is pronominalized
    while Cb (Susan) is a proper name ⇒ Rule 1 VIOLATION. -/
def c10 : Utterance String :=
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
    Rule1Holds D7_10.b D7_10.c7 := by decide

/-- Variant 8 satisfies Rule 1 (Susan as Cb pronominalized via "her"). -/
theorem d8_satisfies_rule1 :
    Rule1Holds D7_10.b D7_10.c8 := by decide

/-- **Variant 9 violates Rule 1**: Betsy is pronominalized but Cb
    (Susan) is realized as a proper name. -/
theorem d9_violates_rule1 :
    ¬ Rule1Holds D7_10.b D7_10.c9 := by decide

/-- **Variant 10 violates Rule 1**: Betsy is pronominalized but Cb
    (Susan) is realized as a proper name. The paper calls this case
    "completely unacceptable". -/
theorem d10_violates_rule1 :
    ¬ Rule1Holds D7_10.b D7_10.c10 := by decide

/-- The Rule-1 split (`d7,8 OK` vs `d9,10 violate`) tracks the paper's
    acceptability ordering: variants 7 and 8 are acceptable, 9 and 10
    are degraded. The framework predicts this directly from Rule 1
    plus the subject>object Cf ranking. -/
theorem rule1_distinguishes_variants_7_8_from_9_10 :
    (Rule1Holds D7_10.b D7_10.c7 ∧ Rule1Holds D7_10.b D7_10.c8) ∧
    (¬ Rule1Holds D7_10.b D7_10.c9 ∧ ¬ Rule1Holds D7_10.b D7_10.c10) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 6. Discourse 20: full CONTINUE / RETAIN / SHIFT pattern
-- ════════════════════════════════════════════════════

namespace D20

/-- (20a) John has been having a lot of trouble arranging his vacation. -/
def a : Utterance String := ⟨[⟨"John", .subject, false⟩]⟩

/-- (20b) He cannot find anyone to take over his responsibilities. -/
def b : Utterance String := ⟨[⟨"John", .subject, true⟩]⟩

/-- (20c) He called up Mike yesterday. -/
def c : Utterance String :=
  ⟨[⟨"John", .subject, true⟩, ⟨"Mike", .object, false⟩]⟩

/-- (20d) Mike has annoyed him a lot recently. -/
def d : Utterance String :=
  ⟨[⟨"Mike", .subject, false⟩, ⟨"John", .object, true⟩]⟩

/-- (20e) He called John at 5 AM on Friday last week. -/
def e : Utterance String :=
  ⟨[⟨"Mike", .subject, true⟩, ⟨"John", .object, false⟩]⟩

end D20

/-- The paper-stipulated transition labels b→c, c→d, d→e:
    CONTINUE, RETAIN, SHIFT. -/
theorem discourse20_b_to_c_continuation :
    classifyTransition D20.b D20.c (cb D20.a D20.b) = .continuation := by decide

theorem discourse20_c_to_d_retaining :
    classifyTransition D20.c D20.d (cb D20.b D20.c) = .retaining := by decide

theorem discourse20_d_to_e_shifting :
    classifyTransition D20.d D20.e (cb D20.c D20.d) = .shifting := by decide

/-- Rule 1 holds throughout Discourse 20 (the paper's claim). -/
theorem discourse20_rule1_a_b : Rule1Holds D20.a D20.b := by decide
theorem discourse20_rule1_b_c : Rule1Holds D20.b D20.c := by decide
theorem discourse20_rule1_c_d : Rule1Holds D20.c D20.d := by decide
theorem discourse20_rule1_d_e : Rule1Holds D20.d D20.e := by decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to @cite{kehler-rohde-2013} (Topichood)
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
-- § 8. Bridge to @cite{kwon-lee-2026} (Korean Pronouns)
-- ════════════════════════════════════════════════════

/-! @cite{kwon-lee-2026}'s Korean Exp 3 finding (null pronouns
    strongly prefer subject antecedents) is **predicted** by Centering
    Theory:

    1. Subject is the highest-ranked Cf element (`subject_gt_object`).
    2. The subject of `U_n` typically becomes the Cb of `U_{n+1}`.
    3. By Rule 1, the Cb is preferentially realized by a pronoun.
    4. In Korean, the highest-accessibility marker (most preferred
       pronominal form) is the *null* pronoun (@cite{ariel-2001}).

    Composing: subject → Cb → pronoun → null in Korean.

    The derivation is anchored on a concrete two-utterance Korean
    continuation pattern: utterance (a) introduces a subject-marked
    referent; utterance (b) refers back to it with a null pronoun. We
    show that (1) the Cb of (b) is the prior subject by the centering
    definition, (2) Rule 1 is satisfied iff the Cb is pronominalized,
    and (3) the null pronoun is the highest-accessibility Korean form,
    so it is the form most consistent with realizing the Cb pronominally
    under the universal scale. The 71% null-subject choice in
    @cite{kwon-lee-2026} Exp 3 is the empirical consequence. -/

namespace KoreanContinuation

/-- (a) Mary often took Tom to the sea. — adapted from
    @cite{kwon-lee-2026} Exp 3 stimulus pattern. -/
def utt_a : Utterance String :=
  ⟨[⟨"Mary", .subject, false⟩, ⟨"Tom", .object, false⟩,
    ⟨"sea", .other, false⟩]⟩

/-- (b) [pro] achieved the dream of becoming a sea navigator.
    Korean null subject; the realization is pronominal (the empty
    category counts as pronominal in the Centering sense). -/
def utt_b_null : Utterance String :=
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
    Rule1Holds KoreanContinuation.utt_a KoreanContinuation.utt_b_null := by
  decide

/-- Step 3: among Korean's three referential forms, the null pronoun is
    the most accessible (top of the Korean-form linear order, derived
    from `Ariel2001.AccessibilityLevel.rank` in `KwonLee2026`). -/
theorem korean_null_is_top_form :
    ∀ f : KwonLee2026.KoreanRefForm,
      f ≤ KwonLee2026.KoreanRefForm.nullPro := by
  intro f; cases f <;> decide

/-- **Centering predicts Korean's null-subject preference**: combining
    Rule 1 with Korean's accessibility-scale calibration. The Cb of a
    canonical Korean continuation is the prior subject; Rule 1 says
    the Cb is preferentially pronominal; the most-preferred-pronominal
    form in Korean is the null. The 71% empirical subject bias for null
    pronouns (@cite{kwon-lee-2026} Exp 3) is the predicted consequence
    of this composition.

    This theorem packages the empirical anchor: the subject bias for
    null exceeds chance, as Centering+accessibility theory predicts. -/
theorem korean_subject_bias_for_null_exceeds_chance :
    KwonLee2026.exp3_pro.subjectPercent > 50 := by decide

-- ════════════════════════════════════════════════════
-- § 9. Bridge to @cite{ariel-2001} (Accessibility Marking)
-- ════════════════════════════════════════════════════

open Core.Discourse.Accessibility

/-- Centering's Cb (the "currently centered" entity) corresponds to a
    high-accessibility referent on @cite{ariel-2001}'s scale. Rule 1
    predicts that the Cb's realization should use a high-accessibility
    marker — typically a pronoun (rank ≥ 13 on the 18-level scale). -/
def cbExpectedAccessibility : AccessibilityLevel := .unstressedPron

theorem cb_marker_is_high_accessibility :
    cbExpectedAccessibility.rank ≥ AccessibilityLevel.shortDefDescription.rank := by
  decide

end GroszJoshiWeinstein1995
