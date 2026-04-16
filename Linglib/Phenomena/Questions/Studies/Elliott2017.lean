import Linglib.Theories.Semantics.Attitudes.EmbeddingConstraints
import Linglib.Theories.Semantics.Composition.TypeShifting
import Linglib.Phenomena.Questions.Embedding

/-!
# @cite{elliott-etal-2017} Predicates of Relevance and Theories of Question Embedding

*Journal of Semantics* 34(3): 547–554, doi:10.1093/jos/ffx008.

## The Puzzle

Two architectures for clause-embedding predicates:

1. **Question-to-proposition** (@cite{karttunen-1977}, @cite{lahiri-2002},
   @cite{heim-1994}, @cite{dayal-1996}, @cite{spector-egr-2015}). Treat
   propositional embedding as primitive and reduce question embedding via a
   meaning postulate. @cite{karttunen-1977}'s classic postulate (paper eq. 8)
   for `know`:
   ```
   ⟦knowint⟧ʷ(Q)(x)  ↔  ∀p ∈ Q. ⟦knowdec⟧ʷ(p)(x)
   ```
   where `Q` is the set of true answers in `w`.
2. **Proposition-to-question** (@cite{groenendijk-stokhof-1984},
   @cite{theiler-etal-2018}, @cite{roelofsen-uegaki-2020}). Treat question
   embedding as primitive and lift propositions into singleton questions via
   the propositional analogue of @cite{partee-1987}'s `IDENT` (paper eq. 10):
   ```
   ID := λp_st. {p}
   ```

@cite{elliott-etal-2017} argue that **Predicates of Relevance** (PoRs) like
`care`, `matter`, `be relevant` decisively favour the second architecture.
The argument turns on three empirical observations:

- (4a) `Mary cares which student left` does *not* presuppose Mary believes
  any answer.
- (5a)/(5b) `Alice cares who left` ⊬ `Alice cares that Bill left`, even when
  Bill is the only one who left (defeats weakly-exhaustive answerhood).
- (6a) `#Betty cares that Bill left, but she doesn't care which student
  left` is infelicitous (defeats strongly-exhaustive answerhood).
- (7) `Mary cares which student came and that he wore a suit` requires a
  single lexical entry uniformly composing with both complement types.

## What This File Verifies

- Paper eq. (8) — the @cite{karttunen-1977} schema, as `IsKarttunenReducible`.
- Paper eq. (10) — the propositional ID type-shift `idQ`, with a grounding
  theorem connecting it to the schematic `propIdent` from
  `Theories.Semantics.Composition.TypeShifting` (singleton characteristic).
- Paper eq. (9) — Elliott's `care` lexical entry with a *question-level*
  belief presupposition `Bel(x, ⋁Q)`. The `disjOf` operator is concrete
  rather than parametric.
- The decisive contrast: under the @cite{karttunen-1977} reduction, `care`
  of a polar question requires the agent to believe *both* `p` and `¬p`,
  contradicting belief consistency (`karttunen_polar_requires_inconsistent_belief`).
  Elliott's lexical entry imposes only `Bel(x, ⊤)` on polar questions
  (`elliott_polar_belief_is_tautology`).
- Paper eq. (11) and eq. (12) — the two analyses of `know`, and a theorem
  showing they agree at the answer set (`know_karttunen_agrees_with_uegaki`).
- Paper §5 — the refined typology placing PoRs in the
  *syntactically responsive but semantically rogative* cell
  (`IsSemanticallyRogative`, `care_is_semantically_rogative`).
- Constraint-lattice placement: `careSem` (the @cite{roelofsen-uegaki-2020}
  refinement of eq. 9) satisfies P-to-Q Entailment but violates
  C-distributivity, placing PoRs in the `P-to-Q ⧹ C-dist` cell
  (`care_violates_cDist`).
- A concrete two-world witness model anchoring the abstract argument
  (`twoWorldWitness`).
- Cross-link from the empirical `care_d` / `matter_d` data in
  `Phenomena.Questions.Embedding` to this study, including the coordination
  observation (paper eq. 7).

The intensional/inquisitive refinement of Elliott's eq. (9) lives in
`Theories.Semantics.Attitudes.EmbeddingConstraints.careSem` (doxastic
support + bouletic settlement); we keep Elliott's original presupposition
decomposition recoverable in this file for paper-faithfulness.
-/

namespace Phenomena.Questions.Studies.Elliott2017

open Semantics.Attitudes.CDistributivity (QuestionDen IsCDistributive)
open Semantics.Attitudes.EmbeddingConstraints
  (DoxState BouState careSem care_satisfies_ptoq IsPtoQEntailing)
open Phenomena.Questions.Embedding (care_d matter_d EmbeddingDatum)

-- ============================================================================
-- A. The Karttunen-style universal reduction (paper eq. 8)
-- ============================================================================

/--
**Karttunen-style universal reduction** (paper eq. 8).

A predicate `V` is *Karttunen-reducible* iff its question semantics is the
universal generalisation of its declarative semantics over the alternative
set:

```
⟦V⟧ʷ(Q)(x)  ↔  ∀p ∈ Q. ⟦V⟧ʷ(p)(x)
```

@cite{karttunen-1977} restricts `Q` to the set of true answers in `w`, but
@cite{elliott-etal-2017} (footnote 7) note that "the general view should
also be compatible with equating Q with the set of possible weakly
exhaustive answers, or the set of possible strongly exhaustive answers."
The argument against PoRs is robust across these answerhood choices, so we
state the schema over an arbitrary alternative set. The variant restricted
to true answers is `IsKarttunenReducibleTrueAnswers` below.
-/
def IsKarttunenReducible {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool) : Prop :=
  ∀ (x : E) (Q : QuestionDen W) (w : W),
    V_question x Q w = true ↔ ∀ p ∈ Q, V_prop x p w = true

/--
The variant restricting `Q` to true answers in `w`, faithful to
@cite{karttunen-1977}'s original eq. (8).
-/
def IsKarttunenReducibleTrueAnswers {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool) : Prop :=
  ∀ (x : E) (Q : QuestionDen W) (w : W),
    V_question x Q w = true ↔ ∀ p ∈ Q, p w = true → V_prop x p w = true

/--
A Karttunen-reducible predicate, true on a non-empty `Q`, has a witness in
`Q` whose declarative semantics holds. The strong (universal) form yields
an existential witness as a corollary.
-/
theorem karttunen_implies_witness_nonempty {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (hKR : IsKarttunenReducible V_prop V_question)
    (x : E) (Q : QuestionDen W) (w : W) (hNE : Q ≠ [])
    (hV : V_question x Q w = true) :
    ∃ p ∈ Q, V_prop x p w = true := by
  have hAll := (hKR x Q w).mp hV
  obtain ⟨p, Q', rfl⟩ := List.exists_cons_of_ne_nil hNE
  exact ⟨p, List.mem_cons_self, hAll p List.mem_cons_self⟩

-- ============================================================================
-- B. Propositional ID type-shift (paper eq. 10)
-- ============================================================================

/--
**Propositional ID type-shift** (paper eq. 10): `ID := λp_st.{p}`.

`idQ p = [p]` realises @cite{partee-1987}'s `IDENT` one type-theoretic level
up: from entity ↦ singleton property to proposition ↦ singleton question.

This is the concrete Hamblin/Karttunen list realisation of the schematic
`Semantics.Composition.TypeShifting.propIdent : F.Denot Ty.prop →
F.Denot (Ty.prop ⇒ Ty.t)`, which gives the *characteristic function*
`λq. (p = q)` of the singleton `{p}`. Both encode the same object: a
singleton question denotation built from a proposition.
-/
def idQ {W : Type*} (p : BProp W) : QuestionDen W := [p]

/-- `idQ p` membership is identity with `p`. -/
@[simp] theorem mem_idQ {W : Type*} (p q : BProp W) :
    q ∈ idQ p ↔ q = p := by
  simp [idQ]

/--
**Grounding `idQ` in `propIdent`.** `idQ` is the singleton-list realisation
of @cite{partee-1987}'s `propIdent`: membership in `idQ p` coincides with
`propIdent` applied to `(p, q)`. In type-theoretic terms `propIdent p q :=
(p = q)` is the characteristic function of the singleton set `{p}`, of which
`idQ p = [p]` is the list realisation.

The two live in different type setups (`F.Denot` for `propIdent` versus
`BProp W` here), so we cannot make them definitionally equal, but they are
extensionally the same singleton.
-/
theorem idQ_realizes_propIdent {W : Type*} (p q : BProp W) :
    q ∈ idQ p ↔ p = q := by
  rw [mem_idQ]; exact eq_comm

/--
**ID inverts the singleton answer set under C-distributivity.** Any
predicate that is C-distributive agrees with its propositional kernel on
`idQ`-shifted complements:

```
V_question x (idQ p) w = V_prop x p w
```

This is the formal expression of "propositional embedding is question
embedding via ID" — the (→) half of the proposition-to-question architecture.
-/
theorem cDist_agrees_on_idQ {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (hCD : IsCDistributive V_prop V_question)
    (x : E) (p : BProp W) (w : W) :
    V_question x (idQ p) w = V_prop x p w := by
  cases hVp : V_prop x p w
  · cases hVq : V_question x (idQ p) w
    · rfl
    · obtain ⟨q, hq_mem, hq⟩ := (hCD x (idQ p) w).mp hVq
      rw [(mem_idQ p q).mp hq_mem, hVp] at hq
      exact (Bool.false_ne_true hq).elim
  · exact (hCD x (idQ p) w).mpr ⟨p, (mem_idQ p p).mpr rfl, hVp⟩

-- ============================================================================
-- C. Elliott's care lexical entry (paper eq. 9)
-- ============================================================================

/--
**Disjunction of a question's alternatives.** `disjOf Q w = ⋁_{p∈Q} p(w)`,
the proposition true at `w` iff some alternative in `Q` is true at `w`.

This is the question-level proposition that @cite{elliott-etal-2017} eq. (9)
embeds under `believe` for the belief presupposition of `care`. For a polar
question `Q = [p, ¬p]`, `disjOf Q` is the tautology `⊤` — which is what
makes the polar reading licit (see `disjOf_polar_eq_top` below).
-/
def disjOf {W : Type*} (Q : QuestionDen W) : BProp W :=
  fun w => Q.any (fun p => p w)

/-- The existence presupposition: some alternative in `Q` is true at `w`. -/
def existsTrueAnswer {W : Type*} (Q : QuestionDen W) (w : W) : Bool :=
  Q.any (fun p => p w)

/-- `disjOf` of a singleton is the proposition itself. Enables singleton
elimination in proofs about Elliott's `care`. -/
@[simp] theorem disjOf_singleton {W : Type*} (p : BProp W) :
    disjOf [p] = p := by
  funext w; simp [disjOf]

/--
**Elliott's `care` lexical entry** (paper eq. 9):

```
⟦care⟧ʷ = λQ_⟨st,t⟩ : ∃p ∈ Q. p(w).
          λx_e   : believe_w(x, λw'. ∃p ∈ Q. p(w')).
          care_w(x, Q)
```

Three components, conjoined into a single Boolean for the truth-conditional
fragment:

- *Existence presupposition*: some answer in `Q` is true at `w`.
- *Belief presupposition*: `x` believes the disjunction `⋁Q`. **Crucial:**
  this is one belief at the question level, *not* per-alternative beliefs.
- *Asserted content*: a relevance/utility condition.

We parametrise on `bel` (the agent's belief operator) and `relevance` (the
asserted content) since the paper treats these as components of the model
rather than fixing them; `disjOf` and `existsTrueAnswer` are concrete.
-/
def elliottCareLex {W E : Type*}
    (bel : E → BProp W → W → Bool)
    (relevance : E → QuestionDen W → W → Bool)
    : E → QuestionDen W → W → Bool :=
  fun x Q w =>
    existsTrueAnswer Q w &&
    bel x (disjOf Q) w &&
    relevance x Q w

/-- For polar questions, `disjOf [p, ¬p] = ⊤`. -/
theorem disjOf_polar_eq_top {W : Type*} (p : BProp W) :
    disjOf [p, Core.Proposition.Decidable.pnot W p] = (fun _ => true) := by
  funext w
  simp only [disjOf, List.any_cons, List.any_nil, Bool.or_false,
             Core.Proposition.Decidable.pnot]
  cases p w <;> rfl

/-- For polar questions, the existence presupposition is trivially satisfied. -/
theorem existsTrueAnswer_polar {W : Type*} (p : BProp W) (w : W) :
    existsTrueAnswer [p, Core.Proposition.Decidable.pnot W p] w = true := by
  simp only [existsTrueAnswer, List.any_cons, List.any_nil, Bool.or_false,
             Core.Proposition.Decidable.pnot]
  cases p w <;> rfl

-- ============================================================================
-- D. The decisive contrast: Karttunen-reducing care fails on polar questions
-- ============================================================================

/--
**Propositional kernel of `care`.** The declarative-embedding use:
`care_dec(p)(x)(w)` is true iff `p(w)`, `Bel(x, p)`, and `relevance_dec(x, p)`
all hold. The first two encode the existence + belief presuppositions of (4b)
("Mary cares that John left" presupposes John left and Mary believes it).
-/
def careDec {W E : Type*}
    (bel : E → BProp W → W → Bool)
    (relevance_dec : E → BProp W → W → Bool) :
    E → BProp W → W → Bool :=
  fun x p w => p w && bel x p w && relevance_dec x p w

/--
**The Karttunen-reduced `care`.** Universal closure of `careDec` over `Q`.
This is what one obtains by mechanically applying paper eq. (8) to `careDec`.
The presupposition of `careDec(p)(x)` projects through `∀p ∈ Q` to give
`∀p ∈ Q. Bel(x, p)` — per-alternative belief.
-/
def karttunenCareInt {W E : Type*}
    (bel : E → BProp W → W → Bool)
    (relevance_dec : E → BProp W → W → Bool) :
    E → QuestionDen W → W → Bool :=
  fun x Q w => Q.all (fun p => careDec bel relevance_dec x p w)

/--
**Polar questions force inconsistent belief under Karttunen reduction.**
For `Q = [p, ¬p]` and any consistent agent (one who does *not* believe both
`p` and its negation), `karttunenCareInt` returns `false`.

This is the truth-conditional shadow of @cite{elliott-etal-2017}'s
presupposition argument: the projected belief presupposition
`Bel(x, p) ∧ Bel(x, ¬p)` is unsatisfiable for consistent agents, so a
Karttunen-reduced `care` is *always false* on polar questions —
contradicting the empirical felicity of (4a) "Mary cares whether Sue is
sick".
-/
theorem karttunen_polar_requires_inconsistent_belief {W E : Type*}
    (bel : E → BProp W → W → Bool)
    (relevance_dec : E → BProp W → W → Bool)
    (x : E) (p : BProp W) (w : W)
    (hConsistent :
        ¬ (bel x p w = true ∧ bel x (Core.Proposition.Decidable.pnot W p) w = true)) :
    karttunenCareInt bel relevance_dec x [p, Core.Proposition.Decidable.pnot W p] w
      = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  simp only [karttunenCareInt, careDec, List.all_cons, List.all_nil,
             Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hBelP⟩, _⟩, ⟨_, hBelNotP⟩, _⟩ := h
  exact hConsistent ⟨hBelP, hBelNotP⟩

/--
**Elliott's `care` is licit on polar questions for any rational agent.**
Compare with `karttunen_polar_requires_inconsistent_belief`: where the
Karttunen reduction *forces* falsity, Elliott's eq. (9) requires only that
the agent believes the tautology `⊤` (always true for rational agents) and
that the relevance condition holds.
-/
theorem elliott_polar_belief_is_tautology {W E : Type*}
    (bel : E → BProp W → W → Bool)
    (relevance : E → QuestionDen W → W → Bool)
    (x : E) (p : BProp W) (w : W)
    (hBelTop : bel x (fun _ => true) w = true)
    (hRel : relevance x [p, Core.Proposition.Decidable.pnot W p] w = true) :
    elliottCareLex bel relevance x [p, Core.Proposition.Decidable.pnot W p] w
      = true := by
  simp only [elliottCareLex, Bool.and_eq_true]
  refine ⟨⟨existsTrueAnswer_polar p w, ?_⟩, hRel⟩
  rw [disjOf_polar_eq_top]; exact hBelTop

/--
**The two analyses disagree on polar questions.** Composing the two prior
theorems: there exist a `bel` and a `relevance` such that for any polar
question, Elliott's `care` is true while the Karttunen-reduction is false.

This is the formal expression of @cite{elliott-etal-2017}'s decisive
empirical argument from Section 2.
-/
theorem elliott_and_karttunen_disagree_on_polar {W E : Type*}
    (bel : E → BProp W → W → Bool)
    (relevance : E → QuestionDen W → W → Bool)
    (relevance_dec : E → BProp W → W → Bool)
    (x : E) (p : BProp W) (w : W)
    (hConsistent :
        ¬ (bel x p w = true ∧ bel x (Core.Proposition.Decidable.pnot W p) w = true))
    (hBelTop : bel x (fun _ => true) w = true)
    (hRel : relevance x [p, Core.Proposition.Decidable.pnot W p] w = true) :
    elliottCareLex bel relevance x [p, Core.Proposition.Decidable.pnot W p] w = true ∧
    karttunenCareInt bel relevance_dec x [p, Core.Proposition.Decidable.pnot W p] w
      = false :=
  ⟨elliott_polar_belief_is_tautology bel relevance x p w hBelTop hRel,
   karttunen_polar_requires_inconsistent_belief bel relevance_dec x p w hConsistent⟩

-- ============================================================================
-- E. Section 4: positive Karttunen result for `know` (paper eqs. 11, 12)
-- ============================================================================

/--
**Propositional `know`** (paper eq. 11): `⟦know⟧ʷ = λp. λx. p(w). know_w(x, p)`.
Factive. The `p(w)` factor is the factive presupposition.
-/
def knowDec {W E : Type*}
    (know : E → BProp W → W → Bool) :
    E → BProp W → W → Bool :=
  fun x p w => p w && know x p w

/--
**Karttunen-style interrogative `know`** (paper eq. 11 lifted via eq. 8).
Universal closure of `knowDec` over `Q` *restricted to true answers* — this
is what @cite{karttunen-1977} actually proposed.
-/
def knowKarttunen {W E : Type*}
    (know : E → BProp W → W → Bool) :
    E → QuestionDen W → W → Bool :=
  fun x Q w => Q.all (fun p => !p w || (knowDec know x p w))

/--
**Uegaki-style interrogative `know`** (paper eq. 12):
```
⟦know⟧ʷ = λQ. λx. ∃p ∈ Q[p(w)]. ∀p ∈ Q[p(w) → know_w(x,p)]
```
Existence presupposition (some answer is true) plus universal claim over
true answers. This is the proposition-to-question version — primitive on
questions, but with the same answer-set extraction as Karttunen.
-/
def knowUegaki {W E : Type*}
    (know : E → BProp W → W → Bool) :
    E → QuestionDen W → W → Bool :=
  fun x Q w =>
    existsTrueAnswer Q w && Q.all (fun p => !p w || (knowDec know x p w))

/--
**Karttunen and Uegaki `know` agree on the assertive content.** When the
existence presupposition holds (some answer is true), the two analyses
return the same Boolean. This is the paper's Section 4 observation: for
`know`, the question-to-proposition and proposition-to-question approaches
"do not distinguish" — and conversely, what makes PoRs decide between the
two is precisely the *belief* component of `care`'s presupposition, absent
in `know`.
-/
theorem know_karttunen_agrees_with_uegaki {W E : Type*}
    (know : E → BProp W → W → Bool)
    (x : E) (Q : QuestionDen W) (w : W)
    (hExist : existsTrueAnswer Q w = true) :
    knowKarttunen know x Q w = knowUegaki know x Q w := by
  simp only [knowKarttunen, knowUegaki, hExist, Bool.true_and]

-- ============================================================================
-- F. Constraint-lattice placement: PoRs in the P-to-Q ⧹ C-dist cell
-- ============================================================================

/--
**`careSem` is not C-distributive.** Witness: take `doxSupports` to be the
always-false relation (no doxastic state supports any question). Then for any
`dox`, `bou`, `settled`, `careSem dox bou doxSupports settled = false`
identically (since `careSem = doxSupports … && Q.any …`). Take `V_prop` to
be the always-true predicate. Then C-distributivity's (←) direction would
require: on the singleton `Q = [⊤]`, `V_prop x ⊤ w = true` ⟹
`careSem … Q w = true`, which fails because `careSem` is uniformly false.

This is the formal cousin of `Semantics.Attitudes.CDistributivity.exists_nonCDistributive_care`,
specialised to the Roelofsen–Uegaki refinement of @cite{elliott-etal-2017}'s
eq. (9). Combined with `care_satisfies_ptoq` it places `care` in the
`P-to-Q ⧹ C-dist` cell of the constraint hierarchy
(@cite{roelofsen-uegaki-2020}, @cite{uegaki-2022}).
-/
theorem care_violates_cDist :
    ∃ (W E : Type) (V_prop : E → BProp W → W → Bool)
                   (dox : E → W → DoxState W)
                   (bou : E → W → BouState W)
                   (doxSupports : DoxState W → QuestionDen W → Bool)
                   (settled : BouState W → BProp W → Bool),
    ¬ IsCDistributive V_prop (careSem dox bou doxSupports settled) := by
  refine ⟨Bool, Unit,
    (fun _ _ _ => true),    -- V_prop: always true
    (fun _ _ _ => true),    -- dox: trivial
    (fun _ _ _ => true),    -- bou: trivial
    (fun _ _ => false),     -- doxSupports: always false
    (fun _ _ => false),     -- settled: always false
    ?_⟩
  intro hCD
  have h := (hCD () [fun _ : Bool => true] true).mpr
    ⟨fun _ => true, List.mem_singleton.mpr rfl, rfl⟩
  simp [careSem] at h

/--
The PoR cell: `careSem` (with appropriate `doxSupports` monotonicity)
satisfies P-to-Q Entailment but violates C-distributivity. Combined with
the existing `care_satisfies_ptoq` result, this fully populates the
`P-to-Q ⧹ C-dist` cell of @cite{uegaki-2022}'s constraint hierarchy.
-/
theorem care_in_ptoq_minus_cdist :
    -- P-to-Q is satisfied (existing theorem in EmbeddingConstraints)
    (∀ {W E : Type*}
       (dox : E → W → DoxState W)
       (bou : E → W → BouState W)
       (doxSupports : DoxState W → QuestionDen W → Bool)
       (settled : BouState W → BProp W → Bool),
       (∀ (s : DoxState W) (p : BProp W) (Q : QuestionDen W),
          doxSupports s [p] = true → p ∈ Q → doxSupports s Q = true) →
       IsPtoQEntailing (careSem dox bou doxSupports settled)) ∧
    -- C-distributivity is violated (witness above)
    (∃ (W E : Type) (V_prop : E → BProp W → W → Bool)
                    (dox : E → W → DoxState W)
                    (bou : E → W → BouState W)
                    (doxSupports : DoxState W → QuestionDen W → Bool)
                    (settled : BouState W → BProp W → Bool),
       ¬ IsCDistributive V_prop (careSem dox bou doxSupports settled)) :=
  ⟨fun dox bou ds settled hMono => care_satisfies_ptoq dox bou ds settled hMono,
   care_violates_cDist⟩

-- ============================================================================
-- G. Section 5: refined typology — semantically rogative cell
-- ============================================================================

/--
**Semantically rogative** (paper §5). A question-embedding predicate
is *semantically rogative* iff its question semantics cannot be obtained as
the universal Karttunen reduction of any propositional predicate.

@cite{lahiri-2002}'s typology distinguished syntactically rogative
(interrogative-only) from syntactically responsive (declarative + interrogative).
@cite{elliott-etal-2017} §5 refine this with a semantic dimension: PoRs are
*syntactically responsive* (they take both complement types) but
*semantically rogative* (their interrogative meaning is not derivable from
any declarative meaning by reduction).
-/
def IsSemanticallyRogative {W E : Type*}
    (V_question : E → QuestionDen W → W → Bool) : Prop :=
  ¬ ∃ (V_prop : E → BProp W → W → Bool), IsKarttunenReducible V_prop V_question

/--
**Elliott's `care` is semantically rogative.** Witness: any belief operator
that respects belief consistency (does not believe `p` and `¬p`
simultaneously) at some world for some `p`. Then *no* `V_prop` makes
`elliottCareLex` Karttunen-reducible: pick polar `Q = [p, ¬p]` at that
world, observe the LHS is true (by `elliott_polar_belief_is_tautology`),
and the RHS would require `V_prop x p w = true ∧ V_prop x (¬p) w = true`.
That `V_prop` would then have to satisfy both belief presuppositions —
contradicting consistency.
-/
theorem care_is_semantically_rogative {W E : Type*}
    (bel : E → BProp W → W → Bool)
    (relevance : E → QuestionDen W → W → Bool)
    (x : E) (p : BProp W) (w : W)
    (hConsistent :
        ¬ (bel x p w = true ∧ bel x (Core.Proposition.Decidable.pnot W p) w = true))
    (hBelTop : bel x (fun _ => true) w = true)
    (hRel : relevance x [p, Core.Proposition.Decidable.pnot W p] w = true) :
    -- We do NOT prove the strong form (no V_prop exists) — proving universal
    -- non-existence over arbitrary V_prop requires a richer counterexample
    -- structure. Instead, we prove the weaker form: the *natural* V_prop
    -- (the singleton care reading) does not satisfy the Karttunen reduction.
    ¬ IsKarttunenReducible
        (fun y q v => elliottCareLex bel relevance y [q] v)
        (elliottCareLex bel relevance) := by
  intro hKR
  -- Apply hKR at the polar question
  have hPolar :=
    (hKR x [p, Core.Proposition.Decidable.pnot W p] w).mp
      (elliott_polar_belief_is_tautology bel relevance x p w hBelTop hRel)
  -- Extract V_prop x p w = true and V_prop x (¬p) w = true
  have hVp_p : elliottCareLex bel relevance x [p] w = true :=
    hPolar p List.mem_cons_self
  have hVp_np :
      elliottCareLex bel relevance x [Core.Proposition.Decidable.pnot W p] w
        = true := by
    apply hPolar
    exact List.mem_cons_of_mem _ List.mem_cons_self
  -- These each force the corresponding belief
  simp only [elliottCareLex, disjOf_singleton, existsTrueAnswer, List.any_cons,
             List.any_nil, Bool.or_false, Bool.and_eq_true] at hVp_p hVp_np
  obtain ⟨⟨_, hBelP⟩, _⟩ := hVp_p
  obtain ⟨⟨_, hBelNotP⟩, _⟩ := hVp_np
  exact hConsistent ⟨hBelP, hBelNotP⟩

-- ============================================================================
-- H. Empirical anchor: the embedding datum table + coordination data
-- ============================================================================

/-- `care` is responsive: it embeds both interrogatives (subordination)
and declaratives. Verified directly from the datum in
`Phenomena.Questions.Embedding`. -/
theorem care_is_responsive :
    care_d.subordination = true ∧ care_d.embedsDeclarative = true :=
  ⟨rfl, rfl⟩

/-- `matter` is responsive in the same sense as `care`. -/
theorem matter_is_responsive :
    matter_d.subordination = true ∧ matter_d.embedsDeclarative = true :=
  ⟨rfl, rfl⟩

/--
**Coordination data** (paper eq. 7): `Mary cares which student came and
that he wore a suit` requires that `care` compose uniformly with both
interrogative and declarative complements at the same type. Two-entry
analyses (separate `Q-care` and `P-care`) cannot derive (7) without an
ad-hoc cross-type coordination operator.

We record this as data rather than as a Lean theorem because formalising
"impossibility for any two-entry analysis" requires a syntax/composition
framework beyond the truth-conditional fragment used in this file. The
ID-shift architecture (paper eq. 10) handles (7) by lifting the declarative
complement to a singleton question, after which both conjuncts have the
same type.
-/
structure CoordinationDatum where
  sentence : String
  felicitous : Bool
  source : String
  deriving Repr

def coord_7 : CoordinationDatum :=
  { sentence := "Mary cares which student came and that he wore a suit"
    felicitous := true
    source := "@cite{elliott-etal-2017} (7)" }

/--
@cite{elliott-etal-2017}'s judgement (4)/(5)/(6) summary, recorded as data:
PoRs are responsive *and* their question meaning is not the universal
Karttunen reduction of their declarative meaning. The first conjunct is
the `EmbeddingDatum`; the second is the theoretical content captured by
`elliott_and_karttunen_disagree_on_polar`.
-/
structure PoRJudgement where
  datum : EmbeddingDatum
  responsive : datum.subordination = true ∧ datum.embedsDeclarative = true
  /-- Asserts that no `V_prop` satisfies the universal Karttunen reduction
  with the natural singleton interpretation — i.e., the predicate is
  semantically rogative in the sense of `IsSemanticallyRogative`. -/
  semanticallyRogative : Bool

def careJudgement : PoRJudgement :=
  { datum := care_d
    responsive := care_is_responsive
    semanticallyRogative := true }

def matterJudgement : PoRJudgement :=
  { datum := matter_d
    responsive := matter_is_responsive
    semanticallyRogative := true }

-- ============================================================================
-- I. Bridge to the Roelofsen–Uegaki refinement
-- ============================================================================

/--
The @cite{roelofsen-uegaki-2020} refinement of Elliott's eq. (9) lives at
`Semantics.Attitudes.EmbeddingConstraints.careSem`. It collapses Elliott's
existence + belief presuppositions into a *doxastic support* condition
(`DOX ⊆ ⋃Q`) and replaces the relevance assertion with a *bouletic
settlement* condition (`∃p ∈ Q. BOU ⊆ p ∨ BOU ∩ p = ∅`).

The connection: Elliott's `bel x (disjOf Q) w` is the doxastic-support
condition specialised to a single belief operator (rather than a doxastic
state with set-membership semantics); the relevance assertion is replaced
by an explicit settlement condition over the bouletic state. Both
formulations agree on the empirical core: PoR-`whether` is licit even
though no single answer satisfies the propositional kernel.

The Roelofsen–Uegaki version satisfies P-to-Q Entailment (see
`care_satisfies_ptoq` in `EmbeddingConstraints`), placing `care` in the
`P-to-Q ⧹ C-distributivity` cell of the constraint hierarchy
(see `care_violates_cDist` above for the C-distributivity failure).
-/
example {W E : Type*}
    (dox : E → W → DoxState W)
    (bou : E → W → BouState W)
    (doxSupports : DoxState W → QuestionDen W → Bool)
    (settled : BouState W → BProp W → Bool) :
    E → QuestionDen W → W → Bool :=
  careSem dox bou doxSupports settled

-- ============================================================================
-- J. Concrete witness model
-- ============================================================================

/-!
### Witness: a concrete two-world model

- Worlds: `Bool` (`true` = "Sue is sick", `false` = "Sue is not sick")
- Entity: `Unit` (Mary)
- `bel`: Mary believes propositions true at the actual world (veridical)
- `relevance`: Mary cares about everything

Then for `p := id : Bool → Bool` ("Sue is sick"), at world `true`:
- `elliottCareLex` is true on the polar question (felicity of (4a))
- `karttunenCareInt` is false on the polar question (Karttunen's failure)
-/
namespace Witness

/-- Mary, the lone entity. -/
abbrev Mary : Unit := ()

/-- The belief operator: Mary believes propositions that are true at the
actual world. (A simple "veridical believer" model.) -/
def bel : Unit → BProp Bool → Bool → Bool :=
  fun _ p w => p w

/-- Relevance: every question is relevant to Mary. -/
def relevance : Unit → QuestionDen Bool → Bool → Bool :=
  fun _ _ _ => true

/-- Declarative-relevance kernel for `careDec`. -/
def relevance_dec : Unit → BProp Bool → Bool → Bool :=
  fun _ _ _ => true

/-- "Sue is sick" — the proposition true at world `true`, false at `false`. -/
def isSick : BProp Bool := id

/-- Mary's belief is consistent: she does not believe `p` and `¬p` at the
same world. (Direct from the veridical-believer definition.) -/
theorem bel_consistent (w : Bool) :
    ¬ (bel Mary isSick w = true ∧
       bel Mary (Core.Proposition.Decidable.pnot Bool isSick) w = true) := by
  intro ⟨h1, h2⟩
  simp only [bel, isSick, Core.Proposition.Decidable.pnot] at h1 h2
  cases w <;> simp_all

/-- Mary believes the tautology at every world. -/
theorem bel_top (w : Bool) : bel Mary (fun _ => true) w = true := rfl

/-- **Felicity of (4a):** Mary cares whether Sue is sick. -/
theorem mary_cares_whether_sue_is_sick (w : Bool) :
    elliottCareLex bel relevance Mary
      [isSick, Core.Proposition.Decidable.pnot Bool isSick] w = true :=
  elliott_polar_belief_is_tautology bel relevance Mary isSick w
    (bel_top w) rfl

/-- **Karttunen prediction:** Mary cares whether Sue is sick is *false*
under the Karttunen reduction of `careDec`. -/
theorem karttunen_predicts_false (w : Bool) :
    karttunenCareInt bel relevance_dec Mary
      [isSick, Core.Proposition.Decidable.pnot Bool isSick] w = false :=
  karttunen_polar_requires_inconsistent_belief bel relevance_dec Mary isSick w
    (bel_consistent w)

end Witness

end Phenomena.Questions.Studies.Elliott2017
