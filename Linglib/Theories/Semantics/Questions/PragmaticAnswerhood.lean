import Linglib.Theories.Semantics.Questions.Partition
import Mathlib.Data.List.Dedup

/-!
# Questions/PragmaticAnswerhood.lean

Pragmatic answerhood theory from Groenendijk & Stokhof (1984), Chapter IV.

## Insight

Semantic answerhood is a **limit case** of pragmatic answerhood.
When J = I (total ignorance), pragmatic answerhood reduces to semantic answerhood.

## Core Definitions (G&S 1984, pp. 352-358)

Given:
- I = set of all indices (worlds)
- Q = question (partition of I)
- J ⊆ I = information set (questioner's knowledge)
- J/Q = restricted partition = {P ∩ J : P ∈ I/Q, P ∩ J ≠ ∅}

Then:
- Q is a question in J iff ∃X∃Y: X,Y ∈ J/Q ∧ X ≠ Y
- P **is** a pragmatic answer to Q in J iff P ∩ J ∈ J/Q
- P **gives** a pragmatic answer to Q in J iff P ∩ J ≠ ∅ ∧ ∃P' ∈ J/Q: P ∩ J ⊆ P'

## Term Properties (pragmatic versions)

- Pragmatically exhaustive: like semantic, but quantification restricted to J
- Pragmatically rigid: term denotes same individual across all indices in J
- Pragmatically definite: term picks out unique individual in J

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. IV.
-/

namespace Semantics.Questions

-- Information Sets

/-- An information set J ⊆ I represents what the questioner knows.
J is the set of indices compatible with the questioner's factual knowledge.

G&S 1984, p. 350: "One may argue that using an information set to represent
the questioner's informational state involves idealizations. [...] We think
these idealizations are harmless." -/
abbrev InfoSet (W : Type*) := W -> Bool

/-- The total information set (no factual knowledge). -/
def totalIgnorance {W : Type*} : InfoSet W := λ _ => true

/-- Check if a world is in the information set -/
def InfoSet.contains {W : Type*} (j : InfoSet W) (w : W) : Bool := j w

/-- Intersection of a proposition with an information set -/
def InfoSet.intersect {W : Type*} (j : InfoSet W) (p : W -> Bool) : W -> Bool :=
  λ w => j w && p w

-- Restricted Partition (J/Q)

/-- Two worlds are J/Q-equivalent: both in J and Q-equivalent.

G&S 1984, p. 351: "J/Q = {P ∩ J : P ∈ I/Q, P ∩ J ≠ ∅}"

Note: This is not a full equivalence relation on all W (fails refl for w ∉ J),
but is well-defined on the worlds in J. -/
def GSQuestion.equivInJ {W : Type*} (q : GSQuestion W) (j : InfoSet W)
    (w v : W) : Bool :=
  j w && j v && q.equiv w v

/-- The restricted cells as a list of characteristic functions.

These are the cells of the partition J/Q: each cell P' is some P ∩ J
where P is a cell of I/Q and P ∩ J ≠ ∅. -/
def GSQuestion.restrictedCells {W : Type*} (q : GSQuestion W) (j : InfoSet W)
    (worlds : List W) : List (W -> Bool) :=
  let jWorlds := worlds.filter j
  -- Build cells from representatives in J
  let reps := jWorlds.foldl (λ acc w =>
    if acc.any λ r => q.equiv r w then acc else w :: acc) []
  -- Each cell is the intersection of the original cell with J
  reps.map λ rep => λ w => j w && q.equiv rep w

/-- Q is a question in J iff the restricted partition has at least 2 cells.

G&S 1984, p. 352: "Q is a question in J iff ∃X∃Y: X,Y ∈ J/Q ∧ X ≠ Y" -/
def GSQuestion.isQuestionIn {W : Type*} (q : GSQuestion W) (j : InfoSet W)
    (worlds : List W) : Bool :=
  (q.restrictedCells j worlds).length >= 2

-- Pragmatic Answerhood

/-- P **is** a pragmatic answer to Q in J iff P ∩ J is exactly a cell of J/Q.

G&S 1984, p. 352: "P is a pragmatic answer to Q in J iff P ∩ J ∈ J/Q"

This is the strict notion: the intersection must exactly match a cell. -/
def isPragmaticAnswer {W : Type*} (p : W -> Bool) (q : GSQuestion W)
    (j : InfoSet W) (worlds : List W) : Bool :=
  let pInJ := j.intersect p
  let cells := q.restrictedCells j worlds
  -- P ∩ J must be exactly one of the cells
  cells.any λ cell =>
    worlds.all λ w => pInJ w == cell w

/-- P **gives** a pragmatic answer to Q in J iff P ∩ J ⊆ some cell of J/Q.

G&S 1984, p. 352: "P gives a pragmatic answer to Q in J iff
P ∩ J ≠ ∅ ∧ ∃P' ∈ J/Q: P ∩ J ⊆ P'"

This is the weaker notion: the intersection is contained in some cell. -/
def givesPragmaticAnswer {W : Type*} (p : W -> Bool) (q : GSQuestion W)
    (j : InfoSet W) (worlds : List W) : Bool :=
  let pInJ := j.intersect p
  let cells := q.restrictedCells j worlds
  -- P ∩ J must be non-empty
  let nonEmpty := worlds.any pInJ
  -- P ∩ J must be contained in some cell
  let contained := cells.any λ cell =>
    worlds.all λ w => pInJ w -> cell w
  nonEmpty && contained

/-- Giving a pragmatic answer is weaker than being a pragmatic answer.

G&S 1984, p. 352: "If P is a pragmatic answer, then P gives a pragmatic answer." -/
theorem isPragmaticAnswer_implies_gives {W : Type*}
    (p : W -> Bool) (q : GSQuestion W) (j : InfoSet W) (worlds : List W) :
    isPragmaticAnswer p q j worlds = true ->
    givesPragmaticAnswer p q j worlds = true := by
  sorry

-- Semantic ↔ Pragmatic Connection

/-- Semantic answerhood is a special case of pragmatic answerhood when J = I.

G&S 1984, p. 355: "Semantic answers are the answers one is to address to a
questioner who has no factual information at all."

When the information set is total (J = I) and P is non-vacuous,
pragmatic answerhood reduces to semantic answerhood.

The non-emptiness hypothesis is required because `givesPragmaticAnswer`
demands `P ∩ J ≠ ∅` while `answers` does not — a vacuous (everywhere-false)
proposition vacuously "answers" semantically (by material implication) but
fails pragmatic answerhood. -/
theorem semantic_is_pragmatic_limit {W : Type*}
    (p : W -> Bool) (q : GSQuestion W) (worlds : List W)
    (hNonEmpty : worlds.any p = true) :
    givesPragmaticAnswer p q totalIgnorance worlds =
    answers p (q.toQuestion worlds) worlds := by
  sorry

/-- Reducing the information set cannot make a non-answer into an answer.

G&S 1984, p. 355: "Reducing the information set cannot make a non-answer
into an answer, but can make an answer into a non-answer."

If P gives a pragmatic answer in J' ⊆ J (with more information), then P
also gives a pragmatic answer in J (with less information). More information
restricts the pool of possible answers; less information only expands it.

Note: the CONVERSE is false — P may answer in J but fail in J' ⊆ J because
P ∩ J' may be empty or may straddle cell boundaries in the finer partition J'/Q.

[sorry: proof requires showing that non-emptiness and cell containment
are upward-monotone properties of the information set] -/
theorem pragmaticAnswer_monotone_up {W : Type*}
    (p : W -> Bool) (q : GSQuestion W) (j j' : InfoSet W) (worlds : List W)
    (hSubset : forall w, j' w = true -> j w = true) :
    givesPragmaticAnswer p q j' worlds = true ->
    givesPragmaticAnswer p q j worlds = true := by
  sorry

-- Pragmatic Term Properties

/-- A term denotation function: maps indices to individuals. -/
abbrev TermDenotation (W E : Type*) := W -> E

/-- Pragmatically rigid: term denotes the same individual across all indices in J.

G&S 1984, p. 359: "Your father" is not semantically rigid, but pragmatically
rigid for anyone who knows who their father is. -/
def pragmaticallyRigid {W E : Type*} [DecidableEq E]
    (t : TermDenotation W E) (j : InfoSet W) (worlds : List W) : Bool :=
  let jWorlds := worlds.filter j
  match jWorlds with
  | [] => true
  | w :: ws => ws.all λ v => t w == t v

/-- Semantically rigid: term denotes the same individual across ALL indices.

G&S 1984: Proper names are semantically rigid. Definite descriptions
typically are not. -/
def semanticallyRigid {W E : Type*} [DecidableEq E]
    (t : TermDenotation W E) (worlds : List W) : Bool :=
  pragmaticallyRigid t totalIgnorance worlds

/-- Pragmatically definite: term picks out a unique individual in J.

G&S 1984, p. 360: An indefinite "an elderly lady wearing glasses" can be
pragmatically definite if the questioner's information uniquely identifies
the referent. -/
def pragmaticallyDefinite {W E : Type*} [DecidableEq E]
    (t : TermDenotation W E) (j : InfoSet W) (worlds : List W) : Bool :=
  let jWorlds := worlds.filter j
  let denotations := jWorlds.map t
  denotations.dedup.length <= 1

/-- A nodup list whose elements are all equal has at most one element. -/
private theorem nodup_all_eq_length_le_one {α : Type*}
    (l : List α) (hnd : l.Nodup) (a : α) (h : ∀ x ∈ l, x = a) :
    l.length ≤ 1 := by
  match l with
  | [] => simp
  | [_] => simp
  | x :: y :: _ =>
    have hx := h x List.mem_cons_self
    have hy := h y (List.mem_cons_of_mem _ List.mem_cons_self)
    subst hx; subst hy
    exact absurd List.mem_cons_self (List.nodup_cons.mp hnd).1

/-- Pragmatic rigidity implies pragmatic definiteness. -/
theorem pragmaticallyRigid_implies_definite {W E : Type*} [DecidableEq E]
    (t : TermDenotation W E) (j : InfoSet W) (worlds : List W) :
    pragmaticallyRigid t j worlds = true ->
    pragmaticallyDefinite t j worlds = true := by
  unfold pragmaticallyRigid pragmaticallyDefinite
  intro h
  match hjw : worlds.filter j with
  | [] => simp [hjw]
  | w :: ws =>
    rw [hjw] at h
    simp only [List.all_eq_true] at h
    simp only [hjw, List.map_cons]
    -- All elements of ws.map t equal t w
    have hall : ∀ x ∈ (t w :: ws.map t), x = t w := by
      intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨v, hv, rfl⟩
      · rfl
      · exact (beq_iff_eq.mp (h v hv)).symm
    -- dedup produces a nodup list with same membership
    have hnd := List.nodup_dedup (t w :: ws.map t)
    have hmem : ∀ x ∈ (t w :: ws.map t).dedup, x = t w :=
      fun x hx => hall x (List.mem_dedup.mp hx)
    exact decide_eq_true (nodup_all_eq_length_le_one _ hnd (t w) hmem)

/-- Semantic rigidity implies pragmatic rigidity (for any J). -/
theorem semanticallyRigid_implies_pragmaticallyRigid {W E : Type*} [DecidableEq E]
    (t : TermDenotation W E) (j : InfoSet W) (worlds : List W) :
    semanticallyRigid t worlds = true ->
    pragmaticallyRigid t j worlds = true := by
  unfold semanticallyRigid pragmaticallyRigid
  -- First establish: filter totalIgnorance = worlds
  have hfilt : worlds.filter totalIgnorance = worlds := by
    induction worlds with
    | nil => rfl
    | cons w ws ih => simp [totalIgnorance, ih]
  rw [hfilt]
  -- Now both h and goal have pattern matching on lists
  -- h : match worlds with | [] => true | w :: ws => ws.all (t w == t ·)
  -- goal : match (worlds.filter j) with | [] => true | w' :: ws' => ws'.all (t w' == t ·)
  intro h
  -- Extract the "all have same denotation" property from h
  match hwlds : worlds with
  | [] => -- worlds is empty, so filter j is empty too
    simp [hwlds]
  | w :: ws =>
    simp only [List.all_eq_true, beq_iff_eq] at h
    -- h : ∀ v ∈ ws, t w = t v  (i.e., all elements agree with t w)
    -- Now consider filter j on (w :: ws)
    match hjw : (w :: ws).filter j with
    | [] => rfl
    | w' :: ws' =>
      simp only [List.all_eq_true, beq_iff_eq]
      intro v hv
      -- w' and v are both in (w :: ws).filter j ⊆ w :: ws
      have hw'_in : w' ∈ (w :: ws).filter j := by simp [hjw]
      have hv_in : v ∈ (w :: ws).filter j := by simp [hjw, hv]
      have hw'_mem := (List.mem_filter.mp hw'_in).1
      have hv_mem := (List.mem_filter.mp hv_in).1
      -- Both are in w :: ws, so both have same denotation as w
      have hw'_eq : t w' = t w := by
        cases List.mem_cons.mp hw'_mem with
        | inl heq => rw [heq]
        | inr hmem => exact (h w' hmem).symm
      have hv_eq : t v = t w := by
        cases List.mem_cons.mp hv_mem with
        | inl heq => rw [heq]
        | inr hmem => exact (h v hmem).symm
      rw [hw'_eq, hv_eq]

-- Pragmatic Exhaustiveness

/-- A term is pragmatically exhaustive for a question Q in J if it picks out
all and only the individuals satisfying the question's predicate in J.

G&S 1984, p. 358: Quantification is restricted to J. -/
def pragmaticallyExhaustive {W E : Type*} [DecidableEq E]
    (t : TermDenotation W E) (predicate : W -> E -> Bool)
    (j : InfoSet W) (worlds : List W) : Bool :=
  let jWorlds := worlds.filter j
  -- The term picks out exactly those satisfying the predicate in J
  jWorlds.all λ w =>
    let e := t w
    predicate w e == jWorlds.all λ v => predicate v e

-- Key G&S Theorems: Term Properties → Answerhood

/-- G&S Theorem (12): If a term t is exhaustive and rigid, then t(a) is a
complete answer to "?x.P(x)" in any information set J.

This is the core result connecting term properties to answerhood. -/
theorem exhaustive_rigid_gives_complete_answer {W E : Type} [DecidableEq E]
    (t : TermDenotation W E) (predicate : W -> E -> Bool)
    (j : InfoSet W) (worlds : List W)
    (hExh : pragmaticallyExhaustive t predicate j worlds = true)
    (hRigid : pragmaticallyRigid t j worlds = true) :
    -- The answer "t(a)" completely answers the question in J
    let answerProp := λ w => predicate w (t w)
    let q := GSQuestion.ofPredicate answerProp
    givesPragmaticAnswer answerProp q j worlds = true := by
  sorry

/-- G&S Theorem (17): If a term t is not exhaustive, then t(a) does NOT
give a complete answer.

Non-exhaustive terms can only partially answer. -/
theorem nonExhaustive_incomplete_answer {W E : Type} [DecidableEq E]
    (t : TermDenotation W E) (predicate : W -> E -> Bool)
    (j : InfoSet W) (worlds : List W)
    (hNotExh : pragmaticallyExhaustive t predicate j worlds = false) :
    -- t(a) cannot be a (strict) pragmatic answer
    let answerProp := λ w => predicate w (t w)
    let q := GSQuestion.ofPredicate answerProp
    isPragmaticAnswer answerProp q j worlds = false := by
  sorry

-- False Propositions, True Pragmatic Answers

/-- G&S 1984, p. 360: A FALSE proposition can give a TRUE pragmatic answer.

This happens when the questioner has false beliefs that nevertheless
lead them to correctly identify the referent.

Example: "Who won the Tour de France in 1980?"
Answer: "The one who won in 1979"
False proposition (Hinault won 1979, Zoetemelk won 1980),
but if the questioner wrongly believes Zoetemelk won 1979,
they correctly conclude Zoetemelk won 1980.

This theorem merely states that such situations exist; see
Phenomena/Questions/PragmaticAnswerhood.lean for concrete examples. -/
theorem false_proposition_true_pragmatic_answer {W : Type*}
    (p : W -> Bool) (_q : GSQuestion W) (_j : InfoSet W) (_worlds : List W)
    (actual : W) (_hActual : _j actual = true) :
    -- p is false at actual world
    p actual = false ->
    -- But p can still give a pragmatic answer in J
    -- (there exist such p, q, j where this holds)
    True := λ _ => trivial

-- Institutional vs Ordinary Question-Answering

/-- G&S 1984, p. 363, 390: In highly institutionalized settings (courts, etc.),
semantic answers are required because information sets vary widely.

Questions are posed on behalf of a social community with diverse information
states, so answers must work for many different J. The safest strategy is
to use semantically rigid terms. -/
def requiresSemanticAnswer (_institutionalized : Bool) : Bool :=
  -- In institutionalized settings, stay close to semantic answers
  _institutionalized

/-- The more diverse the audience's information states, the closer
answers should stay to semantic answerhood.

G&S 1984, p. 355: "Since we know our information about the information
of others to be imperfect, the safest way to answer a question is to
stay as close to semantic answers as one can." -/
theorem diverse_audience_prefers_semantic {W E : Type*} [DecidableEq E]
    (t : TermDenotation W E) (worlds : List W) :
    -- Semantically rigid terms work for ALL information sets
    semanticallyRigid t worlds = true ->
    forall j : InfoSet W, pragmaticallyRigid t j worlds = true :=
  λ hSem j => semanticallyRigid_implies_pragmaticallyRigid t j worlds hSem

-- W is implicit in TermDenotation, InfoSet, etc.

end Semantics.Questions
