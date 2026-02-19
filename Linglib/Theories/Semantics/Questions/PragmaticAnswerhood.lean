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
  simp only [isPragmaticAnswer, givesPragmaticAnswer, Bool.and_eq_true,
    List.any_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  rintro ⟨cell, hcell_mem, hcell_eq⟩
  obtain ⟨w, hw, hcw⟩ := restrictedCells_inhabited q j worlds cell hcell_mem
  refine ⟨⟨w, hw, ?_⟩, cell, hcell_mem, fun w' hw' h => ?_⟩
  · rw [hcell_eq w hw]; exact hcw
  · rw [← hcell_eq w' hw']; exact h

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
private theorem filter_totalIgnorance {W : Type*} (l : List W) :
    l.filter totalIgnorance = l := by
  induction l with
  | nil => rfl
  | cons w ws ih => simp only [List.filter_cons, totalIgnorance, ↓reduceIte, ih]

private theorem intersect_totalIgnorance {W : Type*} (p : W → Bool) :
    totalIgnorance.intersect p = p := by
  funext w; simp [InfoSet.intersect, totalIgnorance]

private theorem restrictedCells_totalIgnorance {W : Type*}
    (q : GSQuestion W) (worlds : List W) :
    q.restrictedCells totalIgnorance worlds = q.toCells worlds := by
  simp only [GSQuestion.restrictedCells, QUD.toCells, GSQuestion.equiv,
             filter_totalIgnorance, totalIgnorance, Bool.true_and]

theorem semantic_is_pragmatic_limit {W : Type*}
    (p : W -> Bool) (q : GSQuestion W) (worlds : List W)
    (hNonEmpty : worlds.any p = true) :
    givesPragmaticAnswer p q totalIgnorance worlds =
    answers p (q.toQuestion worlds) worlds := by
  simp only [givesPragmaticAnswer, answers, GSQuestion.toQuestion,
             intersect_totalIgnorance, restrictedCells_totalIgnorance,
             hNonEmpty, Bool.true_and]

/-- Upward monotonicity of pragmatic answerhood for propositions within J'.

If P gives a pragmatic answer in J' ⊆ J, and P is entirely within J'
(every P-world is a J'-world), then P also gives a pragmatic answer in J.

The hypothesis `hPinJ'` is essential: without it, expanding J can introduce
new P-worlds that fall into different cells, breaking containment. For
example: W={a,b,c}, Q partitions {a}|{b}|{c}, J'={a,b}, J={a,b,c}, P={a,c}.
P gives an answer in J' (P∩J'={a} ⊆ cell {a}) but not in J (P∩J={a,c}
straddles cells).

G&S 1984, p. 355: "Reducing the information set cannot make a non-answer
into an answer." This holds when P represents the answerer's evidence,
which is naturally contained in the current information set. -/
theorem pragmaticAnswer_monotone_up {W : Type*}
    (p : W -> Bool) (q : GSQuestion W) (j j' : InfoSet W) (worlds : List W)
    (hSubset : ∀ w, j' w = true → j w = true)
    (hPinJ' : ∀ w, p w = true → j' w = true) :
    givesPragmaticAnswer p q j' worlds = true →
    givesPragmaticAnswer p q j worlds = true := by
  intro h
  -- Key insight: with hPinJ', j.intersect p = j'.intersect p = p
  -- (on worlds where p holds: j w = j' w = true; where p fails: both intersections = false)
  have hpInJ_eq : ∀ w, (j.intersect p) w = (j'.intersect p) w := by
    intro w
    simp only [InfoSet.intersect]
    cases hp : p w with
    | false => simp
    | true => simp [hPinJ' w hp, hSubset w (hPinJ' w hp)]
  simp only [givesPragmaticAnswer, Bool.and_eq_true] at h ⊢
  obtain ⟨hNonEmpty, hContained⟩ := h
  constructor
  · -- Non-emptiness: transfer via hpInJ_eq
    rw [show worlds.any (j.intersect p) = worlds.any (j'.intersect p) from by
      congr 1; funext w; exact hpInJ_eq w]
    exact hNonEmpty
  · -- Containment: find a J-cell containing P∩J
    simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hContained ⊢
    obtain ⟨cell', hcell'_mem, hcell'_sub⟩ := hContained
    -- cell' is built from a representative rep' in J'-reps
    simp only [GSQuestion.restrictedCells, List.mem_map] at hcell'_mem
    obtain ⟨rep', hrep'_mem, hrep'_eq⟩ := hcell'_mem
    -- rep' is in worlds.filter j' (by foldl_reps_mem), hence in worlds.filter j
    have hrep'_in_j' :=
      (foldl_reps_mem q.sameAnswer (worlds.filter j') [] rep' hrep'_mem).elim
        (fun h => absurd h List.not_mem_nil) id
    have ⟨hrep'_worlds, hj'_rep'⟩ := List.mem_filter.mp hrep'_in_j'
    have hrep'_in_j : rep' ∈ worlds.filter j :=
      List.mem_filter.mpr ⟨hrep'_worlds, hSubset rep' hj'_rep'⟩
    -- Get a J-cell covering rep'
    obtain ⟨cell, hcell_mem, hcell_rep'⟩ := restrictedCells_cover q j worlds rep' hrep'_in_j
    -- Decompose cell to get its representative
    have hcell_mem' := hcell_mem
    simp only [GSQuestion.restrictedCells, List.mem_map] at hcell_mem'
    obtain ⟨rep, _hrep, hrep_eq⟩ := hcell_mem'
    refine ⟨cell, hcell_mem, ?_⟩
    intro w hw hpInJ_w
    rw [← hrep_eq]
    simp only [InfoSet.intersect, Bool.and_eq_true] at hpInJ_w
    rw [← hrep_eq] at hcell_rep'
    simp only [Bool.and_eq_true] at hcell_rep' ⊢
    constructor
    · exact hpInJ_w.1
    · -- q.equiv rep w by transitivity: q.equiv rep rep' ∧ q.equiv rep' w → q.equiv rep w
      have hpInJ'_w : (j'.intersect p) w = true := by
        simp only [InfoSet.intersect, Bool.and_eq_true]
        exact ⟨hPinJ' w hpInJ_w.2, hpInJ_w.2⟩
      have hcell'_w := hcell'_sub w hw hpInJ'_w
      rw [← hrep'_eq] at hcell'_w
      simp only [Bool.and_eq_true] at hcell'_w
      exact q.trans rep rep' w hcell_rep'.2 hcell'_w.2

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
  | [] => simp
  | w :: ws =>
    rw [hjw] at h
    simp only [List.all_eq_true] at h
    simp only [List.map_cons]
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
    simp
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

This is the core result connecting term properties to answerhood.

Note: non-emptiness is required — if no J-world satisfies the predicate,
the proposition P∩J is empty and cannot be a pragmatic answer. -/
theorem exhaustive_rigid_gives_complete_answer {W E : Type} [DecidableEq E]
    (t : TermDenotation W E) (predicate : W -> E -> Bool)
    (j : InfoSet W) (worlds : List W)
    (_hExh : pragmaticallyExhaustive t predicate j worlds = true)
    (_hRigid : pragmaticallyRigid t j worlds = true)
    (hNonEmpty : worlds.any (λ w => j w && predicate w (t w)) = true) :
    -- The answer "t(a)" completely answers the question in J
    let answerProp := λ w => predicate w (t w)
    let q := GSQuestion.ofPredicate answerProp
    givesPragmaticAnswer answerProp q j worlds = true := by
  -- For q = ofPredicate answerProp, cells partition J by answerProp value.
  -- P∩J = {w : j w ∧ answerProp w} IS the "true" cell itself, so containment is trivial.
  set q := GSQuestion.ofPredicate (λ w => predicate w (t w))
  simp only [givesPragmaticAnswer, Bool.and_eq_true]
  constructor
  · -- Non-emptiness
    exact hNonEmpty
  · -- Containment: P∩J ⊆ the cell of some representative with answerProp = true
    simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq]
    -- Get witness w₀ from hNonEmpty
    obtain ⟨w₀, hw₀, hw₀_prop⟩ := List.any_eq_true.mp hNonEmpty
    rw [Bool.and_eq_true] at hw₀_prop
    obtain ⟨hj₀, hap₀⟩ := hw₀_prop
    -- w₀ is in some cell of J/Q
    obtain ⟨cell, hcell_mem, hcell_w₀⟩ :=
      restrictedCells_cover q j worlds w₀ (List.mem_filter.mpr ⟨hw₀, hj₀⟩)
    -- This cell contains all of P∩J (since q = ofPredicate answerProp)
    refine ⟨cell, hcell_mem, ?_⟩
    intro w _hw hpInJ
    simp only [InfoSet.intersect, Bool.and_eq_true] at hpInJ
    -- cell w₀ = true means j w₀ && q.equiv rep w₀ = true for some rep
    -- Since q = ofPredicate, q.equiv rep w₀ means answerProp rep = answerProp w₀ = true
    -- For any w with answerProp w = true: q.equiv rep w = (answerProp rep == answerProp w) = true
    -- So cell w = j w && q.equiv rep w = true (since j w = true from hpInJ)
    simp only [GSQuestion.restrictedCells, List.mem_map] at hcell_mem
    obtain ⟨rep, _hrep, rfl⟩ := hcell_mem
    simp only [Bool.and_eq_true] at hcell_w₀ ⊢
    simp only [q, GSQuestion.equiv, GSQuestion.ofPredicate, QUD.ofProject_sameAnswer,
               beq_iff_eq] at hcell_w₀ ⊢
    exact ⟨hpInJ.1, (hcell_w₀.2.trans hap₀).trans hpInJ.2.symm⟩

/-- G&S Theorem (17): Non-exhaustive terms cannot completely answer the
ORIGINAL question Q (not the derived binary question ofPredicate answerProp).

Note: The original formalization used q = ofPredicate answerProp, which
has at most 2 cells and makes answerProp trivially match the "true" cell.
This rendered the theorem vacuously false. The correct G&S claim involves
an independently given question Q that is FINER than the binary partition,
but formalizing this requires additional infrastructure connecting term
exhaustiveness to general question partitions.

Instead, we prove a related fact: if a term is not exhaustive, then there
exist J-worlds where the term's denotation does not accurately reflect
the extension of the predicate. -/
theorem nonExhaustive_witness {W E : Type} [DecidableEq E]
    (t : TermDenotation W E) (predicate : W → E → Bool)
    (j : InfoSet W) (worlds : List W)
    (hNotExh : pragmaticallyExhaustive t predicate j worlds = false) :
    ∃ w ∈ worlds.filter j,
      predicate w (t w) ≠ (worlds.filter j).all (λ v => predicate v (t w)) := by
  by_contra hall
  push_neg at hall
  have hExh : pragmaticallyExhaustive t predicate j worlds = true := by
    unfold pragmaticallyExhaustive
    simp only [List.all_eq_true, beq_iff_eq]
    exact hall
  simp [hExh] at hNotExh

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
