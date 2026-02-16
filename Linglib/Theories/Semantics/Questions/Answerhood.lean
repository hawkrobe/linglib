import Linglib.Theories.Semantics.Questions.Partition
import Linglib.Theories.Semantics.Questions.Hamblin

/-
The ANS operator and the answerhood thesis (Groenendijk & Stokhof 1984, Ch. I).

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Karttunen (1977). Syntax and Semantics of Questions.
- Bennett & Belnap (1990). Conditional Assertion and Restricted Quantification.
-/

namespace QuestionSemantics.Answerhood

open QuestionSemantics
open scoped GSQuestion  -- For ⊑ notation

/-- ANS(Q, i) = cell of Q's partition containing i (G&S 1984, p. 14-15). -/
def ans {W : Type*} (q : GSQuestion W) (i : W) : W → Bool :=
  λ w => q.sameAnswer i w

/-- ANS is true at the index of evaluation. -/
theorem ans_true_at_index {W : Type*} (q : GSQuestion W) (i : W) :
    ans q i i = true :=
  q.refl i

/-- Worlds in the same cell get the same ANS. -/
theorem ans_constant_on_cells {W : Type*} (q : GSQuestion W) (w v : W)
    (hEquiv : q.sameAnswer w v = true) :
    ∀ u, ans q w u = ans q v u := by
  intro u
  simp only [ans]
  cases hu : q.sameAnswer w u with
  | false =>
    cases hvu : q.sameAnswer v u with
    | false => rfl
    | true =>
      have hwu := q.trans w v u hEquiv hvu
      rw [hwu] at hu
      exact absurd hu (by simp)
  | true =>
    have hvw : q.sameAnswer v w = true := by rw [q.symm]; exact hEquiv
    exact (q.trans v w u hvw hu).symm

/-- ANS propositions from different cells are disjoint. -/
theorem ans_disjoint {W : Type*} (q : GSQuestion W) (w v u : W)
    (hNotEquiv : q.sameAnswer w v = false) :
    ¬(ans q w u = true ∧ ans q v u = true) := by
  intro ⟨hwu, hvu⟩
  simp only [ans] at hwu hvu
  have huv : q.sameAnswer u v = true := by rw [q.symm]; exact hvu
  have hwv := q.trans w u v hwu huv
  rw [hwv] at hNotEquiv
  exact absurd hNotEquiv (by simp)

/-- Wh-question refines the polar question for any individual in the domain.
    Core result of G&S 1984: knowing the answer to "Who walks?" determines
    the answer to "Does John walk?" because the full extension determines
    each individual's value.
    Proof: If the lists `domain.map (pred · w)` and `domain.map (pred · v)` are
    equal (same wh-answer), then `pred e w = pred e v` for any `e ∈ domain`
    (same polar answer). -/
theorem wh_refines_polar {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (e : E) (he : e ∈ domain) :
    let whQ := GSQuestion.ofProject (λ w => domain.map (λ x => pred x w))
    let polarQ := polarQuestion (pred e)
    whQ ⊑ polarQ := by
  -- Intro let-bindings, then unfold refinement
  intro _ _ w v h
  -- Bypass let-bindings: restate h and goal in terms of BEq
  change (pred e w == pred e v) = true
  have h' : (domain.map (λ x => pred x w) == domain.map (λ x => pred x v)) = true := h
  rw [beq_iff_eq] at h' ⊢
  -- h' : domain.map (λ x => pred x w) = domain.map (λ x => pred x v)
  -- goal : pred e w = pred e v
  simpa using List.map_eq_map_iff.mp h' e he

/-- If ANS("Who walks?", i) is known, ANS("Does John walk?", i) is determined. -/
theorem wh_ans_determines_polar_ans {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (e : E) (he : e ∈ domain)
    (w v : W) :
    let whQ := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    ans whQ w v = true →
    let polarQ := polarQuestion (pred e)
    ans polarQ w v = true := by
  intro whQ h polarQ
  exact wh_refines_polar domain pred e he w v h

/-- Composed polar questions refine their components. -/
theorem composed_polar_refines {W : Type*} (p1 p2 : W → Bool) :
    QUD.compose (polarQuestion p1) (polarQuestion p2) ⊑ polarQuestion p1 :=
  QUD.compose_refines_left _ _

/-- Karttunen denotation: set of true answer-propositions at index w (de re). -/
def karttunenDenotation {W E : Type*} [BEq W]
    (domain : List E) (pred : E → W → Bool) (w : W) (_worlds : List W) :
    List (W → Bool) :=
  (domain.filter (pred · w)).map λ e => pred e

/-- Karttunen complete answer: conjunction of all true answer-propositions. -/
def karttunenCompleteAnswer {W E : Type*} [BEq W]
    (domain : List E) (pred : E → W → Bool) (w : W) (worlds : List W) :
    W → Bool :=
  λ v => (karttunenDenotation domain pred w worlds).all λ p => p v

/-- G&S ANS implies Karttunen's complete answer (G&S 1984, pp. 53-54).
    If the full extension matches at v (G&S), then a fortiori the positive
    extension matches (Karttunen). This is the sound direction: G&S is
    strictly stronger than Karttunen.
    Proof: G&S ANS says every entity has the same truth value at w and v.
    Karttunen only checks entities true at w — which is a subset of "all entities". -/
theorem gs_ans_implies_karttunen {W E : Type*} [BEq W] [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (w : W) (worlds : List W) :
    let gsQ := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    ∀ v, ans gsQ w v = true →
         karttunenCompleteAnswer domain pred w worlds v = true := by
  intro _ v hGS
  -- Extract that full extensions match from G&S sameAnswer
  change (domain.map (λ x => pred x w) == domain.map (λ x => pred x v)) = true at hGS
  rw [beq_iff_eq] at hGS
  -- hGS : domain.map (λ x => pred x w) = domain.map (λ x => pred x v)
  simp only [karttunenCompleteAnswer, karttunenDenotation]
  rw [List.all_eq_true]
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨e, he, rfl⟩ := hp
  rw [List.mem_filter] at he
  -- he.1 : e ∈ domain, he.2 : pred e w = true
  -- From hGS: pred e w = pred e v, so pred e v = true
  have hSame : (λ x => pred x w) e = (λ x => pred x v) e :=
    List.map_eq_map_iff.mp hGS e he.1
  simp at hSame
  rw [← hSame]; exact he.2

/-- The converse fails: Karttunen's complete answer does NOT imply G&S ANS.
    Karttunen only tracks the positive extension (entities satisfying pred at w),
    while G&S requires the *full* extension to match.
    Counterexample (G&S 1984, pp. 53-54): domain = {john, mary}.
    At w: john walks, mary doesn't. At v: both walk.
    Karttunen: true (john walks at v ✓ — all who walk at w also walk at v).
    G&S: false (extension [T,F] ≠ [T,T] — mary's value differs).
    This is the central weakness G&S identify in Karttunen's semantics:
    it only tracks who *does* φ, not who *doesn't*. -/
theorem karttunen_not_implies_gs :
    let domain : List Bool := [true, false]
    let pred : Bool → Bool → Bool := λ e w =>
      match e, w with
      | true, _ => true       -- john walks in both worlds
      | false, true => false   -- mary doesn't walk at w
      | false, false => true   -- mary walks at v
    let w := true; let v := false
    karttunenCompleteAnswer domain pred w [w, v] v = true ∧
    ans (GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))) w v = false := by
  native_decide

/-- Karttunen entailment: denotation inclusion at every index. -/
def karttunenEntails {W E : Type*} [BEq W]
    (domain1 : List E) (pred1 : E → W → Bool)
    (domain2 : List E) (pred2 : E → W → Bool)
    (worlds : List W) : Prop :=
  ∀ w, ∀ p ∈ karttunenDenotation domain2 pred2 w worlds,
    p ∈ karttunenDenotation domain1 pred1 w worlds

/-- Karttunen's intersection-based coordination fails for questions with
    different predicates (G&S 1984, Ch. VI §3.1).

    Setup: W = {w₁, w₂}, E = {john, mary}.
    "Who walks?" — john walks at w₁, mary at w₂ (complementary).
    "Who talks?" — john always talks, mary never talks (constant).

    Both Karttunen denotations are non-empty at w₁, but no proposition
    appears in both: `walk(john) = id` while `talk(john) = const true`,
    so their pointwise intersection is empty.

    Meanwhile, G&S partition composition correctly cross-classifies:
    walkQ distinguishes the two worlds (different extensions), and
    compose(walkQ, talkQ) inherits this, yielding a non-trivial partition.

    This witnesses that Karttunen's approach to question coordination
    (denotation intersection) is fundamentally broken for multi-predicate
    coordinations, while G&S's algebraic approach (partition meet) works. -/
theorem karttunen_coordination_problem :
    let domain : List Bool := [true, false]
    -- "walk": john walks at w₁, mary at w₂ (complementary distribution)
    let walk : Bool → Bool → Bool := λ e w => e == w
    -- "talk": john always talks, mary never talks
    let talk : Bool → Bool → Bool := λ e _w => e
    let w := true
    let worlds := [true, false]
    -- (1) Both Karttunen denotations are non-empty at w₁
    (karttunenDenotation domain walk w worlds).length > 0 ∧
    (karttunenDenotation domain talk w worlds).length > 0 ∧
    -- (2) No proposition in walk's denotation agrees with any in talk's
    --     on all worlds (pointwise intersection is empty)
    (karttunenDenotation domain walk w worlds).all (λ p =>
      (karttunenDenotation domain talk w worlds).all (λ q =>
        !(worlds.all (λ v => p v == q v)))) = true ∧
    -- (3) But G&S composition is non-trivial (distinguishes w₁ from w₂)
    (QUD.compose
      (GSQuestion.ofProject (λ w => domain.map (walk · w)))
      (GSQuestion.ofProject (λ w => domain.map (talk · w)))).sameAnswer true false = false := by
  native_decide

/-- Answerhood thesis: complete true answer at any index is determined by Q (G&S 1984, p. 15). -/
theorem answerhood_thesis {W : Type*} (q : GSQuestion W) (i : W) :
    ∃ (p : W → Bool), p = ans q i :=
  ⟨ans q i, rfl⟩

/-- The same question can have different answers at different indices. -/
theorem ans_situation_dependent {W : Type*} (q : GSQuestion W) (w v : W)
    (hDiff : q.sameAnswer w v = false) :
    ∃ u, ans q w u ≠ ans q v u := by
  use w
  simp only [ans, ne_eq]
  rw [q.refl w]
  rw [q.symm] at hDiff
  simp [hDiff]

/-- Partial answer: eliminates some cells but not all. -/
def isPartialAnswer {W : Type*} (p : W → Bool) (q : GSQuestion W)
    (worlds : List W) : Bool :=
  let cells := q.toCells worlds
  let compatible := cells.filter λ cell =>
    worlds.any λ w => p w && cell w
  compatible.length > 1 && compatible.length < cells.length

/-- Exhaustive answers: ANS pins down the full extension of the predicate. -/
theorem exhaustive_answers {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (w v : W) :
    let q := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    ans q w v = true ↔
    (∀ e ∈ domain, pred e w = pred e v) := by
  simp only [ans, GSQuestion.ofProject, QUD.ofProject]
  constructor
  · intro h
    rw [beq_iff_eq] at h
    intro e he
    have := List.map_eq_map_iff.mp h e he
    simp at this
    exact this
  · intro h
    rw [beq_iff_eq]
    exact List.map_eq_map_iff.mpr λ e he => by simp [h e he]

/-- De dicto answer via a (possibly non-rigid) description. -/
def deDictoAnswer {W E : Type*} [DecidableEq E]
    (description : W → E) (pred : E → W → Bool) : W → Bool :=
  λ w => pred (description w) w

/-- Non-rigid descriptions may fail to be semantic answers (G&S 1984, p. 27).
    For any non-rigid description, there exists a predicate and question such that
    the de dicto answer holds at one world but fails at another world in the same
    cell — witnessing that de dicto answers are not semantic (partition-based).

    Proof: Given description(w₀) ≠ description(v₀), let pred(e,_) := (e = description(w₀))
    and q := trivial (all worlds equivalent). Then:
    - de dicto at w₀ = pred(description(w₀), w₀) = true  (reflexivity)
    - de dicto at v₀ = pred(description(v₀), v₀) = false (non-rigidity)

    N.B. The original statement universally quantified `pred`, which is false —
    a constant predicate makes de dicto answers trivially uniform. The correct
    G&S claim is that non-rigid descriptions are *not guaranteed* to give
    semantic answers, i.e., there exists a breaking scenario for any non-rigid
    description. -/
theorem nonrigid_may_fail_semantic {W E : Type*} [DecidableEq E]
    (description : W → E)
    (hNonrigid : ∃ w v, description w ≠ description v) :
    ∃ (pred : E → W → Bool) (q : GSQuestion W) (w v : W),
      q.sameAnswer w v = true ∧
      deDictoAnswer description pred w = true ∧
      deDictoAnswer description pred v = false := by
  obtain ⟨w₀, v₀, hNeq⟩ := hNonrigid
  refine ⟨λ e _ => decide (e = description w₀), QUD.trivial, w₀, v₀, rfl, ?_, ?_⟩
  · show decide (description w₀ = description w₀) = true
    exact decide_eq_true rfl
  · show decide (description v₀ = description w₀) = false
    exact decide_eq_false (Ne.symm hNeq)

/-- Convert G&S question to Hamblin denotation. -/
def gsToHamblin {W : Type*} (q : GSQuestion W) (worlds : List W) :
    Hamblin.QuestionDen W :=
  λ p =>
    worlds.any λ w => worlds.all λ v => p v == ans q w v

/-- ANS propositions are recognized by the derived Hamblin denotation.
    The Hamblin denotation checks: ∃ w' ∈ worlds, ∀ v ∈ worlds, p v == ans q w' v.
    Taking w' = w gives ans q w v == ans q w v, which is true by refl. -/
theorem gsToHamblin_recognizes_ans {W : Type*} (q : GSQuestion W)
    (worlds : List W) (w : W) (hw : w ∈ worlds) :
    gsToHamblin q worlds (ans q w) = true := by
  simp only [gsToHamblin]
  rw [List.any_eq_true]
  exact ⟨w, hw, List.all_eq_true.mpr λ v _ => by simp [ans]⟩

/-- Representatives computed by toCells come from the input list. -/
private theorem foldl_reps_subset {M : Type*} (q : QUD M) :
    ∀ (elements : List M) (acc : List M) (rep : M),
      rep ∈ elements.foldl (λ acc w =>
        if acc.any (λ r => q.sameAnswer r w) then acc else w :: acc) acc →
      rep ∈ acc ∨ rep ∈ elements := by
  intro elements
  induction elements with
  | nil => intro acc rep h; exact Or.inl h
  | cons hd tl ih =>
    intro acc rep h
    simp only [List.foldl_cons] at h
    split at h
    · -- hd already covered by acc; accumulator unchanged
      rcases ih acc rep h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')
    · -- hd added to accumulator
      rcases ih (hd :: acc) rep h with h' | h'
      · cases List.mem_cons.mp h' with
        | inl h'' => exact Or.inr (List.mem_cons.mpr (Or.inl h''))
        | inr h'' => exact Or.inl h''
      · exact Or.inr (List.mem_cons_of_mem _ h')

/-- The foldl accumulator only grows: elements of acc persist in the result. -/
private theorem foldl_acc_preserved {M : Type*} (q : QUD M) :
    ∀ (elements : List M) (acc : List M) (a : M),
      a ∈ acc →
      a ∈ elements.foldl (λ acc w =>
        if acc.any (λ r => q.sameAnswer r w) then acc else w :: acc) acc := by
  intro elements
  induction elements with
  | nil => intro acc a h; exact h
  | cons hd tl ih =>
    intro acc a h
    simp only [List.foldl_cons]
    split
    · exact ih acc a h
    · exact ih (hd :: acc) a (List.mem_cons_of_mem _ h)

/-- Every element of the input has a covering representative in the foldl result.
    Generalized: also handles elements already covered by the initial accumulator. -/
private theorem foldl_has_rep {M : Type*} (q : QUD M) :
    ∀ (elements : List M) (acc : List M) (i : M),
      (i ∈ elements ∨ ∃ rep ∈ acc, q.sameAnswer rep i = true) →
      ∃ rep ∈ elements.foldl (λ acc w =>
        if acc.any (λ r => q.sameAnswer r w) then acc else w :: acc) acc,
        q.sameAnswer rep i = true := by
  intro elements
  induction elements with
  | nil =>
    intro acc i h
    rcases h with h | h
    · simp at h
    · exact h
  | cons hd tl ih =>
    intro acc i h
    simp only [List.foldl_cons]
    split
    · -- hd already covered; acc unchanged
      rename_i hAny
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h'
        · rw [List.any_eq_true] at hAny
          obtain ⟨rep, hRepAcc, hRepSame⟩ := hAny
          exact ih acc i (Or.inr ⟨rep, hRepAcc, hRepSame⟩)
        · exact ih acc i (Or.inl h')
      · exact ih acc i (Or.inr h)
    · -- hd added to acc
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact ih (i :: acc) i (Or.inr ⟨i, List.mem_cons.mpr (Or.inl rfl), q.refl i⟩)
        · exact ih (hd :: acc) i (Or.inl h')
      · obtain ⟨rep, hRepAcc, hRepSame⟩ := h
        exact ih (hd :: acc) i (Or.inr ⟨rep, List.mem_cons_of_mem _ hRepAcc, hRepSame⟩)

/-- Representatives in the foldl result are from distinct equivalence classes.
    No two representatives are equivalent under q. -/
private theorem foldl_reps_no_dup {M : Type*} (q : QUD M) :
    ∀ (elements : List M) (acc : List M),
      (∀ r1 ∈ acc, ∀ r2 ∈ acc, q.sameAnswer r1 r2 = true → r1 = r2) →
      let result := elements.foldl (λ acc w =>
        if acc.any (λ r => q.sameAnswer r w) then acc else w :: acc) acc
      ∀ r1 ∈ result, ∀ r2 ∈ result, q.sameAnswer r1 r2 = true → r1 = r2 := by
  intro elements
  induction elements with
  | nil => intro acc hNoDup; exact hNoDup
  | cons hd tl ih =>
    intro acc hNoDup
    simp only [List.foldl_cons]
    split
    · -- hd already covered; acc unchanged, invariant preserved
      exact ih acc hNoDup
    · -- hd added to acc; need to show hd :: acc has no duplicates
      rename_i hNotAny
      apply ih (hd :: acc)
      intro r1 hr1 r2 hr2 hSame
      rcases List.mem_cons.mp hr1 with rfl | hr1'
      · rcases List.mem_cons.mp hr2 with rfl | hr2'
        · rfl
        · -- r1 = hd, r2 ∈ acc, sameAnswer r1 r2 = true
          -- But hNotAny says no element of acc is equivalent to r1
          have : q.sameAnswer r2 r1 = true := by rw [q.symm]; exact hSame
          exact absurd (List.any_eq_true.mpr ⟨r2, hr2', this⟩) hNotAny
      · rcases List.mem_cons.mp hr2 with rfl | hr2'
        · -- r1 ∈ acc, r2 = hd, sameAnswer r1 r2 = true
          exact absurd (List.any_eq_true.mpr ⟨r1, hr1', hSame⟩) hNotAny
        · exact hNoDup r1 hr1' r2 hr2' hSame

/-- Filter commutes with map: filtering a mapped list = mapping a filtered list. -/
private theorem filter_map_comm {α β : Type*} (l : List α) (f : α → β) (g : β → Bool) :
    (l.map f).filter g = (l.filter (g ∘ f)).map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.filter_cons, Function.comp]
    split <;> simp [ih]

/-- The foldl result is Nodup (no duplicate elements).
    Follows from reflexivity: if hd ∈ acc, then acc.any returns true. -/
private theorem foldl_nodup {M : Type*} (q : QUD M) :
    ∀ (elements : List M) (acc : List M),
      acc.Nodup →
      (∀ a ∈ acc, ∀ b ∈ acc, q.sameAnswer a b = true → a = b) →
      (elements.foldl (fun acc w =>
        if (acc.any fun r => q.sameAnswer r w) = true then acc else w :: acc) acc).Nodup := by
  intro elements
  induction elements with
  | nil => intro acc hND _; exact hND
  | cons hd tl ih =>
    intro acc hND hClassUniq
    simp only [List.foldl_cons]
    split
    · exact ih acc hND hClassUniq
    · rename_i hNotAny
      apply ih
      · rw [List.nodup_cons]
        exact ⟨fun hIn => hNotAny (List.any_eq_true.mpr ⟨hd, hIn, q.refl hd⟩), hND⟩
      · intro r1 hr1 r2 hr2 hSame
        rcases List.mem_cons.mp hr1 with rfl | hr1'
        · rcases List.mem_cons.mp hr2 with rfl | hr2'
          · rfl
          · have : q.sameAnswer r2 r1 = true := by rw [q.symm]; exact hSame
            exact absurd (List.any_eq_true.mpr ⟨r2, hr2', this⟩) hNotAny
        · rcases List.mem_cons.mp hr2 with rfl | hr2'
          · exact absurd (List.any_eq_true.mpr ⟨r1, hr1', hSame⟩) hNotAny
          · exact hClassUniq r1 hr1' r2 hr2' hSame

/-- On a Nodup list, if exactly one element satisfies p, the filter is a singleton. -/
private theorem nodup_filter_eq_singleton {α : Type*}
    (l : List α) (p : α → Bool) (x : α)
    (hx : x ∈ l) (hp : p x = true)
    (huniq : ∀ y ∈ l, p y = true → y = x)
    (hnodup : l.Nodup) :
    l.filter p = [x] := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.filter_cons]
    split
    · rename_i hphd
      have heq := huniq hd (List.mem_cons.mpr (Or.inl rfl)) hphd
      subst heq
      congr 1
      have hxNotTl := (List.nodup_cons.mp hnodup).1
      match hfl : tl.filter p with
      | [] => rfl
      | y :: _ =>
        exfalso
        have hyMem : y ∈ tl.filter p := hfl ▸ List.mem_cons.mpr (Or.inl rfl)
        have hyTl := (List.mem_filter.mp hyMem).1
        have hpy := (List.mem_filter.mp hyMem).2
        exact hxNotTl (huniq y (List.mem_cons_of_mem _ hyTl) hpy ▸ hyTl)
    · rename_i hnphd
      have hxTl : x ∈ tl := by
        rcases List.mem_cons.mp hx with rfl | h
        · exact absurd hp hnphd
        · exact h
      exact ih hxTl (fun y hy => huniq y (List.mem_cons_of_mem _ hy)) hnodup.of_cons

/-- ANS(Q, i) answers Q in the sense of Basic.answers.
    Requires i ∈ worlds; otherwise toCells may be empty. -/
theorem ans_answers {W : Type*} (q : GSQuestion W) (i : W) (worlds : List W)
    (hIn : i ∈ worlds) :
    answers (ans q i) (q.toQuestion worlds) worlds = true := by
  obtain ⟨rep, hRepResult, hRepSame⟩ := foldl_has_rep q worlds [] i (Or.inl hIn)
  simp only [answers, GSQuestion.toQuestion]
  rw [List.any_eq_true]
  exact ⟨(λ w => q.sameAnswer rep w), List.mem_map.mpr ⟨rep, hRepResult, rfl⟩, by
    rw [List.all_eq_true]
    intro w _
    simp only [ans, decide_eq_true_eq]
    exact q.trans rep i w hRepSame⟩

/-- ANS(Q, i) selects exactly one cell (completeness).
    Uses filter_map_comm to pull the filter through toCells' map,
    then nodup_filter_eq_singleton to show exactly one representative passes. -/
theorem ans_completely_answers {W : Type*} (q : GSQuestion W) (i : W) (worlds : List W)
    (hIn : i ∈ worlds) :
    completelyAnswers (ans q i) (q.toQuestion worlds) worlds = true := by
  obtain ⟨rep, hRepResult, hRepSame⟩ := foldl_has_rep q worlds [] i (Or.inl hIn)
  have hClassUniq := foldl_reps_no_dup q worlds [] (by intro r1 h; simp at h)
  have hND := foldl_nodup q worlds [] List.nodup_nil (by intro r1 h; simp at h)
  simp only [completelyAnswers, GSQuestion.toQuestion, QUD.toCells]
  rw [beq_iff_eq]
  -- Pull filter through map: (reps.map f).filter g = (reps.filter (g ∘ f)).map f
  rw [filter_map_comm]
  -- The filter on reps selects exactly [rep], so map gives a singleton
  have hfilt : (worlds.foldl (fun acc w =>
      if (acc.any fun r => q.sameAnswer r w) = true then acc else w :: acc) []).filter
    ((fun cell => worlds.any fun w => ans q i w && cell w) ∘ fun rep w => q.sameAnswer rep w) = [rep] := by
    apply nodup_filter_eq_singleton _ _ _ hRepResult
    · -- rep passes the overlap test (witnessed by i)
      simp only [Function.comp_apply]
      rw [List.any_eq_true]
      exact ⟨i, hIn, by simp only [ans, Bool.and_eq_true]; exact ⟨q.refl i, hRepSame⟩⟩
    · -- uniqueness: any passing rep' must equal rep
      intro rep' hrep' hg
      simp only [Function.comp_apply] at hg
      rw [List.any_eq_true] at hg
      obtain ⟨w, _, hw⟩ := hg
      simp only [ans, Bool.and_eq_true] at hw
      have hSame' : q.sameAnswer rep' i = true :=
        q.trans rep' w i hw.2 (by rw [q.symm]; exact hw.1)
      have hSameReps : q.sameAnswer rep rep' = true :=
        q.trans rep i rep' hRepSame (by rw [q.symm]; exact hSame')
      exact hClassUniq rep' hrep' rep hRepResult (by rw [q.symm]; exact hSameReps)
    · exact hND
  rw [hfilt]; rfl

/-- A complete answer is not a partial answer. -/
theorem complete_not_partial {W : Type*} (q : GSQuestion W) (i : W)
    (worlds : List W) (hIn : i ∈ worlds) :
    isPartialAnswer (ans q i) q worlds = false := by
  have hComplete := ans_completely_answers q i worlds hIn
  simp only [completelyAnswers, GSQuestion.toQuestion, beq_iff_eq] at hComplete
  simp only [isPartialAnswer]
  rw [hComplete]
  simp

theorem partition_cells_are_hamblin_alternatives {W : Type*}
    (q : GSQuestion W) (worlds : List W) :
    ∀ cell ∈ q.toCells worlds,
      gsToHamblin q worlds cell = true := by
  intro cell hCell
  -- Unfold toCells: cell = (λ w => q.sameAnswer rep w) for some representative
  simp only [QUD.toCells] at hCell
  rw [List.mem_map] at hCell
  obtain ⟨rep, hRep, rfl⟩ := hCell
  -- rep comes from the foldl over worlds, so rep ∈ worlds
  have hRepMem : rep ∈ worlds := by
    rcases foldl_reps_subset q worlds [] rep hRep with h | h
    · simp at h
    · exact h
  -- cell = (λ w => q.sameAnswer rep w) = ans q rep
  exact gsToHamblin_recognizes_ans q worlds rep hRepMem

/-- G&S refinement ↔ ANS-transfer between questions. -/
theorem refinement_transfers_answers {W : Type*} (q1 q2 : GSQuestion W)
    (hRefines : q1 ⊑ q2) (w : W) :
    ∀ v, ans q1 w v = true → ans q2 w v = true :=
  λ v h => hRefines w v h

/-- Converse: ANS-transfer implies refinement. -/
theorem answer_transfer_implies_refinement {W : Type*} (q1 q2 : GSQuestion W)
    (hTransfer : ∀ w v, ans q1 w v = true → ans q2 w v = true) :
    q1 ⊑ q2 :=
  hTransfer

/-- G&S refinement ↔ answer transfer. -/
theorem refinement_iff_answer_transfer {W : Type*} (q1 q2 : GSQuestion W) :
    q1 ⊑ q2 ↔ (∀ w v, ans q1 w v = true → ans q2 w v = true) :=
  ⟨λ h => refinement_transfers_answers q1 q2 h,
   λ h => answer_transfer_implies_refinement q1 q2 h⟩

end QuestionSemantics.Answerhood
