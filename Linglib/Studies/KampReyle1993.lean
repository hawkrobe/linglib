import Linglib.Semantics.Dynamic.DRS.Dynamics
import Mathlib.Data.Fin.VecNotation

/-!
# Kamp & Reyle (1993) [kamp-reyle-1993]

*From Discourse to Logic* interprets discourse by DRS construction and verifies DRSs by
embeddings into a model. This file evaluates the book's worked examples through the
substrate denotation `DRS.trueRel` (`Semantics/Dynamic/DRS/`; [muskens-1996]'s
relational truth, the existential closure of Def. 1.4.5): "Jones owns Ulysses. It
fascinates him." (1.1) is true of a single owning pair, its pronoun equations adding no
quantificational force (`ulysses_tc`); "Jones does not own a Porsche." (1.56) is the
non-existence of a verifying extension (`porsche_tc`), the referent under `¬` being
inaccessible from the top level while the outer referent stays visible inside
(`porsche_referent_inaccessible`, `outer_referent_accessible`); and "If a farmer owns a
donkey he beats it." (2.47) receives the universal reading through the `⇒` verification
clause of (2.31)/Def. 2.1.4 (`donkey_universal_reading`), the pronoun-completed
(2.45)-style variant having the same truth conditions (`donkeyPronoun_agree`).

The structural facts — subordination of the donkey boxes (Def. 1.4.10/2.1.2), the
accessibility asymmetry ([geurts-beaver-maier-2024] §4.2: the antecedent is accessible
to the consequent, not conversely), properness, truth in concrete models — are proved
by evaluation or by cases on the geometry; the truth-conditions are claims over
arbitrary models, proved by unfolding the verifying-embedding semantics. Sequencing a discourse is `DRS.merge`, whose
dynamics is the substrate Merging Lemma `DRS.toRel_merge`, so merged-vs-compositional
equalities are definitional.
-/

open FirstOrder FirstOrder.Language

namespace KampReyle1993

/-- The relation symbols of the worked examples; names (`jones`, `ulysses`, `porsche`)
enter as the unary conditions the construction algorithm writes for them (`Jones(x)`). -/
inductive KRRel : ℕ → Type
  | jones : KRRel 1 | ulysses : KRRel 1 | porsche : KRRel 1
  | farmer : KRRel 1 | donkey : KRRel 1
  | owns : KRRel 2 | fascinates : KRRel 2 | beats : KRRel 2

/-- The first-order language of the examples (no functions). -/
def krLang : Language := ⟨fun _ => Empty, KRRel⟩

open DRT

variable {M : Type*} [krLang.Structure M]

/-- `RelMap` with the language pinned (a relation symbol alone does not determine
`L`). Lets truth-conditions read as `rm .farmer ![e]`. -/
abbrev rm {n} (R : krLang.Relations n) (x : Fin n → M) : Prop := Structure.RelMap R x

/-- Reindex a composed vector argument componentwise: with `comp_vecEmpty`, folds
`fun i => v (![k₁, …] i)` to `![v k₁, …]`, so truth-condition proofs work with the
atoms' assigned values directly. Point-ful because `Embedding.verifies_rel` produces
the eta-expanded form, which the point-free mathlib lemmas (`Fin.comp_cons`,
`FinVec.map_eq`) do not match. -/
private theorem comp_vecCons {α β : Type*} (v : α → β) (k : α) {n : ℕ} (t : Fin n → α) :
    (fun i => v (Matrix.vecCons k t i)) = Matrix.vecCons (v k) (fun i => v (t i)) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Base case of `comp_vecCons`. -/
private theorem comp_vecEmpty {α β : Type*} (v : α → β) :
    (fun i => v (Matrix.vecEmpty i)) = (![] : Fin 0 → β) := by
  funext i
  exact i.elim0

/-! ### Names and pronouns: "Jones owns Ulysses. It fascinates him." (1.1) -/

/-- The completed §1.1 DRS of (1.1) —
`[u₁ u₂ u₃ u₄ | Jones u₁, Ulysses u₂, u₁ owns u₂, u₃ = u₂, u₄ = u₁, u₃ fascinates u₄]`:
each name and pronoun introduces a referent; the pronouns *it* and *him* are resolved by
the (1.17)-style equations to the first sentence's referents. -/
def ulyssesDiscourse : DRS krLang ℕ :=
  .mk {1, 2, 3, 4} [.rel .jones (![1]), .rel .ulysses (![2]), .rel .owns (![1, 2]),
    .eq 3 2, .eq 4 1, .rel .fascinates (![3, 4])]

/-- The (1.1) discourse is true iff a single pair verifies both sentences: the
pronouns' referents and equations add no quantificational force, and the first
sentence's referents persist into the second. -/
theorem ulysses_tc (a : ℕ → M) :
    DRS.trueRel ulyssesDiscourse a ↔
      ∃ x y : M, rm .jones ![x] ∧ rm .ulysses ![y] ∧ rm .owns ![x, y] ∧
        rm .fascinates ![y, x] := by
  simp only [DRS.trueRel_iff, ulyssesDiscourse, DRS.toRel_iff, Box.Extends,
    Embedding.verifies_mk, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, Embedding.verifies_rel, Embedding.verifies_eq, comp_vecCons,
    comp_vecEmpty, and_true]
  constructor
  · rintro ⟨a', -, hj, hu, ho, h32, h41, hf⟩
    rw [h32, h41] at hf
    exact ⟨a' 1, a' 2, hj, hu, ho, hf⟩
  · rintro ⟨x, y, hj, hu, ho, hf⟩
    exact ⟨fun n => match n with | 1 => x | 2 => y | 3 => y | 4 => x | n => a n,
      fun z hz => by dsimp only; split <;> simp_all, hj, hu, ho, rfl, rfl, hf⟩

/-- The completed (1.1) DRS is proper (Def. 1.4.2–1.4.3): every referent the conditions
use is introduced by the discourse itself. -/
theorem ulysses_proper : ulyssesDiscourse.IsProper := by
  simp [DRS.IsProper, ulyssesDiscourse]; decide

/-! ### Negation blocks anaphora: "Jones does not own a Porsche." (1.56) -/

/-- The box under `¬` in (1.57): `[u₂ | Porsche u₂, u₁ owns u₂]`. -/
def porscheNeg : DRS krLang ℕ := .mk {2} [.rel .porsche (![2]), .rel .owns (![1, 2])]

/-- The DRS (1.57) of (1.56) — `[u₁ | Jones u₁, ¬[u₂ | Porsche u₂, u₁ owns u₂]]`: the
indefinite's referent is introduced *inside* the negation. -/
def porscheDiscourse : DRS krLang ℕ := .mk {1} [.rel .jones (![1]), .neg porscheNeg]

/-- Truth of (1.57): there is *no* Porsche that Jones owns — the negated box is
verified by the non-existence of a verifying extension. -/
theorem porsche_tc (a : ℕ → M) :
    DRS.trueRel porscheDiscourse a ↔
      ∃ x : M, rm .jones ![x] ∧ ¬ ∃ y : M, rm .porsche ![y] ∧ rm .owns ![x, y] := by
  simp only [DRS.trueRel_iff, porscheDiscourse, porscheNeg, DRS.toRel_iff, Box.Extends,
    Embedding.verifies_mk, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, Embedding.verifies_neg, Embedding.verifies_rel, comp_vecCons,
    comp_vecEmpty, and_true]
  constructor
  · rintro ⟨a', -, hj, hneg⟩
    exact ⟨a' 1, hj, fun ⟨y, hp, ho⟩ => hneg
      ⟨fun n => match n with | 2 => y | n => a' n,
        fun z hz => by dsimp only; split <;> simp_all, hp, ho⟩⟩
  · rintro ⟨x, hj, hn⟩
    refine ⟨fun n => match n with | 1 => x | n => a n,
      fun z hz => by dsimp only; split <;> simp_all, hj, fun ⟨g, hag, hp, ho⟩ => hn ⟨g 2, hp, ?_⟩⟩
    rw [hag 1 (by simp)] at ho
    exact ho

/-- From the top-level position, the referent trapped under `¬` is not accessible
(Def. 2.1.3) — the reason a continuation "*It fascinates him." cannot resolve *it*. -/
theorem porsche_referent_inaccessible : ¬ DRS.Accessible porscheDiscourse 1 2 := by
  simp [DRS.Accessible, DRS.accessibleFrom, DRS.accScope, porscheDiscourse]

/-- Accessibility looks "left and up": from inside the negation, the outer referent
*is* accessible — the asymmetry of Def. 2.1.3. -/
theorem outer_referent_accessible : DRS.Accessible porscheDiscourse 2 1 := by
  simp [DRS.Accessible, DRS.accessibleFrom, DRS.accScope, porscheDiscourse, porscheNeg,
    Condition.accScopeL, Condition.accScope, Option.orElse]

/-- A continuation resolved to the trapped referent anyway is improper
(Def. 1.4.2–1.4.3): merging "It fascinates him." with *it* forced to `u₂` leaves `u₂`
free. -/
theorem continuation_improper :
    ¬ (porscheDiscourse.merge (.mk ∅ [.rel .fascinates (![2, 1])])).IsProper := by
  simp [DRS.IsProper, DRS.merge, porscheDiscourse, porscheNeg]; decide

/-! ### Donkey anaphora: "If a farmer owns a donkey he beats it." (2.47) -/

/-- The antecedent box `[u₁ u₂ | farmer u₁, donkey u₂, owns u₁ u₂]`. -/
def donkeyAnte : DRS krLang ℕ :=
  .mk {1, 2} [.rel .farmer (![1]), .rel .donkey (![2]), .rel .owns (![1, 2])]
/-- The consequent box `[ | beats u₁ u₂]` (pronouns resolved directly, (2.44)-style). -/
def donkeyCons : DRS krLang ℕ := .mk ∅ [.rel .beats (![1, 2])]
/-- (2.47) as `[ | donkeyAnte ⇒ donkeyCons]`. -/
def donkey : DRS krLang ℕ := .mk ∅ [.imp donkeyAnte donkeyCons]

/-- The donkey universal reading: the `⇒` verification clause ((2.31)/Def. 2.1.4) makes
the antecedent's existentials universal — every owning farmer-donkey pair satisfies
`beats`. The empty-universe consequent reuses the antecedent's values (the anaphora). -/
theorem donkey_universal_reading (a : ℕ → M) :
    DRS.trueRel donkey a ↔
    ∀ e₁ e₂ : M, (rm .farmer ![e₁] ∧ rm .donkey ![e₂] ∧ rm .owns ![e₁, e₂]) →
      rm .beats ![e₁, e₂] := by
  simp only [DRS.trueRel_iff, donkey, donkeyAnte, donkeyCons, DRS.toRel_iff, Box.Extends,
    Embedding.verifies_mk, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, Embedding.verifies_imp, Embedding.verifies_rel,
    comp_vecCons, comp_vecEmpty, and_true]
  constructor
  · rintro ⟨a', -, himp⟩ e₁ e₂ ⟨hf, hd, ho⟩
    obtain ⟨v'', hag, hb⟩ := himp (fun n => match n with | 1 => e₁ | 2 => e₂ | n => a' n)
      (fun z hz => by split <;> simp_all) ⟨hf, hd, ho⟩
    simpa [hag 1 (by simp), hag 2 (by simp)] using hb
  · intro hall
    exact ⟨a, fun _ _ => rfl, fun v' _ ⟨hf, hd, ho⟩ =>
      ⟨v', fun _ _ => rfl, hall (v' 1) (v' 2) ⟨hf, hd, ho⟩⟩⟩

/-- The donkey DRS is proper: the consequent's referents are supplied by the
antecedent — the `⇒`-accessibility in the free-variable computation. -/
theorem donkey_proper : donkey.IsProper := by
  simp [DRS.IsProper, donkey, donkeyAnte, donkeyCons]; decide

/-- The (2.45)-style consequent `[u₃ | u₃ = u₂, beats u₁ u₃]`: the pronoun *it*
introduces its own referent, resolved to the donkey by an equation. -/
def donkeyPronounCons : DRS krLang ℕ := .mk {3} [.eq 3 2, .rel .beats (![1, 3])]
/-- (2.47) with the pronoun completed by referent-plus-equation. -/
def donkeyPronoun : DRS krLang ℕ := .mk ∅ [.imp donkeyAnte donkeyPronounCons]

/-- The pronoun-completed conditional has the same universal truth conditions: the
equation forces the new referent to the donkey's value. -/
theorem donkeyPronoun_tc (a : ℕ → M) :
    DRS.trueRel donkeyPronoun a ↔
    ∀ e₁ e₂ : M, (rm .farmer ![e₁] ∧ rm .donkey ![e₂] ∧ rm .owns ![e₁, e₂]) →
      rm .beats ![e₁, e₂] := by
  simp only [DRS.trueRel_iff, donkeyPronoun, donkeyAnte, donkeyPronounCons, DRS.toRel_iff,
    Box.Extends, Embedding.verifies_mk, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, Embedding.verifies_imp, Embedding.verifies_rel,
    Embedding.verifies_eq, comp_vecCons, comp_vecEmpty, and_true]
  constructor
  · rintro ⟨a', -, himp⟩ e₁ e₂ ⟨hf, hd, ho⟩
    obtain ⟨v'', hag, h32, hb⟩ := himp (fun n => match n with | 1 => e₁ | 2 => e₂ | n => a' n)
      (fun z hz => by split <;> simp_all) ⟨hf, hd, ho⟩
    rw [h32] at hb
    simpa [hag 1 (by simp), hag 2 (by simp)] using hb
  · intro hall
    exact ⟨a, fun _ _ => rfl, fun v' _ ⟨hf, hd, ho⟩ =>
      ⟨fun n => match n with | 3 => v' 2 | n => v' n,
        fun z hz => by dsimp only; split <;> simp_all, rfl, hall (v' 1) (v' 2) ⟨hf, hd, ho⟩⟩⟩

/-- (2.44) vs (2.45), for the donkey conditional: completing the pronoun directly or by
referent-plus-equation gives the same truth conditions — the book's "clearly identical
truth conditions" (p. 167). -/
theorem donkeyPronoun_agree (a : ℕ → M) :
    DRS.trueRel donkeyPronoun a ↔ DRS.trueRel donkey a :=
  (donkeyPronoun_tc a).trans (donkey_universal_reading a).symm

/-! ### Subordination and accessibility geometry -/

/-- The antecedent box is directly subordinate to the donkey DRS (Def. 1.4.10 as
extended by Def. 2.1.2). -/
theorem donkey_antecedent_subordinate : DirectlySubordinate donkeyAnte donkey :=
  .impAnte (c := donkeyCons) (by simp [donkey])

/-- The consequent box is likewise directly subordinate to the donkey DRS. -/
theorem donkey_consequent_subordinate : DirectlySubordinate donkeyCons donkey :=
  .impCons (a := donkeyAnte) (by simp [donkey])

/-- The antecedent is accessible to the consequent ([geurts-beaver-maier-2024]
§4.2) — the geometry that licenses the donkey anaphora. -/
theorem donkey_antecedent_accessible : AccessibleTo donkey donkeyAnte donkeyCons :=
  .single (.impCons .refl (by simp [donkey]))

private theorem weakSubordinate_donkey {K : DRS krLang ℕ} (h : WeakSubordinate K donkey) :
    K = donkey ∨ K = donkeyAnte ∨ K = donkeyCons := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl rfl
  | head hstep hrest ih =>
    rcases ih with rfl | rfl | rfl
    · cases hstep with
      | neg hc => simp [donkey] at hc
      | impAnte hc => simp [donkey] at hc; exact .inr (.inl hc.1)
      | impCons hc => simp [donkey] at hc; exact .inr (.inr hc.2)
      | disL hc => simp [donkey] at hc
      | disR hc => simp [donkey] at hc
    · cases hstep with
      | neg hc | impAnte hc | impCons hc | disL hc | disR hc => simp [donkeyAnte] at hc
    · cases hstep with
      | neg hc | impAnte hc | impCons hc | disL hc | disR hc => simp [donkeyCons] at hc

/-- Not conversely: the consequent has no outgoing accessibility edge, so its
(empty) universe contributes nothing to the antecedent — the `⇒` asymmetry. -/
theorem donkey_not_consequent_accessible : ¬ AccessibleTo donkey donkeyCons donkeyAnte := by
  intro h
  rcases h.cases_head with heq | ⟨X, hedge, -⟩
  · exact absurd (congrArg Box.referents heq) (by decide)
  · cases hedge with
    | neg hK hc => simp [donkeyCons] at hc
    | impAnte hK hc => simp [donkeyCons] at hc
    | disLeft hK hc => simp [donkeyCons] at hc
    | disRight hK hc => simp [donkeyCons] at hc
    | impCons hK hc =>
      rcases weakSubordinate_donkey hK with rfl | rfl | rfl
      · simp [donkey, donkeyAnte, donkeyCons] at hc
      · simp [donkeyAnte] at hc
      · simp [donkeyCons] at hc

/-! ### Model evaluation: the donkey conditional in concrete models

Positive: a two-element domain where farmer `0` owns and beats donkey `1`. Negative: a
domain where the owning pair goes unbeaten falsifies the conditional. -/

instance : krLang.Structure (Fin 2) where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .farmer => fun args => args 0 = 0
    | 1, .donkey => fun args => args 0 = 1
    | 2, .owns => fun args => args 0 = 0 ∧ args 1 = 1
    | 2, .beats => fun args => args 0 = 0 ∧ args 1 = 1
    | _, _ => fun _ => False

/-- The donkey conditional is true in this model: the only owning pair is `(0,1)`,
which `beats` holds of. -/
theorem donkey_true_in_model (a : ℕ → Fin 2) : DRS.trueRel donkey a := by
  rw [donkey_universal_reading]
  rintro e₁ e₂ ⟨hf, hd, -⟩
  exact ⟨hf, hd⟩

instance : krLang.Structure Bool where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .farmer => fun args => args 0 = false
    | 1, .donkey => fun args => args 0 = true
    | 2, .owns => fun args => args 0 = false ∧ args 1 = true
    | _, _ => fun _ => False

/-- The donkey conditional is false when the owning pair goes unbeaten: farmer `false`
owns donkey `true` but `beats` is empty. -/
theorem donkey_false_in_model (a : ℕ → Bool) : ¬ DRS.trueRel donkey a := by
  rw [donkey_universal_reading]
  exact fun h => h false true ⟨rfl, rfl, rfl, rfl⟩

end KampReyle1993
