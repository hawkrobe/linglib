import Linglib.Core.Data.Trivalent
import Linglib.Logic.Assignment

/-!
# Spector (2025): Trivalence and Transparency

This file formalizes the static, trivalent semantics for anaphora of [spector-2025]. A
first-order language is interpreted at world–assignment pairs with partial assignments: a
predicate of an unvalued variable is undefined, the connectives follow the Middle Kleene
tables ([peters-1979], [beaver-krahmer-2001]), and the existential carries the witness
condition of [mandelkern-2022], true only when the assignment already values the variable
with a witness, false when every value falsifies the scope, undefined otherwise. A sentence
is true at a world when some assignment makes it true, which delivers the classical truth
conditions of *a table is in the room and it is purple* and of the bathroom sentence *either
there is no bathroom or it is upstairs* (`trueAt_conj_iff`, `trueAt_bathroom_iff`).

Free variables presuppose that they are valued, and presupposition satisfaction is the
symmetric Transparency of [schlenker-2007] and [schlenker-2008]: an occurrence in a sentence
is transparent in a context when filling it with *valued(x) ∧ φ* and with *φ* gives the same
value throughout the context, for every *φ* (`Transparent`). The conjunction *∃xT(x) ∧ P(x)*
and the bathroom disjunction are transparent in every context because a true existential
values its variable
(`transparent_forward_conj`, `transparent_bathroom`); a bare pronoun, the reversed
conjunction and the reversed disjunction fail in the null context; a pronoun after an
accepted existential is transparent because the update keeps the variable valued
(`transparent_id_of_update_ex`). The Novelty Condition bars a repeated existential, which
would otherwise mean one existential over the conjunction (`eval_and_ex_ex_eq_true_iff`).
The simplified system fails covariation: *¬∃x¬∃yS(x, y)* is true exactly when one
individual is spoken to by everyone (`trueAt_notExNotEx_iff`).

The full system evaluates at plural assignments, sets of partial assignments, reading a
variable as atomic when the assignments valuing it agree; the existential is false only when
the plural assignment covers the domain, and the universal is true under that coverage.
Transparency of the conjunction and the bathroom sentence survives, a universal does not
license a singular pronoun (`not_transparentP_forall_conj`), and covariation is restored:
*¬∃x¬∃yS(x, y)* and *∀x∃yS(x, y)* are true exactly when everyone spoke to someone
(`trueAtP_notExNotEx_iff`, `trueAtP_allEx_iff`). Weak truth, some plural assignment verifying
the sentence, and strong truth, none falsifying it either, coincide on a simple existential
(`stronglyTrueAt_ex_iff`) and part on *there is a bathroom and it is upstairs* when one of
two bathrooms is upstairs. The strong-truth operator internalizes strong truth
(`trueAtP_strong_iff`), respects logical equivalence (`evalP_strong_congr`), and violates
Transparency under an existential (`not_transparentP_ex_and_strong`).

## Implementation notes

One language serves both systems: `valued` reads as the paper's *U(x)* in the simplified
system and as *atomic(x)* in the full one, and the simplified evaluation leaves the
universal and the strong-truth operator undefined, since the paper's first language lacks
them. Frames stand for sentences with the occurrence under test as a hole, so Transparency is
stated per frame. Quantificational subordination, the donkey sentences, the functional
variables of the appendix, and the paper's remark that no universal can be added to the
simplified system are not formalized.

## References

* [spector-2025]
* [schlenker-2007]
* [schlenker-2008]
* [mandelkern-2022]
* [peters-1979]
* [beaver-krahmer-2001]
-/

namespace Spector2025

open Trivalent (meetMiddle joinMiddle ofBool ofProp)

/-! ### The language -/

/-- The language: one- and two-place predicates on variables, the valuedness predicate that
Transparency introduces, the connectives, and the quantifiers. -/
inductive Formula (P R : Type*) where
  | pred (p : P) (x : ℕ)
  | rel (r : R) (x y : ℕ)
  | valued (x : ℕ)
  | not (φ : Formula P R)
  | and (φ ψ : Formula P R)
  | or (φ ψ : Formula P R)
  | ex (x : ℕ) (φ : Formula P R)
  | all (x : ℕ) (φ : Formula P R)
  | strong (φ : Formula P R)

/-- A model: extensions of the predicates at each world. -/
structure Model (W D P R : Type*) where
  pred : P → W → Set D
  rel : R → W → Set (D × D)

/-- The variables an existential binds, for the Novelty Condition. -/
def Formula.binders {P R : Type*} : Formula P R → List ℕ
  | .pred _ _ | .rel _ _ _ | .valued _ => []
  | .not φ => φ.binders
  | .and φ ψ | .or φ ψ => φ.binders ++ ψ.binders
  | .ex x φ => x :: φ.binders
  | .all _ φ | .strong φ => φ.binders

/-- The Novelty Condition: across a discourse no existential binds the same variable twice. -/
def Novel {P R : Type*} (S : List (Formula P R)) : Prop := (S.flatMap Formula.binders).Nodup

variable {W D P R : Type*} (M : Model W D P R)

/-! ### The simplified system: partial assignments -/

/-- The parametric core of Transparency for conjunction: whenever the first conjunct's truth
guarantees the presupposition, the presupposition can be dropped. -/
theorem conj_transparency_parametric : ∀ (E presup φ : Trivalent),
    (E = .true → presup = .true) → meetMiddle E (meetMiddle presup φ) = meetMiddle E φ
  | .true, _, φ, hw => by
    rw [hw rfl, Trivalent.meetMiddle_true_left, Trivalent.meetMiddle_true_left]
  | .false, _, _, _ => by simp [meetMiddle]
  | .indet, _, _, _ => rfl

/-- The parametric core for disjunction: whenever the first disjunct's falsity guarantees
the presupposition, the presupposition can be dropped. -/
theorem disj_transparency_parametric : ∀ (negE presup φ : Trivalent),
    (negE = .false → presup = .true) → joinMiddle negE (meetMiddle presup φ) = joinMiddle negE φ
  | .true, _, _, _ => by simp [joinMiddle]
  | .indet, _, _, _ => rfl
  | .false, _, φ, hw => by rw [hw rfl, Trivalent.meetMiddle_true_left]

open Classical in
/-- Evaluation at a world and a partial assignment. A predicate of an unvalued variable is
undefined; the existential is true when its scope is, false when every value falsifies the
scope, undefined otherwise. The universal and the strong-truth operator belong to the full
system and are left undefined here. -/
noncomputable def eval : Formula P R → W → PartialAssign ℕ D → Trivalent
  | .pred p x, w, g => (g x).elim .indet λ d => ofProp (d ∈ M.pred p w)
  | .rel r x y, w, g =>
    match g x, g y with
    | some a, some b => ofProp ((a, b) ∈ M.rel r w)
    | _, _ => .indet
  | .valued x, _, g => ofBool (g x).isSome
  | .not φ, w, g => (eval φ w g).neg
  | .and φ ψ, w, g => meetMiddle (eval φ w g) (eval ψ w g)
  | .or φ ψ, w, g => joinMiddle (eval φ w g) (eval ψ w g)
  | .ex x φ, w, g =>
    if eval φ w g = .true then .true
    else if ∀ a, eval φ w (g.update x a) = .false then .false
    else .indet
  | .all _ _, _, _ | .strong _, _, _ => .indet

/-- Truth at a world: some assignment makes the sentence true. -/
def TrueAt (φ : Formula P R) (w : W) : Prop := ∃ g : PartialAssign ℕ D, eval M φ w g = .true

variable {M}

theorem eval_pred_none {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D} (h : g x = none) :
    eval M (.pred p x) w g = .indet := by
  simp [eval, h]

open Classical in
theorem eval_pred_some {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D} {d : D}
    (h : g x = some d) : eval M (.pred p x) w g = ofProp (d ∈ M.pred p w) := by
  simp [eval, h]

theorem eval_pred_eq_true_iff {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D} :
    eval M (.pred p x) w g = .true ↔ ∃ d, g x = some d ∧ d ∈ M.pred p w := by
  cases h : g x with
  | none => simp [eval_pred_none h]
  | some d => simp [eval_pred_some h]

theorem eval_pred_eq_false_iff {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D} :
    eval M (.pred p x) w g = .false ↔ ∃ d, g x = some d ∧ d ∉ M.pred p w := by
  cases h : g x with
  | none => simp [eval_pred_none h]
  | some d => simp [eval_pred_some h]

theorem eval_valued {x : ℕ} {w : W} {g : PartialAssign ℕ D} :
    eval M (.valued x) w g = ofBool (g x).isSome := rfl

theorem eval_valued_of_isSome {x : ℕ} {w : W} {g : PartialAssign ℕ D} (h : (g x).isSome) :
    eval M (.valued x) w g = .true := by
  simp [eval_valued, h, ofBool]

theorem eval_valued_of_none {x : ℕ} {w : W} {g : PartialAssign ℕ D} (h : g x = none) :
    eval M (.valued x) w g = .false := by
  simp [eval_valued, h, ofBool]

@[simp] theorem eval_valued_empty (x : ℕ) (w : W) :
    eval M (.valued x) w (PartialAssign.empty : PartialAssign ℕ D) = .false := rfl

theorem eval_not {φ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.not φ) w g = (eval M φ w g).neg := rfl

theorem eval_and {φ ψ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.and φ ψ) w g = meetMiddle (eval M φ w g) (eval M ψ w g) := rfl

theorem eval_or {φ ψ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.or φ ψ) w g = joinMiddle (eval M φ w g) (eval M ψ w g) := rfl

/-- The existential is true exactly when its scope is: the assignment supplies the witness. -/
theorem eval_ex_eq_true_iff {x : ℕ} {φ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.ex x φ) w g = .true ↔ eval M φ w g = .true := by
  simp only [eval]
  split_ifs with h h' <;> simp [h]

/-- The existential is false exactly when its scope is not true and every value falsifies
it, the classical falsity condition. -/
theorem eval_ex_eq_false_iff {x : ℕ} {φ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.ex x φ) w g = .false ↔
      eval M φ w g ≠ .true ∧ ∀ a, eval M φ w (g.update x a) = .false := by
  simp only [eval]
  split_ifs <;> simp [*]

/-- The witness connection: a true existential over a predicate values its variable. -/
theorem isSome_of_eval_ex_pred {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D}
    (h : eval M (.ex x (.pred p x)) w g = .true) : (g x).isSome := by
  obtain ⟨d, hd, -⟩ := eval_pred_eq_true_iff.1 (eval_ex_eq_true_iff.1 h)
  simp [hd]

/-! ### Truth conditions -/

/-- *A table is in the room and it is purple* is true at a world exactly when some individual
is both, the classical reading of *∃x(T(x) ∧ P(x))*. -/
theorem trueAt_conj_iff (T Q : P) (x : ℕ) (w : W) :
    TrueAt M (.and (.ex x (.pred T x)) (.pred Q x)) w ↔
      ∃ d, d ∈ M.pred T w ∧ d ∈ M.pred Q w := by
  constructor
  · rintro ⟨g, hg⟩
    rw [eval_and] at hg
    have h1 : eval M (.ex x (.pred T x)) w g = .true := by
      cases h : eval M (.ex x (.pred T x)) w g <;> simp_all [meetMiddle]
    rw [h1, Trivalent.meetMiddle_true_left] at hg
    obtain ⟨d, hd, hT⟩ := eval_pred_eq_true_iff.1 (eval_ex_eq_true_iff.1 h1)
    obtain ⟨d', hd', hQ⟩ := eval_pred_eq_true_iff.1 hg
    rw [hd] at hd'
    exact ⟨d, hT, Option.some_inj.1 hd' ▸ hQ⟩
  · rintro ⟨d, hT, hQ⟩
    refine ⟨PartialAssign.empty.update x d, ?_⟩
    rw [eval_and, eval_ex_eq_true_iff.2 (eval_pred_eq_true_iff.2 ⟨d, by simp, hT⟩),
      Trivalent.meetMiddle_true_left]
    exact eval_pred_eq_true_iff.2 ⟨d, by simp, hQ⟩

/-- The bathroom sentence *¬∃xB(x) ∨ F(x)* is true at a world exactly when either no
individual is a bathroom or some bathroom is upstairs, the classical reading of
*¬∃xB(x) ∨ ∃x(B(x) ∧ F(x))*. -/
theorem trueAt_bathroom_iff (B F : P) (x : ℕ) (w : W) :
    TrueAt M (.or (.not (.ex x (.pred B x))) (.pred F x)) w ↔
      (∀ d, d ∉ M.pred B w) ∨ ∃ d, d ∈ M.pred B w ∧ d ∈ M.pred F w := by
  constructor
  · rintro ⟨g, hg⟩
    rw [eval_or, eval_not] at hg
    cases hE : eval M (.ex x (.pred B x)) w g with
    | indet => simp [hE, Trivalent.joinMiddle_indet_left] at hg
    | «false» =>
      left
      intro d hd
      obtain ⟨-, hall⟩ := eval_ex_eq_false_iff.1 hE
      obtain ⟨d', hd', hnot⟩ := eval_pred_eq_false_iff.1 (hall d)
      rw [PartialAssign.update_at] at hd'
      exact hnot (Option.some_inj.1 hd' ▸ hd)
    | «true» =>
      right
      rw [hE, Trivalent.neg_true, Trivalent.joinMiddle_false_left] at hg
      obtain ⟨d, hd, hB⟩ := eval_pred_eq_true_iff.1 (eval_ex_eq_true_iff.1 hE)
      obtain ⟨d', hd', hF⟩ := eval_pred_eq_true_iff.1 hg
      rw [hd] at hd'
      exact ⟨d, hB, Option.some_inj.1 hd' ▸ hF⟩
  · rintro (hnone | ⟨d, hB, hF⟩)
    · refine ⟨PartialAssign.empty, ?_⟩
      rw [eval_or, eval_not, eval_ex_eq_false_iff.2 ⟨?_, λ a => ?_⟩]
      · rfl
      · rw [eval_pred_none rfl]; decide
      · exact eval_pred_eq_false_iff.2 ⟨a, PartialAssign.update_at _ _ _, hnone a⟩
    · refine ⟨PartialAssign.empty.update x d, ?_⟩
      rw [eval_or, eval_not, eval_ex_eq_true_iff.2 (eval_pred_eq_true_iff.2 ⟨d, by simp, hB⟩),
        Trivalent.neg_true, Trivalent.joinMiddle_false_left]
      exact eval_pred_eq_true_iff.2 ⟨d, by simp, hF⟩

/-! ### Contexts and Transparency -/

/-- A context: a set of world–assignment pairs. -/
abbrev Ctx (W D : Type*) := Set (W × PartialAssign ℕ D)

/-- The null context, all world–assignment pairs. -/
def nullCtx : Ctx W D := Set.univ

variable (M) in
/-- Stalnakerian update: the pairs of the context at which the accepted sentence is true. -/
def update (C : Ctx W D) (φ : Formula P R) : Ctx W D := {p ∈ C | eval M φ p.1 p.2 = .true}

/-- A frame: a sentence with the occurrence under test as a hole. -/
abbrev Frame (P R : Type*) := Formula P R → Formula P R

variable (M) in
/-- Transparency of the occurrence at the hole of `F`, whose free variable is `x`, in context
`C`: filling the hole with *valued(x) ∧ φ* and with *φ* gives the same value throughout `C`,
for every `φ`. -/
def Transparent (C : Ctx W D) (F : Frame P R) (x : ℕ) : Prop :=
  ∀ φ : Formula P R, ∀ p ∈ C, eval M (F (.and (.valued x) φ)) p.1 p.2 = eval M (F φ) p.1 p.2

/-- A bare pronoun is not transparent in the null context: where the variable is unvalued,
*valued(x) ∧ φ* is false while *φ* may be true. -/
theorem not_transparent_id_null [Nonempty W] (x : ℕ) : ¬ Transparent M nullCtx id x := by
  intro h
  have := h (.not (.valued x)) (Classical.arbitrary W, PartialAssign.empty) trivial
  simp only [id, eval_and, eval_not, eval_valued_empty] at this
  exact absurd this (by decide)

/-- A bare pronoun is transparent wherever the context values its variable. -/
theorem transparent_id_of_valued {C : Ctx W D} {x : ℕ} (hC : ∀ p ∈ C, (p.2 x).isSome) :
    Transparent M C id x := λ _ p hp => by
  simp only [id, eval_and, eval_valued_of_isSome (hC p hp), Trivalent.meetMiddle_true_left]

/-- Accepting *∃xT(x)* leaves `x` valued throughout the updated context. -/
theorem isSome_of_mem_update_ex {C : Ctx W D} {T : P} {x : ℕ} {p : W × PartialAssign ℕ D}
    (hp : p ∈ update M C (.ex x (.pred T x))) : (p.2 x).isSome :=
  isSome_of_eval_ex_pred hp.2

/-- *A table is in the room. It is purple.*: the pronoun is transparent after the accepted
existential. -/
theorem transparent_id_of_update_ex (C : Ctx W D) (T : P) (x : ℕ) :
    Transparent M (update M C (.ex x (.pred T x))) id x :=
  transparent_id_of_valued λ _ hp => isSome_of_mem_update_ex hp

/-- *∃xT(x) ∧ P(x)* is transparent in every context: a true first conjunct values `x`. -/
theorem transparent_forward_conj (C : Ctx W D) (T : P) (x : ℕ) :
    Transparent M C (λ ψ => .and (.ex x (.pred T x)) ψ) x := λ φ p _ => by
  simp only [eval_and]
  exact conj_transparency_parametric _ _ _ λ h => eval_valued_of_isSome (isSome_of_eval_ex_pred h)

/-- *P(x) ∧ ∃xT(x)* is not transparent in the null context: with *φ = P(x)* at an unvalued
variable the plain sentence is undefined and the presuppositional one false. -/
theorem not_transparent_reverse_conj [Nonempty W] (T : P) (x : ℕ) :
    ¬ Transparent M nullCtx (λ ψ => .and ψ (.ex x (.pred T x))) x := by
  intro h
  have := h (.pred T x) (Classical.arbitrary W, PartialAssign.empty) trivial
  simp only [eval_and, eval_valued_empty, eval_pred_none (g := PartialAssign.empty) rfl,
    Trivalent.meetMiddle_false_left, Trivalent.meetMiddle_indet_left] at this
  exact absurd this (by decide)

/-- The bathroom sentence *¬∃xB(x) ∨ H(x)* is transparent in every context: a false first
disjunct is a true existential, which values `x`. -/
theorem transparent_bathroom (C : Ctx W D) (B : P) (x : ℕ) :
    Transparent M C (λ ψ => .or (.not (.ex x (.pred B x))) ψ) x := λ φ p _ => by
  simp only [eval_or, eval_not]
  exact disj_transparency_parametric _ _ _ λ h =>
    eval_valued_of_isSome (isSome_of_eval_ex_pred (Trivalent.neg_eq_false_iff.1 h))

/-- The reversed bathroom sentence *H(x) ∨ ¬∃xB(x)* is not transparent in the null context:
with a tautological *φ* and an unvalued variable, at a world with a bathroom the plain
sentence is true and the presuppositional one undefined. -/
theorem not_transparent_reverse_bathroom (B : P) (x : ℕ) (hw : ∃ w d, d ∈ M.pred B w) :
    ¬ Transparent M nullCtx (λ ψ => .or ψ (.not (.ex x (.pred B x)))) x := by
  intro h
  obtain ⟨w, d, hd⟩ := hw
  have := h (.or (.valued x) (.not (.valued x))) (w, PartialAssign.empty) trivial
  have hE : eval M (.ex x (.pred B x)) w PartialAssign.empty = .indet := by
    cases hE : eval M (.ex x (.pred B x)) w PartialAssign.empty with
    | indet => rfl
    | «true» =>
      have := eval_ex_eq_true_iff.1 hE
      rw [eval_pred_none rfl] at this
      cases this
    | «false» =>
      obtain ⟨-, hall⟩ := eval_ex_eq_false_iff.1 hE
      obtain ⟨d', hd', hnot⟩ := eval_pred_eq_false_iff.1 (hall d)
      rw [PartialAssign.update_at] at hd'
      exact (hnot (Option.some_inj.1 hd' ▸ hd)).elim
  simp only [eval_or, eval_and, eval_not, hE, eval_valued_empty,
    Trivalent.meetMiddle_false_left] at this
  exact absurd this (by decide)

/-! ### Novelty -/

/-- A repeated existential means the same as one existential over the conjunction, which is
never the reading of *someone smokes; someone drinks*. -/
theorem eval_and_ex_ex_eq_true_iff (p q : P) (x : ℕ) (w : W) (g : PartialAssign ℕ D) :
    eval M (.and (.ex x (.pred p x)) (.ex x (.pred q x))) w g = .true ↔
      eval M (.ex x (.and (.pred p x) (.pred q x))) w g = .true := by
  rw [eval_ex_eq_true_iff, eval_and, eval_and]
  constructor
  · intro h
    have h1 : eval M (.ex x (.pred p x)) w g = .true := by
      cases h1 : eval M (.ex x (.pred p x)) w g <;> simp_all [meetMiddle]
    rw [h1, Trivalent.meetMiddle_true_left, eval_ex_eq_true_iff] at h
    rw [eval_ex_eq_true_iff.1 h1, Trivalent.meetMiddle_true_left, h]
  · intro h
    have h1 : eval M (.pred p x) w g = .true := by
      cases h1 : eval M (.pred p x) w g <;> simp_all [meetMiddle]
    rw [h1, Trivalent.meetMiddle_true_left] at h
    rw [eval_ex_eq_true_iff.2 h1, Trivalent.meetMiddle_true_left, eval_ex_eq_true_iff.2 h]

/-- The Novelty Condition rules the repeated existential out. -/
theorem not_novel_repeat (p q : P) (x : ℕ) :
    ¬ Novel [(Formula.ex x (.pred p x) : Formula P R), .ex x (.pred q x)] := by
  simp [Novel, Formula.binders]

/-! ### The failure of covariation -/

/-- In the simplified system *¬∃x¬∃yS(x, y)* is true at a world exactly when some one
individual is spoken to by everyone: the embedded existential takes wide scope. -/
theorem trueAt_notExNotEx_iff [Nonempty D] (S : R) {x y : ℕ} (hxy : x ≠ y) (w : W) :
    TrueAt M (.not (.ex x (.not (.ex y (.rel S x y))))) w ↔
      ∃ b, ∀ a, (a, b) ∈ M.rel S w := by
  have key : ∀ (g : PartialAssign ℕ D) (a : D),
      eval M (.not (.ex y (.rel S x y))) w (g.update x a) = .false ↔
        ∃ b, g y = some b ∧ (a, b) ∈ M.rel S w := by
    intro g a
    rw [eval_not, Trivalent.neg_eq_false_iff, eval_ex_eq_true_iff]
    cases hy : g y with
    | none => simp [eval, hy, PartialAssign.update_ne _ _ hxy.symm]
    | some b => simp [eval, hy, PartialAssign.update_ne _ _ hxy.symm]
  constructor
  · rintro ⟨g, hg⟩
    rw [eval_not, Trivalent.neg_eq_true_iff, eval_ex_eq_false_iff] at hg
    obtain ⟨-, hall⟩ := hg
    obtain ⟨a₀⟩ := ‹Nonempty D›
    obtain ⟨b, hb, -⟩ := (key g a₀).1 (hall a₀)
    refine ⟨b, λ a => ?_⟩
    obtain ⟨b', hb', hS⟩ := (key g a).1 (hall a)
    rw [hb] at hb'
    exact Option.some_inj.1 hb' ▸ hS
  · rintro ⟨b, hb⟩
    refine ⟨PartialAssign.empty.update y b, ?_⟩
    rw [eval_not, Trivalent.neg_eq_true_iff, eval_ex_eq_false_iff]
    refine ⟨λ hne => ?_, λ a => (key _ a).2 ⟨b, by simp, hb a⟩⟩
    rw [eval_not, Trivalent.neg_eq_true_iff, eval_ex_eq_false_iff] at hne
    obtain ⟨a₀⟩ := ‹Nonempty D›
    have := hne.2 a₀
    simp [eval, PartialAssign.update_ne _ _ hxy, PartialAssign.empty] at this

/-! ### The full system: plural assignments -/

variable (M) in
open Classical in
/-- Evaluation at a world and a plural assignment. A predicate of a variable is defined when
the assignments valuing the variable agree, and `valued` now reads as the paper's *atomic*;
the existential is false only when the plural assignment covers the domain and every
restriction falsifies the scope; the universal is true under that coverage when every
restriction verifies the scope; the strong-truth operator is true when its argument is true
here and false at no plural assignment, false when its argument is false here and true at no
plural assignment. -/
noncomputable def evalP : Formula P R → W → PluralAssign ℕ D → Trivalent
  | .pred p x, w, G =>
    if ∃ d, G.SingularAt x d ∧ d ∈ M.pred p w then .true
    else if ∃ d, G.SingularAt x d ∧ d ∉ M.pred p w then .false
    else .indet
  | .rel r x y, w, G =>
    if ∃ a b, G.SingularAt x a ∧ G.SingularAt y b ∧ (a, b) ∈ M.rel r w then .true
    else if ∃ a b, G.SingularAt x a ∧ G.SingularAt y b ∧ (a, b) ∉ M.rel r w then .false
    else .indet
  | .valued x, _, G => ofProp (G.Singular x)
  | .not φ, w, G => (evalP φ w G).neg
  | .and φ ψ, w, G => meetMiddle (evalP φ w G) (evalP ψ w G)
  | .or φ ψ, w, G => joinMiddle (evalP φ w G) (evalP ψ w G)
  | .ex x φ, w, G =>
    if evalP φ w G = .true then .true
    else if ∀ a, (G.restrict x a).Nonempty ∧ evalP φ w (G.restrict x a) = .false then .false
    else .indet
  | .all x φ, w, G =>
    if ∀ a, (G.restrict x a).Nonempty ∧ evalP φ w (G.restrict x a) = .true then .true
    else if (∀ a, (G.restrict x a).Nonempty) ∧ ∃ a, evalP φ w (G.restrict x a) = .false then
      .false
    else .indet
  | .strong φ, w, G =>
    if evalP φ w G = .true ∧ ∀ G', evalP φ w G' ≠ .false then .true
    else if evalP φ w G = .false ∧ ∀ G', evalP φ w G' ≠ .true then .false
    else .indet

variable (M) in
/-- Weak truth at a world: some plural assignment makes the sentence true. -/
def TrueAtP (φ : Formula P R) (w : W) : Prop := ∃ G : PluralAssign ℕ D, evalP M φ w G = .true

variable (M) in
/-- Strong truth at a world: some plural assignment makes the sentence true and none makes
it false. -/
def StronglyTrueAt (φ : Formula P R) (w : W) : Prop :=
  TrueAtP M φ w ∧ ∀ G : PluralAssign ℕ D, evalP M φ w G ≠ .false

theorem StronglyTrueAt.trueAtP {φ : Formula P R} {w : W} (h : StronglyTrueAt M φ w) :
    TrueAtP M φ w :=
  h.1

section Lemmas

variable {p : P} {r : R} {x y : ℕ} {φ ψ : Formula P R} {w : W} {G : PluralAssign ℕ D}

theorem evalP_pred_eq_true_iff :
    evalP M (.pred p x) w G = .true ↔ ∃ d, G.SingularAt x d ∧ d ∈ M.pred p w := by
  simp only [evalP]
  split_ifs <;> simp [*]

theorem evalP_pred_eq_false_iff :
    evalP M (.pred p x) w G = .false ↔ ∃ d, G.SingularAt x d ∧ d ∉ M.pred p w := by
  simp only [evalP]
  split_ifs with h1 h2
  · refine iff_of_false (by decide) ?_
    rintro ⟨d', hd', hn⟩
    obtain ⟨d, hd, hm⟩ := h1
    exact hn (by rw [hd'.unique hd]; exact hm)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2

theorem evalP_rel_eq_true_iff :
    evalP M (.rel r x y) w G = .true ↔
      ∃ a b, G.SingularAt x a ∧ G.SingularAt y b ∧ (a, b) ∈ M.rel r w := by
  simp only [evalP]
  split_ifs with h1 h2
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

theorem evalP_rel_eq_false_iff :
    evalP M (.rel r x y) w G = .false ↔
      ∃ a b, G.SingularAt x a ∧ G.SingularAt y b ∧ (a, b) ∉ M.rel r w := by
  simp only [evalP]
  split_ifs with h1 h2
  · refine iff_of_false (by decide) ?_
    rintro ⟨a', b', ha', hb', hn⟩
    obtain ⟨a, b, ha, hb, hm⟩ := h1
    exact hn (by rw [ha'.unique ha, hb'.unique hb]; exact hm)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2

theorem evalP_valued_eq_true_iff : evalP M (.valued x) w G = .true ↔ G.Singular x := by
  simp [evalP]

theorem evalP_valued_eq_false_iff : evalP M (.valued x) w G = .false ↔ ¬ G.Singular x := by
  simp [evalP]

theorem evalP_not : evalP M (.not φ) w G = (evalP M φ w G).neg := rfl

theorem evalP_and : evalP M (.and φ ψ) w G = meetMiddle (evalP M φ w G) (evalP M ψ w G) := rfl

theorem evalP_or : evalP M (.or φ ψ) w G = joinMiddle (evalP M φ w G) (evalP M ψ w G) := rfl

theorem evalP_ex_eq_true_iff : evalP M (.ex x φ) w G = .true ↔ evalP M φ w G = .true := by
  simp only [evalP]
  split_ifs <;> simp [*]

theorem evalP_ex_eq_false_iff :
    evalP M (.ex x φ) w G = .false ↔ evalP M φ w G ≠ .true ∧
      ∀ a, (G.restrict x a).Nonempty ∧ evalP M φ w (G.restrict x a) = .false := by
  simp only [evalP]
  split_ifs <;> simp [*]

theorem evalP_all_eq_true_iff :
    evalP M (.all x φ) w G = .true ↔
      ∀ a, (G.restrict x a).Nonempty ∧ evalP M φ w (G.restrict x a) = .true := by
  simp only [evalP]
  split_ifs with h1 h2
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

theorem evalP_strong_eq_true_iff :
    evalP M (.strong φ) w G = .true ↔
      evalP M φ w G = .true ∧ ∀ G', evalP M φ w G' ≠ .false := by
  simp only [evalP]
  split_ifs <;> simp [*]

/-- The witness connection: a true existential over a predicate makes its variable atomic. -/
theorem singular_of_evalP_ex_pred (h : evalP M (.ex x (.pred p x)) w G = .true) :
    G.Singular x :=
  (evalP_pred_eq_true_iff.1 (evalP_ex_eq_true_iff.1 h)).elim λ _ h => h.1.singular

theorem evalP_strong_eq_false_iff :
    evalP M (.strong φ) w G = .false ↔
      evalP M φ w G = .false ∧ ∀ G', evalP M φ w G' ≠ .true := by
  simp only [evalP]
  split_ifs <;> simp [*]

end Lemmas

/-! ### Transparency in the full system -/

/-- A context of world–plural-assignment pairs. -/
abbrev CtxP (W D : Type*) := Set (W × PluralAssign ℕ D)

variable (M) in
/-- Transparency with the atomicity presupposition: filling the hole of `F` with
*atomic(x) ∧ φ* and with *φ* gives the same value throughout `C`, for every `φ`. -/
def TransparentP (C : CtxP W D) (F : Frame P R) (x : ℕ) : Prop :=
  ∀ φ : Formula P R, ∀ p ∈ C,
    evalP M (F (.and (.valued x) φ)) p.1 p.2 = evalP M (F φ) p.1 p.2

/-- *∃xT(x) ∧ P(x)* is transparent in every context of the full system. -/
theorem transparentP_forward_conj (C : CtxP W D) (T : P) (x : ℕ) :
    TransparentP M C (λ ψ => .and (.ex x (.pred T x)) ψ) x := λ φ p _ => by
  simp only [evalP_and]
  exact conj_transparency_parametric _ _ _ λ h =>
    evalP_valued_eq_true_iff.2 (singular_of_evalP_ex_pred h)

/-- The bathroom sentence is transparent in every context of the full system. -/
theorem transparentP_bathroom (C : CtxP W D) (B : P) (x : ℕ) :
    TransparentP M C (λ ψ => .or (.not (.ex x (.pred B x))) ψ) x := λ φ p _ => by
  simp only [evalP_or, evalP_not]
  exact disj_transparency_parametric _ _ _ λ h =>
    evalP_valued_eq_true_iff.2 (singular_of_evalP_ex_pred (Trivalent.neg_eq_false_iff.1 h))

/-- A plural assignment covering a domain with two individuals is not atomic at the covered
variable. -/
theorem not_singular_of_covers {G : PluralAssign ℕ D} {x : ℕ} {a b : D} (hab : a ≠ b)
    (hcov : ∀ a, (G.restrict x a).Nonempty) : ¬ G.Singular x := by
  rintro ⟨d, hd⟩
  obtain ⟨_, hga⟩ := hcov a
  obtain ⟨_, hgb⟩ := hcov b
  exact hab ((hd.eq_of_mem_restrict hga).trans (hd.eq_of_mem_restrict hgb).symm)

/-- *∀xP(x) ∧ Q(x)*: a universal does not license a singular pronoun. In a context
containing a pair at which *∀xP(x)* is true, over a domain with two individuals, the
occurrence *Q(x)* is not transparent, because *∀xP(x) ∧ (atomic(x) ∧ φ)* is never true
there while *∀xP(x) ∧ φ* is for a tautological *φ*. -/
theorem not_transparentP_forall_conj {a b : D} (hab : a ≠ b) {C : CtxP W D} {P₀ : P} {x : ℕ}
    {w : W} {G : PluralAssign ℕ D} (hC : (w, G) ∈ C)
    (hall : evalP M (.all x (.pred P₀ x)) w G = .true) :
    ¬ TransparentP M C (λ ψ => .and (.all x (.pred P₀ x)) ψ) x := by
  intro h
  have hx : evalP M (.valued x) w G = .false :=
    evalP_valued_eq_false_iff.2
      (not_singular_of_covers hab λ a => ((evalP_all_eq_true_iff.1 hall) a).1)
  have := h (.not (.valued x)) (w, G) hC
  simp only [evalP_and, evalP_not, hall, hx, Trivalent.meetMiddle_true_left,
    Trivalent.meetMiddle_false_left] at this
  exact absurd this (by decide)

variable (D) in
/-- The plural assignment mapping `x` to every individual, one row each. -/
def covering (x : ℕ) : PluralAssign ℕ D := Set.range (PartialAssign.empty.update x)

theorem restrict_covering_nonempty (x : ℕ) (a : D) : ((covering D x).restrict x a).Nonempty :=
  ⟨PartialAssign.empty.update x a, ⟨a, rfl⟩, by simp⟩

/-- The null context contains such a pair whenever some world makes the universal true. -/
theorem not_transparentP_forall_conj_univ {a b : D} (hab : a ≠ b) {P₀ : P} (x : ℕ)
    (hw : ∃ w, ∀ d, d ∈ M.pred P₀ w) :
    ¬ TransparentP M Set.univ (λ ψ => .and (.all x (.pred P₀ x)) ψ) x := by
  obtain ⟨w, hw⟩ := hw
  refine not_transparentP_forall_conj hab (w := w) (G := covering D x) (Set.mem_univ _)
    (evalP_all_eq_true_iff.2 λ a => ⟨restrict_covering_nonempty x a, ?_⟩)
  exact evalP_pred_eq_true_iff.2
    ⟨a, PluralAssign.singularAt_restrict (restrict_covering_nonempty x a), hw a⟩

/-- *∃xP(x) ∧ ∀xQ(x)* is never true over a domain with two individuals: the existential
makes the variable atomic and the universal requires it to cover the domain. -/
theorem evalP_ex_and_all_ne_true {a b : D} (hab : a ≠ b) (P₀ Q : P) (x : ℕ) (w : W)
    (G : PluralAssign ℕ D) :
    evalP M (.and (.ex x (.pred P₀ x)) (.all x (.pred Q x))) w G ≠ .true := by
  intro h
  rw [evalP_and, Trivalent.meetMiddle_eq_true_iff] at h
  exact not_singular_of_covers hab (λ a => ((evalP_all_eq_true_iff.1 h.2) a).1)
    (singular_of_evalP_ex_pred h.1)

/-! ### Truth conditions in the full system -/

/-- The bathroom sentence keeps its classical truth conditions in the full system. -/
theorem trueAtP_bathroom_iff (B F : P) (x : ℕ) (w : W) :
    TrueAtP M (.or (.not (.ex x (.pred B x))) (.pred F x)) w ↔
      (∀ d, d ∉ M.pred B w) ∨ ∃ d, d ∈ M.pred B w ∧ d ∈ M.pred F w := by
  constructor
  · rintro ⟨G, hG⟩
    rw [evalP_or, evalP_not] at hG
    cases hE : evalP M (.ex x (.pred B x)) w G with
    | indet => simp [hE, Trivalent.joinMiddle_indet_left] at hG
    | «false» =>
      left
      intro d hd
      obtain ⟨-, hall⟩ := evalP_ex_eq_false_iff.1 hE
      obtain ⟨hne, hfalse⟩ := hall d
      obtain ⟨d', hd', hn⟩ := evalP_pred_eq_false_iff.1 hfalse
      exact hn ((PluralAssign.singularAt_restrict_iff.1 hd').2 ▸ hd)
    | «true» =>
      right
      rw [hE, Trivalent.neg_true, Trivalent.joinMiddle_false_left] at hG
      obtain ⟨d, hd, hB⟩ := evalP_pred_eq_true_iff.1 (evalP_ex_eq_true_iff.1 hE)
      obtain ⟨d', hd', hF⟩ := evalP_pred_eq_true_iff.1 hG
      exact ⟨d, hB, hd.unique hd' ▸ hF⟩
  · rintro (hnone | ⟨d, hB, hF⟩)
    · refine ⟨covering D x, ?_⟩
      rw [evalP_or, evalP_not, evalP_ex_eq_false_iff.2 ⟨?_, λ a => ?_⟩, Trivalent.neg_false,
        Trivalent.joinMiddle_true_left]
      · rw [Ne, evalP_pred_eq_true_iff]
        rintro ⟨d, -, hd⟩
        exact hnone d hd
      · exact ⟨restrict_covering_nonempty x a, evalP_pred_eq_false_iff.2
          ⟨a, PluralAssign.singularAt_restrict (restrict_covering_nonempty x a), hnone a⟩⟩
    · refine ⟨{PartialAssign.empty.update x d}, ?_⟩
      have hsing : ({PartialAssign.empty.update x d} : PluralAssign ℕ D).SingularAt x d :=
        PluralAssign.singularAt_singleton.2 (by simp)
      rw [evalP_or, evalP_not, evalP_ex_eq_true_iff.2 (evalP_pred_eq_true_iff.2 ⟨d, hsing, hB⟩),
        Trivalent.neg_true, Trivalent.joinMiddle_false_left]
      exact evalP_pred_eq_true_iff.2 ⟨d, hsing, hF⟩

/-- The plural assignment pairing each individual `a` at `x` with `f a` at `y`. -/
def pairing (x y : ℕ) (f : D → D) : PluralAssign ℕ D :=
  Set.range λ a => (PartialAssign.empty.update x a).update y (f a)

/-- A restriction of the pairing to `x = a` is nonempty and atomic at `y` with value `f a`. -/
theorem restrict_pairing {x y : ℕ} (hxy : x ≠ y) (f : D → D) (a : D) :
    ((pairing x y f).restrict x a).Nonempty ∧
      ((pairing x y f).restrict x a).SingularAt y (f a) := by
  have hmem : ∀ a', (PartialAssign.empty.update x a').update y (f a') ∈
      (pairing x y f).restrict x a ↔ a' = a := by
    intro a'
    constructor
    · rintro ⟨-, h⟩
      simpa [PartialAssign.update_ne _ _ hxy] using h
    · rintro rfl
      exact ⟨⟨a', rfl⟩, by simp [PartialAssign.update_ne _ _ hxy]⟩
  refine ⟨⟨_, (hmem a).2 rfl⟩, ⟨_, (hmem a).2 rfl, by simp⟩, ?_⟩
  rintro g ⟨⟨a', rfl⟩, hga⟩ -
  rw [(hmem a').1 ⟨⟨a', rfl⟩, hga⟩]
  simp

/-- Covariation restored: *¬∃x¬∃yS(x, y)* is true in the full system exactly when everyone
spoke to someone, because the embedded existential is evaluated at each restriction. -/
theorem trueAtP_notExNotEx_iff [Nonempty D] (S : R) {x y : ℕ} (hxy : x ≠ y) (w : W) :
    TrueAtP M (.not (.ex x (.not (.ex y (.rel S x y))))) w ↔
      ∀ a, ∃ b, (a, b) ∈ M.rel S w := by
  constructor
  · rintro ⟨G, hG⟩
    rw [evalP_not, Trivalent.neg_eq_true_iff, evalP_ex_eq_false_iff] at hG
    intro a
    obtain ⟨hne, hfalse⟩ := hG.2 a
    rw [evalP_not, Trivalent.neg_eq_false_iff, evalP_ex_eq_true_iff,
      evalP_rel_eq_true_iff] at hfalse
    obtain ⟨a', b, ha', hb, hS⟩ := hfalse
    exact ⟨b, (PluralAssign.singularAt_restrict_iff.1 ha').2 ▸ hS⟩
  · intro hS
    choose f hf using hS
    refine ⟨pairing x y f, ?_⟩
    rw [evalP_not, Trivalent.neg_eq_true_iff, evalP_ex_eq_false_iff]
    refine ⟨?_, λ a => ?_⟩
    · rw [Ne, evalP_not, Trivalent.neg_eq_true_iff, evalP_ex_eq_false_iff]
      rintro ⟨-, hall⟩
      obtain ⟨a₀⟩ := ‹Nonempty D›
      obtain ⟨-, hfalse⟩ := hall (f a₀)
      obtain ⟨a', b', ha', hb', hn⟩ := evalP_rel_eq_false_iff.1 hfalse
      have hg₀ : (PartialAssign.empty.update x a₀).update y (f a₀) ∈
          (pairing x y f).restrict y (f a₀) :=
        ⟨⟨a₀, rfl⟩, by simp⟩
      have hx := ha'.2 _ hg₀ (by simp [PartialAssign.update_ne _ _ hxy])
      rw [PartialAssign.update_ne _ _ hxy, PartialAssign.update_at, Option.some_inj] at hx
      rw [← hx, (PluralAssign.singularAt_restrict_iff.1 hb').2] at hn
      exact hn (hf a₀)
    · obtain ⟨hne, hsing⟩ := restrict_pairing hxy f a
      refine ⟨hne, ?_⟩
      rw [evalP_not, Trivalent.neg_eq_false_iff, evalP_ex_eq_true_iff, evalP_rel_eq_true_iff]
      exact ⟨a, f a, PluralAssign.singularAt_restrict hne, hsing, hf a⟩

/-- *∀x∃yS(x, y)* is true exactly when everyone spoke to someone. -/
theorem trueAtP_allEx_iff (S : R) {x y : ℕ} (hxy : x ≠ y) (w : W) :
    TrueAtP M (.all x (.ex y (.rel S x y))) w ↔ ∀ a, ∃ b, (a, b) ∈ M.rel S w := by
  constructor
  · rintro ⟨G, hG⟩
    intro a
    obtain ⟨-, htrue⟩ := evalP_all_eq_true_iff.1 hG a
    obtain ⟨a', b, ha', hb, hS⟩ := evalP_rel_eq_true_iff.1 (evalP_ex_eq_true_iff.1 htrue)
    exact ⟨b, (PluralAssign.singularAt_restrict_iff.1 ha').2 ▸ hS⟩
  · intro hS
    choose f hf using hS
    refine ⟨pairing x y f, evalP_all_eq_true_iff.2 λ a => ?_⟩
    obtain ⟨hne, hsing⟩ := restrict_pairing hxy f a
    exact ⟨hne, evalP_ex_eq_true_iff.2 (evalP_rel_eq_true_iff.2
      ⟨a, f a, PluralAssign.singularAt_restrict hne, hsing, hf a⟩)⟩

/-- *Everybody spoke to someone* and *not a single person failed to speak to someone* are
true at the same worlds. -/
theorem trueAtP_allEx_iff_notExNotEx [Nonempty D] (S : R) {x y : ℕ} (hxy : x ≠ y) (w : W) :
    TrueAtP M (.all x (.ex y (.rel S x y))) w ↔
      TrueAtP M (.not (.ex x (.not (.ex y (.rel S x y))))) w := by
  rw [trueAtP_allEx_iff S hxy, trueAtP_notExNotEx_iff S hxy]

/-! ### Weak and strong truth -/

/-- On a simple existential, strong truth and weak truth coincide. -/
theorem stronglyTrueAt_ex_iff (P₀ : P) (x : ℕ) (w : W) :
    StronglyTrueAt M (.ex x (.pred P₀ x)) w ↔ TrueAtP M (.ex x (.pred P₀ x)) w := by
  refine ⟨StronglyTrueAt.trueAtP, λ h => ⟨h, λ G' hG' => ?_⟩⟩
  obtain ⟨G, hG⟩ := h
  obtain ⟨d, -, hd⟩ := evalP_pred_eq_true_iff.1 (evalP_ex_eq_true_iff.1 hG)
  obtain ⟨-, hall⟩ := evalP_ex_eq_false_iff.1 hG'
  obtain ⟨-, hfalse⟩ := hall d
  obtain ⟨d', hd', hn⟩ := evalP_pred_eq_false_iff.1 hfalse
  exact hn (by rw [(PluralAssign.singularAt_restrict_iff.1 hd').2]; exact hd)

/-- *There is a bathroom and it is upstairs* is weakly but not strongly true at a world with
a bathroom upstairs and a bathroom that is not. -/
theorem trueAtP_not_stronglyTrueAt_conj (B F : P) (x : ℕ) (w : W) {b₁ b₂ : D}
    (h₁ : b₁ ∈ M.pred B w) (h₂ : b₂ ∈ M.pred B w) (hF₁ : b₁ ∈ M.pred F w)
    (hF₂ : b₂ ∉ M.pred F w) :
    TrueAtP M (.and (.ex x (.pred B x)) (.pred F x)) w ∧
      ¬ StronglyTrueAt M (.and (.ex x (.pred B x)) (.pred F x)) w := by
  have hs : ∀ d : D, ({PartialAssign.empty.update x d} : PluralAssign ℕ D).SingularAt x d :=
    λ d => PluralAssign.singularAt_singleton.2 (by simp)
  refine ⟨⟨{PartialAssign.empty.update x b₁}, ?_⟩,
    λ h => h.2 {PartialAssign.empty.update x b₂} ?_⟩
  · rw [evalP_and, evalP_ex_eq_true_iff.2 (evalP_pred_eq_true_iff.2 ⟨b₁, hs b₁, h₁⟩),
      Trivalent.meetMiddle_true_left]
    exact evalP_pred_eq_true_iff.2 ⟨b₁, hs b₁, hF₁⟩
  · rw [evalP_and, evalP_ex_eq_true_iff.2 (evalP_pred_eq_true_iff.2 ⟨b₂, hs b₂, h₂⟩),
      Trivalent.meetMiddle_true_left]
    exact evalP_pred_eq_false_iff.2 ⟨b₂, hs b₂, hF₂⟩

/-- Weak truth of *O(S)* is strong truth of *S*. -/
theorem trueAtP_strong_iff (φ : Formula P R) (w : W) :
    TrueAtP M (.strong φ) w ↔ StronglyTrueAt M φ w := by
  constructor
  · rintro ⟨G, hG⟩
    obtain ⟨h1, h2⟩ := evalP_strong_eq_true_iff.1 hG
    exact ⟨⟨G, h1⟩, h2⟩
  · rintro ⟨⟨G, hG⟩, h⟩
    exact ⟨G, evalP_strong_eq_true_iff.2 ⟨hG, h⟩⟩

/-- Logically equivalent sentences stay equivalent under *O*. -/
theorem evalP_strong_congr {φ ψ : Formula P R} {w : W}
    (h : ∀ G, evalP M φ w G = evalP M ψ w G) (G : PluralAssign ℕ D) :
    evalP M (.strong φ) w G = evalP M (.strong ψ) w G := by
  simp only [evalP]
  rw [funext h]

/-- *O(atomic(x))* is undefined everywhere: a singleton plural assignment makes *atomic(x)*
true and the empty one makes it false. -/
theorem evalP_strong_valued [Nonempty D] (x : ℕ) (w : W) (G : PluralAssign ℕ D) :
    evalP M (.strong (.valued x)) w G = .indet := by
  obtain ⟨d⟩ := ‹Nonempty D›
  have ht : evalP M (.valued x) w {PartialAssign.empty.update x d} = .true :=
    evalP_valued_eq_true_iff.2 ⟨d, PluralAssign.singularAt_singleton.2 (by simp)⟩
  have hf : evalP M (.valued x) w ∅ = .false :=
    evalP_valued_eq_false_iff.2 (by simp [PluralAssign.Singular, PluralAssign.SingularAt])
  cases h : evalP M (.strong (.valued x)) w G with
  | indet => rfl
  | «true» => exact absurd hf ((evalP_strong_eq_true_iff.1 h).2 _)
  | «false» => exact absurd ht ((evalP_strong_eq_false_iff.1 h).2 _)

/-- *∃xS(x) ∧ O(H(x))* means that something is an *S* and everything is an *H*. -/
theorem trueAtP_ex_and_strong_iff (S H : P) (x : ℕ) (w : W) :
    TrueAtP M (.and (.ex x (.pred S x)) (.strong (.pred H x))) w ↔
      (∃ d, d ∈ M.pred S w) ∧ ∀ d, d ∈ M.pred H w := by
  constructor
  · rintro ⟨G, hG⟩
    rw [evalP_and, Trivalent.meetMiddle_eq_true_iff, evalP_ex_eq_true_iff,
      evalP_pred_eq_true_iff, evalP_strong_eq_true_iff] at hG
    obtain ⟨⟨d, -, hd⟩, -, hall⟩ := hG
    refine ⟨⟨d, hd⟩, λ d => by_contra λ hn => hall {PartialAssign.empty.update x d} ?_⟩
    exact evalP_pred_eq_false_iff.2 ⟨d, PluralAssign.singularAt_singleton.2 (by simp), hn⟩
  · rintro ⟨⟨d, hd⟩, hall⟩
    have hs : ({PartialAssign.empty.update x d} : PluralAssign ℕ D).SingularAt x d :=
      PluralAssign.singularAt_singleton.2 (by simp)
    refine ⟨{PartialAssign.empty.update x d}, ?_⟩
    rw [evalP_and, Trivalent.meetMiddle_eq_true_iff, evalP_ex_eq_true_iff,
      evalP_strong_eq_true_iff]
    refine ⟨evalP_pred_eq_true_iff.2 ⟨d, hs, hd⟩, evalP_pred_eq_true_iff.2 ⟨d, hs, hall d⟩,
      λ G' hG' => ?_⟩
    obtain ⟨d', -, hn⟩ := evalP_pred_eq_false_iff.1 hG'
    exact hn (hall d')

/-- *∃xS(x) ∧ O(H(x))* violates Transparency: at a pair where *∃xS(x)* is true, a
tautological *φ* makes *∃xS(x) ∧ O(φ)* true but *∃xS(x) ∧ O(atomic(x) ∧ φ)* undefined. -/
theorem not_transparentP_ex_and_strong {C : CtxP W D} {S : P} {x : ℕ} {w : W}
    {G : PluralAssign ℕ D} (hC : (w, G) ∈ C) (hS : evalP M (.ex x (.pred S x)) w G = .true) :
    ¬ TransparentP M C (λ ψ => .and (.ex x (.pred S x)) (.strong ψ)) x := by
  intro h
  obtain ⟨d, -⟩ := singular_of_evalP_ex_pred hS
  have : Nonempty D := ⟨d⟩
  have htaut : ∀ G', evalP M (.or (.valued x) (.not (.valued x))) w G' = .true := by
    intro G'
    rw [evalP_or, evalP_not]
    cases hv : evalP M (.valued x) w G' with
    | indet => exact absurd hv (by simp [evalP])
    | «true» | «false» => rfl
  have hconj : ∀ G', evalP M (.and (.valued x) (.or (.valued x) (.not (.valued x)))) w G' =
      evalP M (.valued x) w G' := λ G' => by
    rw [evalP_and, htaut, Trivalent.meetMiddle_true_right]
  have := h (.or (.valued x) (.not (.valued x))) (w, G) hC
  simp only [evalP_and, hS, Trivalent.meetMiddle_true_left, evalP_strong_congr hconj,
    evalP_strong_valued, evalP_strong_eq_true_iff.2 ⟨htaut G, λ G' => by rw [htaut G']; decide⟩]
    at this
  exact absurd this (by decide)

end Spector2025
