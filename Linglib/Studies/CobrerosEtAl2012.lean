import Linglib.Logic.Modal.Basic
import Linglib.Logic.Trivalent.Propositional

/-!
# Cobreros, Égré, Ripley and van Rooij 2012: Tolerant, classical, strict

A T-model is a classical model whose predicates each carry an indifference relation `∼_P`,
reflexive and symmetric but possibly non-transitive (Definition 4), the vague predicate's
"looks the same with respect to `P`". Besides classical truth a T-model supports two further
notions defined by simultaneous induction (Definition 9): `Pa` is strictly true when every
`∼_P`-neighbour of `a` is classically `P` and tolerantly true when some neighbour is, negation
swapping the two, so that the strict extension sharpens and the tolerant extension coarsens
the classical one (Lemma 1) and the tolerance principle `Pa ∧ a I_P b → Pb` is tolerantly
valid (Fact 2) up to two similarity steps (Fact 3). Borderline cases are the tolerantly-but-
not-strictly `P` individuals (Definition 10), the ones tolerantly both `P` and `¬P`. On the
similarity-free vocabulary tolerant validity is classical validity while nothing is strictly
valid (Theorems 1 and 2), so strict validity is not supervaluationist validity ([fine-1975]),
which is classical; and tolerant and strict consequence are Priest's LP and strong Kleene K3
([kleene-1952]) (Theorem 3), via the model correspondences of Lemmas 4 and 5. Mixing the three
notions gives nine consequence relations `⊨ᵐⁿ` (Definition 17), ordered by Lemma 7, dualised
by Lemma 6, collapsing to four on the restricted vocabulary (Lemmas 8 and 9) but distinct once
similarity statements are expressible (§3.4), where the deduction theorem singles out the
self-dual `st`, `cc` and `ts` (Lemma 10). The paper's choice is `st`, strict premises to
tolerant conclusions: it validates tolerance and modus ponens and is non-transitive, so it
validates every step of a sorites while invalidating the chain (§3.6, Version 1), and it makes
the tolerance-premise sorites valid but unsound, its tolerance premise not being strictly true
(Version 2). The five-men model of §4.2.3 gives the paper's account of
[alxatib-pelletier-2011]'s data: the median man is borderline however he is classified.

## Main definitions

* `TModel`, `TModel.Realize`, `Mode` — T-models and their three notions of truth, the modes
  ordered by strength `strict < classical < tolerant`.
* `TModel.Borderline` — Definition 10.
* `Valid`, `Consequence` — Definitions 11 and 17.
* `IsRestricted`, `TModel.identity`, `allBorderline`, `toMV`, `ofMV` — the restricted
  vocabulary and the models of Lemmas 2, 3, 4 and 5.
* `series` — the sorites series of §3.4.1 and §3.6, whose instances are the four-element model
  of p. 354 and the five-men model of §4.2.3.

## Main results

* `TModel.realize_mono` (Lemma 1), `satDuality` (Remark 1), `tolerance_valid` (Fact 2),
  `st_two_step` (Fact 3).
* `TModel.Borderline.exists_ne` — a model with a borderline case has two (footnote 4);
  `TModel.eq_tolerant_of_realize_conj_neg` — a contradiction can only be tolerantly true.
* `valid_tolerant_iff`, `unsat_strict_iff` (Theorem 1); `not_valid_strict`,
  `exists_realize_tolerant` (Theorem 2); `consequence_tolerant_iff_lp`,
  `consequence_strict_iff_k3` (Theorem 3).
* `Consequence.dual` (Lemma 6), `Consequence.mono` (Lemma 7), `Consequence.restricted_iff`
  (Lemma 8), `not_consequence_tolerant_strict` (Lemma 9), `Consequence.imp_iff` (Lemma 10).
* `not_cc_one_step`, `not_valid_classical_tolerance`, `not_sc_two_step`, `not_ct_two_step` —
  the §3.4 distinctness of `cc`, `sc`, `ct` and `st`, on the four-element model.
* `not_st_version1`, `st_version2`, `not_series_realize_strict_tolerance` — the sorites of
  §3.6.
* `alxatibPelletier_median_borderline` — the five-men model of §4.2.3.

## Implementation notes

The language is the paper's propositional fragment over a set of constants `C`: negation and
conjunction over predications `Pa` and similarity statements `a I_P b`, with disjunction and
the conditional defined classically. The universally quantified principles appear as their
instances, which the paper notes changes nothing (§3.6). Identity, which the paper adds in
§2.3.1, is not represented. Consequence quantifies over T-models of every domain in the
universe of `C` (`TModels`), as the paper's does; the atomic strict and tolerant clauses are
`ModalLogic.box` and `ModalLogic.diamond` along `∼_P`, so Lemma 1's atomic case is the T axiom.

## References

* [P. Cobreros, P. Égré, D. Ripley and R. van Rooij, *Tolerant, Classical, Strict*
  (2012)][cobreros-etal-2012]
* [S. Alxatib and F. J. Pelletier, *The Psychology of Vagueness: Borderline Cases and
  Contradictions* (2011)][alxatib-pelletier-2011]
* [K. Fine, *Vagueness, truth and logic* (1975)][fine-1975]
* [S. C. Kleene, *Introduction to Metamathematics* (1952)][kleene-1952]
-/

universe u

namespace CobrerosEtAl2012

open ModalLogic (IsKTBFrame box diamond box_T)
open scoped ModalLogic Trivalent.Formula
open Consequence (MixedConsequence mnValid mnValid_iff_emptyPremise IsSelfDual mixed_monotone
  consequence_dual)

/-! ### T-models -/

/-- A T-model (Definition 4): a classical model of the constants `C` and predicates `Pred` over
the domain `D`, with for each predicate a reflexive and symmetric, possibly non-transitive,
indifference relation `∼_P`. -/
structure TModel (Pred C : Type*) (D : Type*) where
  /-- The interpretation of the constants. -/
  const : C → D
  /-- The classical extension of each predicate. -/
  interp : Pred → D → Prop
  /-- The indifference relation `∼_P` of each predicate. -/
  sim : Pred → D → D → Prop
  sim_ktb : ∀ P, IsKTBFrame (sim P)

variable {Pred : Type*} {C : Type u} {D : Type*}

instance (M : TModel Pred C D) (P : Pred) : IsKTBFrame (M.sim P) := M.sim_ktb P

/-- The three notions of truth, ordered by strength: `strict < classical < tolerant`. -/
inductive Mode
  | strict
  | classical
  | tolerant
  deriving DecidableEq, Fintype

namespace Mode

/-- The duality of Definition 20: `d(t) = s`, `d(s) = t`, `d(c) = c`. -/
def dual : Mode → Mode
  | strict => tolerant
  | classical => classical
  | tolerant => strict

theorem dual_involutive : Function.Involutive dual := λ m => by cases m <;> rfl

@[simp] theorem dual_dual (m : Mode) : m.dual.dual = m := dual_involutive m

@[simp] theorem dual_strict : strict.dual = tolerant := rfl
@[simp] theorem dual_classical : classical.dual = classical := rfl
@[simp] theorem dual_tolerant : tolerant.dual = strict := rfl

private def rank : Mode → Fin 3
  | strict => 0
  | classical => 1
  | tolerant => 2

instance : LinearOrder Mode := LinearOrder.lift' rank (by decide)

theorem strict_le (m : Mode) : strict ≤ m := by cases m <;> decide

theorem le_tolerant (m : Mode) : m ≤ tolerant := by cases m <;> decide

end Mode

/-- Atomic sentences: predications `Pa` and similarity statements `a I_P b` (Definition 8). -/
inductive Atom (Pred C : Type*)
  | pred : Pred → C → Atom Pred C
  | sim : Pred → C → C → Atom Pred C

/-- The propositional fragment of the language (Definition 2). -/
abbrev Formula (Pred C : Type*) := Trivalent.Formula (Atom Pred C)

/-- The instance `Pa ∧ a I_P b → Pb` of the tolerance principle (1). -/
def tolerance (P : Pred) (a b : C) : Formula Pred C :=
  Trivalent.Formula.imp (.conj (.atom (.pred P a)) (.atom (.sim P a b))) (.atom (.pred P b))

namespace TModel

/-- Definition 9, with Definition 5 for the classical mode: a predication is strictly true when
`P` holds throughout the `∼_P`-neighbourhood of the individual, `□`, and tolerantly true when it
holds somewhere in it, `◇`; negation swaps to the dual mode; similarity statements are classical
in every mode (Remark 2). -/
def Realize (M : TModel Pred C D) : Mode → Formula Pred C → Prop
  | _, .atom (.sim P a b) => M.sim P (M.const a) (M.const b)
  | .classical, .atom (.pred P a) => M.interp P (M.const a)
  | .strict, .atom (.pred P a) => □[M.sim P] (M.interp P) (M.const a)
  | .tolerant, .atom (.pred P a) => ◇[M.sim P] (M.interp P) (M.const a)
  | m, .neg φ => ¬ M.Realize m.dual φ
  | m, .conj φ ψ => M.Realize m φ ∧ M.Realize m ψ

variable (M : TModel Pred C D)

@[simp] theorem realize_sim (m : Mode) (P : Pred) (a b : C) :
    M.Realize m (.atom (.sim P a b)) ↔ M.sim P (M.const a) (M.const b) := by cases m <;> rfl

@[simp] theorem realize_classical_pred (P : Pred) (a : C) :
    M.Realize .classical (.atom (.pred P a)) ↔ M.interp P (M.const a) := Iff.rfl

@[simp] theorem realize_strict_pred (P : Pred) (a : C) :
    M.Realize .strict (.atom (.pred P a)) ↔ □[M.sim P] (M.interp P) (M.const a) := Iff.rfl

@[simp] theorem realize_tolerant_pred (P : Pred) (a : C) :
    M.Realize .tolerant (.atom (.pred P a)) ↔ ◇[M.sim P] (M.interp P) (M.const a) := Iff.rfl

@[simp] theorem realize_neg (m : Mode) (φ : Formula Pred C) :
    M.Realize m (.neg φ) ↔ ¬ M.Realize m.dual φ := Iff.rfl

@[simp] theorem realize_conj (m : Mode) (φ ψ : Formula Pred C) :
    M.Realize m (.conj φ ψ) ↔ M.Realize m φ ∧ M.Realize m ψ := Iff.rfl

@[simp] theorem realize_disj (m : Mode) (φ ψ : Formula Pred C) :
    M.Realize m (φ.disj ψ) ↔ M.Realize m φ ∨ M.Realize m ψ := by
  simp [Trivalent.Formula.disj, or_iff_not_imp_left]

/-- `M ⊨ᵐ φ → ψ` iff `M ⊨ⁿ ψ` whenever `M ⊨^{d(m)} φ` (the proof of Fact 3). -/
@[simp] theorem realize_imp (m : Mode) (φ ψ : Formula Pred C) :
    M.Realize m (φ.imp ψ) ↔ (M.Realize m.dual φ → M.Realize m ψ) := by
  simp [Trivalent.Formula.imp]

instance decidableRealize [Fintype D] [∀ P, DecidableRel (M.sim P)]
    [∀ P, DecidablePred (M.interp P)] : ∀ (m : Mode) (φ : Formula Pred C), Decidable (M.Realize m φ)
  | _, .atom (.sim P a b) => inferInstanceAs (Decidable (M.sim P (M.const a) (M.const b)))
  | .classical, .atom (.pred P a) => inferInstanceAs (Decidable (M.interp P (M.const a)))
  | .strict, .atom (.pred P a) =>
    inferInstanceAs (Decidable (□[M.sim P] (M.interp P) (M.const a)))
  | .tolerant, .atom (.pred P a) =>
    inferInstanceAs (Decidable (◇[M.sim P] (M.interp P) (M.const a)))
  | m, .neg φ => @instDecidableNot _ (decidableRealize m.dual φ)
  | m, .conj φ ψ => @instDecidableAnd _ _ (decidableRealize m φ) (decidableRealize m ψ)

/-- **Lemma 1**: strict truth implies classical truth, which implies tolerant truth. -/
theorem realize_mono (φ : Formula Pred C) : Monotone (M.Realize · φ) := by
  have h : ∀ φ : Formula Pred C,
      (M.Realize .strict φ → M.Realize .classical φ) ∧
      (M.Realize .classical φ → M.Realize .tolerant φ) := by
    intro φ
    induction φ with
    | atom α =>
      cases α with
      | pred P a => exact ⟨box_T, λ h => ⟨M.const a, Std.Refl.refl _, h⟩⟩
      | sim => exact ⟨id, id⟩
    | neg ψ ih => exact ⟨λ h hc => h (ih.2 hc), λ h hs => h (ih.1 hs)⟩
    | conj ψ χ ihψ ihχ =>
      exact ⟨λ h => ⟨ihψ.1 h.1, ihχ.1 h.2⟩, λ h => ⟨ihψ.2 h.1, ihχ.2 h.2⟩⟩
  intro m m' hm x
  cases m <;> cases m' <;> first
    | exact x
    | exact absurd hm (by decide)
    | exact (h φ).1 x
    | exact (h φ).2 x
    | exact (h φ).2 ((h φ).1 x)

/-- A contradiction is true only tolerantly (§4.1). -/
theorem eq_tolerant_of_realize_conj_neg {m : Mode} {φ : Formula Pred C}
    (h : M.Realize m (.conj φ (.neg φ))) : m = .tolerant := by
  cases m with
  | tolerant => rfl
  | classical => exact absurd h.1 h.2
  | strict => exact absurd (M.realize_mono φ (by decide : Mode.strict ≤ .tolerant) h.1) h.2

/-- Excluded middle fails only strictly (§2.4). -/
theorem realize_disj_neg {m : Mode} (hm : m ≠ .strict) (φ : Formula Pred C) :
    M.Realize m (φ.disj (.neg φ)) := by
  rw [realize_disj, realize_neg]
  cases m with
  | strict => exact absurd rfl hm
  | classical => exact em _
  | tolerant => exact (em _).imp_left (M.realize_mono φ (by decide))

/-! ### Borderline cases -/

/-- Definition 10: `d` is a borderline case of `P` iff it is tolerantly but not strictly `P`. -/
def Borderline (P : Pred) (d : D) : Prop :=
  ◇[M.sim P] (M.interp P) d ∧ ¬ □[M.sim P] (M.interp P) d

instance [Fintype D] [∀ P, DecidableRel (M.sim P)] [∀ P, DecidablePred (M.interp P)]
    (P : Pred) (d : D) : Decidable (M.Borderline P d) :=
  inferInstanceAs (Decidable (_ ∧ ¬ _))

/-- A borderline case is one indifferent both from a `P` and from a non-`P` individual (p. 365). -/
theorem borderline_iff (P : Pred) (d : D) :
    M.Borderline P d ↔ (∃ e, M.sim P d e ∧ M.interp P e) ∧ ∃ e, M.sim P d e ∧ ¬ M.interp P e := by
  simp [Borderline, box, diamond]

/-- A borderline case is tolerantly both `P` and `¬P` (Definition 10). -/
theorem borderline_iff_realize_conj_neg (P : Pred) (a : C) :
    M.Borderline P (M.const a) ↔
      M.Realize .tolerant (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) := Iff.rfl

/-- A borderline case is neither strictly `P` nor strictly `¬P` (Definition 10). -/
theorem borderline_iff_not_realize_strict (P : Pred) (a : C) :
    M.Borderline P (M.const a) ↔
      ¬ M.Realize .strict (.atom (.pred P a)) ∧ ¬ M.Realize .strict (.neg (.atom (.pred P a))) := by
  simp [Borderline, and_comm]

/-- Excluded middle fails strictly at a borderline case (§2.4). -/
theorem Borderline.not_realize_strict_disj {P : Pred} {a : C} (h : M.Borderline P (M.const a)) :
    ¬ M.Realize .strict ((Trivalent.Formula.atom (.pred P a)).disj (.neg (.atom (.pred P a)))) := by
  rw [realize_disj, realize_neg]
  exact λ hd => hd.elim h.2 (λ hn => hn h.1)

/-- By symmetry, a model with a borderline case has at least two (footnote 4). -/
theorem Borderline.exists_ne {P : Pred} {d : D} (h : M.Borderline P d) :
    ∃ e ≠ d, M.Borderline P e := by
  obtain ⟨⟨e₁, h₁, hP₁⟩, e₂, h₂, hP₂⟩ := (M.borderline_iff P d).1 h
  by_cases hd : M.interp P d
  · exact ⟨e₂, λ he => hP₂ (he ▸ hd),
      (M.borderline_iff P e₂).2 ⟨⟨d, Std.Symm.symm _ _ h₂, hd⟩, e₂, Std.Refl.refl _, hP₂⟩⟩
  · exact ⟨e₁, λ he => hd (he ▸ hP₁),
      (M.borderline_iff P e₁).2 ⟨⟨e₁, Std.Refl.refl _, hP₁⟩, d, Std.Symm.symm _ _ h₁, hd⟩⟩

end TModel

/-! ### Consequence -/

/-- The T-models of the language over every domain, which validity and consequence quantify
over (Definitions 11 and 17). -/
abbrev TModels (Pred : Type*) (C : Type u) := (D : Type u) × TModel Pred C D

/-- Truth in a bundled model. -/
abbrev TModels.Realize (M : TModels Pred C) : Mode → Formula Pred C → Prop := M.2.Realize

/-- Definition 11: `φ` is `n`-valid iff every T-model `n`-satisfies it. -/
abbrev Valid (n : Mode) (φ : Formula Pred C) : Prop :=
  mnValid (TModels.Realize (Pred := Pred) (C := C)) n φ

/-- Definition 12: `φ` is `n`-unsatisfiable iff no T-model `n`-satisfies it. -/
abbrev Unsat (n : Mode) (φ : Formula Pred C) : Prop := ∀ M : TModels Pred C, ¬ M.Realize n φ

/-- Definition 17: `Γ ⊨ᵐⁿ φ` iff every T-model that `m`-satisfies `Γ` `n`-satisfies `φ`. -/
abbrev Consequence (m n : Mode) (Γ : List (Formula Pred C)) (φ : Formula Pred C) : Prop :=
  MixedConsequence (TModels.Realize (Pred := Pred) (C := C)) m n Γ φ

variable {m n : Mode} {Γ : List (Formula Pred C)} {φ ψ : Formula Pred C}

/-- `mn`-validity is `n`-validity (Definition 18). -/
theorem consequence_nil (m n : Mode) (φ : Formula Pred C) : Consequence m n [] φ ↔ Valid n φ :=
  mnValid_iff_emptyPremise _ _ _ _

/-- **Remark 1**, for unsatisfiability: `φ` is `n`-unsatisfiable iff `¬φ` is `d(n)`-valid. -/
theorem unsat_iff_valid_neg (n : Mode) (φ : Formula Pred C) :
    Unsat n φ ↔ Valid n.dual (.neg φ) := by
  simp [Valid, mnValid]

/-- **Lemma 7**: consequence grows as premises are held to a stronger standard and conclusions
to a weaker one. -/
theorem Consequence.mono {m' n' : Mode} (hm : m' ≤ m) (hn : n ≤ n') (h : Consequence m n Γ φ) :
    Consequence m' n' Γ φ :=
  mixed_monotone (λ M φ => M.2.realize_mono φ hm) (λ M φ => M.2.realize_mono φ hn) h

/-- **Remark 1**: negation swaps tolerant and strict truth and fixes classical truth. -/
theorem satDuality :
    Bilateral.SatDuality (TModels.Realize (Pred := Pred) (C := C)) .neg Mode.dual where
  dual_invol := Mode.dual_dual
  neg_swap _ _ _ := Iff.rfl

/-- **Lemma 6**: `⊨ᵐⁿ` is the dual of `⊨^{d(n)d(m)}`. -/
theorem Consequence.dual (h : Consequence m n [φ] ψ) :
    Consequence n.dual m.dual [.neg ψ] (.neg φ) :=
  consequence_dual satDuality h

/-- The self-dual relations are `st`, `cc` and `ts` (§3.1). -/
theorem isSelfDual_iff (m n : Mode) :
    IsSelfDual Mode.dual m n ↔
      (m = .strict ∧ n = .tolerant) ∨ (m = .classical ∧ n = .classical) ∨
        (m = .tolerant ∧ n = .strict) := by
  cases m <;> cases n <;> simp [IsSelfDual]

/-- **Lemma 10**, the deduction theorem for self-dual consequence relations. Its converse rests
on the nine relations being distinct (§3.4). -/
theorem Consequence.imp_iff (h : IsSelfDual Mode.dual m n) :
    Consequence m n [φ] ψ ↔ Valid n (φ.imp ψ) := by
  obtain rfl : m = n.dual := h.symm
  simp [Consequence, MixedConsequence, Valid, mnValid]

/-! ### Tolerance -/

/-- **Fact 2**: the tolerance principle is tolerantly valid. -/
theorem tolerance_valid (P : Pred) (a b : C) : Valid .tolerant (tolerance P a b) := by
  rintro ⟨D, M⟩
  simp only [TModels.Realize, tolerance, TModel.realize_imp, TModel.realize_conj,
    TModel.realize_sim, Mode.dual_tolerant, TModel.realize_strict_pred,
    TModel.realize_tolerant_pred]
  exact λ ⟨hs, hab⟩ => ⟨M.const b, Std.Refl.refl _, hs _ hab⟩

/-- `{Pa, a I_P b} ⊨ˢᶜ Pb` (§3.4). -/
theorem sc_one_step (P : Pred) (a b : C) :
    Consequence .strict .classical [.atom (.pred P a), .atom (.sim P a b)] (.atom (.pred P b)) := by
  rintro ⟨D, M⟩ h
  simp only [TModels.Realize, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq,
    TModel.realize_strict_pred, TModel.realize_sim] at h
  exact h.1 _ h.2

/-- `{Pa, a I_P b} ⊨ᶜᵗ Pb` (§3.4). -/
theorem ct_one_step (P : Pred) (a b : C) :
    Consequence .classical .tolerant [.atom (.pred P a), .atom (.sim P a b)]
      (.atom (.pred P b)) := by
  rintro ⟨D, M⟩ h
  simp only [TModels.Realize, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq,
    TModel.realize_classical_pred, TModel.realize_sim] at h
  exact ⟨M.const a, Std.Symm.symm _ _ h.2, h.1⟩

/-- Each step of a sorites is `st`-valid (§3.6). -/
theorem st_one_step (P : Pred) (a b : C) :
    Consequence .strict .tolerant [.atom (.pred P a), .atom (.sim P a b)] (.atom (.pred P b)) :=
  (sc_one_step P a b).mono le_rfl (by decide)

/-- **Fact 3**: tolerance holds up to two similarity steps. -/
theorem st_two_step (P : Pred) (a b c : C) :
    Consequence .strict .tolerant
      [.atom (.pred P a), .atom (.sim P a b), .atom (.sim P b c)] (.atom (.pred P c)) := by
  rintro ⟨D, M⟩ h
  simp only [TModels.Realize, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq,
    TModel.realize_strict_pred, TModel.realize_sim] at h
  exact ⟨M.const b, Std.Symm.symm _ _ h.2.2, h.1 _ h.2.1⟩

/-! ### The restricted vocabulary -/

/-- Membership in the restricted vocabulary (§2): no similarity statements. -/
def IsRestricted : Formula Pred C → Prop
  | .atom (.pred _ _) => True
  | .atom (.sim _ _ _) => False
  | .neg φ => IsRestricted φ
  | .conj φ ψ => IsRestricted φ ∧ IsRestricted ψ

namespace TModel

variable (M : TModel Pred C D)

/-- The T-model of Lemma 2: `M` with identity as every indifference relation. -/
def identity : TModel Pred C D :=
  { M with sim := λ _ => Eq, sim_ktb := λ _ => { refl := λ _ => rfl, symm := λ _ _ => Eq.symm } }

/-- **Lemma 2**: in an identity model every mode agrees with classical truth. -/
theorem identity_realize (m : Mode) (φ : Formula Pred C) :
    M.identity.Realize m φ ↔ M.identity.Realize .classical φ := by
  induction φ generalizing m with
  | atom α =>
    cases α with
    | pred P a => cases m <;> simp [identity, box, diamond]
    | sim P a b => simp
  | neg ψ ih => simp [ih]
  | conj ψ χ ihψ ihχ => simp [ihψ, ihχ]

/-- The identity model agrees classically with `M` on the restricted vocabulary. -/
theorem identity_realize_classical {φ : Formula Pred C} (hφ : IsRestricted φ) :
    M.identity.Realize .classical φ ↔ M.Realize .classical φ := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a => exact Iff.rfl
    | sim P a b => exact hφ.elim
  | neg ψ ih => simp [ih hφ]
  | conj ψ χ ihψ ihχ => simp [ihψ hφ.1, ihχ hφ.2]

end TModel

/-- **Theorem 1**: on the restricted vocabulary, tolerant validity is classical validity. -/
theorem valid_tolerant_iff (hφ : IsRestricted φ) : Valid .tolerant φ ↔ Valid .classical φ :=
  ⟨λ h ⟨D, M⟩ => (M.identity_realize_classical hφ).1
      ((M.identity_realize _ φ).1 (h ⟨D, M.identity⟩)),
    λ h M => M.2.realize_mono φ (by decide) (h M)⟩

/-- **Theorem 1**: on the restricted vocabulary, strict unsatisfiability is classical
unsatisfiability. -/
theorem unsat_strict_iff (hφ : IsRestricted φ) : Unsat .strict φ ↔ Unsat .classical φ := by
  rw [unsat_iff_valid_neg, unsat_iff_valid_neg, Mode.dual_strict, Mode.dual_classical]
  exact valid_tolerant_iff hφ

/-- The model of Lemma 3: an individual for each constant plus one more, all indifferent, the
extra one alone falling outside every predicate, so that every predication is borderline. -/
def allBorderline (Pred C : Type*) : TModel Pred C (Option C) where
  const := some
  interp _ d := d.isSome
  sim _ _ _ := True
  sim_ktb _ := { refl := λ _ => trivial, symm := λ _ _ _ => trivial }

/-- **Lemma 3**: in `allBorderline` nothing restricted is strictly true and everything restricted
is tolerantly true. -/
theorem allBorderline_realize (hφ : IsRestricted φ) :
    ¬ (allBorderline Pred C).Realize .strict φ ∧ (allBorderline Pred C).Realize .tolerant φ := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a => exact ⟨λ h => by simpa [allBorderline] using h none trivial, some a, trivial, rfl⟩
    | sim P a b => exact hφ.elim
  | neg ψ ih => exact ⟨λ h => h (ih hφ).2, (ih hφ).1⟩
  | conj ψ χ ihψ ihχ => exact ⟨λ h => (ihψ hφ.1).1 h.1, (ihψ hφ.1).2, (ihχ hφ.2).2⟩

/-- **Theorem 2**: no restricted formula is strictly valid. -/
theorem not_valid_strict (hφ : IsRestricted φ) : ¬ Valid .strict φ :=
  λ h => (allBorderline_realize hφ).1 (h ⟨_, allBorderline Pred C⟩)

/-- **Theorem 2**: every restricted formula is tolerantly satisfiable. -/
theorem exists_realize_tolerant (hφ : IsRestricted φ) :
    ∃ M : TModels Pred C, M.Realize .tolerant φ :=
  ⟨⟨_, allBorderline Pred C⟩, (allBorderline_realize hφ).2⟩

/-- **Lemma 8**: on the restricted vocabulary `st`-consequence is classical consequence. -/
theorem Consequence.classical_of_st (hΓ : ∀ γ ∈ Γ, IsRestricted γ) (hφ : IsRestricted φ)
    (h : Consequence .strict .tolerant Γ φ) : Consequence .classical .classical Γ φ := by
  rintro ⟨D, M⟩ hM
  exact (M.identity_realize_classical hφ).1 ((M.identity_realize _ φ).1
    (h ⟨D, M.identity⟩ λ γ hγ =>
      (M.identity_realize _ γ).2 ((M.identity_realize_classical (hΓ γ hγ)).2 (hM γ hγ))))

/-- **Lemma 8**: on the restricted vocabulary `cc`, `sc`, `ct` and `st` coincide. -/
theorem Consequence.restricted_iff (hΓ : ∀ γ ∈ Γ, IsRestricted γ) (hφ : IsRestricted φ)
    (hm : m ≤ .classical) (hn : .classical ≤ n) :
    Consequence m n Γ φ ↔ Consequence .classical .classical Γ φ :=
  ⟨λ h => classical_of_st hΓ hφ (h.mono (Mode.strict_le _) (Mode.le_tolerant _)),
    λ h => h.mono hm hn⟩

/-- **Lemma 9**: on the restricted vocabulary `ts`-consequence is empty. -/
theorem not_consequence_tolerant_strict (hΓ : ∀ γ ∈ Γ, IsRestricted γ) (hφ : IsRestricted φ) :
    ¬ Consequence .tolerant .strict Γ φ :=
  λ h => (allBorderline_realize hφ).1
    (h ⟨_, allBorderline Pred C⟩ λ γ hγ => (allBorderline_realize (hΓ γ hγ)).2)

/-! ### LP and K3 -/

open Classical in
/-- The MV-model of Lemma 4: a predication is `true` when strictly true, `false` when not
tolerantly true and `indet` when borderline; similarity statements are two-valued. -/
noncomputable def toMV (M : TModel Pred C D) : Trivalent.Model (Atom Pred C)
  | .pred P a =>
    if □[M.sim P] (M.interp P) (M.const a) then .true
    else if ◇[M.sim P] (M.interp P) (M.const a) then .indet else .false
  | .sim P a b => if M.sim P (M.const a) (M.const b) then .true else .false

/-- **Lemma 4**: tolerant truth is LP-truth and strict truth K3-truth in `toMV M`. -/
theorem TModel.realize_toMV (M : TModel Pred C D) (φ : Formula Pred C) :
    (M.Realize .tolerant φ ↔ toMV M ⊨[.lp] φ) ∧ (M.Realize .strict φ ↔ toMV M ⊨[.k3] φ) := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a =>
      simp only [TModel.realize_tolerant_pred, TModel.realize_strict_pred,
        Trivalent.Formula.realize_atom, Trivalent.designated_lp_iff, Trivalent.designated_k3_iff,
        toMV]
      split_ifs with hs ht
      · exact ⟨iff_of_true ⟨_, Std.Refl.refl _, box_T hs⟩ (by decide), iff_of_true hs rfl⟩
      · exact ⟨iff_of_true ht (by decide), iff_of_false hs (by decide)⟩
      · exact ⟨iff_of_false ht (λ h => h rfl), iff_of_false hs (by decide)⟩
    | sim P a b =>
      simp only [TModel.realize_sim, Trivalent.Formula.realize_atom, Trivalent.designated_lp_iff,
        Trivalent.designated_k3_iff, toMV]
      split_ifs with h <;> simp [h]
  | neg ψ ih =>
    simp only [TModel.realize_neg, Trivalent.Formula.realize_neg, Mode.dual_tolerant,
      Mode.dual_strict, Trivalent.Designation.dual_lp, Trivalent.Designation.dual_k3]
    exact ⟨not_congr ih.2, not_congr ih.1⟩
  | conj ψ χ ihψ ihχ =>
    simp only [TModel.realize_conj, Trivalent.Formula.realize_conj]
    exact ⟨and_congr ihψ.1 ihχ.1, and_congr ihψ.2 ihχ.2⟩

/-- The T-model of Lemma 5 over the doubled domain: `(a, false)` is `a` and `(a, true)` its
double `a'`, indifferent from each other and from nothing else; `a` is `P` when `v` makes `Pa`
true and `a'` when `v` makes it non-false. -/
def ofMV (v : Trivalent.Model (Atom Pred C)) : TModel Pred C (C × Bool) where
  const a := (a, false)
  interp P
    | (a, false) => v (.pred P a) = .true
    | (a, true) => v (.pred P a) ≠ .false
  sim _ x y := x.1 = y.1
  sim_ktb _ := { refl := λ _ => rfl, symm := λ _ _ => Eq.symm }

/-- **Lemma 5**: on the restricted vocabulary, LP-truth in `v` is tolerant truth and K3-truth
strict truth in `ofMV v`. -/
theorem ofMV_realize (v : Trivalent.Model (Atom Pred C)) (hφ : IsRestricted φ) :
    ((ofMV v).Realize .tolerant φ ↔ v ⊨[.lp] φ) ∧ ((ofMV v).Realize .strict φ ↔ v ⊨[.k3] φ) := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a =>
      simp only [TModel.realize_tolerant_pred, TModel.realize_strict_pred,
        Trivalent.Formula.realize_atom, Trivalent.designated_lp_iff, Trivalent.designated_k3_iff,
        ofMV, box, diamond]
      refine ⟨⟨?_, λ h => ⟨(a, true), rfl, h⟩⟩, ⟨λ h => h (a, false) rfl, ?_⟩⟩
      · rintro ⟨⟨b, i⟩, rfl, h⟩
        cases i <;> simp_all
      · rintro h ⟨b, i⟩ rfl
        cases i <;> simp [h]
    | sim P a b => exact hφ.elim
  | neg ψ ih =>
    simp only [TModel.realize_neg, Trivalent.Formula.realize_neg, Mode.dual_tolerant,
      Mode.dual_strict, Trivalent.Designation.dual_lp, Trivalent.Designation.dual_k3]
    exact ⟨not_congr (ih hφ).2, not_congr (ih hφ).1⟩
  | conj ψ χ ihψ ihχ =>
    simp only [TModel.realize_conj, Trivalent.Formula.realize_conj]
    exact ⟨and_congr (ihψ hφ.1).1 (ihχ hφ.2).1, and_congr (ihψ hφ.1).2 (ihχ hφ.2).2⟩

/-- **Theorem 3**: on the restricted vocabulary, tolerant consequence is LP-consequence. -/
theorem consequence_tolerant_iff_lp (hΓ : ∀ γ ∈ Γ, IsRestricted γ) (hφ : IsRestricted φ) :
    Consequence .tolerant .tolerant Γ φ ↔ Trivalent.Consequence .lp .lp Γ φ :=
  ⟨λ h v hv => (ofMV_realize v hφ).1.1
      (h ⟨_, ofMV v⟩ λ γ hγ => (ofMV_realize v (hΓ γ hγ)).1.2 (hv γ hγ)),
    λ h ⟨_, M⟩ hM => (M.realize_toMV φ).1.2 (h (toMV M) λ γ hγ => (M.realize_toMV γ).1.1 (hM γ hγ))⟩

/-- **Theorem 3**: on the restricted vocabulary, strict consequence is K3-consequence. -/
theorem consequence_strict_iff_k3 (hΓ : ∀ γ ∈ Γ, IsRestricted γ) (hφ : IsRestricted φ) :
    Consequence .strict .strict Γ φ ↔ Trivalent.Consequence .k3 .k3 Γ φ :=
  ⟨λ h v hv => (ofMV_realize v hφ).2.1
      (h ⟨_, ofMV v⟩ λ γ hγ => (ofMV_realize v (hΓ γ hγ)).2.2 (hv γ hγ)),
    λ h ⟨_, M⟩ hM => (M.realize_toMV φ).2.2 (h (toMV M) λ γ hγ => (M.realize_toMV γ).2.1 (hM γ hγ))⟩

/-! ### Sorites series -/

/-- The sorites series of §3.4.1 and §3.6: `n` individuals in a line, each indifferent from its
neighbours, the first `i` classically `P`. `series 4 2` is the four-element model of p. 354,
`a, b, c, d` being `0, 1, 2, 3` and the classical extension `{a, b}`. -/
def series (n i : ℕ) : TModel Unit (Fin n) (Fin n) where
  const := id
  interp _ x := x.val < i
  sim _ x y := x.val ≤ y.val + 1 ∧ y.val ≤ x.val + 1
  sim_ktb _ := { refl := λ _ => ⟨Nat.le_succ _, Nat.le_succ _⟩, symm := λ _ _ => And.symm }

instance (n i : ℕ) (P : Unit) : DecidableRel ((series n i).sim P) :=
  λ x y => inferInstanceAs (Decidable (x.val ≤ y.val + 1 ∧ y.val ≤ x.val + 1))

instance (n i : ℕ) (P : Unit) : DecidablePred ((series n i).interp P) :=
  λ x => inferInstanceAs (Decidable (x.val < i))

variable {n i : ℕ}

theorem series_realize_tolerant (hi : 0 < i) (x : Fin n) :
    (series n i).Realize .tolerant (.atom (.pred () x)) ↔ x.val ≤ i := by
  simp only [TModel.realize_tolerant_pred, diamond, series, id]
  refine ⟨λ ⟨y, ⟨h₁, _⟩, h₃⟩ => by omega, λ h => ?_⟩
  rcases Nat.lt_or_ge x.val i with hx | hx
  · exact ⟨x, ⟨Nat.le_succ _, Nat.le_succ _⟩, hx⟩
  · exact ⟨⟨x.val - 1, by omega⟩, by simp; omega, by simp; omega⟩

theorem series_realize_strict (hin : i < n) (x : Fin n) :
    (series n i).Realize .strict (.atom (.pred () x)) ↔ x.val + 1 < i := by
  simp only [TModel.realize_strict_pred, box, series, id]
  refine ⟨λ h => ?_, λ h y ⟨_, h₂⟩ => by omega⟩
  by_cases hx : x.val + 1 < n
  · simpa using h ⟨x.val + 1, hx⟩ ⟨Nat.le_succ_of_le (Nat.le_succ _), le_rfl⟩
  · have := h x ⟨Nat.le_succ _, Nat.le_succ _⟩
    omega

/-- In a series with a cut the borderline cases are the two individuals either side of it. -/
theorem series_borderline (hi : 0 < i) (hin : i < n) (x : Fin n) :
    (series n i).Borderline () x ↔ x.val + 1 = i ∨ x.val = i := by
  rw [TModel.Borderline, show ◇[(series n i).sim ()] ((series n i).interp ()) x ↔ x.val ≤ i from
    series_realize_tolerant hi x, show □[(series n i).sim ()] ((series n i).interp ()) x ↔
    x.val + 1 < i from series_realize_strict hin x]
  omega

/-- In the four-element model of p. 354 the strict, classical and tolerant extensions of `P`
are `{a}`, `{a, b}` and `{a, b, c}`, so `b` and `c` are borderline. -/
theorem series_four_two (x : Fin 4) :
    ((series 4 2).Realize .strict (.atom (.pred () x)) ↔ x = 0) ∧
    ((series 4 2).Realize .classical (.atom (.pred () x)) ↔ x = 0 ∨ x = 1) ∧
    ((series 4 2).Realize .tolerant (.atom (.pred () x)) ↔ x ≠ 3) ∧
    ((series 4 2).Borderline () x ↔ x = 1 ∨ x = 2) := by
  revert x; decide

/-- `b` is tolerantly both `P` and `¬P` in the four-element model (p. 356). -/
theorem series_four_two_realize_conj_neg :
    (series 4 2).Realize .tolerant
      (.conj (.atom (.pred () 1)) (.neg (.atom (.pred () (1 : Fin 4))))) := by
  decide

/-- `{Pa, a I_P b} ⊨ Pb` is not `cc`-valid (§3.4): `b, c` of the four-element model. -/
theorem not_cc_one_step :
    ¬ Consequence .classical .classical
      [.atom (.pred () 1), .atom (.sim () 1 2)] (.atom (.pred () (2 : Fin 4))) :=
  λ h => absurd (h ⟨_, series 4 2⟩ (by decide)) (by decide)

/-- Tolerance is not classically valid, hence neither `cc`- nor `sc`-valid (§3.4). -/
theorem not_valid_classical_tolerance : ¬ Valid .classical (tolerance () (1 : Fin 4) 2) :=
  λ h => absurd (h ⟨_, series 4 2⟩) (by decide)

/-- `{Pa, a I_P b, b I_P c} ⊨ Pc` is not `sc`-valid (§3.4): `a, b, c` of the four-element
model. -/
theorem not_sc_two_step :
    ¬ Consequence .strict .classical
      [.atom (.pred () 0), .atom (.sim () 0 1), .atom (.sim () 1 2)]
      (.atom (.pred () (2 : Fin 4))) :=
  λ h => absurd (h ⟨_, series 4 2⟩ (by decide)) (by decide)

/-- `{Pa, a I_P b, b I_P c} ⊨ Pc` is not `ct`-valid (§3.4): `b, c, d` of the four-element
model. -/
theorem not_ct_two_step :
    ¬ Consequence .classical .tolerant
      [.atom (.pred () 1), .atom (.sim () 1 2), .atom (.sim () 2 3)]
      (.atom (.pred () (3 : Fin 4))) :=
  λ h => absurd (h ⟨_, series 4 2⟩ (by decide)) (by decide)

/-- The similarity premises `a₁ I_P a₂, …, aₙ I_P aₙ₊₁` of the sorites (§3.6). -/
def steps (n : ℕ) : List (Formula Unit (Fin (n + 1))) :=
  (List.finRange n).map λ k => .atom (.sim () k.castSucc k.succ)

/-- The tolerance premises `Pa₁ ∧ a₁ I_P a₂ → Pa₂, …` of the sorites, Version 2 (§3.6). -/
def tolerances (n : ℕ) : List (Formula Unit (Fin (n + 1))) :=
  (List.finRange n).map λ k => tolerance () k.castSucc k.succ

/-- **The sorites, Version 1**, is `st`-invalid for every series of at least four members, the
four-element model being a countermodel, although each of its steps is `st`-valid
(`st_one_step`). Below four members it is valid by Facts 2 and 3. -/
theorem not_st_version1 (hn : 3 ≤ n) :
    ¬ Consequence .strict .tolerant (.atom (.pred () 0) :: steps n)
      (.atom (.pred () (Fin.last n))) := by
  intro h
  have := (series_realize_tolerant (by omega) _).1 (h ⟨_, series (n + 1) 2⟩ ?_)
  · simp at this
    omega
  intro γ hγ
  simp only [List.mem_cons, steps, List.mem_map, List.mem_finRange, true_and] at hγ
  rcases hγ with rfl | ⟨k, rfl⟩
  · exact (series_realize_strict (by omega) _).2 (by simp)
  · exact ⟨by simp [series]; omega, by simp [series]⟩

/-- **The sorites, Version 2**, with tolerance as a premise, is `st`-valid: it is classically
valid and `st` extends classical consequence. -/
theorem st_version2 (n : ℕ) :
    Consequence .strict .tolerant (.atom (.pred () 0) :: steps n ++ tolerances n)
      (.atom (.pred () (Fin.last n))) := by
  refine Consequence.mono (by decide) (by decide)
    (?_ : Consequence .classical .classical _ _)
  rintro ⟨D, M⟩ h
  have hstep : ∀ k : Fin n, M.Realize .classical (.atom (.pred () k.castSucc)) →
      M.Realize .classical (.atom (.pred () k.succ)) := by
    intro k hk
    have ht : M.Realize .classical (tolerance () k.castSucc k.succ) :=
      h _ (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange k))))
    have hs : M.Realize .classical (.atom (.sim () k.castSucc k.succ)) :=
      h _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange k))))
    rw [tolerance, M.realize_imp, Mode.dual_classical] at ht
    exact ht ⟨hk, hs⟩
  suffices ∀ k (hk : k ≤ n), M.Realize .classical (.atom (.pred () ⟨k, by omega⟩)) from
    this n le_rfl
  intro k
  induction k with
  | zero => exact λ _ => h _ (List.mem_cons_self ..)
  | succ k ih => exact λ hk => hstep ⟨k, by omega⟩ (ih (by omega))

/-- Version 2 is unsound: across the cut of any series, the tolerance premise is not strictly
true (§3.6). -/
theorem not_series_realize_strict_tolerance (hi : 0 < i) (hin : i < n) :
    ¬ (series n i).Realize .strict (tolerance () ⟨i - 1, by omega⟩ ⟨i, hin⟩) := by
  simp only [tolerance, TModel.realize_imp, TModel.realize_conj, TModel.realize_sim,
    Mode.dual_strict, series_realize_tolerant hi, series_realize_strict hin]
  simp [series]
  omega

/-- §4.2.3: [alxatib-pelletier-2011]'s five men ranked by height, `#1 < #4 < #2 < #5 < #3`
as ranks `0` to `4`, with `#1` and `#4` tall and `#5` and `#3` not. Whichever way the median
man `#2`, rank `2`, is classified, `series 5 2` or `series 5 3`, he is borderline: tolerantly
tall and tolerantly not tall. -/
theorem alxatibPelletier_median_borderline (hi : i = 2 ∨ i = 3) :
    (series 5 i).Borderline () 2 :=
  (series_borderline (by omega) (by omega) 2).2 (by show 2 + 1 = i ∨ 2 = i; omega)

end CobrerosEtAl2012
