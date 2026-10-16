module

public import Mathlib.Tactic.FinCases
public import Linglib.Semantics.Presupposition.Trivalent
public import Linglib.Semantics.Dynamic.Partial

/-!
# Yagi (2025): Conflicting Presuppositions in Disjunction

This file formalizes Yagi's survey of disjunctions whose disjuncts carry contradictory
presuppositions (`Conflict`), *Either the King of Buganda is opening parliament or the
President of Buganda is conducting the ceremony*. Such a disjunction presupposes the
disjunction of the two presuppositions and is false when that holds and both disjuncts are
false. Four theories fail the second observation. Under Strong Kleene disjunction the sentence
is true whenever defined, so it is never false and its negation never true
(`orStrong_ne_false`, `neg_orStrong_ne_true`); the symmetric two-dimensional disjunction in the
tradition of Karttunen and Peters has a presupposition that entails the assertion
(`orKPSymmetric_ne_false`), and replacing it by the disjunction of the presuppositions
(`orPresupOr`) fixes the case but predicts a tautologous presupposition for *either baldness is
not hereditary or all of Bill's children are bald* (`orPresupOr_presup_of_left`); the update
semantics of Heim and Beaver, with failure as a designated state, is defined only when the
first disjunct already holds throughout the input, so it is uninformative wherever defined
(`mem_disj_iff`); and Schlenker's local contexts admit only worlds where one disjunct is
defined and true (`local_contexts_force_truth`). Of the two reactions, Beaver and Krahmer's
meta-assertion operator makes the disjunction false, but also where neither presupposition
holds, and leaves it presuppositionless (`or_assertMeta_false_iff`, `or_assertMeta_presup`);
inserting it on one disjunct under Strong Kleene yields only a conditional presupposition
(`orStrong_assertMeta_presup_iff`).

Flexible accommodation evaluates each disjunct in the input restricted by an accommodated
proposition (`flex`). The standard update is the case where the second disjunct's
proposition is the negation of the first (`flex_univ_eq_disj`), which gives the conditional
presupposition of *Either Bill has no child or all of Bill's children are bald*
(`admits_flex_univ_iff`, `bill`). With tautologies accommodated the update is never defined
under conflict (`not_admits_flex_univ_univ`) and is not genuine when a presupposition
contradicts the other disjunct (`not_genuine_flex_univ_univ`); accommodating each disjunct's
negated rival presupposition derives both observations (`mem_flex_rival_iff`,
`neg_flex_rival`, `buganda`), at the cost of demanding accommodation where the standard update
filters the presupposition away (`exists_admits_disj_not_admits_flex_univ_univ`).

## Implementation notes

The designated undefined state of the update semantics is the undefined value of `Part`, the
updates being the substrate's partial context change potentials. The meta-assertion operator
is the trivalent one lifted to partial propositions. The licensing constraint on the operator is
not modelled. The paper's examples are the rows of `Data.Examples.Yagi2025`; (1c) and (4) are
modelled by the Buganda input and (15a) by the Bill input.

## References

* [yagi-2025]
* [beaver-2001]
* [beaver-krahmer-2001]
* [geurts-2005]
* [heim-1982]
* [karttunen-peters-1979]
* [katzir-singh-2012]
* [schlenker-2009]
* [zimmermann-2000]
-/

@[expose] public section

namespace Yagi2025

open Presupposition DynamicSemantics CCP.Partial

variable {W : Type*}

/-- Two partial propositions have conflicting presuppositions. -/
def Conflict (φ ψ : PartialProp W) : Prop := ∀ w, ¬ (φ.presup w ∧ ψ.presup w)

/-- A partial proposition whose presupposition entails its assertion is never false. -/
theorem eval_ne_false_of_imp {d : PartialProp W} {w : W} (h : d.presup w → d.assertion w) :
    d.eval w ≠ -1 := by
  simpa using h

/-- Its negation is never true. -/
theorem eval_neg_ne_true_of_imp {d : PartialProp W} {w : W}
    (h : d.presup w → d.assertion w) : (PartialProp.neg d).eval w ≠ 1 := by
  simpa [PartialProp.neg] using h

/-! ### Strong Kleene and two-dimensional disjunction -/

variable {φ ψ : PartialProp W}

/-- Under conflict, the Strong Kleene presupposition entails the assertion. -/
theorem orStrong_presup_imp (h : Conflict φ ψ) (w : W) :
    (PartialProp.orStrong φ ψ).presup w → (PartialProp.orStrong φ ψ).assertion w := by
  rintro (hpq | hφ | hψ)
  · exact absurd hpq (h w)
  · exact Or.inl hφ
  · exact Or.inr hψ

/-- The Strong Kleene disjunction is never false. -/
theorem orStrong_ne_false (h : Conflict φ ψ) (w : W) :
    (PartialProp.orStrong φ ψ).eval w ≠ -1 :=
  eval_ne_false_of_imp (orStrong_presup_imp h w)

/-- Its negation is never true. -/
theorem neg_orStrong_ne_true (h : Conflict φ ψ) (w : W) :
    (PartialProp.neg (PartialProp.orStrong φ ψ)).eval w ≠ 1 :=
  eval_neg_ne_true_of_imp (orStrong_presup_imp h w)

/-- The symmetric two-dimensional disjunction is never false either. -/
theorem orKPSymmetric_ne_false (h : Conflict φ ψ) (w : W) :
    (PartialProp.orKPSymmetric φ ψ).eval w ≠ -1 :=
  eval_ne_false_of_imp (PartialProp.orKPSymmetric_presup_entails_when_conflicting φ ψ w (h w))

/-- The two-dimensional disjunction whose presupposition is the disjunction of the
presuppositions, (7). -/
def orPresupOr (φ ψ : PartialProp W) : PartialProp W where
  presup w := φ.presup w ∨ ψ.presup w
  assertion w := φ.assertion w ∨ ψ.assertion w

/-- It is false exactly where a presupposition holds and both assertions fail. -/
theorem orPresupOr_eval_false_iff (w : W) :
    (orPresupOr φ ψ).eval w = -1 ↔
      (φ.presup w ∨ ψ.presup w) ∧ ¬ φ.assertion w ∧ ¬ ψ.assertion w := by
  simp [orPresupOr]

/-- With a presuppositionless first disjunct it presupposes nothing, (8). -/
theorem orPresupOr_presup_of_left (h : ∀ w, φ.presup w) (w : W) : (orPresupOr φ ψ).presup w :=
  Or.inl (h w)

/-! ### Update semantics with a designated undefined state -/

/-- Under conflict the update by the disjunction is defined only when the first disjunct
already holds throughout the input, and then it returns the input, so it is defined only if
uninformative. -/
theorem mem_disj_iff (h : Conflict φ ψ) (s t : Set W) :
    t ∈ disj (ofPartialProp φ) (ofPartialProp ψ) s ↔
      (∀ w ∈ s, φ.presup w) ∧ (∀ w ∈ s, φ.assertion w) ∧ t = s := by
  simp only [disj, Part.mem_bind_iff, Part.mem_map_iff, mem_ofPartialProp]
  constructor
  · rintro ⟨a, ⟨hp, rfl⟩, b, ⟨hq, rfl⟩, rfl⟩
    have hφ : ∀ w ∈ s, φ.assertion w := fun w hw ↦
      by_contra fun hn ↦ h w ⟨hp hw, hq ⟨hw, fun ha ↦ hn ha.2⟩⟩
    refine ⟨hp, hφ, ?_⟩
    ext w
    simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_sdiff]
    exact ⟨fun h ↦ h.elim (·.1) (·.1.1), fun hw ↦ .inl ⟨hw, hφ w hw⟩⟩
  · rintro ⟨hp, hφ, rfl⟩
    refine ⟨_, ⟨hp, rfl⟩, ∅, ⟨fun w hw ↦ absurd (hφ w hw.1) fun ha ↦ hw.2 ⟨hw.1, ha⟩, ?_⟩, ?_⟩
    · ext w; simp only [Set.mem_sep_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
      exact fun ⟨⟨hw, hn⟩, _⟩ ↦ hn ⟨hw, hφ w hw⟩
    · ext w; simp only [Set.union_empty, Set.mem_sep_iff]
      exact ⟨(·.1), fun hw ↦ ⟨hw, hφ w hw⟩⟩

/-! ### Local contexts -/

/-- If each disjunct's presupposition is entailed by its local context, the negation of the
other disjunct within the global context, then under conflict every world of the global
context makes some disjunct defined and true. -/
theorem local_contexts_force_truth (h : Conflict φ ψ) (s : Set W)
    (h₁ : ∀ w ∈ s, ¬ (φ.presup w ∧ φ.assertion w) → ψ.presup w)
    (h₂ : ∀ w ∈ s, ¬ (ψ.presup w ∧ ψ.assertion w) → φ.presup w) :
    ∀ w ∈ s, (φ.presup w ∧ φ.assertion w) ∨ (ψ.presup w ∧ ψ.assertion w) := by
  intro w hw
  by_cases hp : φ.presup w
  · exact Or.inl (by_contra fun hn ↦ h w ⟨hp, h₁ w hw hn⟩)
  · exact Or.inr (by_contra fun hn ↦ hp (h₂ w hw hn))

/-! ### The meta-assertion operator -/

/-- The meta-assertion operator is the trivalent 𝒜 lifted to partial propositions, always
defined and true where the proposition is defined and true. -/
noncomputable def assertMeta (φ : PartialProp W) : PartialProp W :=
  .ofTrivalent (SignType.metaAssert ∘ φ.eval)

@[simp] theorem assertMeta_presup (w : W) : (assertMeta φ).presup w := by
  cases h : φ.eval w <;> simp [assertMeta, h]

@[simp] theorem assertMeta_assertion (w : W) :
    (assertMeta φ).assertion w ↔ φ.presup w ∧ φ.assertion w := by
  simp [assertMeta]

/-- The disjunction of two meta-asserted disjuncts has no presupposition. -/
theorem or_assertMeta_presup (w : W) :
    (PartialProp.or (assertMeta φ) (assertMeta ψ)).presup w :=
  ⟨assertMeta_presup w, assertMeta_presup w⟩

/-- It is false whenever neither disjunct is defined and true, so also where neither
presupposition holds. -/
theorem or_assertMeta_false_iff (w : W) :
    (PartialProp.or (assertMeta φ) (assertMeta ψ)).eval w = -1 ↔
      ¬ (φ.presup w ∧ φ.assertion w) ∧ ¬ (ψ.presup w ∧ ψ.assertion w) := by
  simp [PartialProp.or, not_or]

/-- Meta-asserting one disjunct under Strong Kleene yields the conditional presupposition
that the first presupposition holds unless the second disjunct is defined and true. -/
theorem orStrong_assertMeta_presup_iff (w : W) :
    (PartialProp.orStrong φ (assertMeta ψ)).presup w ↔
      (¬ (ψ.presup w ∧ ψ.assertion w) → φ.presup w) := by
  simp only [PartialProp.orStrong, assertMeta_presup, assertMeta_assertion, and_true, true_and]
  tauto

/-! ### Flexible accommodation -/

/-- Under flexible accommodation, (13), each disjunct updates the input restricted by its
accommodated proposition, and the results join. -/
def flex (χ ω : Set W) (φ ψ : CCP.Partial W) : CCP.Partial W :=
  fun s ↦ (φ (s ∩ χ)).bind fun a ↦ (ψ (s ∩ ω)).map (a ∪ ·)

/-- (13) requires that the accommodated propositions cover the input. Under conflict each
disjunct's negated rival presupposition covers every input. -/
theorem compl_union_compl_of_conflict (h : Conflict φ ψ) :
    {w | ¬ ψ.presup w} ∪ {w | ¬ φ.presup w} = Set.univ :=
  Set.eq_univ_of_forall fun w ↦ (not_and_or.1 (h w)).symm

/-- Genuineness, Definition 8, requires each disjunct to be true at some world of the input
that survives the update. -/
def Genuine (u φ ψ : CCP.Partial W) (s : Set W) : Prop :=
  (∃ w ∈ s, {w} ∈ φ {w} ∧ ∃ t ∈ u s, w ∈ t) ∧ ∃ w ∈ s, {w} ∈ ψ {w} ∧ ∃ t ∈ u s, w ∈ t

/-- The standard update is flexible accommodation of the negation of the first disjunct for
the second. -/
theorem flex_univ_eq_disj (ψ : CCP.Partial W) :
    flex Set.univ {w | ¬ φ.assertion w} (ofPartialProp φ) ψ = disj (ofPartialProp φ) ψ := by
  funext s
  refine Part.ext fun t ↦ ?_
  simp only [flex, disj, Set.inter_univ, Part.mem_bind_iff, mem_ofPartialProp]
  refine exists_congr fun a ↦ and_congr_right fun ⟨_, ha⟩ ↦ ?_
  subst ha
  rw [show s \ {w ∈ s | φ.assertion w} = s ∩ {w | ¬ φ.assertion w} by
    ext w; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto]

/-- Accommodating the negation of the first disjunct for the second, (15), the update
presupposes the first presupposition and, where the first disjunct fails, the second. This is
the conditional presupposition Katzir and Singh observe, fn. 6. -/
theorem admits_flex_univ_iff (s : Set W) :
    (flex Set.univ {w | ¬ φ.assertion w} (ofPartialProp φ) (ofPartialProp ψ)).Admits s ↔
      ∀ w ∈ s, φ.presup w ∧ (¬ φ.assertion w → ψ.presup w) := by
  rw [flex_univ_eq_disj]
  exact admits_disj_ofPartialProp φ ψ s

/-- With tautologies accommodated the update is defined exactly when both presuppositions hold
throughout, and returns the worlds verifying either assertion. -/
theorem mem_flex_univ_univ_iff (s t : Set W) :
    t ∈ flex Set.univ Set.univ (ofPartialProp φ) (ofPartialProp ψ) s ↔
      (∀ w ∈ s, φ.presup w) ∧ (∀ w ∈ s, ψ.presup w) ∧
        t = {w ∈ s | φ.assertion w} ∪ {w ∈ s | ψ.assertion w} := by
  simp only [flex, Set.inter_univ, Part.mem_bind_iff, Part.mem_map_iff, mem_ofPartialProp]
  constructor
  · rintro ⟨_, ⟨hp, rfl⟩, _, ⟨hq, rfl⟩, rfl⟩
    exact ⟨hp, hq, rfl⟩
  · rintro ⟨hp, hq, rfl⟩
    exact ⟨_, ⟨hp, rfl⟩, _, ⟨hq, rfl⟩, rfl⟩

/-- Under conflict that update is never defined on a nonempty input, (16). -/
theorem not_admits_flex_univ_univ (h : Conflict φ ψ) {s : Set W} (hs : s.Nonempty) :
    ¬ (flex Set.univ Set.univ (ofPartialProp φ) (ofPartialProp ψ)).Admits s := fun hd ↦ by
  obtain ⟨w, hw⟩ := hs
  obtain ⟨hp, hq, -⟩ := (mem_flex_univ_univ_iff s _).1 (Part.get_mem hd)
  exact h w ⟨hp w hw, hq w hw⟩

/-- When the first assertion contradicts the second presupposition, (15), the update with
tautologies accommodated is not genuine, since where defined it presupposes the second
presupposition throughout, which leaves the first disjunct no world. -/
theorem not_genuine_flex_univ_univ (h : ∀ w, ¬ (φ.assertion w ∧ ψ.presup w)) (s : Set W) :
    ¬ Genuine (flex Set.univ Set.univ (ofPartialProp φ) (ofPartialProp ψ))
      (ofPartialProp φ) (ofPartialProp ψ) s := by
  rintro ⟨⟨w, hw, hφ, t, ht, -⟩, -⟩
  exact h w ⟨((mem_ofPartialProp_self _ _).1 hφ).2 rfl,
    ((mem_flex_univ_univ_iff s t).1 ht).2.1 w hw⟩

/-- Accommodating each disjunct's negated rival presupposition, (17), the update is defined
exactly when some presupposition holds at every world of the input, and returns the worlds
where a disjunct is defined and true. -/
theorem mem_flex_rival_iff (h : Conflict φ ψ) (s t : Set W) :
    t ∈ flex {w | ¬ ψ.presup w} {w | ¬ φ.presup w} (ofPartialProp φ) (ofPartialProp ψ) s ↔
      (∀ w ∈ s, φ.presup w ∨ ψ.presup w) ∧
        t = {w ∈ s | (φ.presup w ∧ φ.assertion w) ∨ (ψ.presup w ∧ ψ.assertion w)} := by
  have hset (hs : ∀ w ∈ s, φ.presup w ∨ ψ.presup w) :
      {w ∈ s ∩ {w | ¬ ψ.presup w} | φ.assertion w} ∪
          {w ∈ s ∩ {w | ¬ φ.presup w} | ψ.assertion w} =
        {w ∈ s | (φ.presup w ∧ φ.assertion w) ∨ (ψ.presup w ∧ ψ.assertion w)} := by
    ext w
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h' ↦ h'.elim (fun ⟨⟨hw, hq⟩, ha⟩ ↦ ⟨hw, .inl ⟨(hs w hw).resolve_right hq, ha⟩⟩)
        fun ⟨⟨hw, hp⟩, ha⟩ ↦ ⟨hw, .inr ⟨(hs w hw).resolve_left hp, ha⟩⟩,
      fun ⟨hw, h'⟩ ↦ h'.elim (fun ⟨hp, ha⟩ ↦ .inl ⟨⟨hw, fun hq ↦ h w ⟨hp, hq⟩⟩, ha⟩)
        fun ⟨hq, ha⟩ ↦ .inr ⟨⟨hw, fun hp ↦ h w ⟨hp, hq⟩⟩, ha⟩⟩
  simp only [flex, Part.mem_bind_iff, Part.mem_map_iff, mem_ofPartialProp]
  constructor
  · rintro ⟨_, ⟨h₁, rfl⟩, _, ⟨-, rfl⟩, rfl⟩
    have hs : ∀ w ∈ s, φ.presup w ∨ ψ.presup w := fun w hw ↦
      (em (ψ.presup w)).elim .inr fun hq ↦ .inl (h₁ ⟨hw, hq⟩)
    exact ⟨hs, hset hs⟩
  · rintro ⟨hs, rfl⟩
    exact ⟨_, ⟨fun w hw ↦ (hs w hw.1).resolve_right hw.2, rfl⟩, _,
      ⟨fun w hw ↦ (hs w hw.1).resolve_left hw.2, rfl⟩, hset hs⟩

/-- The negation of that update removes exactly the worlds where both disjuncts are false, so the
disjunction can be false. -/
theorem neg_flex_rival (h : Conflict φ ψ) {s : Set W} (hs : ∀ w ∈ s, φ.presup w ∨ ψ.presup w) :
    neg (flex {w | ¬ ψ.presup w} {w | ¬ φ.presup w} (ofPartialProp φ) (ofPartialProp ψ)) s =
      Part.some {w ∈ s | ¬ (φ.presup w ∧ φ.assertion w) ∧ ¬ (ψ.presup w ∧ ψ.assertion w)} := by
  rw [CCP.Partial.neg, Part.eq_some_iff, Part.mem_map_iff]
  refine ⟨_, (mem_flex_rival_iff h s _).2 ⟨hs, rfl⟩, ?_⟩
  ext w
  simp only [Set.mem_sdiff, Set.mem_sep_iff]
  tauto

/-- The standard update filters a presupposition entailed by the negation of the first disjunct,
(18), where accommodating tautologies still demands it, at a world where the first disjunct holds
and the second presupposition fails. -/
theorem exists_admits_disj_not_admits_flex_univ_univ (hφ : ∀ w, φ.presup w)
    (hf : ∀ w, ¬ φ.assertion w → ψ.presup w) {w : W} (hq : ¬ ψ.presup w) :
    (disj (ofPartialProp φ) (ofPartialProp ψ)).Admits {w} ∧
      ¬ (flex Set.univ Set.univ (ofPartialProp φ) (ofPartialProp ψ)).Admits {w} := by
  refine ⟨(admits_disj_ofPartialProp φ ψ _).2 fun v _ ↦ ⟨hφ v, hf v⟩, fun hd ↦ ?_⟩
  exact hq (((mem_flex_univ_univ_iff _ _).1 (Part.get_mem hd)).2.1 w rfl)

/-! ### The ideal inputs -/

/-- The Buganda input of (1c) has four worlds, in which the king opens parliament, the king does
not open it, the president conducts the ceremony, and the president does not conduct it. -/
abbrev Buganda := Fin 4

/-- *The King of Buganda is opening parliament*. -/
def kingOpens : PartialProp Buganda where
  presup w := w < 2
  assertion w := w = 0

/-- *The President of Buganda is conducting the ceremony*. -/
def presidentConducts : PartialProp Buganda where
  presup w := 2 ≤ w
  assertion w := w = 2

theorem conflict_buganda : Conflict kingOpens presidentConducts := by
  unfold Conflict kingOpens presidentConducts; decide

/-- On the Buganda input the update with the rival presuppositions accommodated keeps the
worlds where the head of state performs the duty, and its negation, (4), the others. -/
theorem buganda :
    flex {w | ¬ presidentConducts.presup w} {w | ¬ kingOpens.presup w}
        (ofPartialProp kingOpens) (ofPartialProp presidentConducts) Set.univ = Part.some {0, 2} ∧
      neg (flex {w | ¬ presidentConducts.presup w} {w | ¬ kingOpens.presup w}
        (ofPartialProp kingOpens) (ofPartialProp presidentConducts)) Set.univ =
        Part.some {1, 3} := by
  have hs : ∀ w ∈ (Set.univ : Set Buganda), kingOpens.presup w ∨ presidentConducts.presup w := by
    unfold kingOpens presidentConducts
    intro w _; fin_cases w <;> decide
  refine ⟨Part.eq_some_iff.2 ((mem_flex_rival_iff conflict_buganda _ _).2 ⟨hs, ?_⟩), ?_⟩
  · ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ,
      true_and, kingOpens, presidentConducts]
    fin_cases w <;> decide
  · rw [neg_flex_rival conflict_buganda hs]
    congr 1
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ,
      true_and, kingOpens, presidentConducts]
    fin_cases w <;> decide

/-- The Bill input of (15a) has three worlds, in which Bill has no child, has children who are
all bald, or has children who are not all bald. -/
abbrev Bill := Fin 3

/-- *Bill has no child*. -/
def noChild : PartialProp Bill := .ofProp (· = 0)

/-- *All of Bill's children are bald*, presupposing that Bill has children. -/
def allBald : PartialProp Bill where
  presup w := w ≠ 0
  assertion w := w = 1

/-- On the Bill input the update with tautologies accommodated is undefined, while
accommodating the negation of the first disjunct for the second, (15), is defined and genuine,
keeping the worlds where Bill has no child or his children are all bald. -/
theorem bill :
    ¬ (flex Set.univ Set.univ (ofPartialProp noChild) (ofPartialProp allBald)).Admits
        Set.univ ∧
      {0, 1} ∈ flex Set.univ {w | ¬ noChild.assertion w} (ofPartialProp noChild)
        (ofPartialProp allBald) Set.univ ∧
      Genuine (flex Set.univ {w | ¬ noChild.assertion w} (ofPartialProp noChild)
        (ofPartialProp allBald)) (ofPartialProp noChild) (ofPartialProp allBald) Set.univ := by
  have hd : {0, 1} ∈ flex Set.univ {w | ¬ noChild.assertion w} (ofPartialProp noChild)
      (ofPartialProp allBald) Set.univ := by
    simp only [flex, Set.inter_univ, Part.mem_bind_iff, Part.mem_map_iff, mem_ofPartialProp,
      PartialProp.Admits]
    refine ⟨_, ⟨fun _ _ ↦ trivial, rfl⟩, _, ⟨fun w hw ↦ ?_, rfl⟩, ?_⟩
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, noChild, PartialProp.ofProp_assertion]
        at hw
      exact hw.2
    · ext w
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_univ, true_and,
        Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, noChild,
        PartialProp.ofProp_assertion, allBald]
      fin_cases w <;> decide
  refine ⟨fun h ↦ ?_, hd, ⟨0, trivial, ?_, _, hd, by simp⟩, ⟨1, trivial, ?_, _, hd, by simp⟩⟩
  · exact (((mem_flex_univ_univ_iff _ _).1 (Part.get_mem h)).2.1 0 trivial) rfl
  · exact (mem_ofPartialProp_self _ _).2 ⟨fun _ _ ↦ trivial, fun _ hw ↦ hw⟩
  · refine (mem_ofPartialProp_self _ _).2 ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩ <;>
      rw [Set.mem_singleton_iff.1 hv]
    exacts [(by decide : (1 : Fin 3) ≠ 0), rfl]

end Yagi2025
