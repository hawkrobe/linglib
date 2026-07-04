/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Alternatives.AltMeaning
import Linglib.Semantics.Focus.Interpretation
import Linglib.Semantics.Questions.Hamblin

/-!
# Focus antecedents

The anaphoric source of the squiggle's contrast set ([rooth-1992]):
what the preceding discourse supplies — a question, a prior assertion
to correct, explicitly offered alternatives, or a parallel focus
([uhmann-1991]'s focus-control taxonomy, adopted by
[hartmann-zimmermann-2007] §1.2). `Use` classifies the shapes;
felicity (`Antecedent.Admits`) is `fip` on the antecedent's contrast
set, uniformly across uses — and `use_not_factorsThrough_contrastSet`
shows the four-way split is invisible to the semantics.

`SquiggleSet`/`SquiggleInd` state the full presuppositions of
[rooth-1992]'s ~ operator (his (40), set and individual cases):
`Admits` is only the first set-case clause, and the contrast clauses
are what make ~ anaphorically demanding — `not_squiggleSet_unfeatured`
derives "the argument must contain a focus" from the unit focus value
of focus-free phrases. `Antecedent.Resolves` routes each antecedent
shape through the appropriate case.

## Implementation notes

Payloads are flat Hamblin sets (`PropFocusValue`), keeping antecedents
over finite models `decide`-friendly; the inquisitive layer plugs in
via `Antecedent.ofQuestion` and `Question.alt`, with
`alt_which_singleton` identifying the two Hamblin constructions. The
`assertion` payload is a raw prior proposition; the
`Discourse.CommonGround.HasAssertion` hookup (a correction/denial
move) is deferred.
-/

namespace Semantics.Focus

open Semantics.Focus.Interpretation (fip PropFocusValue qaCongruentWeak)

variable {W : Type*}

/-- The four pragmatic uses of one semantic focus ([uhmann-1991]):
the image of `Antecedent.use`. -/
inductive Use where
  | newInfo      -- controlled by a question
  | corrective   -- correction of a prior assertion
  | selective    -- selection from explicitly offered alternatives
  | contrastive  -- parallel contrast across utterances
  deriving DecidableEq, Repr, Inhabited

/-- A focus antecedent: the discourse object that supplies the
squiggle's antecedent — a contrast set for [rooth-1992]'s set case, or
a single contrasting ordinary value for the individual case. -/
inductive Antecedent (W : Type*) where
  /-- A question with (flat Hamblin) denotation `q`. -/
  | question (q : PropFocusValue W)
  /-- A prior assertion `p`, corrected among alternatives `alts`. -/
  | assertion (p : Set W) (alts : PropFocusValue W)
  /-- Explicitly offered alternatives ('coffee or tea?'). -/
  | offer (alts : PropFocusValue W)
  /-- A parallel focus with focus value `alts`. -/
  | parallel (alts : PropFocusValue W)
  /-- A contrasting phrase's ordinary value ([rooth-1992]'s individual
  case; the "contrasting phrases" rule). -/
  | phrase (γ : Set W)

/-- The contrast set Γ an antecedent supplies to the squiggle. -/
def Antecedent.contrastSet : Antecedent W → PropFocusValue W
  | .question q        => q
  | .assertion _ alts  => alts
  | .offer alts        => alts
  | .parallel alts     => alts
  | .phrase γ          => {γ}

/-- The pragmatic use an antecedent shape licenses. -/
def Antecedent.use : Antecedent W → Use
  | .question _     => .newInfo
  | .assertion _ _  => .corrective
  | .offer _        => .selective
  | .parallel _     => .contrastive
  | .phrase _       => .contrastive

@[simp] theorem contrastSet_question (q : PropFocusValue W) :
    (Antecedent.question q).contrastSet = q := rfl
@[simp] theorem contrastSet_assertion (p : Set W) (alts : PropFocusValue W) :
    (Antecedent.assertion p alts).contrastSet = alts := rfl
@[simp] theorem contrastSet_offer (alts : PropFocusValue W) :
    (Antecedent.offer alts).contrastSet = alts := rfl
@[simp] theorem contrastSet_parallel (alts : PropFocusValue W) :
    (Antecedent.parallel alts).contrastSet = alts := rfl

@[simp] theorem use_question (q : PropFocusValue W) :
    (Antecedent.question q).use = .newInfo := rfl
@[simp] theorem use_assertion (p : Set W) (alts : PropFocusValue W) :
    (Antecedent.assertion p alts).use = .corrective := rfl
@[simp] theorem use_offer (alts : PropFocusValue W) :
    (Antecedent.offer alts).use = .selective := rfl
@[simp] theorem use_parallel (alts : PropFocusValue W) :
    (Antecedent.parallel alts).use = .contrastive := rfl
@[simp] theorem contrastSet_phrase (γ : Set W) :
    (Antecedent.phrase γ).contrastSet = {γ} := rfl
@[simp] theorem use_phrase (γ : Set W) :
    (Antecedent.phrase γ).use = .contrastive := rfl

/-- The canonical antecedent of each use over a designated
ordinary-value/alternative pair `(o, a)`: a question, an assertion of
the alternative to be corrected, an offer, or a parallel focus — the
minimal contentful model of the four controlling contexts. -/
def Use.model (o a : Set W) : Use → Antecedent W
  | .newInfo     => .question {o, a}
  | .corrective  => .assertion a {o, a}
  | .selective   => .offer {o, a}
  | .contrastive => .parallel {o, a}

@[simp] theorem use_model (o a : Set W) (u : Use) :
    (Use.model o a u).use = u := by cases u <;> rfl

/-- Every pragmatic use is realised by some antecedent shape. -/
theorem use_surjective : Function.Surjective (Antecedent.use (W := W)) :=
  fun u => ⟨Use.model ∅ ∅ u, use_model ∅ ∅ u⟩

/-- Roothian felicity of a focus value against an antecedent: `fip` on
the antecedent's contrast set. -/
def Antecedent.Admits (c : Antecedent W) (fv : PropFocusValue W) : Prop :=
  fip c.contrastSet fv

/-- The question case is the substrate's Q-A congruence. -/
theorem question_admits_iff (q fv : PropFocusValue W) :
    (Antecedent.question q).Admits fv ↔ qaCongruentWeak fv q := Iff.rfl

/-- `Admits` is monotone in the focus value. -/
theorem Antecedent.Admits.mono {c : Antecedent W} {fv fv' : PropFocusValue W}
    (hc : c.Admits fv) (h : fv ⊆ fv') : c.Admits fv' := hc.trans h

/-- An intersection of focus values is admitted iff both are. -/
theorem admits_inter_iff {c : Antecedent W} {fv fv' : PropFocusValue W} :
    c.Admits (fv ∩ fv') ↔ c.Admits fv ∧ c.Admits fv' :=
  Set.subset_inter_iff

/-! ### The squiggle presupposition

[rooth-1992]'s ~ operator introduces the presuppositions of its (40),
over an ordinary value `o` and focus value `fv` of any type: in the set
case the resolved antecedent `Γ` is a subset of `fv` containing `o` and
a distinct alternative; in the individual case the antecedent is a
member of `fv` distinct from `o`. `Admits` is the first set-case clause;
the contrast clauses are what make ~ anaphorically demanding. -/

section Squiggle

variable {α : Type*}

/-- The ~ presupposition, set case: `Γ ⊆ fv`, `o ∈ Γ`, and `Γ` contains
an alternative distinct from `o` ([rooth-1992] (40)). -/
def SquiggleSet (o : α) (fv Γ : Set α) : Prop :=
  Γ ⊆ fv ∧ o ∈ Γ ∧ ∃ x ∈ Γ, x ≠ o

/-- The ~ presupposition, individual case: the antecedent is a member
of `fv` distinct from `o` ([rooth-1992] (40)); the contrasting-phrases
rule is this with `γ := ⟦β⟧ᵒ`. -/
def SquiggleInd (o : α) (fv : Set α) (γ : α) : Prop :=
  γ ∈ fv ∧ γ ≠ o

/-- The first set-case clause alone: the antecedent is a subset of the
focus value (at the propositional level, exactly `fip`). -/
theorem SquiggleSet.subset {o : α} {fv Γ : Set α} (h : SquiggleSet o fv Γ) :
    Γ ⊆ fv := h.1

/-- A resolved antecedent is nontrivial: it contains the ordinary value
and a distinct alternative. -/
theorem SquiggleSet.nontrivial {o : α} {fv Γ : Set α}
    (h : SquiggleSet o fv Γ) : Γ.Nontrivial :=
  let ⟨_, ho, x, hx, hne⟩ := h; ⟨x, hx, o, ho, hne⟩

/-- A unit focus value defeats the contrast clause: nothing resolves
against `{o}`. -/
theorem not_squiggleSet_singleton (o : α) (Γ : Set α) :
    ¬ SquiggleSet o {o} Γ :=
  fun ⟨hsub, _, _, hx, hne⟩ => hne (hsub hx)

theorem not_squiggleInd_singleton (o γ : α) : ¬ SquiggleInd o {o} γ :=
  fun ⟨hγ, hne⟩ => hne hγ

open Alternatives in
/-- "The argument must contain a focus": a focus-free phrase has a unit
focus value, so no antecedent resolves against it ([rooth-1992] §10). -/
theorem not_squiggleSet_unfeatured (x : α) (Γ : Set α) :
    ¬ SquiggleSet (AltMeaning.unfeatured x).oValue
      (AltMeaning.unfeatured x).aSet Γ := by
  rw [AltMeaning.unfeatured_aSet, AltMeaning.unfeatured_oValue]
  exact not_squiggleSet_singleton x Γ

end Squiggle

/-- Full Roothian resolution of an antecedent against a two-dimensional
meaning `(o, fv)`: the set case for question / offer / parallel
antecedents, the individual case for contrasting phrases — and for
assertion antecedents additionally the correction clause: the resolved
ordinary value replaces (differs from) the prior assertion. -/
def Antecedent.Resolves : Antecedent W → Set W → PropFocusValue W → Prop
  | .phrase γ, o, fv         => SquiggleInd o fv γ
  | .assertion p alts, o, fv => SquiggleSet o fv alts ∧ o ≠ p
  | c, o, fv                 => SquiggleSet o fv c.contrastSet

/-- Full resolution entails felicity: `Admits` is the set case's first
clause, and a resolved contrasting phrase is a member of the focus
value. -/
theorem Antecedent.Resolves.admits {c : Antecedent W} {o : Set W}
    {fv : PropFocusValue W} (h : c.Resolves o fv) : c.Admits fv := by
  cases c with
  | phrase γ => exact Set.singleton_subset_iff.mpr h.1
  | question q => exact h.1
  | assertion p alts => exact h.1.1
  | offer alts => exact h.1
  | parallel alts => exact h.1


/-- Felicity factors through the contrast set: the semantics sees Γ,
never the use label. -/
theorem admits_factorsThrough_contrastSet (fv : PropFocusValue W) :
    Function.FactorsThrough (Antecedent.Admits · fv)
      (Antecedent.contrastSet (W := W)) :=
  fun _ _ h => congrArg (fip · fv) h

/-- Distinct uses can supply one and the same Γ (a question and an
explicit offer, say), so the four-way split is invisible to the
Roothian semantics — pragmatic, not semantic. -/
theorem use_not_factorsThrough_contrastSet :
    ¬ Function.FactorsThrough (Antecedent.use (W := W))
        Antecedent.contrastSet :=
  fun h => absurd (h (a := .question ∅) (b := .offer ∅) rfl) (by simp)

/-! ### Hamblin antecedents -/

/-- The flat Hamblin set of complete answers over a domain. -/
def hamblin (D : Type*) : PropFocusValue D := Set.range fun d => ({d} : Set D)

/-- The wh-question antecedent over a whole domain. -/
def whAntecedent (D : Type*) : Antecedent D := .question (hamblin D)

theorem whAntecedent_admits (D : Type*) :
    (whAntecedent D).Admits (hamblin D) := subset_rfl

/-- A wh-antecedent over a domain with two distinct elements fully
resolves against the Hamblin focus value of any complete answer. -/
theorem whAntecedent_resolves {D : Type*} (d d' : D) (hne : d' ≠ d) :
    (whAntecedent D).Resolves {d} (hamblin D) :=
  ⟨subset_rfl, ⟨d, rfl⟩, ⟨{d'}, ⟨d', rfl⟩,
    fun h => hne (Set.singleton_eq_singleton_iff.mp h)⟩⟩

/-! ### Composed answers over a pair

The minimal contentful scenario: a two-point answer domain
`{d, d'}` with `d` the true answer. The answer is built by the
composition engine — the singleton complete-answer predicate mapped
over the F-marked argument — and every canonical antecedent shape
fully resolves against it. -/

open Alternatives in
/-- The composed focused answer `d` over the pair `{d, d'}`. -/
def pairAnswer {W : Type*} (d d' : W) : AltMeaning (Set W) :=
  (fun x => ({x} : Set W)) <$> (⟨d, [d, d']⟩ : AltMeaning W)

open Alternatives in
@[simp] theorem pairAnswer_oValue {W : Type*} (d d' : W) :
    (pairAnswer d d').oValue = {d} := rfl

open Alternatives in
@[simp] theorem pairAnswer_aSet {W : Type*} (d d' : W) :
    (pairAnswer d d').aSet = {{d}, {d'}} := by
  ext q
  simp only [pairAnswer, AltMeaning.mem_aSet_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases (by simpa using ha : a = d ∨ a = d') with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨d, by simp, rfl⟩
    · exact ⟨d', by simp, rfl⟩

/-- **Uniform resolution across the four uses**: every canonical
antecedent shape fully resolves — all squiggle clauses, including the
correction clause — against the composed answer over its pair. One
semantics, four pragmatic uses. -/
theorem use_model_resolves {W : Type*} {d d' : W} (hne : d' ≠ d) (u : Use) :
    (Use.model {d} {d'} u).Resolves
      (pairAnswer d d').oValue (pairAnswer d d').aSet := by
  have hne' : ({d'} : Set W) ≠ {d} :=
    fun h => hne (Set.singleton_eq_singleton_iff.mp h)
  have hSq : SquiggleSet (pairAnswer d d').oValue (pairAnswer d d').aSet
      {{d}, {d'}} := by
    rw [pairAnswer_oValue, pairAnswer_aSet]
    exact ⟨subset_rfl, Or.inl rfl, ⟨{d'}, Or.inr rfl, hne'⟩⟩
  cases u with
  | newInfo     => exact hSq
  | corrective  => exact ⟨hSq, by rw [pairAnswer_oValue]; exact hne'.symm⟩
  | selective   => exact hSq
  | contrastive => exact hSq

/-! ### Strong-theory *only*

[rooth-1992]'s official semantics: *only* quantifies over the resolved
contrast variable `C`; the focus constraint `C ⊆ ⟦·⟧f` is supplied
separately by the squiggle, "leaving room for a pragmatic process of
constructing a domain of quantification". The operator has no lexical
access to focus values — direct-association implementations carry an
alternative list lexically instead, and the two provably diverge under
domain restriction (`Studies/Rooth1992.lean`). -/

/-- The strong-theory *only* assertion, transposed to the propositional
level: every true member of the resolved contrast set is the prejacent.
The prejacent presupposition is carried separately. -/
def onlyVia (C : PropFocusValue W) (prejacent : Set W) : Set W :=
  {w | ∀ q ∈ C, w ∈ q → q = prejacent}

@[simp] theorem mem_onlyVia {C : PropFocusValue W} {p : Set W} {w : W} :
    w ∈ onlyVia C p ↔ ∀ q ∈ C, w ∈ q → q = p := Iff.rfl

/-- Narrowing the domain weakens *only* — the pragmatic domain
restriction that repairs the over-generation of a fixed full-focus
domain. -/
theorem onlyVia_antitone {C C' : PropFocusValue W} (h : C ⊆ C')
    (p : Set W) : onlyVia C' p ⊆ onlyVia C p :=
  fun _ hw q hq => hw q (h hq)

/-- Against a squiggle-resolved contrast set, *only* genuinely
excludes: the contrast clause supplies a distinct alternative that the
assertion rules out wherever it holds. -/
theorem onlyVia_excludes_of_squiggleSet {o : Set W} {fv C : PropFocusValue W}
    (h : SquiggleSet o fv C) :
    ∃ q ∈ C, q ≠ o ∧ ∀ w ∈ onlyVia C o, w ∉ q :=
  let ⟨_, _, q, hq, hne⟩ := h
  ⟨q, hq, hne, fun _ hw hwq => hne (hw q hq hwq)⟩

/-- A `Question` supplies its maximal alternatives as a question
antecedent — the bridge from the inquisitive layer. -/
def Antecedent.ofQuestion (q : Question W) : Antecedent W :=
  .question (Question.alt q)

/-- The maximal alternatives of the inquisitive wh-question over the
singleton predicates are exactly the flat Hamblin set. -/
theorem alt_which_singleton (D : Type*) [Nonempty D] :
    Question.alt (Question.which (Set.univ : Set D) fun d => ({d} : Set D)) =
      hamblin D := by
  have hA : IsAntichain (· ⊆ ·) ((fun d => ({d} : Set D)) '' Set.univ) := by
    rintro p ⟨a, -, rfl⟩ q ⟨b, -, rfl⟩ hne hsub
    exact hne (by rw [Set.singleton_subset_singleton.mp hsub])
  rw [Question.alt_which_of_antichain Set.univ_nonempty
      (fun d _ => Set.singleton_nonempty d) hA, Set.image_univ]
  rfl

/-- The inquisitive wh-question and the flat Hamblin antecedent
coincide. -/
theorem ofQuestion_which_eq_whAntecedent (D : Type*) [Nonempty D] :
    Antecedent.ofQuestion
        (Question.which (Set.univ : Set D) fun d => ({d} : Set D)) =
      whAntecedent D :=
  congrArg Antecedent.question (alt_which_singleton D)

end Semantics.Focus
