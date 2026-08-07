import Linglib.Semantics.Entailment.Polarity
import Mathlib.Data.Set.Lattice

/-!
# Chierchia 2004: parallel recursive strengthening

[chierchia-2004] ("Scalar Implicatures, Polarity Phenomena, and the
Syntax/Pragmatics Interface", §3) computes two meanings for every expression in
tandem: a plain value `‖α‖` and a strengthened value `‖α‖^S` that folds scalar
implicatures in as soon as their triggers appear. Direct implicatures enter at
scope sites by a variant of [krifka-1995a]'s rule (75); the Strength Condition
(§3.1) requires `‖α‖^S` to entail `‖α‖` at every step; and Strong Application
(84) dispatches on entailment behaviour: non-DE functions pass strengthened
values through, DE functions strip the argument's implicatures and add indirect
implicatures at the matrix level. Implicature suspension in exactly the
*any*-licensing environments — the Generalization on SIs (53) — is `Antitone`
reversal of the Strength Condition, and intervention (§4.3) follows from NPIs
competing with strong rather than plain meanings (127).

## Implementation notes

Numbered items follow the circulated manuscript (the "Bicocca, May 2001"
version); the published chapter may renumber. The paper's scalar assertion `σ`
is a definite description — *the* weakest alternative asymmetrically entailing
the target, ⊥ if none — well-defined only when the stronger alternatives have a
greatest element, as on the paper's linearly ordered scales. `krifkaRule` and
`strongApplyDE` instead negate *all* strictly stronger alternatives, a total
operation that coincides with negating `σ` exactly where `σ` is defined
(`krifkaRule_strong_eq_of_isGreatest`, `strongApplyDE_strong_eq_of_isGreatest`;
the `σ = ⊥` case is the empty intersection). The
appendix's `‖α‖^S` is a *set* of admissible strong meanings (implicature
addition at a scope site is optional); `Meaning.strong` tracks the maximal
admissible strengthening, the path the paper's own computations follow.
-/

namespace Chierchia2004

open Entailment (IsDE IsUE)

variable {World : Type*}

/-! ### Strengthened meanings -/

/-- The semantic values the parallel recursion assigns to a propositional
node: the plain value `‖α‖`, the strengthened value `‖α‖^S`, and the active
scalar alternatives. -/
structure Meaning (World : Type*) where
  /-- The plain semantic value `‖α‖`. -/
  plain : Set World
  /-- The strengthened semantic value `‖α‖^S`. -/
  strong : Set World
  /-- The active scalar alternatives. -/
  alternatives : Set (Set World)

/-- (73a): a lexical item's strong meaning is its plain meaning. -/
def Meaning.lexical (φ : Set World) (ALT : Set (Set World)) :
    Meaning World :=
  ⟨φ, φ, ALT⟩

/-- The Strength Condition (§3.1): the strong value entails the plain value,
`sm.strong ⊆ sm.plain`. -/
def Meaning.StrengthCondition (sm : Meaning World) : Prop :=
  sm.strong ⊆ sm.plain

/-! ### Krifka's rule -/

/-- Krifka's rule (75): at a scope site, conjoin the plain value with the
negations of its strictly stronger alternatives. -/
def krifkaRule (φ : Set World) (ALT : Set (Set World)) : Meaning World where
  plain := φ
  strong := φ ∩ ⋂ a ∈ {a ∈ ALT | a ⊂ φ}, aᶜ
  alternatives := ALT

@[simp]
theorem mem_krifkaRule_strong {φ : Set World} {ALT : Set (Set World)} {w : World} :
    w ∈ (krifkaRule φ ALT).strong ↔ w ∈ φ ∧ ∀ a ∈ ALT, a ⊂ φ → w ∉ a := by
  simp [krifkaRule]

theorem krifkaRule_strengthCondition (φ : Set World) (ALT : Set (Set World)) :
    (krifkaRule φ ALT).StrengthCondition :=
  λ _ hw => hw.1

/-- Agreement with the paper's scalar assertion `σ`: whenever the strictly
stronger alternatives have a weakest member `a₀` — the case in which (2)'s
definite description is defined, as on linearly ordered scales — negating all
of them is negating `a₀` alone. -/
theorem krifkaRule_strong_eq_of_isGreatest {φ a₀ : Set World} {ALT : Set (Set World)}
    (h : IsGreatest {a ∈ ALT | a ⊂ φ} a₀) :
    (krifkaRule φ ALT).strong = φ ∩ a₀ᶜ := by
  ext w
  simp only [mem_krifkaRule_strong, Set.mem_inter_iff, Set.mem_compl_iff]
  exact ⟨λ ⟨hw, hall⟩ => ⟨hw, hall a₀ h.1.1 h.1.2⟩,
    λ ⟨hw, h₀⟩ => ⟨hw, λ a haA haφ hwa => h₀ (h.2 ⟨haA, haφ⟩ hwa)⟩⟩

/-! ### Scale axioms -/

/-- The scale axioms (99): the context selects a subset of the uttered term's
lexical scale (99a) with at least two members (99b), and the uttered term is not
the strongest selected member whenever the lexical scale offers a stronger one —
the "if possible" proviso of (99c). -/
def ScaleAxioms (lexicalScale chosen : Set (Set World)) (utt : Set World) : Prop :=
  chosen ⊆ lexicalScale ∧ chosen.Nontrivial ∧ utt ∈ chosen ∧
    ((∃ a ∈ lexicalScale, a ⊂ utt) → ∃ a ∈ chosen, a ⊂ utt)

/-- Krifka's rule strengthens properly whenever some activated alternative is
strictly stronger and consistent. -/
theorem krifkaRule_strong_ssubset {φ : Set World} {ALT : Set (Set World)}
    (h : ∃ a ∈ ALT, a ⊂ φ ∧ a.Nonempty) :
    (krifkaRule φ ALT).strong ⊂ φ := by
  obtain ⟨a, haALT, haφ, w, hwa⟩ := h
  refine ssubset_iff_subset_not_subset.mpr ⟨λ _ hw => hw.1, λ hsub => ?_⟩
  exact (mem_krifkaRule_strong.1 (hsub (haφ.1 hwa))).2 a haALT haφ hwa

/-- Under the scale axioms, a stronger lexical alternative guarantees proper
strengthening — the point of the (99c) proviso. -/
theorem ScaleAxioms.krifkaRule_ssubset {lex chosen : Set (Set World)} {utt : Set World}
    (h : ScaleAxioms lex chosen utt) (hstr : ∃ a ∈ lex, a ⊂ utt)
    (hne : ∀ a ∈ chosen, a ⊂ utt → a.Nonempty) :
    (krifkaRule utt chosen).strong ⊂ utt :=
  let ⟨a, ha, hau⟩ := h.2.2.2 hstr
  krifkaRule_strong_ssubset ⟨a, ha, hau, hne a ha hau⟩

/-! ### Downward entailingness suspends implicatures -/

/-- Generalization on SIs (53): a DE function maps the strengthened argument to
a *weaker* matrix value, so keeping a direct implicature under DE embedding
would violate the Strength Condition — implicatures are suspended in exactly
the *any*-licensing environments. -/
theorem si_npi_generalization {f : Set World → Set World} (hDE : IsDE f)
    {g : Meaning World} (hg : g.StrengthCondition) :
    f g.plain ⊆ f g.strong :=
  hDE hg

/-- Instantiation of (53) at Krifka-strengthened arguments. -/
theorem de_blocks_direct_si {f : Set World → Set World} (hDE : IsDE f)
    (φ : Set World) (ALT : Set (Set World)) :
    f φ ⊆ f (krifkaRule φ ALT).strong :=
  hDE (krifkaRule_strengthCondition φ ALT)

/-! ### Strong Application -/

/-- Strong Application (84), non-DE clause: `‖[β γ]‖^S = ‖β‖^S(‖γ‖^S)`, with
alternatives projected pointwise through the function ((82b)). -/
def strongApplyUE (f fS : Set World → Set World) (g : Meaning World) :
    Meaning World where
  plain := f g.plain
  strong := fS g.strong
  alternatives := f '' g.alternatives

/-- Strong Application (84), DE clause: apply the strengthened function to the
*plain* argument — stripping the argument's direct implicatures — and negate the
strictly stronger matrix-level images of its alternatives (the indirect
implicatures). -/
def strongApplyDE (f fS : Set World → Set World) (g : Meaning World) :
    Meaning World where
  plain := f g.plain
  strong := fS g.plain ∩ ⋂ a ∈ {a ∈ g.alternatives | f a ⊂ f g.plain}, (f a)ᶜ
  alternatives := f '' g.alternatives

@[simp]
theorem mem_strongApplyDE_strong {f fS : Set World → Set World}
    {g : Meaning World} {w : World} :
    w ∈ (strongApplyDE f fS g).strong ↔
      w ∈ fS g.plain ∧ ∀ a ∈ g.alternatives, f a ⊂ f g.plain → w ∉ f a := by
  simp [strongApplyDE]

/-- Agreement with (84)'s matrix-level `σ`: whenever the strictly stronger
alternative images have a weakest member `ψ₀`, the DE clause's intersection
negates `ψ₀` alone. -/
theorem strongApplyDE_strong_eq_of_isGreatest {f fS : Set World → Set World}
    {g : Meaning World} {ψ₀ : Set World}
    (h : IsGreatest {ψ ∈ f '' g.alternatives | ψ ⊂ f g.plain} ψ₀) :
    (strongApplyDE f fS g).strong = fS g.plain ∩ ψ₀ᶜ := by
  ext w
  simp only [mem_strongApplyDE_strong, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · rintro ⟨hw, hall⟩
    obtain ⟨⟨a, haA, rfl⟩, hψφ⟩ := h.1
    exact ⟨hw, hall a haA hψφ⟩
  · exact λ ⟨hw, h₀⟩ =>
      ⟨hw, λ a haA haφ hwa => h₀ (h.2 ⟨⟨a, haA, rfl⟩, haφ⟩ hwa)⟩

/-- The non-DE clause of (84) preserves the Strength Condition when the
function's strengthening entails its plain value and the function is UE. -/
theorem strongApplyUE_strengthCondition {f fS : Set World → Set World}
    (hf : IsUE f) (hfS : ∀ X, fS X ⊆ f X) {g : Meaning World}
    (hg : g.StrengthCondition) :
    (strongApplyUE f fS g).StrengthCondition :=
  λ _ hw => hf hg (hfS g.strong hw)

/-- The DE clause of (84) satisfies the Strength Condition by construction: it
already falls back to the plain argument. -/
theorem strongApplyDE_strengthCondition {f fS : Set World → Set World}
    (hfS : ∀ X, fS X ⊆ f X) (g : Meaning World) :
    (strongApplyDE f fS g).StrengthCondition :=
  λ _ hw => hfS g.plain hw.1

/-! ### The direct implicature of "some" -/

/-- Worlds for "John saw some students": saw none, some-but-not-all, or all. -/
def sawSome : Set (Fin 3) := {w | w ≠ 0}

/-- "John saw every student" — true only in the saw-all world. -/
def sawEvery : Set (Fin 3) := {w | w = 2}

theorem sawEvery_ssubset : sawEvery ⊂ sawSome := by
  refine ssubset_iff_subset_not_subset.mpr ⟨λ w hw => ?_, λ h => ?_⟩
  · simp only [sawEvery, Set.mem_setOf_eq] at hw
    simp [sawSome, hw]
  · exact absurd (h (show (1 : Fin 3) ∈ sawSome by simp [sawSome])) (by simp [sawEvery])

/-- (74)–(76): Krifka's rule computes the direct implicature of "John saw some
students" — some but not every. -/
theorem some_not_all_implicature :
    (krifkaRule sawSome {sawSome, sawEvery}).strong = sawSome \ sawEvery := by
  ext w
  simp only [mem_krifkaRule_strong, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_sdiff, forall_eq_or_imp, forall_eq]
  exact ⟨λ ⟨hw, _, he⟩ => ⟨hw, he sawEvery_ssubset⟩,
    λ ⟨hw, he⟩ => ⟨hw, λ hss => absurd rfl hss.ne, λ _ => he⟩⟩

/-! ### The doubt example -/

/-- Worlds valuate ⟨John drinks, John drives⟩. -/
def drinkAndDrive : Set (Bool × Bool) := {w | w.1 ∧ w.2}

/-- The *or*-alternative of `drinkAndDrive` on the ⟨or, and⟩ scale. -/
def drinkOrDrive : Set (Bool × Bool) := {w | w.1 ∨ w.2}

theorem drinkAndDrive_ssubset : drinkAndDrive ⊂ drinkOrDrive := by
  refine ssubset_iff_subset_not_subset.mpr
    ⟨λ w hw => Or.inl hw.1, λ h => ?_⟩
  exact absurd (h (show (true, false) ∈ drinkOrDrive from Or.inl rfl)) (by simp [drinkAndDrive])

/-- The (81)–(83) computation: embedding "John drinks and drives" under DE
*doubt* (modelled as complement) yields the indirect implicature (83b) — doubt
the conjunction yet believe the disjunction. -/
theorem doubt_and_indirect_implicature :
    (strongApplyDE compl compl
        (.lexical drinkAndDrive {drinkAndDrive, drinkOrDrive})).strong =
      drinkAndDriveᶜ ∩ drinkOrDrive := by
  have hoc : drinkOrDriveᶜ ⊂ drinkAndDriveᶜ :=
    compl_lt_compl_iff_lt.mpr drinkAndDrive_ssubset
  ext w
  simp only [mem_strongApplyDE_strong, Meaning.lexical,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    Set.mem_inter_iff]
  exact ⟨λ ⟨hw, _, ho⟩ => ⟨hw, Set.notMem_compl_iff.1 (ho hoc)⟩,
    λ ⟨hw, ho⟩ => ⟨hw, λ hss => absurd rfl hss.ne, λ _ => Set.notMem_compl_iff.2 ho⟩⟩

/-! ### Intervention -/

/-- Worlds valuate ⟨John ate the cake, drank coffee c₁, drank coffee c₂⟩;
`{c₁}` is the default coffee domain and `{c₁, c₂}` its widening. -/
def ateCake : Set (Bool × Bool × Bool) := {w | w.1}

/-- "John drank some coffee" on the default domain `{c₁}`. -/
def drankC1 : Set (Bool × Bool × Bool) := {w | w.2.1}

/-- "John drank coffee c₂" — the widened part of the domain. -/
def drankC2 : Set (Bool × Bool × Bool) := {w | w.2.2}

/-- (128b): universal closure over domain choices of "I doubt that John ate the
cake and drank any coffee", spelled out over the nonempty subdomains of
`{c₁, c₂}`. -/
def anyAndClosure : Set (Bool × Bool × Bool) :=
  (ateCake ∩ drankC1)ᶜ ∩ (ateCake ∩ drankC2)ᶜ ∩ (ateCake ∩ (drankC1 ∪ drankC2))ᶜ

/-- The *some*-competitor of (128): "I doubt that John ate the cake and drank
some coffee" ((129a)), strengthened by the DE clause of (84). -/
def someAndCompetitor : Meaning (Bool × Bool × Bool) :=
  strongApplyDE compl compl
    (.lexical (ateCake ∩ drankC1) {ateCake ∩ drankC1, ateCake ∪ drankC1})

theorem cakeAnd_ssubset : ateCake ∩ drankC1 ⊂ ateCake ∪ drankC1 := by
  refine ssubset_iff_subset_not_subset.mpr
    ⟨λ w hw => Or.inl hw.1, λ h => ?_⟩
  exact absurd (h (show (true, false, false) ∈ ateCake ∪ drankC1 from Or.inl rfl))
    (by simp [ateCake, drankC1])

/-- (129b): the competitor's strong meaning — doubt the conjunction yet believe
John did one of the two. -/
theorem someAndCompetitor_strong :
    someAndCompetitor.strong = (ateCake ∩ drankC1)ᶜ ∩ (ateCake ∪ drankC1) := by
  have hoc : (ateCake ∪ drankC1)ᶜ ⊂ (ateCake ∩ drankC1)ᶜ :=
    compl_lt_compl_iff_lt.mpr cakeAnd_ssubset
  ext w
  simp only [someAndCompetitor, mem_strongApplyDE_strong, Meaning.lexical,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    Set.mem_inter_iff]
  exact ⟨λ ⟨hw, _, ho⟩ => ⟨hw, Set.notMem_compl_iff.1 (ho hoc)⟩,
    λ ⟨hw, ho⟩ => ⟨hw, λ hss => absurd rfl hss.ne, λ _ => Set.notMem_compl_iff.2 ho⟩⟩

/-- (127)/(128): *any* is blocked under *doubt … and*. The universal closure
fails to entail the competitor's *strong* meaning — the indirect implicature of
the intervening *and* is what breaks the entailment. -/
theorem and_blocks_any : ¬anyAndClosure ⊆ someAndCompetitor.strong := by
  intro h
  have hw : (false, false, false) ∈ anyAndClosure := by
    simp [anyAndClosure, ateCake, drankC1, drankC2]
  have := (someAndCompetitor_strong ▸ h hw).2
  simp [ateCake, drankC1] at this

/-- The closure does entail the competitor's *plain* meaning: competition with
plain meanings ((122)-style) would wrongly license *any* under *and*. -/
theorem and_any_entails_plain : anyAndClosure ⊆ (ateCake ∩ drankC1)ᶜ :=
  λ _ hw => hw.1.1

/-- (130): universal closure of "I doubt that John ate the cake or drank any
coffee" over the nonempty subdomains of `{c₁, c₂}`. -/
def anyOrClosure : Set (Bool × Bool × Bool) :=
  (ateCake ∪ drankC1)ᶜ ∩ (ateCake ∪ drankC2)ᶜ ∩ (ateCake ∪ (drankC1 ∪ drankC2))ᶜ

/-- The *some*-competitor of (130): under *doubt*, *or* is the strongest member
of its scale, so no indirect implicature arises. -/
def someOrCompetitor : Meaning (Bool × Bool × Bool) :=
  strongApplyDE compl compl
    (.lexical (ateCake ∪ drankC1) {ateCake ∩ drankC1, ateCake ∪ drankC1})

/-- (130): the or-competitor's strong meaning is its plain meaning — the
strongest member of a scale triggers no implicature. -/
theorem someOrCompetitor_strong :
    someOrCompetitor.strong = (ateCake ∪ drankC1)ᶜ := by
  ext w
  simp only [someOrCompetitor, mem_strongApplyDE_strong, Meaning.lexical,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  refine ⟨λ ⟨hw, _, _⟩ => hw, λ hw => ⟨hw, λ hss => ?_, λ hss => absurd rfl hss.ne⟩⟩
  exact absurd (compl_lt_compl_iff_lt.1 hss) (λ hlt => hlt.not_subset (λ _ h => Or.inl h.1))

/-- (130): *any* is licensed under *doubt … or* — the closure entails the
competitor's strong meaning, which never gained an indirect implicature. -/
theorem or_licenses_any : anyOrClosure ⊆ someOrCompetitor.strong := by
  rw [someOrCompetitor_strong]
  exact λ _ hw => hw.1.1

end Chierchia2004
