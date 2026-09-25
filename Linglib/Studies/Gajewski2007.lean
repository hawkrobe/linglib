module

public import Linglib.Semantics.Presupposition.Quantified
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Natural.Strawson.Basic
public import Linglib.Data.Examples.Gajewski2007

/-!
# Gajewski (2007): Neg-Raising and Polarity

This file formalizes [gajewski-2007]'s presuppositional account of neg-raising and its argument
from the licensing of strict negative polarity items. After [bartsch-1973], a neg-raising
predicate such as *think* presupposes that its subject is settled about the complement, and its
negation then entails the negated complement: *Bill doesn't think Mary is here* entails *Bill
thinks Mary is not here*. Strict NPIs such as punctual *until* and *in years* need an
anti-additive environment ([zwarts-1998]), and the presupposition makes a negated neg-raising
predicate anti-additive where a negated universal is not. Since the presupposition of a
complement projects into the subject's beliefs whatever the attitude ([karttunen-peters-1979],
[heim-1992]), the negation lowers through *think* into the complement of *want* but not through
*want* into the complement of *think*, the asymmetry of stacked neg-raising predicates that
[horn-1978] reports.

## Main definitions

* `nrp`: a neg-raising predicate over a modal base and a heritage base, the entries of
  Appendix 2.
* `every`: universal quantification with existential import over a relation, as a function on
  propositions.
* `Env`, `Env.AntiAdditive`: the environments of the paper's strict NPIs and their
  anti-additivity.

## Main results

* `holds_neg_nrp`, `holds_neg_nrp_self`: (60)–(61), a negated neg-raising predicate asserts the
  negated complement throughout its modal base, and passes through to the negated complement when
  its heritage base is its modal base.
* `isAntiAdditive_negNR`, `not_isAntiAdditive_negUniversal`: (62)–(65), a negated neg-raising
  predicate is anti-additive and a negated universal is not.
* `isAntiAdditive_noOneNR`: (83)–(90), *no one thinks* is anti-additive under universal
  projection.
* `isAntiAdditive_negStack_self`, `not_isAntiAdditive_negStack`: (97), *not think want* is
  anti-additive and *not want think* is not.
* `strawsonAntiAdditive_not_sufficient`: Appendix 1, Strawson anti-additivity does not
  characterize the licensers of strict NPIs.
* `rows_licensed`: the paper's judgments follow the anti-additivity of their environments, with
  the superlatives the exception the paper records (`superlative_exception`) and a finite clause
  boundary degrading the remaining case (`finite_boundary`).

## Implementation notes

* Propositions are sets of worlds and attitudes relational boxes (`ModalLogic.box`). An
  environment is the truth set of its sentence, presupposition included, as a function of the
  proposition in the NPI's clause, and its anti-additivity is `NaturalLogic.IsAntiAdditive` of
  that function: standard entailment, which Appendix 1 argues is the relevant notion.
* The excluded middle of `nrp` is stated with the complement's full meaning, `p(u) ≠ 1` rather
  than `p(u) = 0`, as in Appendix 2, so that a complement's own presupposition is cancelled inside
  it and projects only through the heritage base.
* The stressed reading without neg-raising cancels the presupposition with [beaver-krahmer-2001]'s
  assertion operator, which makes it the substrate's external negation `PartialProp.negExt`.

## TODO

* The appendix to §2 explains why *it's not true that* fails to license: *true* cancels the
  complement's presupposition, and disjunction projects presuppositions as in
  [karttunen-peters-1979]. Formalizing it needs complements with presuppositions, and the paper
  calls the explanation technical and incomplete.
* The Romance n-words of A.3 are not formalized.

## References

* [gajewski-2007]
* [bartsch-1973]
* [zwarts-1998]
* [von-fintel-1999]
* [horn-1978]
* [karttunen-peters-1979]
* [heim-1983]
* [heim-1992]
* [beaver-krahmer-2001]
-/

@[expose] public section

namespace Gajewski2007

open Presupposition PartialProp ModalLogic NaturalLogic Data.Examples

variable {W : Type*}

/-! ### Neg-raising predicates ((59)–(61), Appendix 2) -/

/-- (59), Appendix 2 (1)–(2): a neg-raising predicate over the modal base `R`. It presupposes that
the complement is settled throughout the modal base and that the complement's presupposition holds
throughout the heritage base `H`, and asserts the complement throughout the modal base. *Think*
has its beliefs as both bases, *want* its desires as modal base and its beliefs as heritage
base. -/
def nrp (R H : W → W → Prop) (φ : PartialProp W) : PartialProp W where
  presup w := □[H] φ.presup w ∧ (□[R] (fun u ↦ φ.holds u) w ∨ □[R] (fun u ↦ ¬ φ.holds u) w)
  assertion w := □[R] (fun u ↦ φ.holds u) w

variable {R H : W → W → Prop} {φ : PartialProp W} {w : W}

/-- (60)–(61): a negated neg-raising predicate, presupposition included, holds exactly when the
complement's presupposition holds throughout the heritage base, the modal base is nonempty, and the
complement fails throughout it. -/
theorem holds_neg_nrp :
    (neg (nrp R H φ)).holds w ↔
      □[H] φ.presup w ∧ (∃ u, R w u) ∧ □[R] (fun u ↦ ¬ φ.holds u) w := by
  refine ⟨fun ⟨⟨hH, hEM⟩, hna⟩ ↦ ⟨hH, ?_, hEM.resolve_left hna⟩,
    fun ⟨hH, ⟨u, hu⟩, hbox⟩ ↦ ⟨⟨hH, .inr hbox⟩, fun hall ↦ hbox u hu (hall u hu)⟩⟩
  by_contra hne
  push Not at hne
  exact hna fun u hu ↦ absurd hu (hne u)

/-- When the complement's presupposition projects into the predicate's own modal base, as with
*think*, the negation passes through the predicate onto the complement (§3.3.1). -/
theorem holds_neg_nrp_self :
    (neg (nrp R R φ)).holds w ↔ (∃ u, R w u) ∧ □[R] (fun u ↦ (neg φ).holds u) w := by
  rw [holds_neg_nrp]
  refine ⟨fun ⟨hH, hne, hb⟩ ↦ ⟨hne, fun u hu ↦ ⟨hH u hu, fun ha ↦ hb u hu ⟨hH u hu, ha⟩⟩⟩,
    fun ⟨hne, hb⟩ ↦ ⟨fun u hu ↦ (hb u hu).1, hne, fun u hu h ↦ (hb u hu).2 h.2⟩⟩

/-! ### Anti-additivity ((50)–(56)) -/

/-- Universal quantification with existential import over the successors of a world, as a function
on propositions: the EVERY of (92) and (110). -/
def every (R : W → W → Prop) (s : Set W) : Set W := {w | (∃ u, R w u) ∧ □[R] (· ∈ s) w}

/-- (92a): universal quantification over an anti-additive environment is anti-additive. -/
theorem isAntiAdditive_every {V : Type*} {g : Set V → Set W} (hg : IsAntiAdditive g) :
    IsAntiAdditive (every R ∘ g) := by
  rw [isAntiAdditive_iff_mem] at hg ⊢
  intro p q x
  simp only [Function.comp_apply, every, box, Set.mem_ofPred_eq, hg]
  exact ⟨fun ⟨hne, h⟩ ↦ ⟨⟨hne, fun u hu ↦ (h u hu).1⟩, hne, fun u hu ↦ (h u hu).2⟩,
    fun ⟨⟨hne, h₁⟩, _, h₂⟩ ↦ ⟨hne, fun u hu ↦ ⟨h₁ u hu, h₂ u hu⟩⟩⟩

/-- The environment of a negated neg-raising predicate. -/
def negNR (R H : W → W → Prop) (p : Set W) : Set W :=
  (neg (nrp R H (ofProp (· ∈ p)))).truthSet

/-- (61): a negated neg-raising predicate is the universal over the negated complement. -/
theorem negNR_eq (R H : W → W → Prop) (p : Set W) : negNR R H p = every R pᶜ := by
  ext w
  simp only [negNR, mem_truthSet, holds_neg_nrp, every]
  simp [ofProp, holds, box]

/-- (1): *Bill doesn't think Mary is here* entails *Bill thinks Mary is not here*. -/
theorem negNR_subset (R H : W → W → Prop) (p : Set W) : negNR R H p ⊆ {w | □[R] (· ∉ p) w} :=
  fun _ hw ↦ ((negNR_eq R H p).subset hw).2

/-- (62)–(64): a negated neg-raising predicate is anti-additive. -/
theorem isAntiAdditive_negNR (R H : W → W → Prop) : IsAntiAdditive (negNR R H) := by
  rw [show negNR R H = every R ∘ compl from funext (negNR_eq R H)]
  exact isAntiAdditive_every isAntiAdditive_compl

/-- The environment of a negated universal without neg-raising: *didn't claim*, *not every*,
*not required*, *not certain*. -/
def negUniversal (R : W → W → Prop) (p : Set W) : Set W := {w | ¬ □[R] (· ∈ p) w}

/-- (2): *Bill didn't say that Mary is here* does not entail *Bill said that Mary isn't here*. -/
theorem not_negUniversal_subset :
    ¬ ∀ (W : Type) (R : W → W → Prop) (p : Set W), negUniversal R p ⊆ {w | □[R] (· ∉ p) w} :=
  fun h ↦ h Bool (fun _ _ ↦ True) {true}
    (show true ∈ negUniversal (fun _ _ ↦ True) {true} from fun hb ↦ by simpa using hb false trivial)
    true trivial rfl

/-- (51b), (53), (65): a negated universal is not anti-additive. -/
theorem not_isAntiAdditive_negUniversal :
    ¬ IsAntiAdditive (negUniversal (fun _ _ : Bool ↦ True)) := by
  rw [isAntiAdditive_iff_mem]
  intro h
  refine (h {true} {false} true).2 ⟨fun hb ↦ by simpa using hb false trivial,
    fun hb ↦ by simpa using hb true trivial⟩ fun v _ ↦ ?_
  cases v <;> simp

/-- The environment of a negated existential: *not a single*, *not allowed*, *can't*. -/
def negExistential (R : W → W → Prop) (p : Set W) : Set W := {w | ¬ ◇[R] (· ∈ p) w}

/-- (51a), (52), (71): a negated existential is anti-additive. -/
theorem isAntiAdditive_negExistential (R : W → W → Prop) :
    IsAntiAdditive (negExistential R) := by
  rw [isAntiAdditive_iff_mem]
  intro p q x
  simp only [negExistential, diamond, Set.mem_ofPred_eq, Set.mem_union]
  refine ⟨fun h ↦ ⟨fun ⟨u, hu, hp⟩ ↦ h ⟨u, hu, .inl hp⟩, fun ⟨u, hu, hq⟩ ↦ h ⟨u, hu, .inr hq⟩⟩,
    ?_⟩
  rintro ⟨h₁, h₂⟩ ⟨u, hu, hp | hq⟩
  exacts [h₁ ⟨u, hu, hp⟩, h₂ ⟨u, hu, hq⟩]

/-- The environment of a neg-raising predicate under stressed negation, fn. 7 (ii): the assertion
operator cancels the excluded middle. -/
def negNRStressed (R : W → W → Prop) (p : Set W) : Set W :=
  (negExt (nrp R R (ofProp (· ∈ p)))).truthSet

/-- §2.1.3: without its presupposition a negated neg-raising predicate is a negated universal. -/
theorem negNRStressed_eq (R : W → W → Prop) : negNRStressed R = negUniversal R := by
  ext p w
  simp only [negNRStressed, negUniversal, mem_truthSet, negExt, Set.mem_ofPred_eq]
  simp only [holds, neg, truthOp, nrp, ofProp, box]
  refine ⟨fun ⟨_, h⟩ hall ↦ h ⟨⟨fun _ _ ↦ trivial, .inl fun u hu ↦ ⟨trivial, hall u hu⟩⟩,
    fun u hu ↦ ⟨trivial, hall u hu⟩⟩, fun h ↦ ⟨trivial, fun ⟨_, hall⟩ ↦ h fun u hu ↦ (hall u hu).2⟩⟩

/-- The environment of negated *know*, a factive universal without neg-raising, built from the
substrate's negated factive. -/
def negKnow (R : W → W → Prop) (p : Set W) : Set W :=
  (negFactive (ofProp (· ∈ p)) (box R)).truthSet

/-- (58b): negated *know* is not anti-additive. -/
theorem not_isAntiAdditive_negKnow : ¬ IsAntiAdditive (negKnow (W := Fin 3) fun _ _ ↦ True) := by
  rw [isAntiAdditive_iff_mem]
  intro h
  have := (h {0, 1} {0, 2} 0).2
  simp only [negKnow, mem_truthSet, holds, negFactive, ofProp, box, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_union] at this
  revert this
  decide

/-! ### Negative quantifiers (§3.1) -/

/-- (83): *no one thinks p*, with the excluded middle projecting universally from the scope of
the quantifier ([heim-1983]). -/
def noOneNR {E : Type*} (O : Set E) (B : E → W → W → Prop) (p : Set W) : Set W :=
  (negExistsPartial (· ∈ O) fun x ↦ nrp (B x) (B x) (ofProp (· ∈ p))).truthSet

/-- (87)–(89): *no one thinks p* is *everyone thinks not-p*. -/
theorem noOneNR_eq {E : Type*} (O : Set E) (B : E → W → W → Prop) (p : Set W) :
    noOneNR O B p = {w | ∀ x ∈ O, w ∈ every (B x) pᶜ} := by
  ext w
  simp only [noOneNR, mem_truthSet, holds, negExistsPartial, nrp, ofProp, box, every,
    Set.mem_ofPred_eq, not_exists, not_and, Set.mem_compl_iff, true_and]
  refine ⟨fun ⟨hp, ha⟩ x hx ↦ ?_, fun h ↦ ⟨fun x hx ↦ ⟨fun _ _ ↦ trivial, .inr (h x hx).2⟩,
    fun x hx hall ↦ (h x hx).1.elim fun u hu ↦ (h x hx).2 u hu (hall u hu)⟩⟩
  rcases (hp x hx).2 with h | h
  · exact absurd h (ha x hx)
  · refine ⟨?_, fun u hu ↦ h u hu⟩
    by_contra hne
    exact ha x hx fun u hu ↦ absurd ⟨u, hu⟩ hne

/-- (90): *no one thinks* is anti-additive. -/
theorem isAntiAdditive_noOneNR {E : Type*} (O : Set E) (B : E → W → W → Prop) :
    IsAntiAdditive (noOneNR O B) := by
  have hB x := isAntiAdditive_iff_mem.1 (isAntiAdditive_every (R := B x) isAntiAdditive_compl)
  rw [isAntiAdditive_iff_mem]
  intro p q w
  simp only [noOneNR_eq, Set.mem_ofPred_eq]
  exact ⟨fun h ↦ ⟨fun x hx ↦ ((hB x p q w).1 (h x hx)).1, fun x hx ↦ ((hB x p q w).1 (h x hx)).2⟩,
    fun ⟨h₁, h₂⟩ x hx ↦ (hB x p q w).2 ⟨h₁ x hx, h₂ x hx⟩⟩

/-! ### Stacked neg-raising predicates (§3.2–3.3) -/

/-- The environment of a negated neg-raising predicate over another. -/
def negStack (R₁ H₁ R₂ H₂ : W → W → Prop) (p : Set W) : Set W :=
  (neg (nrp R₁ H₁ (nrp R₂ H₂ (ofProp (· ∈ p))))).truthSet

/-- (107)–(110): under a predicate whose heritage base is its modal base, such as *think*, the
negation goes all the way down. -/
theorem negStack_self_eq (R₁ R₂ H₂ : W → W → Prop) (p : Set W) :
    negStack R₁ R₁ R₂ H₂ p = every R₁ (every R₂ pᶜ) := by
  ext w
  simp only [negStack, mem_truthSet, holds_neg_nrp_self, every, box, Set.mem_ofPred_eq]
  exact and_congr_right fun _ ↦ forall₂_congr fun u _ ↦ Set.ext_iff.1 (negNR_eq R₂ H₂ p) u

/-- (95): *I don't believe Bill wanted Harry to die* entails *I believe Bill wanted Harry not to
die*. -/
theorem negStack_self_subset (R₁ R₂ H₂ : W → W → Prop) (p : Set W) :
    negStack R₁ R₁ R₂ H₂ p ⊆ {w | □[R₁] (□[R₂] (· ∉ p)) w} := fun _ hw ↦
  fun u hu ↦ (((negStack_self_eq R₁ R₂ H₂ p).subset hw).2 u hu).2

/-- (97a): *not think want* is anti-additive. -/
theorem isAntiAdditive_negStack_self (R₁ R₂ H₂ : W → W → Prop) :
    IsAntiAdditive (negStack R₁ R₁ R₂ H₂) := by
  rw [show negStack R₁ R₁ R₂ H₂ = every R₁ ∘ (every R₂ ∘ compl) from
    funext (negStack_self_eq R₁ R₂ H₂)]
  exact isAntiAdditive_every (isAntiAdditive_every isAntiAdditive_compl)

/-- (111)–(113): when the inner predicate's heritage base is its modal base, the negated stack
holds exactly when the inner subject is settled throughout the outer heritage base, the outer modal
base is nonempty, and the inner predicate fails throughout it. -/
theorem negStack_eq (R₁ H₁ R₂ : W → W → Prop) (p : Set W) :
    negStack R₁ H₁ R₂ R₂ p = {w | (∀ u, H₁ w u → □[R₂] (· ∈ p) u ∨ □[R₂] (· ∉ p) u) ∧
      (∃ u, R₁ w u) ∧ □[R₁] (fun u ↦ ¬ □[R₂] (· ∈ p) u) w} := by
  ext w
  simp only [negStack, mem_truthSet, holds_neg_nrp, Set.mem_ofPred_eq]
  simp only [holds, nrp, ofProp, box, true_and, implies_true]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun u _ ↦
    ⟨fun h hall ↦ h ⟨.inl hall, hall⟩, fun h ⟨_, hall⟩ ↦ h hall⟩

/-! A frame for *John doesn't want Fred to think*: John's desire world `0` has Fred considering the
worlds `2` and `3` possible, and at John's belief world `1` Fred is settled, considering only
`4`. -/

/-- John's desire alternatives in the frame. -/
abbrev desJohn : Fin 5 → Fin 5 → Prop := fun w u ↦ w = 0 ∧ u = 0

/-- John's belief alternatives in the frame. -/
abbrev belJohn : Fin 5 → Fin 5 → Prop := fun w u ↦ w = 0 ∧ u = 1

/-- Fred's belief alternatives in the frame. -/
abbrev belFred : Fin 5 → Fin 5 → Prop := fun w u ↦ (w = 0 ∧ (u = 2 ∨ u = 3)) ∨ (w = 1 ∧ u = 4)

/-- Fred is settled at John's belief world about any proposition. -/
private theorem belFred_settled (s : Set (Fin 5)) :
    ∀ u, belJohn 0 u → □[belFred] (· ∈ s) u ∨ □[belFred] (· ∉ s) u := by
  rintro u ⟨-, rfl⟩
  by_cases h : (4 : Fin 5) ∈ s
  · refine .inl fun v hv ↦ ?_
    rcases hv with ⟨h', -⟩ | ⟨-, rfl⟩
    exacts [absurd h' (by decide), h]
  · refine .inr fun v hv ↦ ?_
    rcases hv with ⟨h', -⟩ | ⟨-, rfl⟩
    exacts [absurd h' (by decide), h]

/-- At John's desire world Fred believes no proposition excluding `2` or `3`. -/
private theorem belFred_not_box {s : Set (Fin 5)} {x : Fin 5} (hx : x = 2 ∨ x = 3) (hxs : x ∉ s) :
    □[desJohn] (fun u ↦ ¬ □[belFred] (· ∈ s) u) 0 := by
  rintro u ⟨-, rfl⟩ hall
  exact hxs (hall x (.inl ⟨rfl, hx⟩))

/-- (96), (114): *I don't want Bill to believe Harry died* does not entail *I want Bill to believe
Harry didn't die*. -/
theorem not_negStack_subset :
    ¬ negStack desJohn belJohn belFred belFred {2} ⊆
      {w | □[desJohn] (□[belFred] (· ∉ ({2} : Set (Fin 5)))) w} :=
  fun h ↦ h ((negStack_eq _ _ _ _).superset ⟨belFred_settled _, ⟨0, rfl, rfl⟩,
    belFred_not_box (.inr rfl) (by simp)⟩) 0 ⟨rfl, rfl⟩ 2 (.inl ⟨rfl, .inl rfl⟩) rfl

/-- (97b): *not want think* is not anti-additive. John wants Fred not to think `p` and not to
think `q`, and yet Fred thinks `p or q` at John's desire world. -/
theorem not_isAntiAdditive_negStack :
    ¬ IsAntiAdditive (negStack desJohn belJohn belFred belFred) := by
  rw [isAntiAdditive_iff_mem]
  intro h
  obtain ⟨-, -, hna⟩ := (negStack_eq _ _ _ _).subset ((h {2, 4} {3, 4} 0).2
    ⟨(negStack_eq _ _ _ _).superset ⟨belFred_settled _, ⟨0, rfl, rfl⟩,
      belFred_not_box (.inr rfl) (by simp)⟩,
    (negStack_eq _ _ _ _).superset ⟨belFred_settled _, ⟨0, rfl, rfl⟩,
      belFred_not_box (.inl rfl) (by simp)⟩⟩)
  refine hna 0 ⟨rfl, rfl⟩ fun v hv ↦ ?_
  rcases hv with ⟨-, rfl | rfl⟩ | ⟨h', -⟩
  · simp
  · simp
  · exact absurd h' (by decide)

/-! ### Strawson anti-additivity (Appendix 1) -/

/-- (130): a superlative is not classically downward entailing, its presupposition failing at the
empty property. -/
theorem superlative_not_antitone :
    ¬ Antitone fun Q : Unit → Set Unit ↦ (superlative (fun _ : Unit ↦ (0 : ℕ)) Q ()).truthSet :=
  not_antitone_truthSet (p := ⊥) (q := fun _ ↦ Set.univ) (w := ()) bot_le
    ⟨trivial, fun _ _ h ↦ absurd rfl h⟩ id

/-! ### The environments of the paper's strict NPIs -/

/-- The environments in which the paper places a strict NPI. -/
inductive Env
  /-- No licenser, (12a), (13a). -/
  | positive
  /-- Sentential negation, (12b), (13b). -/
  | negation
  /-- A negated existential: *not a single*, *not allowed*, *can't*, *not possible*. -/
  | notSome
  /-- A negated universal: *not every*, *didn't claim*, *not required*, *not certain*. -/
  | notEvery
  /-- A negated neg-raising predicate: *doesn't think*, *doesn't believe*. -/
  | notThink
  /-- A neg-raising predicate under stressed negation, fn. 7 (ii). -/
  | notThinkStressed
  /-- Negated *know*, (58b). -/
  | notKnow
  /-- A negative quantifier over a neg-raising predicate, (83). -/
  | noOneThinks
  /-- A negated doxastic neg-raising predicate over another: *don't believe … wanted*. -/
  | notThinkWant
  /-- A negated bouletic or deontic neg-raising predicate over a doxastic one: *don't want …
  believe*, *shouldn't think*. -/
  | notWantThink
  /-- *Only DP*, (123). -/
  | only
  /-- An adversative attitude, (126). -/
  | adversative
  /-- A conditional antecedent, (127). -/
  | conditional
  /-- The relative clause of a superlative, (132). -/
  | superlative
  deriving DecidableEq, Repr

/-- An environment is anti-additive in every frame. -/
def Env.AntiAdditive : Env → Prop
  | .positive => ∀ W : Type, IsAntiAdditive (id : Set W → Set W)
  | .negation => ∀ W : Type, IsAntiAdditive (compl : Set W → Set W)
  | .notSome => ∀ (W : Type) (R : W → W → Prop), IsAntiAdditive (negExistential R)
  | .notEvery => ∀ (W : Type) (R : W → W → Prop), IsAntiAdditive (negUniversal R)
  | .notThink => ∀ (W : Type) (R H : W → W → Prop), IsAntiAdditive (negNR R H)
  | .notThinkStressed => ∀ (W : Type) (R : W → W → Prop), IsAntiAdditive (negNRStressed R)
  | .notKnow => ∀ (W : Type) (R : W → W → Prop), IsAntiAdditive (negKnow R)
  | .noOneThinks =>
      ∀ (W E : Type) (O : Set E) (B : E → W → W → Prop), IsAntiAdditive (noOneNR O B)
  | .notThinkWant => ∀ (W : Type) (B R H : W → W → Prop), IsAntiAdditive (negStack B B R H)
  | .notWantThink => ∀ (W : Type) (D B R : W → W → Prop), IsAntiAdditive (negStack D B R R)
  | .only => ∀ (W ι : Type) (x : ι),
      IsAntiAdditive fun P : ι → Set W ↦ (NaturalLogic.only x P).truthSet
  | .adversative =>
      ∀ (W : Type) (dox best : W → Set W), IsAntiAdditive fun p ↦ (regret dox best p).truthSet
  | .conditional => ∀ (W : Type) (domain : W → Set W) (q : Set W),
      IsAntiAdditive fun p ↦ (would domain p q).truthSet
  | .superlative => ∀ (W ι D : Type) [Preorder D] (μ : ι → D) (a : ι),
      IsAntiAdditive fun Q : ι → Set W ↦ (NaturalLogic.superlative μ Q a).truthSet

private theorem not_isAntiAdditive_id : ¬ IsAntiAdditive (id : Set Bool → Set Bool) := by
  rw [isAntiAdditive_iff_mem]
  intro h
  exact absurd ((h {true} {false} true).1 (.inl rfl)).2 (by simp)

/-- Of the paper's environments, sentential negation, the negated existentials, the negated
neg-raising predicates, *no one thinks* and *not think want* are anti-additive. -/
theorem Env.antiAdditive_iff (e : Env) :
    e.AntiAdditive ↔ e ∈ [.negation, .notSome, .notThink, .noOneThinks, .notThinkWant] := by
  cases e with
  | positive => exact iff_of_false (fun h ↦ not_isAntiAdditive_id (h Bool)) (by decide)
  | negation => exact iff_of_true (fun _ ↦ isAntiAdditive_compl) (by decide)
  | notSome => exact iff_of_true (fun _ ↦ isAntiAdditive_negExistential) (by decide)
  | notEvery => exact iff_of_false (fun h ↦ not_isAntiAdditive_negUniversal (h _ _)) (by decide)
  | notThink => exact iff_of_true (fun _ ↦ isAntiAdditive_negNR) (by decide)
  | notThinkStressed =>
    exact iff_of_false (fun h ↦ not_isAntiAdditive_negUniversal
      (negNRStressed_eq (W := Bool) _ ▸ h _ _)) (by decide)
  | notKnow => exact iff_of_false (fun h ↦ not_isAntiAdditive_negKnow (h _ _)) (by decide)
  | noOneThinks => exact iff_of_true (fun _ _ ↦ isAntiAdditive_noOneNR) (by decide)
  | notThinkWant => exact iff_of_true (fun _ ↦ isAntiAdditive_negStack_self) (by decide)
  | notWantThink =>
    exact iff_of_false (fun h ↦ not_isAntiAdditive_negStack (h _ _ _ _)) (by decide)
  | only =>
    exact iff_of_false (fun h ↦ only_not_antitone (h Unit Bool true).antitone) (by decide)
  | adversative =>
    exact iff_of_false (fun h ↦ regret_not_antitone (h _ _ _).antitone) (by decide)
  | conditional =>
    exact iff_of_false (fun h ↦ would_not_antitone (h _ _ _).antitone) (by decide)
  | superlative =>
    exact iff_of_false (fun h ↦ superlative_not_antitone (h Unit Unit ℕ _ _).antitone) (by decide)

instance : DecidablePred Env.AntiAdditive := fun e ↦ decidable_of_iff _ e.antiAdditive_iff.symm

/-- (122)–(131): *only DP*, the adversatives, conditional antecedents and superlatives are all
Strawson anti-additive, and none is anti-additive. -/
theorem strawsonAntiAdditive_not_sufficient :
    (∀ (W ι : Type) (x : ι), IsStrawsonAntiAdditive (NaturalLogic.only (W := W) x)) ∧
      (∀ (W : Type) (dox best : W → Set W), IsStrawsonAntiAdditive (regret dox best)) ∧
      (∀ (W : Type) (domain : W → Set W) (q : Set W),
        IsStrawsonAntiAdditive (would domain · q)) ∧
      (∀ (W ι D : Type) [Preorder D] (μ : ι → D) (a : ι),
        IsStrawsonAntiAdditive (NaturalLogic.superlative (W := W) μ · a)) ∧
      ∀ e ∈ [Env.only, .adversative, .conditional, .superlative], ¬ e.AntiAdditive :=
  ⟨fun _ _ x ↦ only_isStrawsonAA x, fun _ dox best ↦ regret_isStrawsonAA dox best,
    fun _ domain q ↦ would_isStrawsonAA domain q, fun _ _ _ _ μ a ↦ superlative_isStrawsonAA μ a,
    by decide⟩

/-! ### The paper's judgments -/

/-- The environments of the rows, keyed as in `Data/Examples/Gajewski2007.json`. -/
def envTable : List (String × Env) :=
  [("positive", .positive), ("negation", .negation), ("notSome", .notSome),
    ("notEvery", .notEvery), ("notThink", .notThink), ("notThinkStressed", .notThinkStressed),
    ("notKnow", .notKnow), ("noOneThinks", .noOneThinks), ("notThinkWant", .notThinkWant),
    ("notWantThink", .notWantThink), ("only", .only), ("adversative", .adversative),
    ("conditional", .conditional), ("superlative", .superlative)]

/-- A sentence with a strict NPI: its environment and its judgment. -/
structure Row where
  /-- The environment of the strict NPI. -/
  env : Env
  /-- The paper's judgment. -/
  judgment : Judgment
  deriving DecidableEq, Repr

/-- The row of an example. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  pure ⟨← ex.parse? "environment" envTable, ex.judgment⟩

/-- Every example of the paper parses to a row. -/
theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

/-- The paper's sentences with strict NPIs. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- (55): a strict NPI is acceptable in an anti-additive environment and unacceptable elsewhere,
the superlatives aside. -/
theorem rows_licensed : ∀ r ∈ rows, r.env ≠ .superlative →
    (r.judgment = .acceptable → r.env.AntiAdditive) ∧
      (r.judgment = .unacceptable → ¬ r.env.AntiAdditive) := by
  decide

/-- (132): strict NPIs are acceptable in superlative relative clauses, which are Strawson
anti-additive but not anti-additive, the exception the paper leaves open. -/
theorem superlative_exception :
    ∀ r ∈ rows, r.env = .superlative → r.judgment = .acceptable ∧ ¬ r.env.AntiAdditive := by
  decide

/-- (73)–(74): where a strict NPI in an anti-additive environment is not acceptable, a finite
clause boundary separates it from its licenser, the room the paper leaves for a locality
condition. -/
theorem finite_boundary : ∀ ex ∈ Examples.all, ∀ e ∈ ex.parse? "environment" envTable,
    e.AntiAdditive → ex.judgment ≠ .acceptable → ex.feature? "clause" = some "finite" := by
  decide

end Gajewski2007
