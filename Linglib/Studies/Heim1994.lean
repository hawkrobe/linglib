import Linglib.Logic.Modal.Epistemic
import Linglib.Semantics.Questions.Exhaustivity
import Linglib.Data.Examples.Heim1994

/-!
# Heim (1994): Interrogative Semantics and Karttunen's Semantics for *know*

This file formalizes [heim-1994]: with [karttunen-1977]'s interrogative intensions, the set
of true answers at each world, the simplified analysis of *know* (4) has the agent believe
the intersection of the true answers, the actual analysis (5) adds that an empty answer set
be known to be empty, and the generalized analysis (9) has the agent believe that the answer
set is what it is, which makes the first clause redundant
(`simplifiedKnow_of_generalizedKnow`). For
"which students called" the generalized analysis coincides with [groenendijk-stokhof-1982]'s
(13)–(14) exactly when distinct individuals call in distinct sets of worlds
(`generalizedKnow_iff_gsKnow`), and the coincidence fails on the paper's two contrived
predicates: identity with oneself (21), where the generalized analysis reduces to knowing
whether there are students, and living with one's actual spouse (24), where the symmetry
of the relation lets the report come out true. Structured propositions (27) restore the
equivalence for any predicate (`structured_eq_gs`).

## Implementation notes

Belief is the substrate's epistemic box over doxastic alternatives, so "x believes p in w"
is `knows Dox x p w`. A Karttunen intension is any `W → Set (Set W)`; the property the
redundancy proof uses, that every member of the answer set at a world is true there, is
`IsKarttunen`. The exhaustiveness failure of the actual analysis (§2) and the two divergences
of §7 are shown on two-individual, two-world models rather than stated over arbitrary
models, as the paper's scenarios are. The answers in the two senses (15)–(16) are the
substrate's `weakAnswer` and its reflective closure, of which the Groenendijk–Stokhof answer
is a subset (`strongAnswer_subset_ans₂`); the ambiguity of *answer* in (17)–(20) is a row.

## References

* [heim-1994]
* [karttunen-1977]
* [groenendijk-stokhof-1982]
* [groenendijk-stokhof-1984]
-/

namespace Heim1994

open ModalLogic.Epistemic Question

variable {W E : Type*}

/-! ### Karttunen intensions and the three analyses of *know* (§1, §2, §4) -/

/-- The property of every intension of an interrogative clause under [karttunen-1977]: each
    member of the answer set at `w` is true at `w`. -/
def IsKarttunen (q : W → Set (Set W)) : Prop := ∀ w, ∀ p ∈ q w, w ∈ p

/-- (2): the intension of "whether φ", the true one of `φ` and its negation. -/
def whether (φ : Set W) : W → Set (Set W) := λ w => {p | (p = φ ∨ p = φᶜ) ∧ w ∈ p}

/-- (3): the intension of "which students called", the propositions that `x` called for the
    students `x` who actually called. -/
def whichK (S C : W → E → Prop) : W → Set (Set W) :=
  λ w => {p | ∃ x, S w x ∧ C w x ∧ p = {w' | C w' x}}

theorem isKarttunen_whether (φ : Set W) : IsKarttunen (whether φ) := λ _ _ h => h.2

theorem isKarttunen_whichK (S C : W → E → Prop) : IsKarttunen (whichK S C) := by
  rintro w p ⟨x, -, hC, rfl⟩
  exact hC

variable (Dox : E → W → Set W) (x : E) (w : W)

/-- (4) The simplified Karttunen analysis: `x` believes the intersection of the true
    answers. -/
def simplifiedKnow (q : W → Set (Set W)) : Prop := knows Dox x (⋂₀ q w) w

/-- (5) The actual Karttunen analysis: (i) as in (4), and (ii) if the answer set is empty,
    `x` believes that it is empty. -/
def actualKnow (q : W → Set (Set W)) : Prop :=
  knows Dox x (⋂₀ q w) w ∧ (q w = ∅ → knows Dox x {w' | q w' = ∅} w)

/-- (9) The generalized Karttunen analysis: `x` believes that the answer set is what it is. -/
def generalizedKnow (q : W → Set (Set W)) : Prop := knows Dox x {w' | q w' = q w} w

/-- (14) [groenendijk-stokhof-1982]'s analysis, over an intension that is a proposition at
    each world. -/
def gsKnow (r : W → Set W) : Prop := knows Dox x (r w) w

variable {Dox x w}

/-- (7): with an empty answer set, believing it empty is believing it to be what it is. -/
theorem actualKnow_iff {q : W → Set (Set W)} (h : q w = ∅) :
    actualKnow Dox x w q ↔ knows Dox x (⋂₀ q w) w ∧ generalizedKnow Dox x w q := by
  simp only [actualKnow, generalizedKnow, h, forall_const]

/-- §4: clause (i) of (8) is redundant given clause (ii): every proposition in `q w'` is
    true in `w'`, so an alternative `w'` with `q w' = q w` lies in the intersection of
    `q w`. -/
theorem simplifiedKnow_of_generalizedKnow {q : W → Set (Set W)} (hq : IsKarttunen q)
    (h : generalizedKnow Dox x w q) : simplifiedKnow Dox x w q := by
  intro w' hw'
  have e : q w' = q w := h w' hw'
  exact Set.mem_sInter.2 λ p hp => hq w' p (e ▸ hp)

/-- Hence (8) and (9) are equivalent, and the generalized analysis implies the actual one. -/
theorem actualKnow_of_generalizedKnow {q : W → Set (Set W)} (hq : IsKarttunen q)
    (h : generalizedKnow Dox x w q) : actualKnow Dox x w q :=
  ⟨simplifiedKnow_of_generalizedKnow hq h, λ e => by unfold generalizedKnow at h; rwa [e] at h⟩

/-- Footnote 11: for a *whether*-question the three analyses coincide with
    [groenendijk-stokhof-1982]'s (12). -/
theorem whether_eq_gs (φ : Set W) :
    {w' | whether φ w' = whether φ w} = {w' | w' ∈ φ ↔ w ∈ φ} := by
  ext w'
  constructor
  · intro h
    simpa [whether] using Set.ext_iff.1 h φ
  · intro h
    ext p
    simp only [whether, Set.mem_ofPred_eq]
    rcases em (p = φ) with rfl | hp
    · simp only [true_or, true_and]
      exact h
    · rcases em (p = φᶜ) with rfl | hp'
      · simp only [or_true, true_and, Set.mem_compl_iff]
        exact not_congr h
      · simp [hp, hp']

theorem sInter_whether (φ : Set W) : ⋂₀ whether φ w = {w' | w' ∈ φ ↔ w ∈ φ} := by
  ext w'
  simp only [Set.mem_sInter, whether, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨λ hw' => by_contra λ hw => h φᶜ ⟨Or.inr rfl, hw⟩ hw', λ hw => h φ ⟨Or.inl rfl, hw⟩⟩
  · rintro h p ⟨hp | hp, hw⟩ <;> subst hp
    · exact h.2 hw
    · exact λ hw' => hw (h.1 hw')

theorem simplifiedKnow_whether_iff (φ : Set W) :
    simplifiedKnow Dox x w (whether φ) ↔ generalizedKnow Dox x w (whether φ) := by
  unfold simplifiedKnow generalizedKnow
  rw [sInter_whether, whether_eq_gs]

/-! ### Constituent questions: Karttunen against Groenendijk and Stokhof (§4–§5) -/

/-- (13): [groenendijk-stokhof-1982]'s intension of "which students called": the worlds
    where the same individuals are students who called. -/
def whichGS (S C : W → E → Prop) : W → Set W :=
  λ w => {w' | ∀ x, S w' x ∧ C w' x ↔ S w x ∧ C w x}

/-- (10) is (11): when distinct individuals call in distinct sets of worlds, believing that
    the set of propositions "x called" for the students `x` who called is what it is, is
    believing that the students who called are who they are. -/
theorem whichK_eq_whichGS {S C : W → E → Prop} (hC : Function.Injective λ x => {w' | C w' x}) :
    {w' | whichK S C w' = whichK S C w} = whichGS S C w := by
  ext w'
  simp only [Set.mem_ofPred_eq, whichGS]
  rw [Set.ext_iff]
  simp only [whichK, Set.mem_ofPred_eq]
  constructor
  · intro h y
    constructor
    · rintro ⟨hS, hC'⟩
      obtain ⟨z, hSz, hCz, hz⟩ := (h {v | C v y}).1 ⟨y, hS, hC', rfl⟩
      obtain rfl := hC hz.symm
      exact ⟨hSz, hCz⟩
    · rintro ⟨hS, hC'⟩
      obtain ⟨z, hSz, hCz, hz⟩ := (h {v | C v y}).2 ⟨y, hS, hC', rfl⟩
      obtain rfl := hC hz.symm
      exact ⟨hSz, hCz⟩
  · intro h p
    constructor
    · rintro ⟨y, hS, hC', rfl⟩
      exact ⟨y, ((h y).1 ⟨hS, hC'⟩).1, ((h y).1 ⟨hS, hC'⟩).2, rfl⟩
    · rintro ⟨y, hS, hC', rfl⟩
      exact ⟨y, ((h y).2 ⟨hS, hC'⟩).1, ((h y).2 ⟨hS, hC'⟩).2, rfl⟩

/-- The generalized Karttunen analysis and Groenendijk and Stokhof's agree on "which
    students called" under the injectivity premise. -/
theorem generalizedKnow_iff_gsKnow {S C : W → E → Prop}
    (hC : Function.Injective λ x => {w' | C w' x}) :
    generalizedKnow Dox x w (whichK S C) ↔ gsKnow Dox x w (whichGS S C) := by
  unfold generalizedKnow gsKnow
  rw [whichK_eq_whichGS hC]

/-! ### The exhaustiveness failure of the actual analysis (§2)

Two individuals, Bill and Mary, both students; Bill called in every world and Mary called
only in the world `true`. In the world `false`, John is agnostic about Mary. -/

/-- Bill (`true`) called everywhere; Mary (`false`) called only in the world `true`. -/
def called : Bool → Bool → Prop := λ w y => y = true ∨ w = true

/-- John's doxastic alternatives: every world, at every world. -/
def agnostic : Unit → Bool → Set Bool := λ _ _ => Set.univ

/-- The actual analysis makes (1) true at `false`, where Mary did not call: the only true
    answer, that Bill called, is believed, and the answer set is not empty. -/
theorem actualKnow_called : actualKnow agnostic () false (whichK (λ _ _ => True) called) := by
  refine ⟨λ w' _ => Set.mem_sInter.2 ?_, λ e => ?_⟩
  · rintro p ⟨y, -, hy, rfl⟩
    rcases y with _ | _
    · exact absurd hy (by simp [called])
    · exact Or.inl rfl
  · have hm : {w' | called w' true} ∈ whichK (λ _ _ => True) called false :=
      ⟨true, trivial, Or.inl rfl, rfl⟩
    rw [e] at hm
    exact (Set.notMem_empty _ hm).elim

/-- The generalized analysis makes (1) false there: in the alternative `true` Mary called
    too, so the answer set differs. -/
theorem not_generalizedKnow_called :
    ¬ generalizedKnow agnostic () false (whichK (λ _ _ => True) called) := by
  intro h
  have e : whichK (λ _ _ => True) called true = whichK (λ _ _ => True) called false :=
    h true trivial
  have hm : {w' | called w' false} ∈ whichK (λ _ _ => True) called true :=
    ⟨false, trivial, Or.inr rfl, rfl⟩
  rw [e] at hm
  obtain ⟨y, -, hy, hp⟩ := hm
  have := Set.ext_iff.1 hp false
  rcases y with _ | _
  · exact absurd hy (by simp [called])
  · simp [called] at this

/-! ### Non-equivalence (§7) -/

/-- With the universally necessary property, the answer set is `{univ}` when there are
    students and empty otherwise. -/
theorem whichK_const_true {S : W → E → Prop} (hS : ∃ y, S w y) :
    whichK S (λ _ _ => True) w = {Set.univ} := by
  ext p
  simp only [whichK, Set.mem_ofPred_eq, true_and, Set.ofPred_true, Set.mem_singleton_iff]
  exact ⟨λ ⟨_, _, h⟩ => h, λ h => hS.imp λ y hy => ⟨hy, h⟩⟩

theorem whichK_const_false {S : W → E → Prop} (hS : ¬ ∃ y, S w y) :
    whichK S (λ _ _ => True) w = ∅ := by
  ext p
  simp only [whichK, Set.mem_ofPred_eq, true_and, Set.notMem_empty, iff_false, not_exists,
    not_and]
  exact λ y hy _ => hS ⟨y, hy⟩

/-- (23): for the universally necessary property, the generalized Karttunen analysis of (21)
    asks only whether there are students. -/
theorem whichK_self {S : W → E → Prop} :
    {w' | whichK S (λ _ _ => True) w' = whichK S (λ _ _ => True) w} =
      {w' | (∃ y, S w' y) ↔ ∃ y, S w y} := by
  ext w'
  simp only [Set.mem_ofPred_eq]
  by_cases h' : ∃ y, S w' y <;> by_cases h : ∃ y, S w y
  · simp [whichK_const_true h', whichK_const_true h, h', h]
  · simp [whichK_const_true h', whichK_const_false h, h', h]
  · simp [whichK_const_false h', whichK_const_true h, h', h]
  · simp [whichK_const_false h', whichK_const_false h, h', h]

/-- Two worlds with one student each, Bill in `true` and Mary in `false`. -/
def oneStudent : Bool → Bool → Prop := λ w y => y = w

/-- On (21), the generalized analysis ascribes knowledge to the agnostic John, since there
    are students in both worlds, while Groenendijk and Stokhof's (22) does not. -/
theorem self_divergence :
    generalizedKnow agnostic () true (whichK oneStudent (λ _ _ => True)) ∧
      ¬ gsKnow agnostic () true (whichGS oneStudent (λ _ _ => True)) := by
  constructor
  · intro w' _
    show whichK oneStudent (λ _ _ => True) w' = whichK oneStudent (λ _ _ => True) true
    rw [whichK_const_true (S := oneStudent) ⟨w', rfl⟩,
      whichK_const_true (S := oneStudent) ⟨true, rfl⟩]
  · intro h
    have := h false trivial true
    simp [oneStudent] at this

/-- In the world `true` both Bill and Sue are students, in `false` only Bill is. -/
def student : Bool → Bool → Prop := λ w y => y = true ∨ w = true

/-- `x` lives with `x`'s actual spouse: Bill's spouse is Sue and Sue's is Bill, and they live
    together in every world, so both propositions are the whole set of worlds. -/
def livesWithSpouse : Bool → Bool → Prop := λ _ _ => True

/-- (24)–(26): the generalized analysis makes the report true although John believes Sue not
    to be a student, because Bill's and Sue's propositions coincide; Groenendijk and Stokhof
    make it false. -/
theorem spouse_divergence :
    generalizedKnow agnostic () true (whichK student livesWithSpouse) ∧
      ¬ gsKnow agnostic () true (whichGS student livesWithSpouse) := by
  constructor
  · intro w' _
    show whichK student (λ _ _ => True) w' = whichK student (λ _ _ => True) true
    rw [whichK_const_true (S := student) ⟨true, Or.inl rfl⟩,
      whichK_const_true (S := student) ⟨true, Or.inl rfl⟩]
  · intro h
    have := h false trivial false
    simp [student, livesWithSpouse] at this

/-! ### Structured propositions (§8) -/

/-- (28): with structured answers, the pairs of a student who called and the property of
    calling, the generalized analysis is Groenendijk and Stokhof's (11) for any predicate. -/
theorem structured_eq_gs (S C : W → E → Prop) :
    {w' | {y | S w' y ∧ C w' y} = {y | S w y ∧ C w y}} = whichGS S C w := by
  ext w'
  simp only [Set.mem_ofPred_eq, whichGS, Set.ext_iff]

/-! ### The two answers (§6) -/

/-- (16): the answer in the second sense, the proposition that the answer in the first sense
    is what it is; the first sense is the substrate's `weakAnswer`. -/
def ans₂ (H : Set (Set W)) (w : W) : Set W := {w' | weakAnswer H w' = weakAnswer H w}

/-- Groenendijk and Stokhof's answer, deciding every alternative as `w` does, has the same
    answer in the first sense. -/
theorem strongAnswer_subset_ans₂ (H : Set (Set W)) (w : W) : strongAnswer H w ⊆ ans₂ H w := by
  intro v hv
  show weakAnswer H v = weakAnswer H w
  ext u
  simp only [mem_weakAnswer]
  exact ⟨λ h p hp hwp => h p hp ((hv p hp).1 hwp), λ h p hp hvp => h p hp ((hv p hp).2 hvp)⟩

end Heim1994
