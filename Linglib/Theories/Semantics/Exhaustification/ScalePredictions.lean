import Linglib.Theories.Semantics.Exhaustification.Operators
import Linglib.Theories.Semantics.Alternatives.Lexical

/-!
# Exhaustification Predictions for Semantic Scales
@cite{spector-2016} @cite{fox-2007} @cite{hurford-1974} @cite{singh-2008}

Exhaustification predictions for the semantic scales defined in
`Alternatives.Lexical`: proves that `exhIE(weaker) → ¬stronger` for
each Horn scale, and derives Hurford rescue and Singh asymmetry predictions.

- **HurfordSemantic**: Disjunction rescue via exhaustification
- **SinghSemantic**: Asymmetry in disjunction order
-/

namespace Exhaustification

open Alternatives (SemanticScale SemQuantWorld ConnWorld ModalWorld
  someQ allQ all_entails_some some_not_entails_all someAllScale
  orConn andConn and_entails_or or_not_entails_and orAndScale
  possibleP necessaryP necessary_entails_possible possible_not_entails_necessary
  possibleNecessaryScale)

-- ============================================================
-- Hurford's Constraint
-- ============================================================

/--
Semantic structure for a Hurford configuration.
Allows proving when exhaustification rescues the violation.
-/
structure HurfordSemantic (World : Type*) where
  /-- First disjunct meaning -/
  disjunctA : Prop' World
  /-- Second disjunct meaning -/
  disjunctB : Prop' World
  /-- The entailment that creates the violation -/
  entailment : (disjunctA ⊆ₚ disjunctB) ∨ (disjunctB ⊆ₚ disjunctA)
  /-- Alternative set for exhaustification -/
  alts : Set (Prop' World)

/--
A Hurford violation is rescued iff after exhaustifying the weaker disjunct,
the entailment no longer holds.
-/
def HurfordSemantic.isRescued {World : Type*} (h : HurfordSemantic World) : Prop :=
  (¬(exhIE h.alts h.disjunctA ⊆ₚ h.disjunctB)) ∨ (¬(exhIE h.alts h.disjunctB ⊆ₚ h.disjunctA))

/--
For cases where B⊆A (stronger entails weaker), rescue requires exh(B) ⊄ A.
-/
def HurfordSemantic.isRescuedFromBA {World : Type*} (h : HurfordSemantic World) : Prop :=
  ¬(exhIE h.alts h.disjunctB ⊆ₚ h.disjunctA)


-- ============================================================
-- Singh's Asymmetry
-- ============================================================

/--
Semantic structure for Singh configurations.
-/
structure SinghSemantic (World : Type*) where
  /-- Weaker disjunct meaning -/
  weaker : Prop' World
  /-- Stronger disjunct meaning -/
  stronger : Prop' World
  /-- Stronger entails weaker -/
  entailment : stronger ⊆ₚ weaker
  /-- Alternative set -/
  alts : Set (Prop' World)
  /-- Is weaker mentioned first? -/
  weakerFirst : Bool

/--
Fox & Spector's prediction: weak-first is felicitous because exh(weak)
can break the entailment to strong.
-/
def SinghSemantic.exhBreaksEntailment {World : Type*} (s : SinghSemantic World) : Prop :=
  ¬(exhIE s.alts s.weaker ⊆ₚ s.stronger)

/--
The asymmetry: felicitous iff (weak-first AND exh breaks entailment).
Strong-first can't be rescued because exh(strong) is vacuous.
-/
def SinghSemantic.predictedFelicitous {World : Type*} (s : SinghSemantic World) : Prop :=
  s.weakerFirst ∧ s.exhBreaksEntailment


-- ============================================================
-- Scale Predictions: exh(weaker) → ¬stronger
-- ============================================================

/--
Prediction: exh(some) → ¬all.
-/
theorem someAll_implicature :
    ∀ w : SemQuantWorld, exhIE someAllScale.alts someQ w → ¬allQ w := by
  intro w hexh hall
  have hie_neg_all : (∼allQ) ∈ IE someAllScale.alts someQ := by
    intro E hE_mc
    by_contra h_not_in
    let E' := E ∪ {∼allQ}
    have hcompat : isCompatible someAllScale.alts someQ E' := by
      obtain ⟨⟨hphi, hform, hcons⟩, _⟩ := hE_mc
      refine ⟨Set.mem_union_left _ hphi, ?_, ?_⟩
      · intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · exact hform ψ hψ_E
        · simp only [Set.mem_singleton_iff] at hψ_new
          right
          refine ⟨allQ, ?_, hψ_new⟩
          simp [someAllScale, SemanticScale.alts]
      · use ⟨1, by omega⟩
        intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · rcases hform ψ hψ_E with rfl | ⟨a, ha, rfl⟩
          · simp [someQ]
          · simp [someAllScale, SemanticScale.alts] at ha
            rcases ha with rfl | rfl
            · exfalso
              obtain ⟨u, hu⟩ := hcons
              exact hu (∼someQ) hψ_E (hu someQ hphi)
            · simp only [pneg, allQ]; omega
        · simp only [Set.mem_singleton_iff] at hψ_new
          rw [hψ_new]
          simp only [pneg, allQ]; omega
    have hsubset : E ⊆ E' := Set.subset_union_left
    have hE'_not_sub_E : ¬(E' ⊆ E) := by
      intro hle
      apply h_not_in
      exact hle (Set.mem_union_right E (Set.mem_singleton _))
    exact hE'_not_sub_E (hE_mc.2 E' hcompat hsubset)
  have hneg_all_w : (∼allQ) w := hexh (∼allQ) hie_neg_all
  simp only [pneg] at hneg_all_w
  exact hneg_all_w hall

/--
Prediction: exh(or) → ¬and.
-/
theorem orAnd_implicature :
    ∀ w : ConnWorld, exhIE orAndScale.alts orConn w → ¬andConn w := by
  intro w hexh hand
  have hie_neg_and : (∼andConn) ∈ IE orAndScale.alts orConn := by
    intro E hE_mc
    by_contra h_not_in
    let E' := E ∪ {∼andConn}
    have hcompat : isCompatible orAndScale.alts orConn E' := by
      obtain ⟨⟨hphi, hform, hcons⟩, _⟩ := hE_mc
      refine ⟨Set.mem_union_left _ hphi, ?_, ?_⟩
      · intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · exact hform ψ hψ_E
        · simp only [Set.mem_singleton_iff] at hψ_new
          right
          refine ⟨andConn, ?_, hψ_new⟩
          simp [orAndScale, SemanticScale.alts]
      · use ConnWorld.onlyA
        intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · rcases hform ψ hψ_E with rfl | ⟨a, ha, rfl⟩
          · simp [orConn]
          · simp [orAndScale, SemanticScale.alts] at ha
            rcases ha with rfl | rfl
            · exfalso
              obtain ⟨u, hu⟩ := hcons
              exact hu (∼orConn) hψ_E (hu orConn hphi)
            · simp only [pneg, andConn]; tauto
        · simp only [Set.mem_singleton_iff] at hψ_new
          rw [hψ_new]
          simp only [pneg, andConn]; tauto
    have hsubset : E ⊆ E' := Set.subset_union_left
    have hE'_not_sub_E : ¬(E' ⊆ E) := by
      intro hle
      apply h_not_in
      exact hle (Set.mem_union_right E (Set.mem_singleton _))
    exact hE'_not_sub_E (hE_mc.2 E' hcompat hsubset)
  have hneg_and_w : (∼andConn) w := hexh (∼andConn) hie_neg_and
  simp only [pneg] at hneg_and_w
  exact hneg_and_w hand

/--
Prediction: exh(possible) → ¬necessary.
-/
theorem possibleNecessary_implicature :
    ∀ w : ModalWorld, exhIE possibleNecessaryScale.alts possibleP w → ¬necessaryP w := by
  intro w hexh hnec
  have hie_neg_nec : (∼necessaryP) ∈ IE possibleNecessaryScale.alts possibleP := by
    intro E hE_mc
    by_contra h_not_in
    let E' := E ∪ {∼necessaryP}
    have hcompat : isCompatible possibleNecessaryScale.alts possibleP E' := by
      obtain ⟨⟨hphi, hform, hcons⟩, _⟩ := hE_mc
      refine ⟨Set.mem_union_left _ hphi, ?_, ?_⟩
      · intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · exact hform ψ hψ_E
        · simp only [Set.mem_singleton_iff] at hψ_new
          right
          refine ⟨necessaryP, ?_, hψ_new⟩
          simp [possibleNecessaryScale, SemanticScale.alts]
      · use ModalWorld.some
        intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · rcases hform ψ hψ_E with rfl | ⟨a, ha, rfl⟩
          · simp [possibleP]
          · simp [possibleNecessaryScale, SemanticScale.alts] at ha
            rcases ha with rfl | rfl
            · exfalso
              obtain ⟨u, hu⟩ := hcons
              exact hu (∼possibleP) hψ_E (hu possibleP hphi)
            · simp only [pneg, necessaryP]; tauto
        · simp only [Set.mem_singleton_iff] at hψ_new
          rw [hψ_new]
          simp only [pneg, necessaryP]; tauto
    have hsubset : E ⊆ E' := Set.subset_union_left
    have hE'_not_sub_E : ¬(E' ⊆ E) := by
      intro hle
      apply h_not_in
      exact hle (Set.mem_union_right E (Set.mem_singleton _))
    exact hE'_not_sub_E (hE_mc.2 E' hcompat hsubset)
  have hneg_nec_w : (∼necessaryP) w := hexh (∼necessaryP) hie_neg_nec
  simp only [pneg] at hneg_nec_w
  exact hneg_nec_w hnec

/--
Main Result: Theory correctly predicts all three Horn scale implicatures.

For each scale, exh(weaker) → ¬stronger.
-/
theorem all_scale_implicatures_derived :
    (∀ w, exhIE someAllScale.alts someQ w → ¬allQ w) ∧
    (∀ w, exhIE orAndScale.alts orConn w → ¬andConn w) ∧
    (∀ w, exhIE possibleNecessaryScale.alts possibleP w → ¬necessaryP w) :=
  ⟨someAll_implicature, orAnd_implicature, possibleNecessary_implicature⟩


-- ============================================================
-- Hurford Predictions
-- ============================================================

/--
Semantic structure for "some or all" (rescued Hurford case).
-/
def someOrAll_semantic : HurfordSemantic SemQuantWorld :=
  { disjunctA := someQ
  , disjunctB := allQ
  , entailment := Or.inr all_entails_some
  , alts := {someQ, allQ}
  }

/--
Prediction: "some or all" is rescued because exh(some) doesn't entail all.
-/
theorem someOrAll_is_rescued : someOrAll_semantic.isRescued := by
  left
  intro h_entails
  have hw1 : exhIE someOrAll_semantic.alts someQ ⟨1, by omega⟩ := by
    intro ψ hψ_IE
    have hMC : isMCSet someOrAll_semantic.alts someQ {someQ, ∼allQ} := by
      constructor
      · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
        · intro ψ' hψ'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ'
          rcases hψ' with rfl | rfl
          · left; rfl
          · right; exact ⟨allQ, Or.inr (Set.mem_singleton _), rfl⟩
        · use ⟨1, by omega⟩
          intro ψ' hψ'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ'
          rcases hψ' with rfl | rfl
          · simp [someQ]
          · simp only [pneg, allQ]; omega
      · intro E' hE'_compat hsubset ψ' hψ'_E'
        rcases hE'_compat.2.1 ψ' hψ'_E' with rfl | ⟨a, ha, rfl⟩
        · exact Or.inl rfl
        · simp only [someOrAll_semantic, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl
          · exfalso
            obtain ⟨u, hu⟩ := hE'_compat.2.2
            have hsomeQ := hE'_compat.1
            exact hu (∼someQ) hψ'_E' (hu someQ hsomeQ)
          · exact Or.inr rfl
    have hψ_in_MC : ψ ∈ ({someQ, ∼allQ} : Set (Prop' SemQuantWorld)) := hψ_IE _ hMC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ_in_MC
    rcases hψ_in_MC with rfl | rfl
    · simp [someQ]
    · simp only [pneg, allQ]; omega
  have hall_w1 : allQ ⟨1, by omega⟩ := h_entails ⟨1, by omega⟩ hw1
  simp [allQ] at hall_w1


-- ============================================================
-- Hyponymy: True Hurford Violation (No Rescue)
-- ============================================================

/-- World type for hyponymy: 3 regions of people -/
inductive HyponymWorld where
  | notAmerican   -- Not American (and therefore not Californian)
  | americanOnly  -- American but not Californian
  | californian   -- Californian (and therefore American)
  deriving DecidableEq, Repr

/-- "American" predicate -/
def americanP : Prop' HyponymWorld := λ w =>
  match w with
  | .notAmerican => False
  | .americanOnly => True
  | .californian => True

/-- "Californian" predicate -/
def californianP : Prop' HyponymWorld := λ w =>
  match w with
  | .californian => True
  | _ => False

/-- Californian entails American (hyponymy) -/
theorem californian_entails_american : californianP ⊆ₚ americanP := by
  intro w hcal
  cases w <;> simp [californianP, americanP] at *

/--
Semantic structure for "American or Californian" (true Hurford violation).
-/
def americanCalifornian_semantic : HurfordSemantic HyponymWorld :=
  { disjunctA := americanP
  , disjunctB := californianP
  , entailment := Or.inr californian_entails_american
  , alts := {americanP, californianP}
  }

/--
Key Lemma: With no scalar alternatives, exh is vacuous.
-/
theorem exh_californian_entails_american :
    exhIE americanCalifornian_semantic.alts californianP ⊆ₚ americanP := by
  intro w hexh
  have hcal : californianP w := by
    apply hexh californianP
    intro E hmc
    exact hmc.1.1
  exact californian_entails_american w hcal

/--
Prediction: "American or Californian" is not rescued.
-/
theorem americanCalifornian_not_rescued :
    ¬americanCalifornian_semantic.isRescuedFromBA := by
  simp only [HurfordSemantic.isRescuedFromBA]
  intro hnotBA
  exact hnotBA exh_californian_entails_american


-- ============================================================
-- Singh Predictions
-- ============================================================

/--
Semantic structure for "A or B, or both" (weak-first Singh case).
-/
def orThenBoth_semantic : SinghSemantic ConnWorld :=
  { weaker := orConn
  , stronger := andConn
  , entailment := and_entails_or
  , alts := {orConn, andConn}
  , weakerFirst := true
  }

/--
Semantic structure for "both, or A or B" (strong-first Singh case).
-/
def bothThenOr_semantic : SinghSemantic ConnWorld :=
  { weaker := orConn
  , stronger := andConn
  , entailment := and_entails_or
  , alts := {orConn, andConn}
  , weakerFirst := false
  }

/--
Prediction: exh(or) breaks entailment to and.
-/
theorem orAnd_exh_breaks_entailment :
    ¬(exhIE {orConn, andConn} orConn ⊆ₚ andConn) := by
  intro h
  have hexh : exhIE {orConn, andConn} orConn ConnWorld.onlyA := by
    intro ψ hψ_IE
    have hMC : isMCSet {orConn, andConn} orConn {orConn, ∼andConn} := by
      constructor
      · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
        · intro ψ' hψ'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ'
          rcases hψ' with rfl | rfl
          · left; rfl
          · right; exact ⟨andConn, Or.inr (Set.mem_singleton _), rfl⟩
        · use ConnWorld.onlyA
          intro ψ' hψ'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ'
          rcases hψ' with rfl | rfl
          · simp [orConn]
          · simp only [pneg, andConn]; tauto
      · intro E' hE'_compat hsubset ψ' hψ'_E'
        rcases hE'_compat.2.1 ψ' hψ'_E' with rfl | ⟨a, ha, rfl⟩
        · exact Or.inl rfl
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl
          · exfalso
            obtain ⟨u, hu⟩ := hE'_compat.2.2
            exact hu (∼orConn) hψ'_E' (hu orConn hE'_compat.1)
          · exact Or.inr rfl
    have hψ_in : ψ ∈ ({orConn, ∼andConn} : Set (Prop' ConnWorld)) := hψ_IE _ hMC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ_in
    rcases hψ_in with rfl | rfl
    · simp [orConn]
    · simp only [pneg, andConn]; tauto
  have hand : andConn ConnWorld.onlyA := h ConnWorld.onlyA hexh
  simp [andConn] at hand

/--
Prediction: "A or B, or both" (weak-first) is predicted felicitous.
-/
theorem orThenBoth_predicted_felicitous : orThenBoth_semantic.predictedFelicitous := by
  constructor
  · rfl
  · exact orAnd_exh_breaks_entailment

/--
Prediction: "both, or A or B" (strong-first) is not predicted felicitous.
-/
theorem bothThenOr_not_predicted_felicitous : ¬bothThenOr_semantic.predictedFelicitous := by
  intro ⟨hwf, _⟩
  simp [bothThenOr_semantic] at hwf

/--
Main Result: Theory correctly predicts Singh asymmetry.
-/
theorem singh_asymmetry_derived :
    orThenBoth_semantic.predictedFelicitous ∧
    ¬bothThenOr_semantic.predictedFelicitous :=
  ⟨orThenBoth_predicted_felicitous, bothThenOr_not_predicted_felicitous⟩

end Exhaustification
