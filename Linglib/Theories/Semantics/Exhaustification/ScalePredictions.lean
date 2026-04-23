import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
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
  disjunctA : Set World
  /-- Second disjunct meaning -/
  disjunctB : Set World
  /-- The entailment that creates the violation -/
  entailment : (disjunctA ⊆ disjunctB) ∨ (disjunctB ⊆ disjunctA)
  /-- Alternative set for exhaustification -/
  alts : Set (Set World)

/--
A Hurford violation is rescued iff after exhaustifying the weaker disjunct,
the entailment no longer holds.
-/
def HurfordSemantic.isRescued {World : Type*} (h : HurfordSemantic World) : Prop :=
  (¬(exhIE h.alts h.disjunctA ⊆ h.disjunctB)) ∨ (¬(exhIE h.alts h.disjunctB ⊆ h.disjunctA))

/--
For cases where B⊆A (stronger entails weaker), rescue requires exh(B) ⊄ A.
-/
def HurfordSemantic.isRescuedFromBA {World : Type*} (h : HurfordSemantic World) : Prop :=
  ¬(exhIE h.alts h.disjunctB ⊆ h.disjunctA)


-- ============================================================
-- Singh's Asymmetry
-- ============================================================

/--
Semantic structure for Singh configurations.
-/
structure SinghSemantic (World : Type*) where
  /-- Weaker disjunct meaning -/
  weaker : Set World
  /-- Stronger disjunct meaning -/
  stronger : Set World
  /-- Stronger entails weaker -/
  entailment : stronger ⊆ weaker
  /-- Alternative set -/
  alts : Set (Set World)
  /-- Is weaker mentioned first? -/
  weakerFirst : Bool

/--
Fox & Spector's prediction: weak-first is felicitous because exh(weak)
can break the entailment to strong.
-/
def SinghSemantic.exhBreaksEntailment {World : Type*} (s : SinghSemantic World) : Prop :=
  ¬(exhIE s.alts s.weaker ⊆ s.stronger)

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
  have hie : IsInnocentlyExcludable someAllScale.alts someQ allQ := by
    apply IsInnocentlyExcludable.of_extension_consistent
    · show allQ ∈ ({someQ, allQ} : Set _)
      exact Set.mem_insert_of_mem _ rfl
    · intro E hE_mc
      refine ⟨⟨1, by omega⟩, fun ψ hψ => ?_⟩
      rcases hψ with hψ_E | hψ_new
      · rcases hE_mc.1.2.1 ψ hψ_E with rfl | ⟨a, ha, rfl⟩
        · simp [someQ]
        · simp [someAllScale, SemanticScale.alts] at ha
          rcases ha with rfl | rfl
          · exfalso
            obtain ⟨v, hv_phi, hv⟩ := hE_mc.1.exists_phi_witness
            exact hv (someQᶜ) hψ_E hv_phi
          · intro h; have : (1 : Nat) = 3 := h; omega
      · simp only [Set.mem_singleton_iff] at hψ_new
        rw [hψ_new]
        intro h; have : (1 : Nat) = 3 := h; omega
  exact hexh _ hie.2 hall

/--
Prediction: exh(or) → ¬and.
-/
theorem orAnd_implicature :
    ∀ w : ConnWorld, exhIE orAndScale.alts orConn w → ¬andConn w := by
  intro w hexh hand
  have hie : IsInnocentlyExcludable orAndScale.alts orConn andConn := by
    apply IsInnocentlyExcludable.of_extension_consistent
    · show andConn ∈ ({orConn, andConn} : Set _)
      exact Set.mem_insert_of_mem _ rfl
    · intro E hE_mc
      refine ⟨ConnWorld.onlyA, fun ψ hψ => ?_⟩
      rcases hψ with hψ_E | hψ_new
      · rcases hE_mc.1.2.1 ψ hψ_E with rfl | ⟨a, ha, rfl⟩
        · simp [orConn]
        · simp [orAndScale, SemanticScale.alts] at ha
          rcases ha with rfl | rfl
          · exfalso
            obtain ⟨v, hv_phi, hv⟩ := hE_mc.1.exists_phi_witness
            exact hv (orConnᶜ) hψ_E hv_phi
          · intro h; exact h
      · simp only [Set.mem_singleton_iff] at hψ_new
        rw [hψ_new]
        intro h; exact h
  exact hexh _ hie.2 hand

/--
Prediction: exh(possible) → ¬necessary.
-/
theorem possibleNecessary_implicature :
    ∀ w : ModalWorld, exhIE possibleNecessaryScale.alts possibleP w → ¬necessaryP w := by
  intro w hexh hnec
  have hie : IsInnocentlyExcludable possibleNecessaryScale.alts possibleP necessaryP := by
    apply IsInnocentlyExcludable.of_extension_consistent
    · show necessaryP ∈ ({possibleP, necessaryP} : Set _)
      exact Set.mem_insert_of_mem _ rfl
    · intro E hE_mc
      refine ⟨ModalWorld.some, fun ψ hψ => ?_⟩
      rcases hψ with hψ_E | hψ_new
      · rcases hE_mc.1.2.1 ψ hψ_E with rfl | ⟨a, ha, rfl⟩
        · simp [possibleP]
        · simp [possibleNecessaryScale, SemanticScale.alts] at ha
          rcases ha with rfl | rfl
          · exfalso
            obtain ⟨v, hv_phi, hv⟩ := hE_mc.1.exists_phi_witness
            exact hv (possiblePᶜ) hψ_E hv_phi
          · intro h; exact h
      · simp only [Set.mem_singleton_iff] at hψ_new
        rw [hψ_new]
        intro h; exact h
  exact hexh _ hie.2 hnec

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
    have hMC : IsMCSet someOrAll_semantic.alts someQ {someQ, allQᶜ} := by
      constructor
      · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
        · intro ψ' hψ'
          rcases hψ' with rfl | rfl
          · left; rfl
          · right; exact ⟨allQ, Or.inr (Set.mem_singleton _), rfl⟩
        · use ⟨1, by omega⟩
          intro ψ' hψ'
          rcases hψ' with rfl | rfl
          · simp [someQ]
          · intro h; have : (1 : Nat) = 3 := h; omega
      · intro E' hE'_compat hsubset ψ' hψ'_E'
        rcases hE'_compat.2.1 ψ' hψ'_E' with rfl | ⟨a, ha, rfl⟩
        · exact Or.inl rfl
        · rcases ha with rfl | rfl
          · exfalso
            obtain ⟨u, hu⟩ := hE'_compat.2.2
            have hsomeQ := hE'_compat.1
            exact hu (someQᶜ) hψ'_E' (hu someQ hsomeQ)
          · exact Or.inr rfl
    have hψ_in_MC : ψ ∈ ({someQ, allQᶜ} : Set (Set SemQuantWorld)) := hψ_IE _ hMC
    rcases hψ_in_MC with rfl | rfl
    · simp [someQ]
    · intro h; have : (1 : Nat) = 3 := h; omega
  have hall_w1 : allQ ⟨1, by omega⟩ := h_entails hw1
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
def americanP : Set HyponymWorld := λ w =>
  match w with
  | .notAmerican => False
  | .americanOnly => True
  | .californian => True

/-- "Californian" predicate -/
def californianP : Set HyponymWorld := λ w =>
  match w with
  | .californian => True
  | _ => False

/-- Californian entails American (hyponymy) -/
theorem californian_entails_american : californianP ⊆ americanP := by
  intro w hcal
  cases w
  · exact hcal.elim
  · exact hcal.elim
  · trivial

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
    exhIE americanCalifornian_semantic.alts californianP ⊆ americanP := by
  intro w hexh
  have hcal : californianP w := by
    apply hexh californianP
    intro E hmc
    exact hmc.1.1
  exact californian_entails_american hcal

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
    ¬(exhIE {orConn, andConn} orConn ⊆ andConn) := by
  intro h
  have hexh : exhIE {orConn, andConn} orConn ConnWorld.onlyA := by
    intro ψ hψ_IE
    have hMC : IsMCSet {orConn, andConn} orConn {orConn, andConnᶜ} := by
      constructor
      · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
        · intro ψ' hψ'
          rcases hψ' with rfl | rfl
          · left; rfl
          · right; exact ⟨andConn, Or.inr (Set.mem_singleton _), rfl⟩
        · use ConnWorld.onlyA
          intro ψ' hψ'
          rcases hψ' with rfl | rfl
          · simp [orConn]
          · intro h; exact h
      · intro E' hE'_compat hsubset ψ' hψ'_E'
        rcases hE'_compat.2.1 ψ' hψ'_E' with rfl | ⟨a, ha, rfl⟩
        · exact Or.inl rfl
        · rcases ha with rfl | rfl
          · exfalso
            obtain ⟨v, hv_phi, hv⟩ := hE'_compat.exists_phi_witness
            exact hv (orConnᶜ) hψ'_E' hv_phi
          · exact Or.inr rfl
    have hψ_in : ψ ∈ ({orConn, andConnᶜ} : Set (Set ConnWorld)) := hψ_IE _ hMC
    rcases hψ_in with rfl | rfl
    · simp [orConn]
    · intro h; exact h
  have hand : andConn ConnWorld.onlyA := h hexh
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
