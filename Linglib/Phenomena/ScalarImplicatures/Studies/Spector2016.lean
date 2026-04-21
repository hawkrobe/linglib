import Linglib.Theories.Semantics.Exhaustification.Operators.Basic

/-!
# Spector (2016): Worked examples of exhaustivity operators

@cite{spector-2016} "Comparing Exhaustivity Operators." *Semantics and
Pragmatics* 9(11): 1–33.

Concrete derivations of `exhMW`, `exhIE`, and their coincidence (Theorem 9)
on the two classic Horn scales:

1. **some/all** scale: "Some students passed" → "Not all students passed"
2. **or/and** scale: "John sang or danced" → exclusive reading

The abstract Spector framework lives in
`Theories/Semantics/Exhaustification/Operators/Basic.lean`. This file holds the
empirical exemplars — small finite worlds, scale-specific alternative
sets, and the per-scale `exhMW ≡ exhIE` corollaries — kept out of the
theory file in line with the project's Theory/Phenomena split.

It also collects the @cite{chierchia-2013} Maximize Strength worked
examples (matrix-clause SI computed, DE-context SI suppressed) as a small
table of `MaximizeStrengthExample` records.

## Results

- `exhMW_some_at_w1`, `exhMW_some_not_w3` — exhMW(some) excludes "all"
- `exhMW_or_at_wSang`, `exhMW_or_not_wBoth` — exhMW(or) excludes "both"
- `someAll_exhMW_iff_exhIE`, `orAnd_exhMW_iff_exhIE` — Theorem 9 instances
- `maximizeStrengthExamples` — Maximize Strength contexts table
-/

namespace Phenomena.ScalarImplicatures.Studies.Spector2016

open Exhaustification
open Semantics.Entailment.Polarity (ContextPolarity)

-- ----------------------------------------------------------------------------
-- 1: SOME/ALL SCALE
-- ----------------------------------------------------------------------------

/-!
### "Some students passed"

- φ = "some students passed" (literal meaning: at least one)
- ALT = {some, all}
- Expected: exhMW(some) = "some but not all"

World model: `Fin 4` represents how many students passed (0–3 of 3).
-/

/-- Worlds for some/all example: number of students who passed (0 to 3). -/
abbrev SomeAllWorld := Fin 4

/-- "Some students passed" (at least one). -/
def someStudents : Set SomeAllWorld := λ w => w.val ≥ 1

/-- "All students passed" (all three). -/
def allStudents : Set SomeAllWorld := λ w => w.val = 3

/-- Alternative set: {some, all}. -/
def someAllALT : Set (Set SomeAllWorld) := {someStudents, allStudents}

/-- World where exactly 1 student passed. -/
def w1 : SomeAllWorld := ⟨1, by omega⟩

/-- World where all 3 students passed. -/
def w3 : SomeAllWorld := ⟨3, by omega⟩

theorem w1_satisfies_some : someStudents w1 := by
  simp only [someStudents, w1]
  decide

theorem w1_not_all : ¬(allStudents w1) := by
  simp only [allStudents, w1]
  decide

theorem w3_satisfies_both : someStudents w3 ∧ allStudents w3 := by
  simp only [someStudents, allStudents, w3]
  constructor <;> decide

theorem w1_leALT_w3 : w1 ≤[someAllALT] w3 := by
  intro a ha hau
  simp only [someAllALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · simp only [someStudents]
    decide
  · simp only [allStudents, w1] at hau
    exact absurd hau (by decide)

theorem w3_not_leALT_w1 : ¬(w3 ≤[someAllALT] w1) := by
  intro h
  have hall_w1 := h allStudents (Or.inr rfl) (by simp only [allStudents, w3])
  simp only [allStudents, w1] at hall_w1
  exact absurd hall_w1 (by decide)

theorem w1_ltALT_w3 : w1 <[someAllALT] w3 :=
  ⟨w1_leALT_w3, w3_not_leALT_w1⟩

theorem w1_minimal_some : IsMinimal someAllALT someStudents w1 := by
  constructor
  · exact w1_satisfies_some
  · intro ⟨v, hv_some, hv_lt_w1⟩
    obtain ⟨_, hw1_not_le⟩ := hv_lt_w1
    apply hw1_not_le
    intro a ha haw1
    simp only [someAllALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hv_some
    · simp only [allStudents, w1] at haw1
      exact absurd haw1 (by decide)

theorem w3_not_minimal_some : ¬IsMinimal someAllALT someStudents w3 := by
  intro ⟨_, hmin⟩
  apply hmin
  exact ⟨w1, w1_satisfies_some, w1_ltALT_w3⟩

/-- exhMW(some) holds at w=1 — the scalar implicature "some but not all". -/
theorem exhMW_some_at_w1 : exhMW someAllALT someStudents w1 :=
  w1_minimal_some

/-- exhMW(some) excludes the "all" world. -/
theorem exhMW_some_not_w3 : ¬exhMW someAllALT someStudents w3 := by
  intro ⟨_, hmin⟩
  apply hmin
  exact ⟨w1, w1_satisfies_some, w1_ltALT_w3⟩

-- ----------------------------------------------------------------------------
-- 2: OR/AND SCALE (EXCLUSIVE DISJUNCTION)
-- ----------------------------------------------------------------------------

/-!
### "John sang or danced"

- World = four possibilities: neither, only sang, only danced, both
- φ = "sang or danced" (inclusive)
- ALT = {or, and}
- Expected: exhMW(or) = "or but not both" (exclusive reading)
-/

/-- Four worlds for or/and example. -/
inductive OrAndWorld where
  | neither
  | onlySang
  | onlyDanced
  | both
  deriving DecidableEq, Repr

def sang : Set OrAndWorld
  | .neither => False
  | .onlySang => True
  | .onlyDanced => False
  | .both => True

def danced : Set OrAndWorld
  | .neither => False
  | .onlySang => False
  | .onlyDanced => True
  | .both => True

def sangOrDanced : Set OrAndWorld := λ w => sang w ∨ danced w

def sangAndDanced : Set OrAndWorld := λ w => sang w ∧ danced w

def orAndALT : Set (Set OrAndWorld) := {sangOrDanced, sangAndDanced}

def wSang : OrAndWorld := .onlySang

def wBoth : OrAndWorld := .both

theorem wSang_satisfies_or : sangOrDanced wSang := by
  simp only [sangOrDanced, sang, danced, wSang]
  left; trivial

theorem wSang_not_and : ¬(sangAndDanced wSang) := by
  simp only [sangAndDanced, sang, danced, wSang]
  intro ⟨_, h⟩; exact h

theorem wBoth_satisfies_both : sangOrDanced wBoth ∧ sangAndDanced wBoth := by
  simp only [sangOrDanced, sangAndDanced, sang, danced, wBoth]
  exact ⟨Or.inl trivial, ⟨trivial, trivial⟩⟩

theorem wSang_leALT_wBoth : wSang ≤[orAndALT] wBoth := by
  intro a ha hau
  simp only [orAndALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact wBoth_satisfies_both.1
  · exact absurd hau wSang_not_and

theorem wBoth_not_leALT_wSang : ¬(wBoth ≤[orAndALT] wSang) := by
  intro h
  have := h sangAndDanced (Or.inr rfl) wBoth_satisfies_both.2
  exact wSang_not_and this

theorem wSang_ltALT_wBoth : wSang <[orAndALT] wBoth :=
  ⟨wSang_leALT_wBoth, wBoth_not_leALT_wSang⟩

theorem wSang_minimal : IsMinimal orAndALT sangOrDanced wSang := by
  constructor
  · exact wSang_satisfies_or
  · intro ⟨v, hv_or, hv_lt⟩
    obtain ⟨_, hwSang_not_le⟩ := hv_lt
    apply hwSang_not_le
    intro a ha ha_wSang
    simp only [orAndALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hv_or
    · exact absurd ha_wSang wSang_not_and

/-- exhMW(or) at wSang: exclusive reading. -/
theorem exhMW_or_at_wSang : exhMW orAndALT sangOrDanced wSang :=
  wSang_minimal

/-- exhMW(or) excludes the "both" world. -/
theorem exhMW_or_not_wBoth : ¬exhMW orAndALT sangOrDanced wBoth := by
  intro ⟨_, hmin⟩
  apply hmin
  exact ⟨wSang, wSang_satisfies_or, wSang_ltALT_wBoth⟩

-- ----------------------------------------------------------------------------
-- 3: APPLYING THEOREM 9 (exhMW ≡ exhIE) ON HORN SCALES
-- ----------------------------------------------------------------------------

/-!
For a two-element Horn scale {weak, strong} where strong ⊆ weak,
exhMW ≡ exhIE without invoking the full closure-under-conjunction
hypothesis: at any exhIE world, the stronger alternative is false,
which makes the world minimal.
-/

theorem allStudents_entails_someStudents : allStudents ⊆ someStudents := by
  intro w h
  show w.val ≥ 1
  change w.val = 3 at h
  omega

/-- Per-scale Theorem 9 instance: some/all. -/
theorem someAll_exhMW_iff_exhIE :
    exhMW someAllALT someStudents = exhIE someAllALT someStudents := by
  apply Set.Subset.antisymm
  · exact exhMW_entails_exhIE someAllALT someStudents
  · intro w hie
    constructor
    · have hsome_in_IE : someStudents ∈ IE someAllALT someStudents := by
        intro E hE_mc
        exact hE_mc.1.1
      exact hie someStudents hsome_in_IE
    · intro ⟨v, hv_some, hv_lt_w⟩
      obtain ⟨_, hw_not_le_v⟩ := hv_lt_w
      simp only [leALT] at hw_not_le_v
      push Not at hw_not_le_v
      obtain ⟨a, ha_ALT, ha_w, hna_v⟩ := hw_not_le_v
      simp only [someAllALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha_ALT
      rcases ha_ALT with rfl | rfl
      · exact hna_v hv_some
      · have hneg_all_in_IE : (allStudentsᶜ) ∈ IE someAllALT someStudents := by
          intro E hE_mc
          by_contra h_not_in
          let E' := E ∪ {allStudentsᶜ}
          have hcompat : IsCompatible someAllALT someStudents E' := by
            obtain ⟨⟨hphi, hform, hcons⟩, _⟩ := hE_mc
            refine ⟨Or.inl hphi, ?_, ?_⟩
            · intro ψ hψ
              rcases hψ with hψ_E | hψ_new
              · exact hform ψ hψ_E
              · simp only [Set.mem_singleton_iff] at hψ_new
                exact Or.inr ⟨allStudents, Or.inr rfl, hψ_new⟩
            · use w1
              intro ψ hψ
              rcases hψ with hψ_E | hψ_new
              · rcases hform ψ hψ_E with rfl | ⟨a, ha, rfl⟩
                · exact w1_satisfies_some
                · simp only [someAllALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
                  rcases ha with rfl | rfl
                  · exfalso
                    obtain ⟨u, hu⟩ := hcons
                    exact hu (someStudentsᶜ) hψ_E (hu someStudents hphi)
                  · exact w1_not_all
              · simp only [Set.mem_singleton_iff] at hψ_new
                rw [hψ_new]
                exact w1_not_all
          have hsubset : E ⊆ E' := Set.subset_union_left
          have hE'_not_sub_E : ¬(E' ⊆ E) := by
            intro hle
            apply h_not_in
            exact hle (Set.mem_union_right E (Set.mem_singleton _))
          exact hE'_not_sub_E (hE_mc.2 E' hcompat hsubset)
        have hna_w : ¬(allStudents w) := hie (allStudentsᶜ) hneg_all_in_IE
        exact hna_w ha_w

theorem sangAndDanced_entails_sangOrDanced : sangAndDanced ⊆ sangOrDanced := by
  intro w h
  change sang w ∧ danced w at h
  exact Or.inl h.1

/-- Per-scale Theorem 9 instance: or/and. -/
theorem orAnd_exhMW_iff_exhIE :
    exhMW orAndALT sangOrDanced = exhIE orAndALT sangOrDanced := by
  apply Set.Subset.antisymm
  · exact exhMW_entails_exhIE orAndALT sangOrDanced
  · intro w hie
    constructor
    · have hor_in_IE : sangOrDanced ∈ IE orAndALT sangOrDanced := λ E hE => hE.1.1
      exact hie sangOrDanced hor_in_IE
    · intro ⟨v, hv_or, hv_lt_w⟩
      obtain ⟨_, hw_not_le_v⟩ := hv_lt_w
      simp only [leALT] at hw_not_le_v
      push Not at hw_not_le_v
      obtain ⟨a, ha_ALT, ha_w, hna_v⟩ := hw_not_le_v
      simp only [orAndALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha_ALT
      rcases ha_ALT with rfl | rfl
      · exact hna_v hv_or
      · have hneg_and_in_IE : (sangAndDancedᶜ) ∈ IE orAndALT sangOrDanced := by
          intro E hE_mc
          by_contra h_not_in
          let E' := E ∪ {sangAndDancedᶜ}
          have hcompat : IsCompatible orAndALT sangOrDanced E' := by
            obtain ⟨⟨hphi, hform, hcons⟩, _⟩ := hE_mc
            refine ⟨Or.inl hphi, ?_, ?_⟩
            · intro ψ hψ
              rcases hψ with hψ_E | hψ_new
              · exact hform ψ hψ_E
              · simp only [Set.mem_singleton_iff] at hψ_new
                exact Or.inr ⟨sangAndDanced, Or.inr rfl, hψ_new⟩
            · use wSang
              intro ψ hψ
              rcases hψ with hψ_E | hψ_new
              · rcases hform ψ hψ_E with rfl | ⟨a, ha, rfl⟩
                · exact wSang_satisfies_or
                · simp only [orAndALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
                  rcases ha with rfl | rfl
                  · exfalso
                    obtain ⟨u, hu⟩ := hcons
                    exact hu (sangOrDancedᶜ) hψ_E (hu sangOrDanced hphi)
                  · exact wSang_not_and
              · simp only [Set.mem_singleton_iff] at hψ_new
                rw [hψ_new]
                exact wSang_not_and
          have hsubset : E ⊆ E' := Set.subset_union_left
          have hE'_not_sub_E : ¬(E' ⊆ E) := by
            intro hle
            apply h_not_in
            exact hle (Set.mem_union_right E (Set.mem_singleton _))
          exact hE'_not_sub_E (hE_mc.2 E' hcompat hsubset)
        have hna_w : ¬(sangAndDanced w) := hie (sangAndDancedᶜ) hneg_and_in_IE
        exact hna_w ha_w

theorem exhIE_some_at_w1 : exhIE someAllALT someStudents w1 :=
  someAll_exhMW_iff_exhIE.subset exhMW_some_at_w1

theorem exhIE_some_not_w3 : ¬exhIE someAllALT someStudents w3 := by
  intro h
  exact exhMW_some_not_w3 (someAll_exhMW_iff_exhIE.symm.subset h)

theorem exhIE_or_at_wSang : exhIE orAndALT sangOrDanced wSang :=
  orAnd_exhMW_iff_exhIE.subset exhMW_or_at_wSang

theorem exhIE_or_not_wBoth : ¬exhIE orAndALT sangOrDanced wBoth := by
  intro h
  exact exhMW_or_not_wBoth (orAnd_exhMW_iff_exhIE.symm.subset h)

-- ----------------------------------------------------------------------------
-- 4: MAXIMIZE STRENGTH EXAMPLES (@cite{chierchia-2013})
-- ----------------------------------------------------------------------------

/-!
A small descriptive table of contexts illustrating @cite{chierchia-2013}'s
Maximize Strength predictions. The principle itself (`maximizeStrength`,
`exh_in_ue_strengthens`, etc.) lives in `Operators.lean`.

| Context | Polarity | SI computed? |
|---------|----------|--------------|
| Matrix clause | UE | yes |
| Negation scope | DE | no |
| Conditional antecedent | DE | no |
| Universal restrictor | DE | no |
-/

structure MaximizeStrengthExample where
  description : String
  contextType : ContextPolarity
  siComputed : Bool
  explanation : String
  deriving Repr

def ms_matrix_clause : MaximizeStrengthExample :=
  { description := "John saw some students"
  , contextType := .upward
  , siComputed := true
  , explanation := "UE context: SI strengthens assertion" }

def ms_negation : MaximizeStrengthExample :=
  { description := "John didn't see some students"
  , contextType := .downward
  , siComputed := false
  , explanation := "DE context: SI would weaken to 'saw none or not all'" }

def ms_antecedent : MaximizeStrengthExample :=
  { description := "If John saw some students, he's happy"
  , contextType := .downward
  , siComputed := false
  , explanation := "Conditional antecedent is DE: SI would weaken" }

def ms_universal_restrictor : MaximizeStrengthExample :=
  { description := "Everyone who saw some students is happy"
  , contextType := .downward
  , siComputed := false
  , explanation := "Universal restrictor is DE: SI would weaken" }

def maximizeStrengthExamples : List MaximizeStrengthExample :=
  [ms_matrix_clause, ms_negation, ms_antecedent, ms_universal_restrictor]

end Phenomena.ScalarImplicatures.Studies.Spector2016
