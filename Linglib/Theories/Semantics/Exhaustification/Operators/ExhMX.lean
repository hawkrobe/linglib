import Linglib.Theories.Semantics.Exhaustification.Operators.Basic

/-!
# exh_mx: The Third Exhaustification Operator @cite{wang-2025}

@cite{wang-2025} "Presupposition, Competition, and Coherence" introduces
`exh_mx`, which yields one exhaustified proposition per maximal consistent
subset (MC-set), rather than intersecting all MC-sets (as `exh_ie` does).

When all MC-sets agree (i.e., `ALT` is closed under ∧), `exh_mx` = `exh_ie`
= `exh_mw` (by Theorem 9). When MC-sets diverge, `exh_mx` produces *multiple
readings*—one per MC-set—capturing ambiguity in presuppositional
alternatives.

### Key relationships
- `exh_mw` = ⋃₀ {⋂₀ E : E is MC-set} (Lemma 3 above)
- `exh_ie` = ⋂₀ (⋂ all MC-sets) (Definition 4 above)
- `exh_mx` = one reading per MC-set: for each E, ⋂₀ E
-/

namespace Exhaustification

variable {World : Type*} (ALT : Set (Set World)) (φ : Set World)

/-- An `exh_mx` reading for a specific MC-set `E`: the conjunction of `E`.

    Unlike `exh_ie` (which is the conjunction of the *intersection* of all
    MC-sets), `exh_mx` gives one reading per MC-set. When MC-sets disagree
    about which alternatives to exclude, `exh_mx` captures the resulting
    ambiguity.

    @cite{wang-2025} Ch4: `exh_mx(ALT, φ, w) = φ(w) ∧ ∀q ∈ Max(φ, ALT)[¬q(w)]`
    where `Max` is a specific maximal consistent subset. -/
def exhMXReading (E : Set (Set World)) : Set World :=
  λ u => ∀ ψ ∈ E, ψ u

/-- The set of all `exh_mx` readings: one per MC-set. -/
def exhMXReadings : Set (Set World) :=
  {p | ∃ E, IsMCSet ALT φ E ∧ p = exhMXReading E}

/-- The conjunction of all `exh_mx` readings entails `exh_ie`. -/
theorem bigConj_exhMX_entails_exhIE (hne : ∃ E, IsMCSet ALT φ E) :
    {u | ∀ p ∈ exhMXReadings ALT φ, p u} ⊆ exhIE ALT φ := by
  intro u hall ψ hψIE
  obtain ⟨E, hmc⟩ := hne
  have hψE : ψ ∈ E := hψIE E hmc
  have hreading : exhMXReading E ∈ exhMXReadings ALT φ := ⟨E, hmc, rfl⟩
  exact hall (exhMXReading E) hreading ψ hψE

/-- Every `exh_mx` reading entails `exh_ie`. -/
theorem exhMXReading_entails_exhIE (E : Set (Set World)) (hmc : IsMCSet ALT φ E) :
    exhMXReading E ⊆ exhIE ALT φ := by
  intro u hread ψ hψIE
  exact hread ψ (hψIE E hmc)

/-- `exh_mw` is the disjunction of all `exh_mx` readings (Lemma 3 restated). -/
theorem exhMW_eq_bigDisj_exhMX :
    exhMW ALT φ = {u | ∃ p ∈ exhMXReadings ALT φ, p u} := by
  apply Set.Subset.antisymm
  · intro u hmw
    obtain ⟨E, hmc, hsat⟩ := (exhMW_iff_satisfies_MCset ALT φ u).mp hmw
    exact ⟨exhMXReading E, ⟨E, hmc, rfl⟩, hsat⟩
  · intro u hex
    obtain ⟨p, hp, hpu⟩ := hex
    obtain ⟨E, hmc, rfl⟩ := hp
    exact (exhMW_iff_satisfies_MCset ALT φ u).mpr ⟨E, hmc, hpu⟩

/-- Under conjunction closure, all three exhaustification operators coincide:
    `exh_ie` = `exh_mw` = ⋃₀ (`exh_mx` readings). -/
theorem exhOperators_coincide_under_closure (hclosed : closedUnderConj ALT) :
    exhIE ALT φ = {u | ∃ p ∈ exhMXReadings ALT φ, p u} := by
  rw [← exhMW_eq_exhIE_of_closedUnderConj ALT φ hclosed, exhMW_eq_bigDisj_exhMX]

/-- When there is a unique MC-set, all `exh_mx` readings are equivalent. -/
theorem exhMX_unique_when_unique_MCset
    {p q : Set World}
    (hp : p ∈ exhMXReadings ALT φ) (hq : q ∈ exhMXReadings ALT φ)
    (huniq : ∀ E₁ E₂, IsMCSet ALT φ E₁ → IsMCSet ALT φ E₂ → E₁ = E₂) :
    p = q := by
  obtain ⟨E₁, hmc₁, rfl⟩ := hp
  obtain ⟨E₂, hmc₂, rfl⟩ := hq
  rw [huniq E₁ E₂ hmc₁ hmc₂]

end Exhaustification
