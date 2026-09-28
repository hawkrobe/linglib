module

public import Linglib.Logic.Truthmaker.Bilateral
public import Mathlib.Tactic.FinCases

/-!
# Champollion and Bernard (2024): Negation and modality in unilateral truthmaker semantics

Champollion and Bernard give a unilateral truthmaker semantics in which negation comes from a
primitive exclusion relation between events rather than from a second set of falsifiers. Two
events conflict when a part of one excludes a part of the other, and an event is possible when it
does not conflict with itself. Possibility, which Fine takes as a primitive lower set of states,
is thereby derived (`possible`, Lemma 4.1). The worlds are the maximal possible events. Under the
axioms of Harmony and Rashōmon a world conflicts with every event it does not contain
(`conflict_of_not_le`, Theorem 8.4). An event verifies the negation of `φ` when it fuses, for each
verifier of `φ`, an event excluding a part of that verifier (`neg`). Every world then contains a
verifier of exactly one of `φ` and its negation (`mem_upperClosure_neg_iff`, Theorems 9.2–9.4). So
`φ` paired with its negation is a bilateral proposition that is exclusive and exhaustive in Fine's
sense (`exclusive_mk_neg`, `exhaustive_mk_neg`).

The paper departs from Fine in admitting emergent exclusion, where an event excludes the fusion
of two events without conflicting with either. Such an event verifies `¬(P ∧ Q)` but not
`¬P ∨ ¬Q` (`mem_neg_sups_diff`). Egg 3's being in a basket with room for two eggs is an example
(`eggs_mem_neg_sups_diff`). The two sides of de Morgan's law still hold at the same worlds
(`mem_upperClosure_neg_sups_iff`). Fine's Downward Exclusion condition rules such excluders out
(`DownwardExclusion.exists_conflict`). Cumulativity of exclusion adds the further verifiers of
`¬(P ∧ Q)` that Ciardelli, Zhang and Champollion's counterfactual data call for
(`neg_sups_neg_subset`). In the canonical frame a literal excludes its mirror image. There the
derived possibility is Fine's consistency (`possible_canonicalExcl`), negation recovers Fine's
falsifiers (`neg_ver_atom`, `neg_ver_conj_atom`), and the axioms hold (`harmony_canonicalExcl`,
`rashomon_canonicalExcl`, `cosmopolitan_canonicalExcl`).

## Implementation notes

The paper takes events to form a complete distributive lattice. No proof here uses
distributivity. Symmetry of exclusion is needed only for Plenitude, which the paper states with
the event before the world while Harmony puts the world first. Occurrence (Theorems 8.1–8.2), the
definitions of necessity, and the results about a formula language (Theorems 9.8–9.9) are not
formalized.

## References

* [L. Champollion and T. Bernard, *Negation and modality in unilateral truthmaker semantics*
  (2024)][champollion-bernard-2024]
* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [I. Ciardelli, L. Zhang and L. Champollion, *Two switches in the theory of counterfactuals: A
  study of truth conditionality and minimal change* (2018)][ciardelli-zhang-champollion-2018]
-/

@[expose] public section

open SetFamily Truthmaker

namespace ChampollionBernard2024

variable {E : Type*} [CompleteLattice E] {excl : E → E → Prop}

/-! ### Conflict and possibility -/

variable (excl) in
/-- Two events conflict when some part of the first excludes some part of the second
(def. 2). -/
def Conflict (e₁ e₂ : E) : Prop :=
  ∃ f₁ ≤ e₁, ∃ f₂ ≤ e₂, excl f₁ f₂

theorem Conflict.mono {e₁ e₂ e₁' e₂' : E} (h : Conflict excl e₁ e₂) (h₁ : e₁ ≤ e₁')
    (h₂ : e₂ ≤ e₂') : Conflict excl e₁' e₂' :=
  let ⟨f₁, hf₁, f₂, hf₂, hx⟩ := h
  ⟨f₁, hf₁.trans h₁, f₂, hf₂.trans h₂, hx⟩

theorem Conflict.symm (hS : Std.Symm excl) {e₁ e₂ : E} (h : Conflict excl e₁ e₂) :
    Conflict excl e₂ e₁ :=
  let ⟨f₁, hf₁, f₂, hf₂, hx⟩ := h
  ⟨f₂, hf₂, f₁, hf₁, hS.symm _ _ hx⟩

variable (excl) in
/-- The possible events are those that do not conflict with themselves (def. 4), and every part
of a possible event is possible (Lemma 4.1). -/
def possible : LowerSet E where
  carrier := {e | ¬ Conflict excl e e}
  lower' := by
    intro e e' hle he hc
    exact he (hc.mono hle hle)

theorem mem_possible {e : E} : e ∈ possible excl ↔ ¬ Conflict excl e e :=
  Iff.rfl

/-! ### Worlds and the axioms on exclusion -/

variable (excl) in
/-- Cosmopolitanism (axiom 19), Fine's W-space condition, holds when every possible event is part
of a world, a maximal possible event. -/
def Cosmopolitan : Prop :=
  ∀ e ∈ possible excl, ∃ w, e ≤ w ∧ Maximal (· ∈ possible excl) w

variable (excl) in
/-- Harmony (axiom 20) holds when every event that coheres with a world is possible. -/
def Harmony : Prop :=
  ∀ ⦃w e : E⦄, Maximal (· ∈ possible excl) w → ¬ Conflict excl w e → e ∈ possible excl

variable (excl) in
/-- Rashōmon (axiom 21) holds when the fusion of two coherent possible events is possible. -/
def Rashomon : Prop :=
  ∀ ⦃e₁ : E⦄, e₁ ∈ possible excl → ∀ ⦃e₂ : E⦄, e₂ ∈ possible excl → ¬ Conflict excl e₁ e₂ →
    e₁ ⊔ e₂ ∈ possible excl

/-- An event is possible exactly when it coheres with some world (Theorem 8.3). -/
theorem mem_possible_iff_exists_world (hS : Std.Symm excl) (hC : Cosmopolitan excl)
    (hH : Harmony excl) {e : E} :
    e ∈ possible excl ↔ ∃ w, ¬ Conflict excl e w ∧ Maximal (· ∈ possible excl) w := by
  refine ⟨fun he ↦ ?_, fun ⟨w, hc, hw⟩ ↦ hH hw fun h ↦ hc (h.symm hS)⟩
  obtain ⟨w, hew, hw⟩ := hC e he
  exact ⟨w, fun hc ↦ hw.prop (hc.mono hew le_rfl), hw⟩

/-- A world conflicts with every event it does not contain (Theorem 8.4). -/
theorem conflict_of_not_le (hH : Harmony excl) (hR : Rashomon excl) {w e : E}
    (hw : Maximal (· ∈ possible excl) w) (he : ¬ e ≤ w) : Conflict excl w e := by
  by_contra hc
  exact he (le_sup_right.trans (hw.le_of_ge (hR hw.prop (hH hw hc) hc) le_sup_left))

/-! ### Negation -/

variable (excl) in
/-- An event verifies the negation of `φ` when it is the fusion of the values of a function
sending each verifier of `φ` to an event that excludes some part of it (defs. 28–29). -/
def neg (φ : Set E) : Set E :=
  {e | ∃ h : E → E, (∀ f ∈ φ, ∃ g ≤ f, excl (h f) g) ∧ sSup (h '' φ) = e}

/-- The negation of a proposition with a single verifier `f` is verified by the events that
exclude a part of `f`. -/
theorem neg_singleton (f : E) : neg excl {f} = {e | ∃ g ≤ f, excl e g} := by
  ext e
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Set.image_singleton, sSup_singleton]
    exact hh f rfl
  · intro hg
    exact ⟨fun _ ↦ e, fun f' hf' ↦ Set.mem_singleton_iff.1 hf' ▸ hg, by simp⟩

/-- No possible event contains both a verifier of `φ` and a verifier of its negation. The paper
states this for worlds (Theorem 9.4). -/
theorem not_mem_upperClosure_neg {φ : Set E} {s : E} (hs : s ∈ possible excl)
    (hφ : s ∈ upperClosure φ) : s ∉ upperClosure (neg excl φ) := by
  intro hn
  obtain ⟨_, ⟨h, hh, rfl⟩, hle⟩ := mem_upperClosure.1 hn
  obtain ⟨f, hf, hfs⟩ := mem_upperClosure.1 hφ
  obtain ⟨g, hgf, hx⟩ := hh f hf
  exact hs ⟨h f, (le_sSup (Set.mem_image_of_mem h hf)).trans hle, g, hgf.trans hfs, hx⟩

/-- Every world contains a verifier of `φ` or a verifier of its negation (Theorem 9.3). -/
theorem mem_upperClosure_or_neg (hH : Harmony excl) (hR : Rashomon excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) (φ : Set E) :
    w ∈ upperClosure φ ∨ w ∈ upperClosure (neg excl φ) := by
  refine or_iff_not_imp_left.2 fun hφ ↦ ?_
  have : ∀ f, ∃ e, f ∈ φ → e ≤ w ∧ ∃ g ≤ f, excl e g := fun f ↦ by
    by_cases hf : f ∈ φ
    · obtain ⟨e, hew, g, hgf, hx⟩ :=
        conflict_of_not_le hH hR hw fun hfw ↦ hφ (mem_upperClosure.2 ⟨f, hf, hfw⟩)
      exact ⟨e, fun _ ↦ ⟨hew, g, hgf, hx⟩⟩
    · exact ⟨⊥, fun h ↦ absurd h hf⟩
  choose h hh using this
  exact mem_upperClosure.2 ⟨sSup (h '' φ), ⟨h, fun f hf ↦ (hh f hf).2, rfl⟩,
    sSup_le (Set.forall_mem_image.2 fun f hf ↦ (hh f hf).1)⟩

/-- A world contains a verifier of the negation of `φ` exactly when it contains no verifier of
`φ` (Theorem 9.2). -/
theorem mem_upperClosure_neg_iff (hH : Harmony excl) (hR : Rashomon excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) {φ : Set E} :
    w ∈ upperClosure (neg excl φ) ↔ w ∉ upperClosure φ :=
  ⟨fun hn hφ ↦ not_mem_upperClosure_neg hw.prop hφ hn,
    (mem_upperClosure_or_neg hH hR hw φ).resolve_left⟩

/-- A proposition paired with its negation is exclusive over the possible events. -/
theorem exclusive_mk_neg (φ : Set E) : (BilProp.mk φ (neg excl φ)).Exclusive (possible excl) :=
  BilProp.exclusive_iff.2 fun _ hs hφ ↦ not_mem_upperClosure_neg hs hφ

/-- A proposition paired with its negation is exhaustive over the possible events. -/
theorem exhaustive_mk_neg (hC : Cosmopolitan excl) (hH : Harmony excl) (hR : Rashomon excl)
    (φ : Set E) : (BilProp.mk φ (neg excl φ)).Exhaustive (possible excl) :=
  (BilProp.exhaustive_iff hC).2 fun _ hw ↦ mem_upperClosure_or_neg hH hR hw φ

/-! ### Emergent exclusion and de Morgan's law -/

variable (excl) in
/-- The individual excluders of `P` are the events that contain an excluder of a member of `P`
and are part of the fusion of all such excluders (defs. 11–12). -/
def individualExcluders (P : Set E) : Set E :=
  ↑(upperClosure {s | ∃ p ∈ P, excl s p}) ∩ Set.Iic (sSup {s | ∃ p ∈ P, excl s p})

variable (excl) in
/-- Fine's Downward Exclusion condition (14) holds when every event that excludes the fusion of
`P` is an individual excluder of `P`. -/
def DownwardExclusion : Prop :=
  ∀ ⦃P : Set E⦄ ⦃s : E⦄, excl s (sSup P) → s ∈ individualExcluders excl P

/-- An event that coheres with every member of `P` is not an individual excluder of `P`, so if
it excludes the fusion of `P` it is an emergent excluder (def. 13). -/
theorem not_mem_individualExcluders {P : Set E} {s : E} (hc : ∀ p ∈ P, ¬ Conflict excl s p) :
    s ∉ individualExcluders excl P := fun ⟨hs, _⟩ ↦
  let ⟨r, ⟨p, hp, hx⟩, hrs⟩ := mem_upperClosure.1 hs
  hc p hp ⟨r, hrs, p, le_rfl, hx⟩

/-- Under Downward Exclusion an event that excludes the fusion of `P` conflicts with a member of
`P`, so there are no emergent excluders. -/
theorem DownwardExclusion.exists_conflict (hD : DownwardExclusion excl) {P : Set E} {s : E}
    (hs : excl s (sSup P)) : ∃ p ∈ P, Conflict excl s p := by
  by_contra h
  exact not_mem_individualExcluders (fun p hp hc ↦ h ⟨p, hp, hc⟩) (hD hs)

/-- An event that excludes `p ⊔ q` while cohering with `p` and with `q` verifies `¬(P ∧ Q)` but not
`¬P ∨ ¬Q`, where `P` is verified by `p` alone and `Q` by `q` alone (§7). -/
theorem mem_neg_sups_diff {p q s : E} (hs : excl s (p ⊔ q)) (hp : ¬ Conflict excl s p)
    (hq : ¬ Conflict excl s q) : s ∈ neg excl ({p} ⊻ {q}) \ (neg excl {p} ∪ neg excl {q}) := by
  rw [Set.singleton_sups_singleton, neg_singleton, neg_singleton, neg_singleton]
  refine ⟨⟨p ⊔ q, le_rfl, hs⟩, ?_⟩
  rintro (⟨g, hg, hx⟩ | ⟨g, hg, hx⟩)
  · exact hp ⟨s, le_rfl, g, hg, hx⟩
  · exact hq ⟨s, le_rfl, g, hg, hx⟩

/-- The two sides of de Morgan's law `¬(φ ∧ ψ) ⇔ ¬φ ∨ ¬ψ` hold at the same worlds (§9). -/
theorem mem_upperClosure_neg_sups_iff (hH : Harmony excl) (hR : Rashomon excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) (φ ψ : Set E) :
    w ∈ upperClosure (neg excl (φ ⊻ ψ)) ↔ w ∈ upperClosure (neg excl φ ∪ neg excl ψ) := by
  rw [upperClosure_union, UpperSet.mem_inf_iff, mem_upperClosure_neg_iff hH hR hw,
    mem_upperClosure_neg_iff hH hR hw, mem_upperClosure_neg_iff hH hR hw, upperClosure_sups,
    UpperSet.mem_sup_iff, not_and_or]

/-- If exclusion is cumulative, the fusion of a verifier of `¬P` with a verifier of `¬Q` verifies
`¬(P ∧ Q)`, for `P` verified by `p` alone and `Q` by `q` alone (§8, fn. 27). -/
theorem neg_sups_neg_subset
    (hCum : ∀ ⦃e e' f f' : E⦄, excl e e' → excl f f' → excl (e ⊔ f) (e' ⊔ f')) (p q : E) :
    neg excl {p} ⊻ neg excl {q} ⊆ neg excl ({p} ⊻ {q}) := by
  rw [Set.singleton_sups_singleton, neg_singleton, neg_singleton, neg_singleton]
  rintro _ ⟨e, ⟨g, hgp, he⟩, f, ⟨g', hgq, hf⟩, rfl⟩
  exact ⟨g ⊔ g', sup_le_sup hgp hgq, hCum he hf⟩

/-! ### The basket with room for two eggs -/

/-- In a basket with room for two of the eggs `0`, `1` and `2`, the event of egg `i`'s being in
the basket excludes the event of the other two eggs' being in it, and conversely (§6). -/
def eggsExcl (s t : Set (Fin 3)) : Prop :=
  ∃ i, s = {i} ∧ t = {i}ᶜ ∨ s = {i}ᶜ ∧ t = {i}

private theorem compl_singleton_not_subset_singleton (i j : Fin 3) :
    ¬ ({i}ᶜ : Set (Fin 3)) ⊆ {j} := by
  simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_singleton_iff]
  revert i j
  decide

/-- No egg's being in the basket conflicts with another's. -/
theorem not_conflict_eggsExcl (i j : Fin 3) : ¬ Conflict eggsExcl {i} {j} := by
  rintro ⟨_, h₁, _, h₂, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact compl_singleton_not_subset_singleton k j h₂
  · exact compl_singleton_not_subset_singleton k i h₁

/-- The third egg's being in the basket verifies *egg 1 and egg 2 are not both in the basket* but
not *either egg 1 or egg 2 is not in the basket* (§7). -/
theorem eggs_mem_neg_sups_diff :
    ({2} : Set (Fin 3)) ∈
      neg eggsExcl ({{0}} ⊻ {{1}}) \ (neg eggsExcl {{0}} ∪ neg eggsExcl {{1}}) :=
  mem_neg_sups_diff ⟨2, .inl ⟨rfl, by ext x; fin_cases x <;> simp⟩⟩ (not_conflict_eggsExcl 2 0)
    (not_conflict_eggsExcl 2 1)

/-! ### The canonical frame -/

section Canonical

open Truthmaker.Canonical

variable {α : Type*}

/-- In the canonical frame over atoms `α`, whose events are sets of literals, a literal excludes
its mirror image and nothing else holds (def. 23). -/
def canonicalExcl (s t : Set (α × Bool)) : Prop :=
  ∃ x, s = {x} ∧ t = {mirror x}

theorem conflict_canonicalExcl_iff {e₁ e₂ : Set (α × Bool)} :
    Conflict canonicalExcl e₁ e₂ ↔ ∃ x ∈ e₁, mirror x ∈ e₂ := by
  constructor
  · rintro ⟨_, h₁, _, h₂, x, rfl, rfl⟩
    exact ⟨x, h₁ rfl, h₂ rfl⟩
  · rintro ⟨x, hx₁, hx₂⟩
    exact ⟨{x}, Set.singleton_subset_iff.2 hx₁, _, Set.singleton_subset_iff.2 hx₂, x, rfl, rfl⟩

/-- Possibility derived from canonical exclusion is Fine's consistency of sets of literals. -/
theorem possible_canonicalExcl : possible (canonicalExcl (α := α)) = Canonical.possible :=
  SetLike.ext fun _ ↦ by simp [mem_possible, conflict_canonicalExcl_iff, Canonical.mem_possible]

/-- In the canonical frame the negation of an atom is verified by its denial alone, the
atom's falsifier in Fine's bilateral semantics. -/
theorem neg_ver_atom (a : α) : neg canonicalExcl (atom a).ver = (atom a).fal := by
  rw [ver_atom, fal_atom, neg_singleton]
  ext e
  constructor
  · rintro ⟨_, hg, x, rfl, rfl⟩
    obtain rfl : x = (a, false) := by
      simpa using congrArg mirror (Set.singleton_subset_singleton.1 hg)
    rfl
  · rintro rfl
    exact ⟨{(a, true)}, le_rfl, (a, false), rfl, rfl⟩

/-- In the canonical frame the negation of a conjunction of two atoms is verified exactly by the
denial of either atom, its falsifiers in Fine's bilateral semantics, so de Morgan's law holds
exactly there (§9). -/
theorem neg_ver_conj_atom (a b : α) :
    neg canonicalExcl ((atom a).conj (atom b)).ver = ((atom a).conj (atom b)).fal := by
  rw [BilProp.ver_conj, BilProp.fal_conj, ver_atom, ver_atom, fal_atom, fal_atom,
    Set.singleton_sups_singleton, neg_singleton]
  ext e
  constructor
  · rintro ⟨_, hg, x, rfl, rfl⟩
    rcases Set.singleton_subset_iff.1 hg with h | h
    · obtain rfl : x = (a, false) := by
        simpa using congrArg mirror (Set.mem_singleton_iff.1 h)
      exact .inl rfl
    · obtain rfl : x = (b, false) := by
        simpa using congrArg mirror (Set.mem_singleton_iff.1 h)
      exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨{(a, true)}, Set.singleton_subset_iff.2 (.inl rfl), (a, false), rfl, rfl⟩
    · exact ⟨{(b, true)}, Set.singleton_subset_iff.2 (.inr rfl), (b, false), rfl, rfl⟩

theorem harmony_canonicalExcl : Harmony (canonicalExcl (α := α)) := by
  intro w e hw hc
  rw [possible_canonicalExcl] at hw ⊢
  intro x hx hx'
  rcases mem_or_mirror_mem_of_maximal hw x with hxw | hxw
  · exact hc (conflict_canonicalExcl_iff.2 ⟨x, hxw, hx'⟩)
  · exact hc (conflict_canonicalExcl_iff.2 ⟨mirror x, hxw, by rwa [mirror_mirror]⟩)

theorem rashomon_canonicalExcl : Rashomon (canonicalExcl (α := α)) := by
  intro e₁ h₁ e₂ h₂ hc
  rw [possible_canonicalExcl] at h₁ h₂ ⊢
  rw [conflict_canonicalExcl_iff] at hc
  rintro x (hx | hx) (hx' | hx')
  · exact h₁ x hx hx'
  · exact hc ⟨x, hx, hx'⟩
  · exact hc ⟨mirror x, hx', by rwa [mirror_mirror]⟩
  · exact h₂ x hx hx'

theorem cosmopolitan_canonicalExcl : Cosmopolitan (canonicalExcl (α := α)) := by
  unfold Cosmopolitan
  rw [possible_canonicalExcl]
  exact fun _ ↦ exists_le_maximal_possible

/-- Fine's bilateral atom is the unilateral atom paired with its negation. -/
theorem mk_neg_ver_atom (a : α) :
    BilProp.mk (atom a).ver (neg canonicalExcl (atom a).ver) = atom a := by
  rw [neg_ver_atom]

/- Fine's classicality of the canonical atoms follows from the exclusion axioms. -/
example (a : α) : (atom a).Exclusive Canonical.possible :=
  possible_canonicalExcl ▸ mk_neg_ver_atom a ▸ exclusive_mk_neg _

example (a : α) : (atom a).Exhaustive Canonical.possible :=
  possible_canonicalExcl ▸ mk_neg_ver_atom a ▸
    exhaustive_mk_neg cosmopolitan_canonicalExcl harmony_canonicalExcl rashomon_canonicalExcl _

end Canonical

end ChampollionBernard2024
