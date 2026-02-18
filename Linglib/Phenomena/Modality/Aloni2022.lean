/-
# Aloni (2022): Bilateral State-based Modal Logic (BSML)

BSML derives free choice inferences SEMANTICALLY via:
1. **Team Semantics**: States as sets of worlds
2. **Bilateral Evaluation**: Support (⊨⁺) and anti-support (⊨⁻)
3. **Split Disjunction**: t ⊨ φ ∨ ψ iff ∃t₁,t₂: t₁ ∪ t₂ = t ∧ t₁ ⊨ φ ∧ t₂ ⊨ ψ
4. **Non-emptiness Atom (NE)**: t ⊨ NE iff t ≠ ∅
5. **Pragmatic Enrichment [·]⁺**: Recursively adds NE constraints

## Key Free Choice Results

| Result | Statement |
|--------|-----------|
| Narrow Scope FC | [◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β |
| Wide Scope FC | [◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β (if R indisputable) |
| Dual Prohibition | [¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β |

## Comparison with BUS (Elliott & Sudo 2025)

| Aspect | BSML (Aloni) | BUS (Elliott & Sudo) |
|--------|-------------|---------------------|
| Semantics | Static (support) | Dynamic (updates) |
| State | Team = Set World | InfoState (world, assignment) |
| Bilateral | Support/anti-support | Positive/negative updates |
| DNE | Swap support | Swap updates |
| FC mechanism | Split ∨ + NE | Modal ∨ precondition |
| Anaphora | No | Yes (bathroom sentences) |

## References

- Aloni, M. (2022). Logic and conversation: The case of free choice. S&P 15.
- Aloni, M., Anttila, A. & Yang, F. (2024). State-based Modal Logics for Free Choice.
-/

import Linglib.Theories.Semantics.Dynamic.TeamSemantics

namespace Phenomena.Modality.Aloni2022

open Semantics.Dynamic.TeamSemantics

-- ============================================================================
-- PART 1: BSML Model Structure
-- ============================================================================

/--
A BSML model consists of:
- A set of worlds W
- An accessibility relation R (for modals)
- A valuation V (atomic propositions)

We represent accessibility as a function from worlds to teams:
R[w] = the team of worlds accessible from w.
-/
structure BSMLModel (W : Type*) where
  /-- Accessibility: R[w] = worlds accessible from w -/
  access : W -> Team W
  /-- Valuation: which atoms are true at which worlds -/
  valuation : String -> W -> Bool

/-- Universal accessibility (S5-like): all worlds accessible from all -/
def BSMLModel.universal {W : Type*} : BSMLModel W where
  access := λ _ => Team.full
  valuation := λ _ _ => false

/-- Indisputable accessibility: all worlds in team have same accessible worlds -/
def BSMLModel.isIndisputable {W : Type*} (M : BSMLModel W) (t : Team W)
    (worlds : List W) : Bool :=
  let members := t.toList worlds
  match members with
  | [] => true
  | w :: rest => rest.all λ v => (M.access w).beq (M.access v) worlds

-- ============================================================================
-- PART 2: BSML Formulas
-- ============================================================================

/--
BSML formulas with bilateral support conditions.

The key innovation is SPLIT DISJUNCTION: a team supports φ ∨ ψ iff
the team can be partitioned into parts supporting each disjunct.
-/
inductive BSMLFormula (W : Type*) where
  /-- Atomic proposition -/
  | atom : String -> BSMLFormula W
  /-- Non-emptiness atom: team is non-empty -/
  | ne : BSMLFormula W
  /-- Negation: swap support/anti-support -/
  | neg : BSMLFormula W -> BSMLFormula W
  /-- Conjunction -/
  | conj : BSMLFormula W -> BSMLFormula W -> BSMLFormula W
  /-- Split disjunction (Aloni's key innovation) -/
  | disj : BSMLFormula W -> BSMLFormula W -> BSMLFormula W
  /-- Possibility modal -/
  | poss : BSMLFormula W -> BSMLFormula W
  /-- Necessity modal -/
  | nec : BSMLFormula W -> BSMLFormula W
  deriving Repr

-- ============================================================================
-- PART 3: Helper Functions for Team Operations
-- ============================================================================

/-- Generate all subsets of a list -/
def allSubsets {α : Type*} : List α -> List (List α)
  | [] => [[]]
  | x :: xs =>
      let withoutX := allSubsets xs
      withoutX ++ withoutX.map (x :: ·)

/-- Generate all possible splits of a team into two parts -/
def generateSplits {W : Type*} [DecidableEq W] (t : Team W) (worlds : List W) :
    List (Team W × Team W) :=
  let members := t.toList worlds
  (allSubsets members).map λ left =>
    let leftTeam : Team W := Team.ofList left
    let rightTeam : Team W := λ w => t w && !leftTeam w
    (leftTeam, rightTeam)

/-- Generate all subteams of a team -/
def generateSubteams {W : Type*} [DecidableEq W] (t : Team W) (worlds : List W) :
    List (Team W) :=
  let members := t.toList worlds
  (allSubsets members).map Team.ofList

-- ============================================================================
-- PART 4: Support and Anti-Support (Mutually Defined)
-- ============================================================================

/-
Positive support: t ⊨⁺ φ (Definition 2 from Aloni 2022)

Negative support (anti-support): t ⊨⁻ φ

These are mutually defined: negation swaps support and anti-support.
-/
mutual
def support {W : Type*} [DecidableEq W] (M : BSMLModel W) (worlds : List W)
    (φ : BSMLFormula W) (t : Team W) : Bool :=
  match φ with
  | .atom p => t.all (M.valuation p) worlds
  | .ne => t.isNonEmpty worlds
  | .neg ψ => antiSupport M worlds ψ t
  | .conj ψ₁ ψ₂ => support M worlds ψ₁ t && support M worlds ψ₂ t
  | .disj ψ₁ ψ₂ =>
      let splits := generateSplits t worlds
      splits.any λ (t1, t2) => support M worlds ψ₁ t1 && support M worlds ψ₂ t2
  | .poss ψ =>
      t.all (λ w =>
        let accessible := M.access w
        let subteams := generateSubteams accessible worlds
        subteams.any λ t' => t'.isNonEmpty worlds && support M worlds ψ t'
      ) worlds
  | .nec ψ =>
      t.all (λ w => support M worlds ψ (M.access w)) worlds

def antiSupport {W : Type*} [DecidableEq W] (M : BSMLModel W) (worlds : List W)
    (φ : BSMLFormula W) (t : Team W) : Bool :=
  match φ with
  | .atom p => t.all (λ w => !M.valuation p w) worlds
  | .ne => t.isEmpty worlds
  | .neg ψ => support M worlds ψ t
  | .conj ψ₁ ψ₂ => antiSupport M worlds ψ₁ t || antiSupport M worlds ψ₂ t
  | .disj ψ₁ ψ₂ => antiSupport M worlds ψ₁ t && antiSupport M worlds ψ₂ t
  | .poss ψ =>
      t.all (λ w =>
        let accessible := M.access w
        let subteams := generateSubteams accessible worlds
        subteams.all λ t' => t'.isEmpty worlds || antiSupport M worlds ψ t'
      ) worlds
  | .nec ψ =>
      t.any (λ w => antiSupport M worlds ψ (M.access w)) worlds
end

-- ============================================================================
-- PART 5: Double Negation Elimination
-- ============================================================================

/--
DNE holds definitionally: ¬¬φ has the same support conditions as φ.

This follows from negation swapping support and anti-support.
-/
theorem dne_support {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula W) (t : Team W) (worlds : List W) :
    support M worlds (.neg (.neg φ)) t = support M worlds φ t := by
  simp only [support, antiSupport]

theorem dne_antiSupport {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula W) (t : Team W) (worlds : List W) :
    antiSupport M worlds (.neg (.neg φ)) t = antiSupport M worlds φ t := by
  simp only [support, antiSupport]

-- ============================================================================
-- PART 5b: Flatness - The Key Structural Property
-- ============================================================================

/-!
## Flatness: Why NE is Special

A team proposition is **flat** (downward closed) if:
  whenever t ⊨ φ and t' ⊆ t, then t' ⊨ φ

Classical propositions lifted to teams are always flat:
  t ⊨ p iff ∀w ∈ t, p(w)
  If t' ⊆ t and t ⊨ p, then ∀w ∈ t', w ∈ t so p(w), hence t' ⊨ p

**NE is NOT flat**: This is the key structural fact enabling free choice!
  - {w₁, w₂} ⊨ NE (non-empty)
  - {w₁} ⊆ {w₁, w₂} and {w₁} ⊨ NE
  - BUT {} ⊆ {w₁, w₂} and {} ⊭ NE!

The non-flatness of NE is what makes enrichment non-trivial.
-/

/-- A team proposition is flat if support is downward closed under subset -/
def isFlat' {W : Type*} (prop : Team W → List W → Bool) (worlds : List W) : Prop :=
  ∀ t t' : Team W, t'.subset t worlds = true → prop t worlds = true → prop t' worlds = true

/-- Atoms are flat: if all worlds in t satisfy p, then all worlds in t' ⊆ t satisfy p -/
theorem atom_is_flat {W : Type*} [DecidableEq W] (M : BSMLModel W) (p : String) (worlds : List W) :
    isFlat' (λ t ws => support M ws (.atom p) t) worlds := by
  intro t t' hSub hSupp
  simp only [support, Team.all] at *
  -- We need: (worlds.all λ w => !t' w || M.valuation p w) = true
  -- We have: (worlds.all λ w => !t w || M.valuation p w) = true
  -- And: t' ⊆ t (so !t' w → !t w, meaning if w ∉ t' then w ∉ t or just !t' w || p w holds)
  simp only [Team.subset, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
              Bool.eq_false_iff] at *
  intro w hw
  cases ht' : t' w
  · simp
  · have h1 := hSub w hw
    simp [ht'] at h1
    have h2 := hSupp w hw
    simp [h1] at h2
    simp [h2]

/-- NE is NOT flat: the empty team doesn't support NE, but is a subset of any team that does -/
theorem ne_not_flat {W : Type*} [DecidableEq W] [Inhabited W] (worlds : List W) (hWorlds : worlds ≠ []) :
    ¬isFlat' (λ t ws => support (BSMLModel.universal : BSMLModel W) ws .ne t) worlds := by
  intro hFlat
  -- Take any non-empty team t (exists since worlds is non-empty)
  -- t ⊨ NE, and ∅ ⊆ t, but ∅ ⊭ NE
  -- This contradicts flatness
  simp only [isFlat'] at hFlat
  -- The empty team is a subset of any team
  have hEmpty : Team.empty.subset Team.full worlds = true := by
    simp [Team.subset, Team.empty, Team.full, List.all_eq_true]
  -- Team.full supports NE (it's non-empty)
  have hFullNE : support BSMLModel.universal worlds .ne Team.full = true := by
    simp only [support, Team.isNonEmpty]
    cases worlds with
    | nil => contradiction
    | cons w ws =>
        simp only [List.any_cons, Team.full]
        rfl
  -- But Team.empty does NOT support NE
  have hEmptyNotNE : support BSMLModel.universal worlds .ne Team.empty = false := by
    simp only [support, Team.isNonEmpty]
    -- Team.empty w = false for all w, so worlds.any Team.empty = false
    have hAnyEmpty : ∀ ws : List W, ws.any Team.empty = false := λ ws => by
      induction ws with
      | nil => rfl
      | cons w ws ih => simp only [List.any_cons, Team.empty, Bool.false_or, ih]
    exact hAnyEmpty worlds
  -- Apply flatness to get a contradiction
  have := hFlat Team.full Team.empty hEmpty hFullNE
  rw [hEmptyNotNE] at this
  exact Bool.false_ne_true this

/-!
### insight

NE being non-flat means that split disjunction behaves differently from conjunction.
In [φ ∨ ψ]⁺, the NE constraint applies to EACH part of the split, forcing both
parts to be non-empty.
-/

-- ============================================================================
-- PART 6: Pragmatic Enrichment
-- ============================================================================

/--
Pragmatic enrichment [·]⁺ (Definition 6 from Aloni 2022).

The key insight: add non-emptiness constraints recursively.
This captures the "neglect-zero" tendency in human cognition.

[p]⁺ = p ∧ NE
[NE]⁺ = NE
[¬φ]⁺ = ¬[φ]⁺ ∧ NE
[φ ∧ ψ]⁺ = [φ]⁺ ∧ [ψ]⁺
[φ ∨ ψ]⁺ = [φ]⁺ ∨ [ψ]⁺
[◇φ]⁺ = ◇[φ]⁺ ∧ NE
[□φ]⁺ = □[φ]⁺ ∧ NE
-/
def enrich {W : Type*} : BSMLFormula W -> BSMLFormula W
  | .atom p => .conj (.atom p) .ne
  | .ne => .ne
  | .neg φ => .conj (.neg (enrich φ)) .ne
  | .conj φ ψ => .conj (enrich φ) (enrich ψ)
  | .disj φ ψ => .disj (enrich φ) (enrich ψ)
  | .poss φ => .conj (.poss (enrich φ)) .ne
  | .nec φ => .conj (.nec (enrich φ)) .ne

-- ============================================================================
-- PART 6b: Enrichment Structure Lemmas
-- ============================================================================

/-!
## Enrichment Preserves Structure

Key properties of enrichment:
1. Atoms, negation, and modals get NE at the top level
2. Conjunction and disjunction do NOT get extra NE (following Aloni's Definition 6)
3. If an enriched formula is supported, the team must be non-empty
-/

/-- Enrichment of negation is negation of enrichment, conjoined with NE -/
theorem enrich_neg_structure {W : Type*} (φ : BSMLFormula W) :
    enrich (.neg φ) = .conj (.neg (enrich φ)) .ne := rfl

/-- Enrichment of conjunction is conjunction of enrichments (no extra NE) -/
theorem enrich_conj_structure {W : Type*} (φ ψ : BSMLFormula W) :
    enrich (.conj φ ψ) = .conj (enrich φ) (enrich ψ) := rfl

/-- Enrichment of disjunction is disjunction of enrichments (no extra NE) -/
theorem enrich_disj_structure {W : Type*} (φ ψ : BSMLFormula W) :
    enrich (.disj φ ψ) = .disj (enrich φ) (enrich ψ) := rfl

/-- Enrichment of possibility is possibility of enrichment, conjoined with NE -/
theorem enrich_poss_structure {W : Type*} (φ : BSMLFormula W) :
    enrich (.poss φ) = .conj (.poss (enrich φ)) .ne := rfl

/-- Helper: extract first component of Bool.and -/
private lemma and_true_left {a b : Bool} (h : a && b = true) : a = true := by
  cases a <;> cases b <;> simp_all

/-- Helper: extract second component of Bool.and -/
private lemma and_true_right {a b : Bool} (h : a && b = true) : b = true := by
  cases a <;> cases b <;> simp_all

/-- Helper: split Bool.and into components -/
private lemma and_true_split {a b : Bool} (h : a && b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- Elements of an allSubsets sublist are in the original list -/
private lemma mem_of_mem_allSubsets {α : Type*} (l sub : List α)
    (hsub : sub ∈ allSubsets l) : ∀ x ∈ sub, x ∈ l := by
  induction l generalizing sub with
  | nil => simp [allSubsets] at hsub; subst hsub; simp
  | cons a as ih =>
    simp only [allSubsets, List.mem_append] at hsub
    intro x hx
    cases hsub with
    | inl h => exact List.mem_cons.mpr (Or.inr (ih _ h x hx))
    | inr h =>
      obtain ⟨sub', hmem, rfl⟩ := List.mem_map.mp h
      cases hx with
      | head => exact List.mem_cons.mpr (Or.inl rfl)
      | tail _ hx => exact List.mem_cons.mpr (Or.inr (ih _ hmem x hx))

/-- Members of a split's left part are in the original team -/
private lemma split_left_mem {W : Type*} [DecidableEq W]
    (t t1 t2 : Team W) (worlds : List W)
    (hmem : (t1, t2) ∈ generateSplits t worlds)
    (v : W) (ht1v : t1 v = true) : t v = true := by
  simp only [generateSplits, List.mem_map] at hmem
  obtain ⟨left, hleft, heq⟩ := hmem
  have ht1_eq : t1 = Team.ofList left := (Prod.ext_iff.mp heq).1.symm
  rw [ht1_eq] at ht1v
  simp only [Team.ofList] at ht1v
  have hv_in_left : v ∈ left := List.mem_of_elem_eq_true ht1v
  have hv_in_toList := mem_of_mem_allSubsets _ _ hleft v hv_in_left
  simp only [Team.toList, List.mem_filter] at hv_in_toList
  exact hv_in_toList.2

/-- If a split part is non-empty, the original team is non-empty -/
private lemma split_nonempty {W : Type*} [DecidableEq W]
    (t t1 t2 : Team W) (worlds : List W)
    (hmem : (t1, t2) ∈ generateSplits t worlds)
    (hne : t1.isNonEmpty worlds = true) : t.isNonEmpty worlds = true := by
  simp only [Team.isNonEmpty, List.any_eq_true] at hne ⊢
  obtain ⟨v, hv, ht1v⟩ := hne
  exact ⟨v, hv, split_left_mem t t1 t2 worlds hmem v ht1v⟩

/-- If an enriched formula (other than NE) is supported, the team is non-empty.

    For atoms, negation, and modals this follows from the top-level NE conjunct.
    For conjunction and disjunction (which lack top-level NE in Definition 6),
    non-emptiness is inherited from the enriched sub-formulas. -/
theorem enriched_support_implies_nonempty {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula W) (t : Team W) (worlds : List W)
    (h : support M worlds (enrich φ) t = true) :
    t.isNonEmpty worlds = true := by
  induction φ generalizing t with
  | ne => exact h
  | atom p =>
      simp only [enrich, support] at h
      cases hA : (t.all (M.valuation p) worlds) <;> cases hB : t.isNonEmpty worlds <;> simp_all
  | neg ψ _ =>
      simp only [enrich, support] at h
      cases hA : (antiSupport M worlds (enrich ψ) t) <;> cases hB : t.isNonEmpty worlds <;> simp_all
  | conj ψ₁ ψ₂ ih₁ _ =>
      -- enrich (.conj ψ₁ ψ₂) = .conj (enrich ψ₁) (enrich ψ₂)
      unfold enrich at h
      unfold support at h
      apply ih₁
      revert h; cases support M worlds (enrich ψ₁) t <;> simp
  | disj ψ₁ ψ₂ ih₁ _ =>
      -- enrich (.disj ψ₁ ψ₂) = .disj (enrich ψ₁) (enrich ψ₂) (definitional)
      -- Extract the split, apply IH to get t₁ non-empty, propagate through split.
      unfold enrich at h; unfold support at h
      obtain ⟨⟨t1, t2⟩, hmem, hsupp⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true] at hsupp
      exact split_nonempty t t1 t2 worlds hmem (ih₁ t1 hsupp.1)
  | poss ψ _ =>
      simp only [enrich, support] at h
      cases hB : t.isNonEmpty worlds <;> simp_all
  | nec ψ _ =>
      simp only [enrich, support] at h
      cases hB : t.isNonEmpty worlds <;> simp_all

-- ============================================================================
-- PART 6c: The Core Split Lemma (FC Derivation)
-- ============================================================================

/-!
## The Core Lemma: Split Disjunction + NE Forces Both Parts Non-empty

This is THE key lemma that derives free choice. The structure is:

1. t ⊨ [φ ∨ ψ]⁺ = (([φ]⁺ ∨ [ψ]⁺) ∧ NE)
2. Split disjunction: ∃ t₁, t₂ with t = t₁ ∪ t₂, t₁ ⊨ [φ]⁺, t₂ ⊨ [ψ]⁺
3. [φ]⁺ supported implies t₁ non-empty (by enriched_support_implies_nonempty)
4. [ψ]⁺ supported implies t₂ non-empty (by enriched_support_implies_nonempty)
5. Therefore BOTH parts of the split are non-empty!

This is why FC arises: the split guarantees both alternatives are "live".
-/

/-- If disjunction is supported, there exists a split where both parts support their disjuncts -/
theorem split_exists {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula W) (t : Team W) (worlds : List W)
    (h : support M worlds (.disj φ ψ) t = true) :
    ∃ t₁ t₂ : Team W, support M worlds φ t₁ = true ∧ support M worlds ψ t₂ = true := by
  simp only [support] at h
  -- The split exists by definition of support for disjunction
  -- generateSplits.any returns true means at least one split works
  have := List.any_eq_true.mp h
  obtain ⟨⟨t1, t2⟩, _, hSupp⟩ := this
  -- Split the conjunction
  have h1 : support M worlds φ t1 = true := by
    cases hA : support M worlds φ t1 <;> simp_all
  have h2 : support M worlds ψ t2 = true := by
    cases hA : support M worlds ψ t2 <;> simp_all
  exact ⟨t1, t2, h1, h2⟩

/-- THE CORE LEMMA: Enriched disjunction forces both parts of split to be non-empty.

This is the derivation of free choice from first principles:
- Split disjunction partitions the team
- Enrichment adds NE to each disjunct
- NE being non-flat means each part must be genuinely non-empty
- Therefore both alternatives are "live" (FC!)
-/
theorem enriched_split_forces_both_nonempty {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula W) (t : Team W) (worlds : List W)
    (h : support M worlds (enrich (.disj φ ψ)) t = true) :
    ∃ t₁ t₂ : Team W,
      t₁.isNonEmpty worlds = true ∧
      t₂.isNonEmpty worlds = true ∧
      support M worlds (enrich φ) t₁ = true ∧
      support M worlds (enrich ψ) t₂ = true := by
  -- enrich (.disj φ ψ) = .disj (enrich φ) (enrich ψ) (no extra NE wrapper)
  simp only [enrich, support] at h
  -- h : (generateSplits t worlds).any (λ x => ...) = true
  have hSplit := List.any_eq_true.mp h
  obtain ⟨⟨t1, t2⟩, _, hBoth⟩ := hSplit
  have hPhi : support M worlds (enrich φ) t1 = true := by
    cases hA : support M worlds (enrich φ) t1 <;> simp_all
  have hPsi : support M worlds (enrich ψ) t2 = true := by
    cases hA : support M worlds (enrich ψ) t2 <;> simp_all
  have hT1NE := enriched_support_implies_nonempty M φ t1 worlds hPhi
  have hT2NE := enriched_support_implies_nonempty M ψ t2 worlds hPsi
  exact ⟨t1, t2, hT1NE, hT2NE, hPhi, hPsi⟩

-- ============================================================================
-- PART 6d: Structural Asymmetry - Why Dual Prohibition Works Differently
-- ============================================================================

/-!
## The Structural Asymmetry: Support vs Anti-Support of Disjunction

Why does FC give ◇α ∧ ◇β but prohibition give ¬◇α ∧ ¬◇β (both conjunctions)?

**Support of φ ∨ ψ**: Uses SPLIT
  t ⊨ φ ∨ ψ iff ∃ t₁, t₂: t = t₁ ∪ t₂ ∧ t₁ ⊨ φ ∧ t₂ ⊨ ψ

**Anti-support of φ ∨ ψ**: Uses CONJUNCTION (no split!)
  t ⊨⁻ φ ∨ ψ iff t ⊨⁻ φ ∧ t ⊨⁻ ψ

This asymmetry is why:
- FC: Split with NE → both parts non-empty → both possibilities exist
- Prohibition: No split, just conjunction → both are anti-supported → neither possible
-/

/-- Anti-support of disjunction is conjunction of anti-supports (no split!) -/
theorem antiSupport_disj_is_conj {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula W) (t : Team W) (worlds : List W) :
    antiSupport M worlds (.disj φ ψ) t =
    (antiSupport M worlds φ t && antiSupport M worlds ψ t) := by
  simp only [antiSupport]

/-- The asymmetry: disjunction support uses existential (split), anti-support uses universal (conj)

This is definitional but worth stating explicitly as it's the key structural difference. -/
theorem support_antiSupport_asymmetry {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula W) (t : Team W) (worlds : List W) :
    -- Support: existential over splits
    (support M worlds (.disj φ ψ) t = true ↔
      (generateSplits t worlds).any (λ (t1, t2) =>
        support M worlds φ t1 && support M worlds ψ t2) = true) ∧
    -- Anti-support: universal (conjunction)
    (antiSupport M worlds (.disj φ ψ) t = true ↔
      antiSupport M worlds φ t = true ∧ antiSupport M worlds ψ t = true) := by
  constructor
  · simp only [support]
  · simp only [antiSupport, Bool.and_eq_true]

-- ============================================================================
-- PART 6e: Helper Lemmas for Free Choice Proofs
-- ============================================================================

/-- Monotonicity for List.all: if f implies g pointwise, then all f implies all g -/
private lemma list_all_mono {α : Type*} (l : List α) (f g : α → Bool)
    (hfg : ∀ x, f x = true → g x = true) (hf : l.all f = true) : l.all g = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at *
    exact ⟨hfg x hf.1, ih hf.2⟩

/-- Monotonicity for Team.all -/
private lemma team_all_mono {W : Type*} (t : Team W) (f g : W → Bool) (worlds : List W)
    (hfg : ∀ w, f w = true → g w = true)
    (hf : t.all f worlds = true) : t.all g worlds = true := by
  unfold Team.all at *
  exact list_all_mono worlds _ _ (fun w hw => by
    cases ht : t w <;> simp_all) hf

/-- Empty team satisfies Team.all for any predicate (vacuous truth) -/
private lemma team_all_of_isEmpty {W : Type*} (t : Team W) (p : W → Bool) (worlds : List W)
    (he : t.isEmpty worlds = true) : t.all p worlds = true := by
  unfold Team.all Team.isEmpty at *
  simp only [Bool.not_eq_true'] at he
  induction worlds with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.any_cons, List.all_cons, Bool.or_eq_false_iff, Bool.and_eq_true] at *
    exact ⟨by simp [he.1], ih he.2⟩

/-- Anti-support of enriched atom disjunction implies anti-support of left atom.

    antiSupport ((a ∧ NE) ∨ (b ∧ NE)) t' = true → antiSupport a t' = true

    Key insight: if t' is empty, antiSupport (.atom a) t' is vacuously true.
    If t' is non-empty, the conjunction's || isEmpty branch is false, so
    antiSupport a t' must be true directly. -/
private lemma antiSupport_enriched_disj_implies_left {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (a b : String) (t' : Team W) (worlds : List W)
    (h : antiSupport M worlds (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) t' = true) :
    antiSupport M worlds (.atom a) t' = true := by
  unfold antiSupport at h
  have h1 : antiSupport M worlds (.conj (.atom a) .ne) t' = true := by
    revert h; cases antiSupport M worlds (.conj (.atom a) .ne) t' <;> simp
  unfold antiSupport at h1
  cases hA : antiSupport M worlds (.atom a) t'
  · exfalso
    rw [hA, Bool.false_or] at h1
    unfold antiSupport at h1 hA
    have := team_all_of_isEmpty t' (fun w => !M.valuation a w) worlds h1
    rw [this] at hA
    simp at hA
  · rfl

/-- Anti-support of enriched atom disjunction implies anti-support of right atom. -/
private lemma antiSupport_enriched_disj_implies_right {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (a b : String) (t' : Team W) (worlds : List W)
    (h : antiSupport M worlds (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) t' = true) :
    antiSupport M worlds (.atom b) t' = true := by
  unfold antiSupport at h
  have h1 : antiSupport M worlds (.conj (.atom b) .ne) t' = true := by
    revert h; cases antiSupport M worlds (.conj (.atom b) .ne) t' <;> simp_all
  unfold antiSupport at h1
  cases hB : antiSupport M worlds (.atom b) t'
  · exfalso
    rw [hB, Bool.false_or] at h1
    unfold antiSupport at h1 hB
    have := team_all_of_isEmpty t' (fun w => !M.valuation b w) worlds h1
    rw [this] at hB
    simp at hB
  · rfl

/-- Anti-support monotonicity for ◇: if anti-support of φ implies anti-support of ψ
    pointwise over teams, then anti-support of ◇φ implies anti-support of ◇ψ. -/
private lemma antiSupport_poss_weaken {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (φ ψ : BSMLFormula W) (t : Team W) (worlds : List W)
    (hmono : ∀ t' : Team W, antiSupport M worlds φ t' = true → antiSupport M worlds ψ t' = true)
    (h : antiSupport M worlds (.poss φ) t = true) :
    antiSupport M worlds (.poss ψ) t = true := by
  unfold antiSupport at h ⊢
  exact team_all_mono t _ _ worlds (fun w hw => by
    exact list_all_mono (generateSubteams (M.access w) worlds) _ _ (fun t' ht' => by
      cases he : t'.isEmpty worlds
      · simp only [he, Bool.false_or] at ht' ⊢
        exact hmono t' ht'
      · simp
    ) hw
  ) h

-- ============================================================================
-- PART 6f: Infrastructure for Positive Free Choice Proofs
-- ============================================================================

/-- The empty list is always in allSubsets -/
private lemma nil_mem_allSubsets {α : Type*} (l : List α) : [] ∈ allSubsets l := by
  induction l with
  | nil => simp [allSubsets]
  | cons _ as ih => simp only [allSubsets, List.mem_append]; left; exact ih

/-- A singleton is in allSubsets when the element is in the list -/
private lemma singleton_mem_allSubsets {α : Type*} [DecidableEq α] (l : List α) (x : α)
    (hx : x ∈ l) : [x] ∈ allSubsets l := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    simp only [allSubsets, List.mem_append]
    cases hx with
    | head => right; exact List.mem_map.mpr ⟨[], nil_mem_allSubsets as, rfl⟩
    | tail _ hx => left; exact ih hx

/-- Members of a split's right part are in the original team -/
private lemma split_right_mem {W : Type*} [DecidableEq W]
    (t t1 t2 : Team W) (worlds : List W)
    (hmem : (t1, t2) ∈ generateSplits t worlds)
    (v : W) (ht2v : t2 v = true) : t v = true := by
  simp only [generateSplits, List.mem_map] at hmem
  obtain ⟨left, _, heq⟩ := hmem
  have ht2_eq : t2 = (λ w => t w && !(Team.ofList left w)) := (Prod.ext_iff.mp heq).2.symm
  rw [ht2_eq] at ht2v
  simp only [Bool.and_eq_true] at ht2v; exact ht2v.1

/-- Members of a subteam are in the original team -/
private lemma subteam_mem {W : Type*} [DecidableEq W]
    (t s : Team W) (worlds : List W)
    (hs : s ∈ generateSubteams t worlds)
    (v : W) (hsv : s v = true) : t v = true := by
  simp only [generateSubteams, List.mem_map] at hs
  obtain ⟨sub, hsub, rfl⟩ := hs
  simp only [Team.ofList] at hsv
  have hv_in_sub : v ∈ sub := List.mem_of_elem_eq_true hsv
  have hv_in_toList := mem_of_mem_allSubsets _ _ hsub v hv_in_sub
  simp only [Team.toList, List.mem_filter] at hv_in_toList
  exact hv_in_toList.2

/-- A singleton team for v is in generateSubteams when v is in the team -/
private lemma singleton_in_generateSubteams {W : Type*} [DecidableEq W]
    (t : Team W) (worlds : List W) (v : W)
    (hv : v ∈ worlds) (htv : t v = true) :
    Team.ofList [v] ∈ generateSubteams t worlds := by
  simp only [generateSubteams, List.mem_map]
  exact ⟨[v], singleton_mem_allSubsets _ v
    (by simp [Team.toList, List.mem_filter, hv, htv]), rfl⟩

/-- Singleton team is non-empty -/
private lemma singleton_isNonEmpty {W : Type*} [DecidableEq W]
    (v : W) (worlds : List W) (hv : v ∈ worlds) :
    (Team.ofList [v]).isNonEmpty worlds = true := by
  simp only [Team.isNonEmpty, List.any_eq_true]
  exact ⟨v, hv, by simp [Team.ofList]⟩

/-- Singleton team supports an atom when the valuation holds at that world -/
private lemma singleton_support_atom {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (p : String) (v : W) (worlds : List W)
    (hv : v ∈ worlds) (hval : M.valuation p v = true) :
    support M worlds (.atom p) (Team.ofList [v]) = true := by
  unfold support Team.all
  apply List.all_eq_true.mpr
  intro w hw
  cases hm : Team.ofList [v] w
  · simp
  · simp only [Bool.not_true, Bool.false_or]
    simp only [Team.ofList] at hm
    have hv_eq := List.mem_of_elem_eq_true hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_eq
    subst hv_eq; exact hval

/-- If v is accessible from w and satisfies atom p, the ◇p subteams.any condition holds
    (via singleton subteam witness) -/
private lemma poss_atom_witness {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (p : String) (worlds : List W) (w v : W)
    (hv : v ∈ worlds) (hacc : M.access w v = true) (hval : M.valuation p v = true) :
    (generateSubteams (M.access w) worlds).any
      (λ t' => t'.isNonEmpty worlds && support M worlds (.atom p) t') = true := by
  apply List.any_eq_true.mpr
  refine ⟨Team.ofList [v],
    singleton_in_generateSubteams (M.access w) worlds v hv hacc, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨singleton_isNonEmpty v worlds hv, singleton_support_atom M p v worlds hv hval⟩

/-- From s ⊨ (atom p) ∧ NE, extract a world witness with membership and valuation -/
private lemma atom_witness_of_enriched_conj {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (p : String) (s : Team W) (worlds : List W)
    (h : support M worlds (.conj (.atom p) .ne) s = true) :
    ∃ v ∈ worlds, s v = true ∧ M.valuation p v = true := by
  unfold support at h
  simp only [Bool.and_eq_true] at h
  have hs := h.1; have hne_raw := h.2
  unfold support at hne_raw
  simp only [Team.isNonEmpty, List.any_eq_true] at hne_raw
  obtain ⟨v, hv, hsv⟩ := hne_raw
  refine ⟨v, hv, hsv, ?_⟩
  unfold support Team.all at hs
  simp only [List.all_eq_true] at hs
  have := hs v hv
  simp only [hsv, Bool.not_true, Bool.false_or] at this
  exact this

/-- From s ⊨ (a ∧ NE) ∨ (b ∧ NE), extract witnesses for both atoms in s.
    The split gives s₁ ⊨ a ∧ NE and s₂ ⊨ b ∧ NE; witnesses are lifted to s
    via split membership. -/
private lemma both_witnesses_of_enriched_disj {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (a b : String) (s : Team W) (worlds : List W)
    (h : support M worlds (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) s = true) :
    (∃ va ∈ worlds, s va = true ∧ M.valuation a va = true) ∧
    (∃ vb ∈ worlds, s vb = true ∧ M.valuation b vb = true) := by
  unfold support at h
  obtain ⟨⟨s1, s2⟩, hsplit, hboth⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hboth
  obtain ⟨va, hva_w, hva_s1, hva_val⟩ := atom_witness_of_enriched_conj M a s1 worlds hboth.1
  obtain ⟨vb, hvb_w, hvb_s2, hvb_val⟩ := atom_witness_of_enriched_conj M b s2 worlds hboth.2
  exact ⟨⟨va, hva_w, split_left_mem s s1 s2 worlds hsplit va hva_s1, hva_val⟩,
         ⟨vb, hvb_w, split_right_mem s s1 s2 worlds hsplit vb hvb_s2, hvb_val⟩⟩

/-- Team.beq gives pointwise equality -/
private lemma team_beq_apply {W : Type*} (t1 t2 : Team W) (worlds : List W) (w : W)
    (hbeq : t1.beq t2 worlds = true) (hw : w ∈ worlds) : t1 w = t2 w := by
  unfold Team.beq at hbeq
  simp only [List.all_eq_true] at hbeq
  exact beq_iff_eq.mp (hbeq w hw)

/-- Indisputability transfers accessibility: if w₁, w₂ ∈ t and R is indisputable,
    then M.access w₁ v = true → M.access w₂ v = true -/
private lemma indisputable_access_transfer {W : Type*} [DecidableEq W]
    (M : BSMLModel W) (t : Team W) (worlds : List W) (w₁ w₂ v : W)
    (hInd : M.isIndisputable t worlds = true)
    (hw₁ : w₁ ∈ worlds) (htw₁ : t w₁ = true)
    (hw₂ : w₂ ∈ worlds) (htw₂ : t w₂ = true)
    (hv : v ∈ worlds)
    (hacc : M.access w₁ v = true) :
    M.access w₂ v = true := by
  unfold BSMLModel.isIndisputable at hInd
  have hw₁_mem : w₁ ∈ t.toList worlds := by
    simp [Team.toList, List.mem_filter, hw₁, htw₁]
  have hw₂_mem : w₂ ∈ t.toList worlds := by
    simp [Team.toList, List.mem_filter, hw₂, htw₂]
  cases hmem : t.toList worlds with
  | nil => rw [hmem] at hw₁_mem; simp at hw₁_mem
  | cons w rest =>
    rw [hmem] at hw₁_mem hw₂_mem hInd
    simp only [List.all_eq_true] at hInd
    have hbeq₁ : (M.access w).beq (M.access w₁) worlds = true := by
      cases hw₁_mem with
      | head =>
        unfold Team.beq; simp only [List.all_eq_true]; intro w' _; exact beq_self_eq_true _
      | tail _ h => exact hInd w₁ h
    have hbeq₂ : (M.access w).beq (M.access w₂) worlds = true := by
      cases hw₂_mem with
      | head =>
        unfold Team.beq; simp only [List.all_eq_true]; intro w' _; exact beq_self_eq_true _
      | tail _ h => exact hInd w₂ h
    rw [← team_beq_apply _ _ worlds v hbeq₂ hv,
        team_beq_apply _ _ worlds v hbeq₁ hv]
    exact hacc

-- ============================================================================
-- PART 7: Free Choice Theorems
-- ============================================================================

/-!
## Why FC Requires Atomic Formulas

The FC theorems below are restricted to atomic α and β. The general version
(for arbitrary BSMLFormula) is FALSE: enrichment [φ]⁺ does not entail φ
for formulas containing □ under negation, because the NE added by enrichment
creates "escape hatches" via empty accessibility sets.

**Counterexample**: α = ¬□□q. On a team {w} where σ(w) = ∅ (empty accessibility):
- [¬□□q]⁺ is supported: the enrichment's anti-support of □ escapes via
  `antiSupport (X ∧ NE) ∅ = ... || ∅.isEmpty = true`
- But ¬□□q is NOT supported: `antiSupport (□q) ∅ = ∅.any (...) = false`

This means the hypothesis of narrowScopeFC can be satisfied while the conclusion
fails, when α contains □ under negation.

For propositional atoms (the paper's intended application), [p]⁺ = p ∧ NE trivially
entails p, so the FC derivation goes through.
-/

/-- Counterexample worlds: w0 has non-empty accessibility (to w1, w2), others have empty -/
private inductive CexWorld where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr

private def cexWorlds : List CexWorld := [.w0, .w1, .w2, .w3]

/-- Counterexample model: w0 accesses {w1, w2}; w1, w2, w3 have empty accessibility -/
private def cexModel : BSMLModel CexWorld where
  access := λ w => match w with
    | .w0 => λ w' => w' == .w1 || w' == .w2
    | _ => λ _ => false
  valuation := λ p w => match p with
    | "p" => w == .w1 || w == .w2
    | _ => false

/-- The general narrowScopeFC is false: ¬□□q creates a gap between enriched
    and original support when accessible worlds have empty accessibility.

    Hypothesis: support (enrich (◇(¬□□q ∨ p))) {w0} = true
    but support (◇(¬□□q)) {w0} = false. -/
theorem narrowScopeFC_false_for_general_formulas :
    support cexModel cexWorlds
      (enrich (.poss (.disj (.neg (.nec (.nec (.atom "q")))) (.atom "p"))))
      (λ w => w == .w0) = true ∧
    support cexModel cexWorlds
      (.poss (.neg (.nec (.nec (.atom "q")))))
      (λ w => w == .w0) = false := by native_decide

/--
Narrow-scope Free Choice: [◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β (for atomic α, β)

Restricted to atoms because [φ]⁺ |= φ fails for general formulas
(see `narrowScopeFC_false_for_general_formulas`).

For atoms the proof is: the split gives s₁ ⊨ [α]⁺ = α ∧ NE, so s₁ ⊨ α
by conjunction elimination. Since s₁ is non-empty and a subteam of σ(w),
it witnesses ◇α.
-/
theorem narrowScopeFC {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (a b : String) (t : Team W) (worlds : List W)
    (h : support M worlds (enrich (.poss (.disj (.atom a) (.atom b)))) t = true) :
    support M worlds (.poss (.atom a)) t = true ∧
    support M worlds (.poss (.atom b)) t = true := by
  simp only [enrich] at h
  unfold support at h
  have hPoss : support M worlds
    (.poss (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne))) t = true := by
    revert h; cases support M worlds _ t <;> simp
  unfold support at hPoss ⊢
  unfold Team.all at hPoss ⊢
  constructor
  · apply List.all_eq_true.mpr
    intro w hw
    have hfw := (List.all_eq_true.mp hPoss) w hw
    cases ht : t w
    · simp
    · simp only [ht, Bool.not_true, Bool.false_or] at hfw ⊢
      obtain ⟨s, hs_mem, hs_supp⟩ := List.any_eq_true.mp hfw
      have hsupp : support M worlds
          (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) s = true := by
        revert hs_supp; cases support M worlds _ s <;> simp_all
      obtain ⟨⟨va, hva_w, hva_s, hva_val⟩, _⟩ :=
        both_witnesses_of_enriched_disj M a b s worlds hsupp
      have hva_acc := subteam_mem (M.access w) s worlds hs_mem va hva_s
      exact poss_atom_witness M a worlds w va hva_w hva_acc hva_val
  · apply List.all_eq_true.mpr
    intro w hw
    have hfw := (List.all_eq_true.mp hPoss) w hw
    cases ht : t w
    · simp
    · simp only [ht, Bool.not_true, Bool.false_or] at hfw ⊢
      obtain ⟨s, hs_mem, hs_supp⟩ := List.any_eq_true.mp hfw
      have hsupp : support M worlds
          (.disj (.conj (.atom a) .ne) (.conj (.atom b) .ne)) s = true := by
        revert hs_supp; cases support M worlds _ s <;> simp_all
      obtain ⟨_, ⟨vb, hvb_w, hvb_s, hvb_val⟩⟩ :=
        both_witnesses_of_enriched_disj M a b s worlds hsupp
      have hvb_acc := subteam_mem (M.access w) s worlds hs_mem vb hvb_s
      exact poss_atom_witness M b worlds w vb hvb_w hvb_acc hvb_val

/--
Wide-scope Free Choice: [◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β (for atomic α, β with indisputable R)

The split gives t₁ ⊨ [◇α]⁺ = ◇(a ∧ NE) ∧ NE and t₂ ⊨ [◇β]⁺.
Indisputability (R[w] = R[v] for all w, v ∈ t) allows extending
the ◇ witness from t₁ to all of t.
-/
theorem wideScopeFC {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (a b : String) (t : Team W) (worlds : List W)
    (hInd : M.isIndisputable t worlds = true)
    (h : support M worlds (enrich (.disj (.poss (.atom a)) (.poss (.atom b)))) t = true) :
    support M worlds (.poss (.atom a)) t = true ∧
    support M worlds (.poss (.atom b)) t = true := by
  simp only [enrich] at h
  -- Extract the split: t₁ ⊨ ◇(a ∧ NE) ∧ NE, t₂ ⊨ ◇(b ∧ NE) ∧ NE
  unfold support at h
  obtain ⟨⟨t1, t2⟩, hsplit, hboth⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hboth
  obtain ⟨ht1_full, ht2_full⟩ := hboth
  unfold support at ht1_full ht2_full
  simp only [Bool.and_eq_true] at ht1_full ht2_full
  obtain ⟨ht1_poss, ht1_ne_raw⟩ := ht1_full
  obtain ⟨ht2_poss, ht2_ne_raw⟩ := ht2_full
  unfold support at ht1_ne_raw ht2_ne_raw
  -- Pick w₁ ∈ t₁, w₂ ∈ t₂ (from non-emptiness)
  simp only [Team.isNonEmpty, List.any_eq_true] at ht1_ne_raw ht2_ne_raw
  obtain ⟨w₁, hw₁_w, htw₁⟩ := ht1_ne_raw
  obtain ⟨w₂, hw₂_w, htw₂⟩ := ht2_ne_raw
  have htw₁_t : t w₁ = true := split_left_mem t t1 t2 worlds hsplit w₁ htw₁
  have htw₂_t : t w₂ = true := split_right_mem t t1 t2 worlds hsplit w₂ htw₂
  -- From ◇(a ∧ NE) at w₁: extract accessible va with M.valuation a va
  unfold support Team.all at ht1_poss
  have hw₁_entry := (List.all_eq_true.mp ht1_poss) w₁ hw₁_w
  simp only [htw₁, Bool.not_true, Bool.false_or] at hw₁_entry
  obtain ⟨s_a, hs_a_mem, hs_a_supp⟩ := List.any_eq_true.mp hw₁_entry
  have hs_a_support : support M worlds (.conj (.atom a) .ne) s_a = true := by
    revert hs_a_supp; cases support M worlds _ s_a <;> simp_all
  obtain ⟨va, hva_w, hva_sa, hva_val⟩ := atom_witness_of_enriched_conj M a s_a worlds hs_a_support
  have hva_acc_w₁ : M.access w₁ va = true :=
    subteam_mem (M.access w₁) s_a worlds hs_a_mem va hva_sa
  -- From ◇(b ∧ NE) at w₂: extract accessible vb with M.valuation b vb
  unfold support Team.all at ht2_poss
  have hw₂_entry := (List.all_eq_true.mp ht2_poss) w₂ hw₂_w
  simp only [htw₂, Bool.not_true, Bool.false_or] at hw₂_entry
  obtain ⟨s_b, hs_b_mem, hs_b_supp⟩ := List.any_eq_true.mp hw₂_entry
  have hs_b_support : support M worlds (.conj (.atom b) .ne) s_b = true := by
    revert hs_b_supp; cases support M worlds _ s_b <;> simp_all
  obtain ⟨vb, hvb_w, hvb_sb, hvb_val⟩ := atom_witness_of_enriched_conj M b s_b worlds hs_b_support
  have hvb_acc_w₂ : M.access w₂ vb = true :=
    subteam_mem (M.access w₂) s_b worlds hs_b_mem vb hvb_sb
  -- Prove both ◇a and ◇b for all of t using indisputability
  unfold support
  unfold Team.all
  constructor
  · apply List.all_eq_true.mpr
    intro w hw
    cases htw : t w
    · simp
    · simp only [Bool.not_true, Bool.false_or]
      exact poss_atom_witness M a worlds w va hva_w
        (indisputable_access_transfer M t worlds w₁ w va hInd hw₁_w htw₁_t hw htw hva_w hva_acc_w₁)
        hva_val
  · apply List.all_eq_true.mpr
    intro w hw
    cases htw : t w
    · simp
    · simp only [Bool.not_true, Bool.false_or]
      exact poss_atom_witness M b worlds w vb hvb_w
        (indisputable_access_transfer M t worlds w₂ w vb hInd hw₂_w htw₂_t hw htw hvb_w hvb_acc_w₂)
        hvb_val

/--
Dual Prohibition: [¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β (for atomic α, β)

This uses anti-support, which is conjunction for disjunction (no split!).
For atoms, anti-support of the enriched disjunction implies anti-support
of each atom individually, because anti-support of (p ∧ NE) on non-empty
teams reduces to anti-support of p.
-/
theorem dualProhibition {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (a b : String) (t : Team W) (worlds : List W)
    (h : support M worlds (enrich (.neg (.poss (.disj (.atom a) (.atom b))))) t = true) :
    support M worlds (.neg (.poss (.atom a))) t = true ∧
    support M worlds (.neg (.poss (.atom b))) t = true := by
  simp only [enrich] at h
  unfold support at h
  have hNeg : support M worlds
    ((((BSMLFormula.atom a).conj BSMLFormula.ne).disj
      ((BSMLFormula.atom b).conj BSMLFormula.ne)).poss.conj BSMLFormula.ne).neg t = true := by
    revert h; cases support M worlds _ t <;> simp
  have hNE : support M worlds BSMLFormula.ne t = true := by
    revert h; cases support M worlds BSMLFormula.ne t <;> simp_all
  unfold support at hNeg
  unfold antiSupport at hNeg
  unfold support at hNE
  have hNotEmpty : antiSupport M worlds BSMLFormula.ne t = false := by
    unfold antiSupport
    simp only [Team.isEmpty, Team.isNonEmpty] at *
    simp [hNE]
  rw [hNotEmpty, Bool.or_false] at hNeg
  unfold support
  constructor
  · exact antiSupport_poss_weaken M _ _ t worlds
      (fun t' => antiSupport_enriched_disj_implies_left M a b t' worlds) hNeg
  · exact antiSupport_poss_weaken M _ _ t worlds
      (fun t' => antiSupport_enriched_disj_implies_right M a b t' worlds) hNeg

-- ============================================================================
-- PART 7b: Key Lemmas for Free Choice Proofs
-- ============================================================================

/-- Anti-support of disjunction is conjunction of anti-supports -/
lemma antiSupport_disj {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula W) (t : Team W) (worlds : List W) :
    antiSupport M worlds (.disj φ ψ) t =
    (antiSupport M worlds φ t && antiSupport M worlds ψ t) := by
  simp only [antiSupport]

/-- Support of negation is anti-support of formula -/
lemma support_neg {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula W) (t : Team W) (worlds : List W) :
    support M worlds (.neg φ) t = antiSupport M worlds φ t := by
  simp only [support]

/-- Anti-support of negation is support of formula -/
lemma antiSupport_neg {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula W) (t : Team W) (worlds : List W) :
    antiSupport M worlds (.neg φ) t = support M worlds φ t := by
  simp only [antiSupport]

/-- Support of conjunction requires both conjuncts supported -/
lemma support_conj {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ ψ : BSMLFormula W) (t : Team W) (worlds : List W) :
    support M worlds (.conj φ ψ) t =
    (support M worlds φ t && support M worlds ψ t) := by
  simp only [support]

/-- Empty team supports all atoms (ex falso / vacuous truth) -/
lemma empty_supports_atom {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (p : String) (worlds : List W) :
    support M worlds (.atom p) Team.empty = true := by
  simp only [support, Team.all, Team.empty]
  induction worlds with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.all_cons, Bool.not_false, Bool.true_or, Bool.true_and]
      exact ih

-- ============================================================================
-- PART 8: Example: Permission Disjunction
-- ============================================================================

/--
Example world type for "You may have coffee or tea"
-/
inductive PermissionWorld where
  | neither : PermissionWorld
  | onlyCoffee : PermissionWorld
  | onlyTea : PermissionWorld
  | both : PermissionWorld
  deriving DecidableEq, Repr

/-- The proposition "coffee is permitted" -/
def coffeePermitted : PermissionWorld -> Bool
  | .onlyCoffee => true
  | .both => true
  | _ => false

/-- The proposition "tea is permitted" -/
def teaPermitted : PermissionWorld -> Bool
  | .onlyTea => true
  | .both => true
  | _ => false

/-- All permission worlds -/
def permissionWorlds : List PermissionWorld :=
  [.neither, .onlyCoffee, .onlyTea, .both]

/-- Deontic model: universal accessibility -/
def deonticModel : BSMLModel PermissionWorld where
  access := λ _ => Team.full
  valuation := λ p w =>
    match p with
    | "coffee" => coffeePermitted w
    | "tea" => teaPermitted w
    | _ => false

/-- The formula ◇(coffee ∨ tea) -/
def mayHaveCoffeeOrTea : BSMLFormula PermissionWorld :=
  .poss (.disj (.atom "coffee") (.atom "tea"))

/-- Team representing "free choice holds" (both options available) -/
def freeChoiceTeam : Team PermissionWorld :=
  λ w => w == .both || w == .onlyCoffee || w == .onlyTea

-- Verify: the enriched formula supports free choice inference
#eval support deonticModel permissionWorlds (enrich mayHaveCoffeeOrTea) freeChoiceTeam

-- The free choice consequences
def mayCoffee : BSMLFormula PermissionWorld := .poss (.atom "coffee")
def mayTea : BSMLFormula PermissionWorld := .poss (.atom "tea")

#eval support deonticModel permissionWorlds mayCoffee freeChoiceTeam
#eval support deonticModel permissionWorlds mayTea freeChoiceTeam

-- ============================================================================
-- PART 8b: Computational Verification of Free Choice Theorems
-- ============================================================================

-- Verify NARROW-SCOPE FC: [◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β
-- The enriched formula implies both ◇coffee and ◇tea are supported
#eval
  let enriched := enrich mayHaveCoffeeOrTea
  let supEnriched := support deonticModel permissionWorlds enriched freeChoiceTeam
  let supCoffee := support deonticModel permissionWorlds mayCoffee freeChoiceTeam
  let supTea := support deonticModel permissionWorlds mayTea freeChoiceTeam
  -- If enriched is supported, then both consequences should be
  (supEnriched, supCoffee, supTea)  -- Expect: (true, true, true)

-- Verify DUAL PROHIBITION: [¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β
-- When prohibition is enriched, both individual prohibitions follow
-- NOTE: Dual prohibition requires RESTRICTED accessibility (not universal)
-- In a prohibition context, accessible worlds are only those where nothing is permitted

/-- Restrictive deontic model: from 'neither', only 'neither' is accessible -/
def restrictiveModel : BSMLModel PermissionWorld where
  access := λ w =>
    match w with
    | .neither => λ w' => w' == .neither  -- Only 'neither' accessible
    | _ => Team.full  -- Other worlds have full access (for free choice)
  valuation := λ p w =>
    match p with
    | "coffee" => coffeePermitted w
    | "tea" => teaPermitted w
    | _ => false

def prohibition : BSMLFormula PermissionWorld :=
  .neg (.poss (.disj (.atom "coffee") (.atom "tea")))

def notMayCoffee : BSMLFormula PermissionWorld := .neg (.poss (.atom "coffee"))
def notMayTea : BSMLFormula PermissionWorld := .neg (.poss (.atom "tea"))

-- Team where neither is permitted (with restricted accessibility)
def prohibitionTeam : Team PermissionWorld :=
  λ w => w == .neither

#eval
  let enrichedProhib := enrich prohibition
  let supProhib := support restrictiveModel permissionWorlds enrichedProhib prohibitionTeam
  let supNotCoffee := support restrictiveModel permissionWorlds notMayCoffee prohibitionTeam
  let supNotTea := support restrictiveModel permissionWorlds notMayTea prohibitionTeam
  -- Dual prohibition: enriched ¬◇(α∨β) implies ¬◇α and ¬◇β
  (supProhib, supNotCoffee, supNotTea)  -- Expect: (true, true, true)

-- Verify WIDE-SCOPE FC: [◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β (with universal R)
def wideScopeDisj : BSMLFormula PermissionWorld :=
  .disj (.poss (.atom "coffee")) (.poss (.atom "tea"))

#eval
  let enrichedWide := enrich wideScopeDisj
  let supWide := support deonticModel permissionWorlds enrichedWide freeChoiceTeam
  let supCoffee := support deonticModel permissionWorlds mayCoffee freeChoiceTeam
  let supTea := support deonticModel permissionWorlds mayTea freeChoiceTeam
  -- Wide-scope FC with universal R (indisputable)
  (supWide, supCoffee, supTea)  -- Expect: (true, true, true)

-- Verify indisputability of the deontic model
#eval deonticModel.isIndisputable freeChoiceTeam permissionWorlds  -- Expect: true

-- ============================================================================
-- PART 9: Comparison with BUS
-- ============================================================================

/-!
## BSML vs BUS: Parallel Structure, Different Mechanisms

Both BSML and BUS are bilateral semantic frameworks that derive free choice,
but they differ in key ways:

### Shared Properties
1. **Bilateral**: Both have positive and negative dimensions
2. **DNE**: Both get double negation elimination from swapping dimensions
3. **FC derivation**: Both derive FC semantically (not pragmatically)
4. **Dual prohibition**: Both derive ¬◇(α∨β) ⊨ ¬◇α ∧ ¬◇β

### Key Differences

| Aspect | BSML | BUS |
|--------|------|-----|
| **Semantics** | Static (support relation) | Dynamic (update functions) |
| **State** | Team = Set World | InfoState = Set (World × Assignment) |
| **Disjunction** | Split (partition team) | Union (combine updates) |
| **FC source** | NE forces both parts non-empty | Precondition forces both contribute |
| **Anaphora** | Not addressed | Primary motivation |
| **Assignments** | No | Yes (discourse referents) |

### When to Use Which

- **BSML**: When you want static team semantics, connection to dependence logic
- **BUS**: When you need cross-disjunct anaphora (bathroom sentences)
-/

/-- Comparison data structure -/
structure BSMLvsBUS where
  aspect : String
  bsml : String
  bus : String
  deriving Repr

def comparisonTable : List BSMLvsBUS :=
  [ { aspect := "Semantics type"
    , bsml := "Static (support relations)"
    , bus := "Dynamic (update functions)" }
  , { aspect := "State representation"
    , bsml := "Team = Set World"
    , bus := "InfoState = Set (World × Assignment)" }
  , { aspect := "Bilateral structure"
    , bsml := "Support / anti-support"
    , bus := "Positive / negative updates" }
  , { aspect := "DNE mechanism"
    , bsml := "Swap support (definitional)"
    , bus := "Swap updates (definitional)" }
  , { aspect := "Disjunction"
    , bsml := "Split (partition team)"
    , bus := "Union (combine updates)" }
  , { aspect := "FC mechanism"
    , bsml := "NE enrichment forces non-empty parts"
    , bus := "Modal ∨ precondition forces both contribute" }
  , { aspect := "Cross-disjunct anaphora"
    , bsml := "Not addressed"
    , bus := "Primary motivation (bathroom sentences)" }
  ]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## Summary: Aloni (2022) BSML

### The Derivation Structure

Free choice is DERIVED from three independent principles:

```
        PRINCIPLE 1              PRINCIPLE 2              PRINCIPLE 3
     Split Disjunction      +   NE Enrichment      +     NE Non-Flat
            │                        │                        │
            └────────────────────────┼────────────────────────┘
                                     │
                                     ▼
                    enriched_split_forces_both_nonempty
                    "Both parts of split must be non-empty"
                                     │
                                     ▼
                              FREE CHOICE
                    "Both alternatives are live"
```

### Key Lemmas (The Real Work)

1. **ne_not_flat**: NE is NOT flat (downward closed)
   - This is WHY enrichment matters - empty teams fail NE

2. **enriched_support_implies_nonempty**: Enriched formulas force non-empty teams
   - This is HOW enrichment propagates non-emptiness

3. **enriched_split_forces_both_nonempty**: THE CORE LEMMA
   - Combines split disjunction + enrichment + non-flatness
   - Derives that both parts of any split must be non-empty

4. **antiSupport_disj_is_conj**: Anti-support of ∨ is ∧ (no split!)
   - This is WHY dual prohibition works differently

### The Structural Asymmetry

| Operation | Support | Anti-support |
|-----------|---------|--------------|
| Disjunction | SPLIT (existential) | CONJUNCTION (universal) |
| Result | Both parts can be non-empty | Both must fail |
| FC consequence | Both alternatives live | Both prohibited |

### Main Results
- **Narrow-scope FC**: [◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β
- **Wide-scope FC**: [◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β (with indisputable R)
- **Dual prohibition**: [¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β

### Position in FC Landscape
BSML is a **semantic** approach to free choice, deriving FC from the meaning
of enriched formulas rather than from pragmatic reasoning. It shares bilateral
structure with BUS but uses static team semantics rather than dynamic updates.

### Limitations
- Does not handle cross-disjunct anaphora (unlike BUS)
- Requires pragmatic enrichment [·]⁺ for FC (not pure semantics)
- Computational complexity of split disjunction

### References
- Aloni (2022). Logic and conversation: The case of free choice. S&P 15.
- Aloni, Anttila & Yang (2024). State-based Modal Logics for Free Choice.
-/

end Phenomena.Modality.Aloni2022
