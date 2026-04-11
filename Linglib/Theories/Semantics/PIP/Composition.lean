import Linglib.Theories.Semantics.PIP.Expr

/-!
# PIP Compositional Operations

@cite{abney-keshet-2025}

Compositional building blocks for PIP beyond the core formula language `PIPExprF`.
Where `PIPExprF` gives truth and felicity for formulas (type t), this file defines
operations whose output is a **set** of individuals (type e): sigma evaluation
(Σxφ), set-based generalized quantifiers (EVERY/SOME), three-argument modals with
explicit modal bases, the FX type-lifting operation for restricted variables, and
the simple/summation pronoun distinction.

These operations correspond to the Glossa paper's enrichment of the S&P formulation
(@cite{keshet-abney-2024}), making PIP's set-based compositional interface explicit.

## Key Design Decision

Sigma evaluation produces a `Set D`, not a `PIPExprF W D`. This is because Σxφ
denotes the set of satisfiers of φ (a semantic object of type e), not a truth
value (type t). It is therefore defined externally from the `PIPExprF` inductive
type and connected to it via bridge theorems.
-/

namespace Semantics.PIP

open Core.ModalLogic (AccessRel)
open Core.Proposition (FiniteWorlds)


-- ============================================================
-- §1: Sigma Evaluation (paper items 25–27)
-- ============================================================

section Sigma

variable {W D : Type*} [FiniteDomain D] [FiniteWorlds W]

/--
Sigma evaluation: Σxφ = {d ∈ D | ⟦φ(d)⟧^w = 1}.

Collects all individuals satisfying a formula body at a given world.
The output is a `Set D` (type e), not a formula (type t). This is the
fundamental bridge between PIP's formula language and its set-based
compositional interface.
-/
def sigmaEval (body : D → PIPExprF W D) (w : W) : Set D :=
  { d | (body d).truth w = true }

@[simp]
theorem sigmaEval_mem (body : D → PIPExprF W D) (w : W) (d : D) :
    d ∈ sigmaEval body w ↔ (body d).truth w = true :=
  Iff.rfl

/-- ∃xφ is true iff the sigma set is nonempty. -/
theorem exists_iff_sigma_nonempty (body : D → PIPExprF W D) (w : W) :
    (PIPExprF.exists_ body).truth w = true ↔ (sigmaEval body w).Nonempty := by
  simp only [PIPExprF.truth, sigmaEval, Set.Nonempty, Set.mem_setOf_eq]
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨d, _, hd⟩ := h
    exact ⟨d, hd⟩
  · intro ⟨d, hd⟩
    rw [List.any_eq_true]
    exact ⟨d, FiniteDomain.complete d, hd⟩

/-- ∀xφ is true iff every individual is in the sigma set. -/
theorem forall_iff_sigma_univ (body : D → PIPExprF W D) (w : W) :
    (PIPExprF.forall_ body).truth w = true ↔ sigmaEval body w = Set.univ := by
  simp only [PIPExprF.truth, sigmaEval, Set.eq_univ_iff_forall, Set.mem_setOf_eq]
  constructor
  · intro h d
    rw [List.all_eq_true] at h
    exact h d (FiniteDomain.complete d)
  · intro h
    rw [List.all_eq_true]
    intro d _
    exact h d

/-- Σx(φ ∧ ψ) = Σxφ ∩ Σxψ. -/
theorem sigmaEval_conj (φ ψ : D → PIPExprF W D) (w : W) :
    sigmaEval (λ d => PIPExprF.conj (φ d) (ψ d)) w =
    sigmaEval φ w ∩ sigmaEval ψ w := by
  ext d
  simp only [sigmaEval, Set.mem_setOf_eq, Set.mem_inter_iff]
  show ((φ d).truth w && (ψ d).truth w) = true ↔ (φ d).truth w = true ∧ (ψ d).truth w = true
  simp only [Bool.and_eq_true]

/-- Σx(φ ∨ ψ) = Σxφ ∪ Σxψ. -/
theorem sigmaEval_disj (φ ψ : D → PIPExprF W D) (w : W) :
    sigmaEval (λ d => PIPExprF.disj (φ d) (ψ d)) w =
    sigmaEval φ w ∪ sigmaEval ψ w := by
  ext d
  simp only [sigmaEval, Set.mem_setOf_eq, Set.mem_union]
  show ((φ d).truth w || (ψ d).truth w) = true ↔ (φ d).truth w = true ∨ (ψ d).truth w = true
  simp only [Bool.or_eq_true]

/-- Σx(¬φ) = (Σxφ)ᶜ. -/
theorem sigmaEval_neg (φ : D → PIPExprF W D) (w : W) :
    sigmaEval (λ d => PIPExprF.neg (φ d)) w = (sigmaEval φ w)ᶜ := by
  ext d
  simp only [sigmaEval, Set.mem_setOf_eq, Set.mem_compl_iff]
  show (!(φ d).truth w) = true ↔ ¬((φ d).truth w = true)
  cases (φ d).truth w <;> simp

/-- Σx(⊤) = D (everything satisfies a tautology). -/
theorem sigmaEval_true (w : W) :
    sigmaEval (D := D) (λ _ => PIPExprF.pred (λ _ => true)) w = Set.univ := by
  ext d; simp only [sigmaEval, Set.mem_setOf_eq, Set.mem_univ, iff_true]; rfl

/-- Σx(⊥) = ∅ (nothing satisfies a contradiction). -/
theorem sigmaEval_false (w : W) :
    sigmaEval (D := D) (λ _ => PIPExprF.pred (λ _ => false)) w = ∅ := by
  ext d; simp only [sigmaEval, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact
    Bool.false_ne_true

/-- Label definitions are truth-transparent for sigma. -/
theorem sigmaEval_labelDef (α : FLabel) (φ : D → PIPExprF W D) (w : W) :
    sigmaEval (λ d => PIPExprF.labelDef α (φ d)) w = sigmaEval φ w := by
  ext d; show (φ d).truth w = true ↔ (φ d).truth w = true; exact Iff.rfl

/-- Presuppositions are truth-transparent for sigma. -/
theorem sigmaEval_presup (φ : D → PIPExprF W D) (ψ : W → Bool) (w : W) :
    sigmaEval (λ d => PIPExprF.presup (φ d) ψ) w = sigmaEval φ w := by
  ext d; show (φ d).truth w = true ↔ (φ d).truth w = true; exact Iff.rfl

end Sigma


-- ============================================================
-- §2: Set-Based Generalized Quantifiers (paper §3.2)
-- ============================================================

section GQ

variable {α : Type*}

/-- EVERY(R, S) = R ⊆ S. Universal quantification as set inclusion. -/
def setEvery (R S : Set α) : Prop := R ⊆ S

/-- SOME(R, S) = (R ∩ S).Nonempty. Existential quantification as intersection. -/
def setSome (R S : Set α) : Prop := (R ∩ S).Nonempty

/-- Conservativity: EVERY(R, S) ↔ EVERY(R, R ∩ S). -/
theorem setEvery_conservative (R S : Set α) :
    setEvery R S ↔ setEvery R (R ∩ S) := by
  simp only [setEvery]
  constructor
  · intro h x hx; exact ⟨hx, h hx⟩
  · intro h x hx; exact (h hx).2

/-- Conservativity: SOME(R, S) ↔ SOME(R, R ∩ S). -/
theorem setSome_conservative (R S : Set α) :
    setSome R S ↔ setSome R (R ∩ S) := by
  simp only [setSome]
  constructor
  · rintro ⟨x, hxR, hxS⟩; exact ⟨x, hxR, hxR, hxS⟩
  · rintro ⟨x, hxR, _, hxS⟩; exact ⟨x, hxR, hxS⟩

/-- EVERY is downward monotone in its first argument. -/
theorem setEvery_antimono_left {R₁ R₂ S : Set α} (h : R₁ ⊆ R₂)
    (hE : setEvery R₂ S) : setEvery R₁ S :=
  Set.Subset.trans h hE

/-- EVERY is upward monotone in its second argument. -/
theorem setEvery_mono_right {R S₁ S₂ : Set α} (h : S₁ ⊆ S₂)
    (hE : setEvery R S₁) : setEvery R S₂ :=
  Set.Subset.trans hE h

/-- SOME is upward monotone in its first argument. -/
theorem setSome_mono_left {R₁ R₂ S : Set α} (h : R₁ ⊆ R₂)
    (hS : setSome R₁ S) : setSome R₂ S := by
  obtain ⟨x, hxR, hxS⟩ := hS
  exact ⟨x, h hxR, hxS⟩

/-- SOME is upward monotone in its second argument. -/
theorem setSome_mono_right {R S₁ S₂ : Set α} (h : S₁ ⊆ S₂)
    (hS : setSome R S₁) : setSome R S₂ := by
  obtain ⟨x, hxR, hxS⟩ := hS
  exact ⟨x, hxR, h hxS⟩

/-- GQ duality: ¬EVERY(R, S) ↔ SOME(R, Sᶜ). -/
theorem gq_duality (R S : Set α) :
    ¬setEvery R S ↔ setSome R Sᶜ := by
  simp only [setEvery, setSome]
  constructor
  · intro h
    rw [Set.not_subset] at h
    obtain ⟨x, hxR, hxS⟩ := h
    exact ⟨x, hxR, hxS⟩
  · rintro ⟨x, hxR, hxS⟩ h
    exact hxS (h hxR)

-- Sigma bridge: connecting set-based GQs to PIPExprF quantifiers

variable {W D : Type*} [FiniteDomain D] [FiniteWorlds W]

/-- EVERY over sigma sets ↔ pointwise universal implication. -/
theorem setEvery_sigma (body_R body_S : D → PIPExprF W D) (w : W) :
    setEvery (sigmaEval body_R w) (sigmaEval body_S w) ↔
    ∀ d, (body_R d).truth w = true → (body_S d).truth w = true := by
  simp [setEvery, Set.subset_def, sigmaEval]

/-- SOME over sigma sets ↔ pointwise existential conjunction. -/
theorem setSome_sigma (body_R body_S : D → PIPExprF W D) (w : W) :
    setSome (sigmaEval body_R w) (sigmaEval body_S w) ↔
    ∃ d, (body_R d).truth w = true ∧ (body_S d).truth w = true := by
  simp [setSome, Set.Nonempty, sigmaEval]

end GQ


-- ============================================================
-- §3: Three-Argument Modals (paper §3.3, items 48–51)
-- ============================================================

section ThreeArgModals

variable {W : Type*}

/--
MUST(β, W₁, W₂) = β ∩ W₁ ⊆ W₂.

Three-argument necessity: the modal base β restricted by W₁ is
included in W₂. When W₁ = ⊤, reduces to β ⊆ W₂.
-/
def mustBase (β W₁ W₂ : Set W) : Prop := β ∩ W₁ ⊆ W₂

/--
MIGHT(β, W₁, W₂) = (β ∩ W₁ ∩ W₂).Nonempty.

Three-argument possibility: some world in the modal base satisfying
W₁ also satisfies W₂.
-/
def mightBase (β W₁ W₂ : Set W) : Prop := (β ∩ W₁ ∩ W₂).Nonempty

/-- Tautological restriction: MUST(β, ⊤, W₂) ↔ β ⊆ W₂. -/
theorem mustBase_taut_restr (β W₂ : Set W) :
    mustBase β Set.univ W₂ ↔ β ⊆ W₂ := by
  simp [mustBase]

/-- MUST as a set-based GQ: MUST(β, W₁, W₂) ↔ EVERY(β ∩ W₁, W₂). -/
theorem mustBase_eq_setEvery (β W₁ W₂ : Set W) :
    mustBase β W₁ W₂ ↔ setEvery (β ∩ W₁) W₂ := Iff.rfl

/-- MIGHT as a set-based GQ: MIGHT(β, W₁, W₂) ↔ SOME(β ∩ W₁, W₂). -/
theorem mightBase_eq_setSome (β W₁ W₂ : Set W) :
    mightBase β W₁ W₂ ↔ setSome (β ∩ W₁) W₂ := by
  simp [mightBase, setSome, Set.inter_assoc]

/--
If the actual world is in the modal base and restriction,
MUST forces the consequent at the actual world.
-/
theorem mustBase_realistic (β W₁ W₂ : Set W) (w : W)
    (hw_β : w ∈ β) (hw_W₁ : w ∈ W₁) (h : mustBase β W₁ W₂) : w ∈ W₂ :=
  h ⟨hw_β, hw_W₁⟩

/-- Modal duality: ¬MUST(β, W₁, W₂) ↔ MIGHT(β, W₁, W₂ᶜ). -/
theorem modal_duality (β W₁ W₂ : Set W) :
    ¬mustBase β W₁ W₂ ↔ mightBase β W₁ W₂ᶜ := by
  rw [mustBase_eq_setEvery, mightBase_eq_setSome]
  exact gq_duality (β ∩ W₁) W₂

/-- Convert an accessibility relation to a modal base at world w. -/
def accessRelToBase (R : AccessRel W) (w : W) : Set W :=
  { w' | R w w' = true }

/-- `PIPExprF.must R φ` truth agrees with three-argument `mustBase`. -/
theorem must_truth_iff_mustBase {D : Type*} [FiniteDomain D] [FiniteWorlds W]
    (R : AccessRel W) (φ : PIPExprF W D) (w : W) :
    (PIPExprF.must R φ).truth w = true ↔
    mustBase (accessRelToBase R w) Set.univ { w' | φ.truth w' = true } := by
  simp only [mustBase, accessRelToBase, Set.inter_univ, Set.subset_def, Set.mem_setOf_eq]
  constructor
  · intro h w' hw'
    exact List.all_eq_true.mp h w' (List.mem_filter.mpr ⟨FiniteWorlds.complete w', hw'⟩)
  · intro h
    apply List.all_eq_true.mpr
    intro w' hw'
    exact h w' (List.mem_filter.mp hw').2

/-- `PIPExprF.might R φ` truth agrees with three-argument `mightBase`. -/
theorem might_truth_iff_mightBase {D : Type*} [FiniteDomain D] [FiniteWorlds W]
    (R : AccessRel W) (φ : PIPExprF W D) (w : W) :
    (PIPExprF.might R φ).truth w = true ↔
    mightBase (accessRelToBase R w) Set.univ { w' | φ.truth w' = true } := by
  simp only [mightBase, accessRelToBase, Set.inter_univ, Set.Nonempty,
             Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨w', hw'_mem, hw'_sat⟩ := List.any_eq_true.mp h
    exact ⟨w', (List.mem_filter.mp hw'_mem).2, hw'_sat⟩
  · intro ⟨w', hw'R, hw'φ⟩
    apply List.any_eq_true.mpr
    exact ⟨w', List.mem_filter.mpr ⟨FiniteWorlds.complete w', hw'R⟩, hw'φ⟩

end ThreeArgModals


-- ============================================================
-- §4: FX Operation — Restricted Variable Lifting (paper §3.4, item 84)
-- ============================================================

section FX

variable {W D : Type*}

/--
FX (↑f): lift a thematic-role predicate into a formula modifier.

  ↑f = λφλx. f(x) ∧ φ

Given a predicate `f : D → W → Bool` (e.g., AGENT, PATIENT),
`fxApply f φ x` conjoins `f(x)` with formula `φ`, producing a
restricted variable: x is constrained to satisfy both `f` and `φ`.
-/
def fxApply (f : D → W → Bool) (φ : W → Bool) (x : D) : W → Bool :=
  λ w => f x w && φ w

/-- FX entails the role predicate. -/
theorem fxApply_entails_role (f : D → W → Bool) (φ : W → Bool) (x : D) (w : W)
    (h : fxApply f φ x w = true) : f x w = true := by
  simp only [fxApply, Bool.and_eq_true] at h; exact h.1

/-- FX entails the formula body. -/
theorem fxApply_entails_body (f : D → W → Bool) (φ : W → Bool) (x : D) (w : W)
    (h : fxApply f φ x w = true) : φ w = true := by
  simp only [fxApply, Bool.and_eq_true] at h; exact h.2

/-- Iterated FX accumulates assertions: ↑g(↑f(φ))(x) = g(x) ∧ f(x) ∧ φ. -/
theorem fxApply_twice (f g : D → W → Bool) (φ : W → Bool) (x : D) (w : W) :
    fxApply g (fxApply f φ x) x w = (g x w && f x w && φ w) := by
  simp [fxApply, Bool.and_assoc]

/-- FX with tautological formula: ↑f(⊤)(x) = f(x). -/
theorem fxApply_true (f : D → W → Bool) (x : D) (w : W) :
    fxApply f (λ _ => true) x w = f x w := by
  simp [fxApply]

end FX


-- ============================================================
-- §5: Simple vs Summation Pronouns (paper §4.1)
-- ============================================================

section Pronouns

variable {W D : Type*} [FiniteDomain D] [FiniteWorlds W]

/--
Summation pronoun denotation: the set of all satisfiers.

A summation pronoun referring to variable x under formula φ
denotes Σxφ = {d | φ(d) is true at w}. This is exhaustive: it
includes every entity satisfying the descriptive content, not
just a single witness.
-/
def summPronounDenot (body : D → PIPExprF W D) (w : W) : Set D :=
  sigmaEval body w

/-- Every satisfier is in the summation pronoun's denotation. -/
theorem summPron_exhaustive (body : D → PIPExprF W D) (w : W) (d : D)
    (h : (body d).truth w = true) : d ∈ summPronounDenot body w := h

/-- A value is in the summation denotation iff it satisfies the body. -/
theorem summPron_iff (body : D → PIPExprF W D) (w : W) (d : D) :
    d ∈ summPronounDenot body w ↔ (body d).truth w = true := Iff.rfl

end Pronouns


-- ============================================================
-- §6: Quantificational Subordination (paper §4.4)
-- ============================================================

section Subordination

variable {W D : Type*} [FiniteDomain D] [FiniteWorlds W]

/-- Sigma is monotone: stronger body conditions produce smaller sets. -/
theorem sigma_monotone (φ ψ : D → PIPExprF W D) (w : W)
    (h : ∀ d, (ψ d).truth w = true → (φ d).truth w = true) :
    sigmaEval ψ w ⊆ sigmaEval φ w :=
  λ _ hd => h _ hd

/--
Quantificational subordination: if ψ extends φ with additional conditions,
then Σx(φ ∧ ψ) ⊆ Σxφ. This is the set-theoretic foundation of cross-sentential
anaphora through label-subordinated quantification.

When a subordinate quantifier's restriction φ ∧ ψ includes the main
quantifier's restrictor φ via a label, the subordinate sigma set is
a subset of the main one.
-/
theorem sigma_subordination (φ ψ : D → PIPExprF W D) (w : W) :
    sigmaEval (λ d => PIPExprF.conj (φ d) (ψ d)) w ⊆ sigmaEval φ w := by
  rw [sigmaEval_conj]
  exact Set.inter_subset_left

/-- Label definitions don't affect subordination relationships. -/
theorem sigmaEval_labelDef_subordination (α : FLabel) (φ ψ : D → PIPExprF W D) (w : W) :
    sigmaEval (λ d => PIPExprF.labelDef α (PIPExprF.conj (φ d) (ψ d))) w ⊆
    sigmaEval φ w := by
  rw [sigmaEval_labelDef]
  exact sigma_subordination φ ψ w

end Subordination


end Semantics.PIP
