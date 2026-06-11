import Linglib.Core.Logic.Modal.BSML.Properties

/-!
# Natural deduction for BSML, and its soundness

[aloni-anttila-yang-2024] [anttila-2025] [aloni-2022]

The natural deduction system for BSML of [aloni-anttila-yang-2024]
(Definition 4.1 boxes (a)–(f), shared by all three systems of the paper; the
same system is [anttila-2025] Definition 2.4.1), encoded as an inductive
derivability relation `Derives`, with **soundness** (`soundness`, the paper's
Theorem 4.3 restricted to the shared rules): derivable consequence is
team-semantic consequence over every model.

The rules for `∨` are constrained because NE breaks downward and union
closure: `∨I` requires the introduced disjunct NE-free, and the subderivation
contexts of `∨E`/`∨Mon`/`¬I` must be NE-free. The classical-fragment
metavariables of `¬I`/`¬E` are NE-freeness side conditions here, since ML is
exactly the NE-free fragment.

## Main declarations

* `BSMLFormula.bot`, `BSMLFormula.botbot` — the weak contradiction `p ∧ ¬p`
  ([aloni-2022]'s definition; the paper takes `⊥` as primitive only to
  simplify exposition) and the strong contradiction `⊥ ∧ NE`.
* `support_bot_iff` — `⊥` is supported exactly by the empty team.
* `eq_empty_of_support_antiSupport` — NE-free formulas are bilaterally
  consistent off the empty team.
* `support_singleton_or_antiSupport_singleton` — bilateral determinacy of
  NE-free formulas on singletons.
* `Derives` — the shared-core natural deduction system; `Derives Γ φ` is the
  paper's `Γ ⊢ φ` (contexts are upper bounds on undischarged assumptions,
  with explicit `weaken`).
* `soundness` — `Derives Γ φ` implies `Γ ⊨ φ` on every model.

## Implementation notes

* `BSMLFormula` has no `⊥` primitive (and `eval`'s shape is load-bearing
  downstream), so rules mentioning `⊥` are parameterized by a witness atom
  `p`; `support_bot_iff` shows support is `p`-independent.
* The three `⊥NETrs` substitution rules completing the full BSML system
  ([aloni-anttila-yang-2024] Definition 4.33) simulate the global
  disjunction of BSML⫶ and need an occurrence-substitution apparatus; they
  matter for completeness, not soundness, and are not yet encoded.
* `□Mon` is finitary via a `List` of discharged premises, matching the
  paper's n-ary rule without needing `DecidableEq` on formulas.
-/

namespace Core.Logic.Modal.BSML

open Core.Logic.Team

variable {Atom : Type*} {W : Type*} [DecidableEq W] [Fintype W]

/-! ### Contradictions -/

/-- The weak contradiction `⊥ := p ∧ ¬p` ([aloni-2022]; supported exactly by
    the empty team, for every choice of `p` — `support_bot_iff`). -/
def BSMLFormula.bot (p : Atom) : BSMLFormula Atom :=
  .conj (.atom p) (.neg (.atom p))

/-- The strong contradiction `⊥⊥ := ⊥ ∧ NE` (supported by no team). -/
def BSMLFormula.botbot (p : Atom) : BSMLFormula Atom :=
  .conj (.bot p) .ne

theorem support_bot_iff (M : BSMLModel W Atom) (p : Atom) (s : Finset W) :
    support M (BSMLFormula.bot p) s ↔ s = ∅ := by
  constructor
  · rintro ⟨hpos, hneg⟩
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun w hw => ?_)
    have h1 := hpos w hw
    have h2 := hneg w hw
    simp [h1] at h2
  · rintro rfl
    exact ⟨fun w hw => absurd hw (by simp), fun w hw => absurd hw (by simp)⟩

theorem not_support_botbot (M : BSMLModel W Atom) (p : Atom) (s : Finset W) :
    ¬ support M (BSMLFormula.botbot p) s := by
  rintro ⟨hbot, hne⟩
  have hs : s = ∅ := (support_bot_iff M p s).mp hbot
  subst hs
  exact Finset.not_nonempty_empty hne

/-! ### Classical-fragment lemmas

NE-free formulas behave classically: bilaterally consistent off the empty
team, and bilaterally determined on singletons ([aloni-2022] Fact 15;
[aloni-anttila-yang-2024]'s `α, β ∈ ML` metavariable convention rests on
these). Anti-support facts come free from support facts at `.neg φ`, which
is NE-free exactly when `φ` is. -/

/-- NE-free formulas cannot be both supported and anti-supported on a
    nonempty team. -/
theorem eq_empty_of_support_antiSupport {φ : BSMLFormula Atom}
    (hNE : φ.isNEFree = true) (M : BSMLModel W Atom) :
    ∀ s : Finset W, support M φ s → antiSupport M φ s → s = ∅ := by
  induction φ with
  | atom p =>
    intro s hs ha
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun w hw => ?_)
    have h1 := hs w hw
    have h2 := ha w hw
    simp [h1] at h2
  | ne => simp [BSMLFormula.isNEFree] at hNE
  | neg ψ ih =>
    intro s hs ha
    exact ih hNE s ha hs
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    rintro s ⟨hs₁, hs₂⟩ ⟨t₁, t₂, hsp, ha₁, ha₂⟩
    have hsub₁ : t₁ ⊆ s := hsp ▸ Finset.subset_union_left
    have hsub₂ : t₂ ⊆ s := hsp ▸ Finset.subset_union_right
    have he₁ := ih₁ h₁ t₁ (isLowerSet_support_of_isNEFree h₁ M hsub₁ hs₁) ha₁
    have he₂ := ih₂ h₂ t₂ (isLowerSet_support_of_isNEFree h₂ M hsub₂ hs₂) ha₂
    rw [← hsp, he₁, he₂, Finset.union_empty]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    rintro s ⟨t₁, t₂, hsp, hs₁, hs₂⟩ ⟨ha₁, ha₂⟩
    have hsub₁ : t₁ ⊆ s := hsp ▸ Finset.subset_union_left
    have hsub₂ : t₂ ⊆ s := hsp ▸ Finset.subset_union_right
    have he₁ := ih₁ h₁ t₁ hs₁
      (isLowerSet_support_of_isNEFree (φ := .neg ψ₁) h₁ M hsub₁ ha₁)
    have he₂ := ih₂ h₂ t₂ hs₂
      (isLowerSet_support_of_isNEFree (φ := .neg ψ₂) h₂ M hsub₂ ha₂)
    rw [← hsp, he₁, he₂, Finset.union_empty]
  | poss ψ ih =>
    intro s hs ha
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun w hw => ?_)
    obtain ⟨t, hsub, hne, hψ⟩ := hs w hw
    have haψ : antiSupport M ψ t :=
      isLowerSet_support_of_isNEFree (φ := .neg ψ) hNE M hsub (ha w hw)
    obtain ⟨v, hv⟩ := hne
    have := ih hNE t hψ haψ
    simp [this] at hv

/-- **Bilateral determinacy on singletons** for NE-free formulas: every
    singleton team supports or anti-supports. -/
theorem support_singleton_or_antiSupport_singleton {φ : BSMLFormula Atom}
    (hNE : φ.isNEFree = true) (M : BSMLModel W Atom) :
    ∀ w : W, support M φ {w} ∨ antiSupport M φ {w} := by
  induction φ with
  | atom p =>
    intro w
    cases h : M.val p w with
    | true => exact Or.inl (fun v hv => by rw [Finset.mem_singleton] at hv; rw [hv, h])
    | false => exact Or.inr (fun v hv => by rw [Finset.mem_singleton] at hv; rw [hv, h])
  | ne => simp [BSMLFormula.isNEFree] at hNE
  | neg ψ ih => exact fun w => (ih hNE w).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    intro w
    rcases ih₁ h₁ w with hs₁ | ha₁
    · rcases ih₂ h₂ w with hs₂ | ha₂
      · exact Or.inl ⟨hs₁, hs₂⟩
      · exact Or.inr ⟨∅, {w}, by simp,
          support_empty_of_isNEFree (φ := .neg ψ₁) h₁ M, ha₂⟩
    · exact Or.inr ⟨{w}, ∅, by simp, ha₁,
        support_empty_of_isNEFree (φ := .neg ψ₂) h₂ M⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    intro w
    rcases ih₁ h₁ w with hs₁ | ha₁
    · exact Or.inl ⟨{w}, ∅, by simp, hs₁, support_empty_of_isNEFree h₂ M⟩
    · rcases ih₂ h₂ w with hs₂ | ha₂
      · exact Or.inl ⟨∅, {w}, by simp, support_empty_of_isNEFree h₁ M, hs₂⟩
      · exact Or.inr ⟨ha₁, ha₂⟩
  | poss ψ ih =>
    intro w
    by_cases h : ∃ t ⊆ M.access w, t.Nonempty ∧ support M ψ t
    · obtain ⟨t, hsub, hne, hψ⟩ := h
      exact Or.inl (fun v hv => by
        rw [Finset.mem_singleton] at hv
        exact hv ▸ ⟨t, hsub, hne, hψ⟩)
    · refine Or.inr (fun v hv => ?_)
      rw [Finset.mem_singleton] at hv
      subst hv
      have hflat := isFlat_support_of_isNEFree (φ := .neg ψ) hNE M
      refine (hflat (M.access v)).mpr (fun u hu => ?_)
      rcases ih hNE u with hs | ha
      · exact absurd ⟨{u}, Finset.singleton_subset_iff.mpr hu, by simp, hs⟩ h
      · exact ha

/-! ### The natural deduction system -/

/-- The shared-core natural deduction system for BSML
    ([aloni-anttila-yang-2024] Definition 4.1 boxes (a)–(f) =
    [anttila-2025] Definition 2.4.1; these are the ⫶-free rules of every
    system in the paper, and all of Definition 4.33's BSML system except the
    three `⊥NETrs` substitution rules). `Derives Γ φ` is the paper's
    `Γ ⊢ φ`: contexts are upper bounds on undischarged assumptions
    (`weaken` is the formal counterpart of the paper's "derivable *from
    formulas in* Φ"), so NE-freeness side conditions on subderivation
    contexts match the paper's conditions on undischarged assumptions.
    Rules mentioning `⊥` carry a witness atom `p` (`BSMLFormula.bot`). -/
inductive Derives :
    Set (BSMLFormula Atom) → BSMLFormula Atom → Prop where
  /-- Assumption. -/
  | hyp (φ) : Derives {φ} φ
  /-- Weakening (the paper's subset-closure of `Φ ⊢ ψ`). -/
  | weaken {Γ Δ φ} : Derives Γ φ → Derives (Γ ∪ Δ) φ
  /-- `∧I`. -/
  | conjI {Γ₁ Γ₂ φ ψ} : Derives Γ₁ φ → Derives Γ₂ ψ →
      Derives (Γ₁ ∪ Γ₂) (.conj φ ψ)
  /-- `∧E` (left). -/
  | conjE₁ {Γ φ ψ} : Derives Γ (.conj φ ψ) → Derives Γ φ
  /-- `∧E` (right). -/
  | conjE₂ {Γ φ ψ} : Derives Γ (.conj φ ψ) → Derives Γ ψ
  /-- `¬I`: classical `α`, NE-free undischarged assumptions. -/
  | negI {Γ α} (p : Atom) : α.isNEFree = true →
      (∀ γ ∈ Γ, BSMLFormula.isNEFree γ = true) →
      Derives (insert α Γ) (.bot p) → Derives Γ (.neg α)
  /-- `¬E`: ex falso for the classical fragment. -/
  | negE {Γ₁ Γ₂ α β} : α.isNEFree = true → β.isNEFree = true →
      Derives Γ₁ α → Derives Γ₂ (.neg α) → Derives (Γ₁ ∪ Γ₂) β
  /-- `¬¬E` (downward half of the invertible rule). -/
  | dneE {Γ φ} : Derives Γ (.neg (.neg φ)) → Derives Γ φ
  /-- `¬¬E` (upward half). -/
  | dneI {Γ φ} : Derives Γ φ → Derives Γ (.neg (.neg φ))
  /-- `DM∧` (downward half). -/
  | dmConjE {Γ φ ψ} : Derives Γ (.neg (.conj φ ψ)) →
      Derives Γ (.disj (.neg φ) (.neg ψ))
  /-- `DM∧` (upward half). -/
  | dmConjI {Γ φ ψ} : Derives Γ (.disj (.neg φ) (.neg ψ)) →
      Derives Γ (.neg (.conj φ ψ))
  /-- `DM∨` (downward half). -/
  | dmDisjE {Γ φ ψ} : Derives Γ (.neg (.disj φ ψ)) →
      Derives Γ (.conj (.neg φ) (.neg ψ))
  /-- `DM∨` (upward half). -/
  | dmDisjI {Γ φ ψ} : Derives Γ (.conj (.neg φ) (.neg ψ)) →
      Derives Γ (.neg (.disj φ ψ))
  /-- `¬NEE` (downward half). -/
  | negNeE {Γ} (p : Atom) : Derives Γ (.neg .ne) → Derives Γ (.bot p)
  /-- `¬NEE` (upward half). -/
  | negNeI {Γ p} : Derives Γ (.bot p) → Derives Γ (.neg .ne)
  /-- `∨I`: the introduced disjunct must be NE-free. -/
  | disjI {Γ φ ψ} : ψ.isNEFree = true → Derives Γ φ →
      Derives Γ (.disj φ ψ)
  /-- `∨W`: unconstrained introduction of the premise itself. -/
  | disjW {Γ φ} : Derives Γ φ → Derives Γ (.disj φ φ)
  /-- `Com∨`. -/
  | disjCom {Γ φ ψ} : Derives Γ (.disj φ ψ) → Derives Γ (.disj ψ φ)
  /-- `Ass∨`. -/
  | disjAss {Γ φ ψ χ} : Derives Γ (.disj φ (.disj ψ χ)) →
      Derives Γ (.disj (.disj φ ψ) χ)
  /-- `∨E`: NE-free subderivation contexts (the `⫶`-freeness condition on
      `χ` is vacuous in the `⫶`-free language). -/
  | disjE {Γ Δ₁ Δ₂ φ ψ χ} :
      (∀ γ ∈ Δ₁, BSMLFormula.isNEFree γ = true) →
      (∀ γ ∈ Δ₂, BSMLFormula.isNEFree γ = true) →
      Derives Γ (.disj φ ψ) → Derives (insert φ Δ₁) χ →
      Derives (insert ψ Δ₂) χ → Derives (Γ ∪ Δ₁ ∪ Δ₂) χ
  /-- `∨Mon`: NE-free subderivation context. -/
  | disjMon {Γ Δ φ ψ χ} :
      (∀ γ ∈ Δ, BSMLFormula.isNEFree γ = true) →
      Derives Γ (.disj φ ψ) → Derives (insert ψ Δ) χ →
      Derives (Γ ∪ Δ) (.disj φ χ)
  /-- `⊥E`. -/
  | botE {Γ p φ} : Derives Γ (.disj (.bot p) φ) → Derives Γ φ
  /-- `⊥⊥Ctr`. -/
  | botbotCtr {Γ p φ} (ψ) : Derives Γ (.disj (.botbot p) φ) → Derives Γ ψ
  /-- `◇Mon`: the subderivation has `φ` as its only undischarged
      assumption. -/
  | possMon {Γ φ ψ} : Derives {φ} ψ → Derives Γ (.poss φ) →
      Derives Γ (.poss ψ)
  /-- `□Mon` (finitary): the subderivation's undischarged assumptions are
      among the boxed premises. -/
  | necMon {Γ ψ} (φs : List (BSMLFormula Atom)) :
      Derives {δ | δ ∈ φs} ψ → (∀ δ ∈ φs, Derives Γ (BSMLFormula.nec δ)) →
      Derives Γ (BSMLFormula.nec ψ)
  /-- `Inter◇□` (downward half). -/
  | interE {Γ φ} : Derives Γ (.neg (.poss φ)) →
      Derives Γ (BSMLFormula.nec (.neg φ))
  /-- `Inter◇□` (upward half). -/
  | interI {Γ φ} : Derives Γ (BSMLFormula.nec (.neg φ)) →
      Derives Γ (.neg (.poss φ))
  /-- `◇Sep` (FC-entailment for pragmatically enriched formulas). -/
  | possSep {Γ φ ψ} : Derives Γ (.poss (.disj φ (.conj ψ .ne))) →
      Derives Γ (.poss ψ)
  /-- `◇Join`. -/
  | possJoin {Γ₁ Γ₂ φ ψ} : Derives Γ₁ (.poss φ) → Derives Γ₂ (.poss ψ) →
      Derives (Γ₁ ∪ Γ₂) (.poss (.disj φ ψ))
  /-- `□Inst`: `□` implies `◇` when accessible worlds exist. -/
  | necInst {Γ φ} : Derives Γ (BSMLFormula.nec (.conj φ .ne)) →
      Derives Γ (.poss φ)
  /-- `□◇Join`. -/
  | necPossJoin {Γ₁ Γ₂ φ ψ} : Derives Γ₁ (BSMLFormula.nec φ) →
      Derives Γ₂ (.poss ψ) →
      Derives (Γ₁ ∪ Γ₂) (BSMLFormula.nec (.disj φ ψ))

/-! ### Soundness -/

/-- **Soundness** ([aloni-anttila-yang-2024] Theorem 4.3, restricted to the
    shared-core rules): derivable consequence is team-semantic consequence —
    on every model, every team supporting all of `Γ` supports `φ`. The
    `∨`-rule cases run on the closure pillars: NE-free downward closure
    (`isLowerSet_support_of_isNEFree`) for discharging side-conditioned
    contexts on sub-teams, and unrestricted union closure
    (`supClosed_support`) for reassembling `∨E`'s conclusion. -/
theorem soundness {Γ : Set (BSMLFormula Atom)} {φ : BSMLFormula Atom}
    (h : Derives Γ φ) (M : BSMLModel W Atom) :
    ∀ s : Finset W, (∀ γ ∈ Γ, support M γ s) → support M φ s := by
  induction h with
  | hyp φ =>
    exact fun s hΓ => hΓ φ rfl
  | weaken _ ih =>
    exact fun s hΓ => ih s (fun γ hγ => hΓ γ (Set.mem_union_left _ hγ))
  | conjI _ _ ih₁ ih₂ =>
    exact fun s hΓ =>
      ⟨ih₁ s (fun γ hγ => hΓ γ (Set.mem_union_left _ hγ)),
       ih₂ s (fun γ hγ => hΓ γ (Set.mem_union_right _ hγ))⟩
  | conjE₁ _ ih => exact fun s hΓ => (ih s hΓ).1
  | conjE₂ _ ih => exact fun s hΓ => (ih s hΓ).2
  | @negI Γ α p hα hΓNE _ ih =>
    intro s hΓ
    show antiSupport M α s
    have hflat := isFlat_support_of_isNEFree (φ := .neg α) hα M
    refine (hflat s).mpr (fun w hw => ?_)
    rcases support_singleton_or_antiSupport_singleton hα M w with hsup | hanti
    · exfalso
      have hbot := ih {w} (fun γ hγ => ?_)
      · have := (support_bot_iff M p {w}).mp hbot
        simp at this
      · rcases hγ with rfl | hγ
        · exact hsup
        · exact isLowerSet_support_of_isNEFree (hΓNE γ hγ) M
            (Finset.singleton_subset_iff.mpr hw) (hΓ γ hγ)
    · exact hanti
  | @negE Γ₁ Γ₂ α β hα hβ _ _ ih₁ ih₂ =>
    intro s hΓ
    have h1 := ih₁ s (fun γ hγ => hΓ γ (Set.mem_union_left _ hγ))
    have h2 := ih₂ s (fun γ hγ => hΓ γ (Set.mem_union_right _ hγ))
    have hs : s = ∅ := eq_empty_of_support_antiSupport hα M s h1 h2
    exact hs ▸ support_empty_of_isNEFree hβ M
  | dneE _ ih => exact ih
  | dneI _ ih => exact ih
  | dmConjE _ ih => exact ih
  | dmConjI _ ih => exact ih
  | dmDisjE _ ih => exact ih
  | dmDisjI _ ih => exact ih
  | @negNeE Γ p _ ih =>
    exact fun s hΓ => (support_bot_iff M p s).mpr (ih s hΓ)
  | @negNeI Γ p _ ih =>
    exact fun s hΓ => (support_bot_iff M p s).mp (ih s hΓ)
  | disjI hψ _ ih =>
    exact fun s hΓ =>
      ⟨s, ∅, by simp, ih s hΓ, support_empty_of_isNEFree hψ M⟩
  | disjW _ ih =>
    exact fun s hΓ => ⟨s, s, by simp, ih s hΓ, ih s hΓ⟩
  | disjCom _ ih =>
    intro s hΓ
    obtain ⟨t₁, t₂, hsp, h1, h2⟩ := ih s hΓ
    exact ⟨t₂, t₁, by show t₂ ∪ t₁ = s; rw [Finset.union_comm]; exact hsp, h2, h1⟩
  | disjAss _ ih =>
    intro s hΓ
    obtain ⟨t₁, t₂₃, hsp, h1, t₂, t₃, hsp', h2, h3⟩ := ih s hΓ
    exact ⟨t₁ ∪ t₂, t₃,
      by show t₁ ∪ t₂ ∪ t₃ = s; rw [Finset.union_assoc, hsp']; exact hsp,
      ⟨t₁, t₂, rfl, h1, h2⟩, h3⟩
  | @disjE Γ Δ₁ Δ₂ φ ψ χ hΔ₁ hΔ₂ _ _ _ ihmaj ih₁ ih₂ =>
    intro s hΓ
    obtain ⟨t₁, t₂, hsp, hφ, hψ⟩ := ihmaj s (fun γ hγ =>
      hΓ γ (Set.mem_union_left _ (Set.mem_union_left _ hγ)))
    have hsub₁ : t₁ ⊆ s := hsp ▸ Finset.subset_union_left
    have hsub₂ : t₂ ⊆ s := hsp ▸ Finset.subset_union_right
    have hχ₁ := ih₁ t₁ (fun γ hγ => by
      rcases hγ with rfl | hγ
      · exact hφ
      · exact isLowerSet_support_of_isNEFree (hΔ₁ γ hγ) M hsub₁
          (hΓ γ (Set.mem_union_left _ (Set.mem_union_right _ hγ))))
    have hχ₂ := ih₂ t₂ (fun γ hγ => by
      rcases hγ with rfl | hγ
      · exact hψ
      · exact isLowerSet_support_of_isNEFree (hΔ₂ γ hγ) M hsub₂
          (hΓ γ (Set.mem_union_right _ hγ)))
    exact hsp ▸ supClosed_support M χ hχ₁ hχ₂
  | @disjMon Γ Δ φ ψ χ hΔ _ _ ihmaj ih =>
    intro s hΓ
    obtain ⟨t₁, t₂, hsp, hφ, hψ⟩ := ihmaj s (fun γ hγ =>
      hΓ γ (Set.mem_union_left _ hγ))
    have hsub₂ : t₂ ⊆ s := hsp ▸ Finset.subset_union_right
    have hχ := ih t₂ (fun γ hγ => by
      rcases hγ with rfl | hγ
      · exact hψ
      · exact isLowerSet_support_of_isNEFree (hΔ γ hγ) M hsub₂
          (hΓ γ (Set.mem_union_right _ hγ)))
    exact ⟨t₁, t₂, hsp, hφ, hχ⟩
  | @botE Γ p φ _ ih =>
    intro s hΓ
    obtain ⟨t₁, t₂, hsp, hbot, hφ⟩ := ih s hΓ
    have ht₁ : t₁ = ∅ := (support_bot_iff M p t₁).mp hbot
    subst ht₁
    have hsp' : ∅ ∪ t₂ = s := hsp
    have ht₂ : t₂ = s := by simpa using hsp'
    exact ht₂ ▸ hφ
  | @botbotCtr Γ p φ ψ _ ih =>
    intro s hΓ
    obtain ⟨t₁, _, _, hbb, _⟩ := ih s hΓ
    exact absurd hbb (not_support_botbot M p t₁)
  | possMon _ _ ihD ihPoss =>
    intro s hΓ w hw
    obtain ⟨t, hsub, hne, hφ⟩ := ihPoss s hΓ w hw
    exact ⟨t, hsub, hne, ihD t (fun γ hγ => hγ ▸ hφ)⟩
  | @necMon Γ ψ φs _ _ ihD ihboxes =>
    intro s hΓ w hw
    show support M ψ (M.access w)
    exact ihD (M.access w) (fun δ hδ => ihboxes δ hδ s hΓ w hw)
  | interE _ ih => exact ih
  | interI _ ih => exact ih
  | possSep _ ih =>
    intro s hΓ w hw
    obtain ⟨t, hsub, _, t₁, t₂, hsp, _, hψ, hne⟩ := ih s hΓ w hw
    exact ⟨t₂, (hsp ▸ Finset.subset_union_right).trans hsub, hne, hψ⟩
  | possJoin _ _ ih₁ ih₂ =>
    intro s hΓ w hw
    obtain ⟨t₁, hsub₁, hne₁, hφ⟩ :=
      ih₁ s (fun γ hγ => hΓ γ (Set.mem_union_left _ hγ)) w hw
    obtain ⟨t₂, hsub₂, _, hψ⟩ :=
      ih₂ s (fun γ hγ => hΓ γ (Set.mem_union_right _ hγ)) w hw
    obtain ⟨v, hv⟩ := hne₁
    exact ⟨t₁ ∪ t₂, Finset.union_subset hsub₁ hsub₂,
      ⟨v, Finset.mem_union_left _ hv⟩, t₁, t₂, rfl, hφ, hψ⟩
  | necInst _ ih =>
    intro s hΓ w hw
    obtain ⟨hφ, hne⟩ := ih s hΓ w hw
    exact ⟨M.access w, subset_rfl, hne, hφ⟩
  | necPossJoin _ _ ih₁ ih₂ =>
    intro s hΓ w hw
    have hφ := ih₁ s (fun γ hγ => hΓ γ (Set.mem_union_left _ hγ)) w hw
    obtain ⟨t, hsub, _, hψ⟩ :=
      ih₂ s (fun γ hγ => hΓ γ (Set.mem_union_right _ hγ)) w hw
    exact ⟨M.access w, t, Finset.union_eq_left.mpr hsub, hφ, hψ⟩

/-- Syntactic narrow-scope free choice: pragmatic enrichment puts `∧ NE` on
    the disjuncts, and one `◇Sep` extracts each conjunct-possibility — the
    proof-theoretic counterpart of [aloni-2022]'s FC-entailment, here for the
    right disjunct. `soundness` transports it to team-semantic consequence. -/
example (φ ψ : BSMLFormula Atom) :
    Derives {BSMLFormula.poss (.disj φ (.conj ψ .ne))} (.poss ψ) :=
  .possSep (.hyp _)

end Core.Logic.Modal.BSML
