import Linglib.Logic.Modal.BSML.Properties
import Linglib.Logic.Modal.BSML.Characteristic

/-!
# Expressive completeness for BSML

[anttila-2025] [aloni-anttila-yang-2024] [aloni-2022]

[anttila-2025] Chapter 3 (= [anttila-knudstorp-2025]) proves that BSML is
**expressively complete** for the class of convex, union-closed,
bounded-bisimulation-invariant modal team properties — solving the BSML
expressive-power problem left open in [aloni-anttila-yang-2024]. In the `Team/Definability.lean` vocabulary this
is `ExpressivelyCompleteFor (support M)` for the cell
`convexProperties ∩ unionClosedProperties ∩ bisimClosedProperties M`.

The theorem splits into two halves:

* **Soundness** (`⟦BSML⟧ ⊆ cell`) — every definable property lies in the cell.
  Fully proved here, assembling the three closure pillars:
  `ordConnected_support` (convexity, Proposition 3.3.1), `supClosed_support`
  (union closure), and `bisimClosed_definedBy` (Theorem 3.8 / bisimulation
  invariance, `BSML/Bisimulation.lean`).
* **Completeness** (`cell ⊆ ⟦BSML⟧`) — the converse: every property in the
  cell is BSML-definable, proved for finite atom types via the
  characteristic-formula machinery of `BSML/Characteristic.lean` (the
  within-model, finite-atom specialisation of [anttila-2025] Ch 3, whose
  cross-model theorem indexes bisimulation by finite atom sets).

## Main declarations

* `BisimClosed M P`, `bisimClosedProperties M` — bounded-bisimulation closure of
  a team property within `M` (the third soundness pillar as a closure cell).
* `bisimInvariant_support` — Theorem 3.8 specialised to one model.
* `bisimClosed_definedBy` — every BSML-definable property is bisim-closed.
* `expressiveSoundness` — `⟦BSML⟧ ⊆` the convex/union-closed/bisim-closed cell.
* `expressiveCompleteness_converse` — the converse.
* `expressivelyComplete` — the headline equality.
-/

namespace BSML

open Team ModalLogic

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

/-! ### Bounded-bisimulation closure (the third soundness pillar) -/

/-- A team property is **bounded-bisimulation-closed** in `M` if for some depth
    `k` it is closed under `k`-bisimulation of teams within `M`. This is the
    closure invariant — alongside convexity and union closure — that
    characterises BSML-definability ([anttila-2025] Ch 3). -/
def BisimClosed (M : KripkeModel W Atom) (P : TeamProperty W) : Prop :=
  ∃ k : ℕ, ∀ s s' : Finset W, StateBisim k M s M s' → (s ∈ P ↔ s' ∈ P)

/-- The class of bounded-bisimulation-closed team properties of `M`. -/
def bisimClosedProperties (M : KripkeModel W Atom) : Set (TeamProperty W) :=
  { P | BisimClosed M P }

/-- **BSML support is bounded-bisimulation invariant within a model**: if
    `s ⇌_k s'` and `k ≥ φ.modalDepth`, then `s` and `s'` agree on `φ`. Immediate
    from Theorem 3.8 (`bisim_invariant_eval`) at `M' := M`. -/
theorem bisimInvariant_support (M : KripkeModel W Atom) (φ : Formula Atom)
    {k : ℕ} (hd : φ.modalDepth ≤ k) {s s' : Finset W}
    (h : StateBisim k M s M s') : support M φ s ↔ support M φ s' :=
  bisim_invariant_eval φ hd h true

/-- Every BSML-definable team property is bounded-bisimulation-closed, with
    witnessing depth the formula's modal depth. -/
theorem bisimClosed_definedBy (M : KripkeModel W Atom) (φ : Formula Atom) :
    BisimClosed M (definedBy (support M) φ) :=
  ⟨φ.modalDepth, fun _ _ h => bisimInvariant_support M φ le_rfl h⟩

/-! ### Expressive completeness -/

/-- **Soundness half** ([anttila-2025] Ch 3): every BSML-definable team
    property is convex, union-closed, and bounded-bisimulation-closed. Assembles
    `ordConnected_support`, `supClosed_support`, and `bisimClosed_definedBy`. -/
theorem expressiveSoundness (M : KripkeModel W Atom) :
    definableClass (support M) ⊆
      convexProperties ∩ unionClosedProperties ∩ bisimClosedProperties M := by
  intro P hP
  simp only [mem_definableClass] at hP
  obtain ⟨φ, rfl⟩ := hP
  exact ⟨⟨ordConnected_support M φ, supClosed_support M φ⟩, bisimClosed_definedBy M φ⟩

/-- **Completeness half** ([anttila-2025] Ch 3 — the hard direction, the
    BSML expressive-power problem left open by [aloni-anttila-yang-2024] —
    in its within-model, finite-atom form): every convex, union-closed,
    bounded-bisimulation-closed team property is BSML-definable.

    The defining formula conjoins an upper bound — the flat disjunction
    `δ_U` of the characteristic formulas of the union `U` of all teams of
    `P` — with, for every set `T` of worlds whose bisimilarity classes meet
    every team of `P`, the hitting disjunct `(δ_T ∧ NE) ∨ δ_U`. A
    supporting team `t` lies under `U` and meets every such transversal;
    the worlds not bisimilar into `t` therefore fail to be a transversal,
    which yields a team `s₀ ∈ P` whose classes `t` covers, and `s₀ ∪ (U`
    restricted to `t`'s classes`)` lies in `P` by convexity between `s₀`
    and `U` and is bisimilar to `t` — so `t ∈ P` by bisimulation closure. -/
theorem expressiveCompleteness_converse [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) :
    convexProperties ∩ unionClosedProperties ∩ bisimClosedProperties M ⊆
      definableClass (support M) := by
  classical
  rintro P ⟨⟨hconv, hsup⟩, hbc⟩
  obtain ⟨k, hbisim⟩ := hbc
  have hconv' : Set.OrdConnected P := hconv
  have hsup' : SupClosed P := hsup
  rw [mem_definableClass]
  rcases Set.eq_empty_or_nonempty P with rfl | hP
  · refine ⟨.conj falsum .ne, ?_⟩
    ext t
    constructor
    · exact fun h => h.elim
    · rintro ⟨⟨h1, h2⟩, w, hw⟩
      exact absurd ((h1 w hw).symm.trans (h2 w hw)) (by decide)
  · set PF : Finset (Finset W) := P.toFinset with hPF
    have hPFne : PF.Nonempty := Set.toFinset_nonempty.mpr hP
    set U : Finset W := PF.sup id with hUdef
    have hUP : U ∈ P :=
      hsup'.finsetSup_mem hPFne (fun s hs => Set.mem_toFinset.mp hs)
    have hsubU : ∀ s ∈ P, s ⊆ U :=
      fun s hs => Finset.le_sup (f := id) (Set.mem_toFinset.mpr hs)
    set 𝒯 : Finset (Finset W) := Finset.univ.filter
      (fun T => ∀ s ∈ PF, ∃ v ∈ s, ∃ w ∈ T, WorldBisim k M w M v) with h𝒯
    set δ : Finset W → Formula Atom :=
      fun S => bigDisj (S.toList.map (charFormula M k)) with hδdef
    refine ⟨.conj (δ U)
      (bigConj (𝒯.toList.map (fun T => .disj (.conj (δ T) .ne) (δ U)))), ?_⟩
    ext t
    constructor
    · intro htP
      refine ⟨(support_charDisj_iff M k U t).mpr
        (fun v hv => ⟨v, hsubU t htP hv, WorldBisim.refl k M v⟩), ?_⟩
      refine (support_bigConj_iff M _ t).mpr (fun ψ hψ => ?_)
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hψ
      have hTtrans := (Finset.mem_filter.mp (Finset.mem_toList.mp hT)).2
      obtain ⟨v, hvt, w, hwT, hb⟩ := hTtrans t (Set.mem_toFinset.mpr htP)
      refine ⟨{v}, t, ?_, ⟨?_, Finset.singleton_nonempty v⟩, ?_⟩
      · show {v} ∪ t = t
        exact Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr hvt)
      · refine (support_charDisj_iff M k T {v}).mpr (fun x hx => ?_)
        obtain rfl := Finset.mem_singleton.mp hx
        exact ⟨w, hwT, hb⟩
      · exact (support_charDisj_iff M k U t).mpr
          (fun x hx => ⟨x, hsubU t htP hx, WorldBisim.refl k M x⟩)
    · rintro ⟨hupper, hhits⟩
      have hcov : ∀ v ∈ t, ∃ w ∈ U, WorldBisim k M w M v :=
        (support_charDisj_iff M k U t).mp hupper
      set T₀ : Finset W := Finset.univ.filter
        (fun w => ¬ ∃ v ∈ t, WorldBisim k M w M v) with hT₀def
      have hT₀notin : T₀ ∉ 𝒯 := by
        intro hmem
        have hhit := (support_bigConj_iff M _ t).mp hhits _
          (List.mem_map.mpr ⟨T₀, Finset.mem_toList.mpr hmem, rfl⟩)
        obtain ⟨t₁, t₂, hsplit, ⟨hδ₁, hne₁⟩, -⟩ := hhit
        obtain ⟨x, hx⟩ := hne₁
        obtain ⟨w, hwT₀, hb⟩ := (support_charDisj_iff M k T₀ t₁).mp hδ₁ x hx
        exact (Finset.mem_filter.mp hwT₀).2
          ⟨x, Team.splitsAs_left_subset hsplit hx, hb⟩
      have hs₀ : ∃ s₀ ∈ PF, ∀ w ∈ s₀, ∃ v ∈ t, WorldBisim k M w M v := by
        by_contra hno
        refine hT₀notin (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun s hs => ?_⟩)
        by_contra hall
        refine hno ⟨s, hs, fun w hw => ?_⟩
        by_contra hwnc
        exact hall ⟨w, hw, w,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwnc⟩, WorldBisim.refl k M w⟩
      obtain ⟨s₀, hs₀PF, hs₀cov⟩ := hs₀
      have hs₀P : s₀ ∈ P := Set.mem_toFinset.mp hs₀PF
      set t'' : Finset W :=
        s₀ ∪ U.filter (fun w => ∃ v ∈ t, WorldBisim k M w M v) with ht''def
      have hbis : StateBisim k M t'' M t := by
        constructor
        · intro w hw
          rcases Finset.mem_union.mp hw with hw₀ | hwU
          · exact hs₀cov w hw₀
          · exact (Finset.mem_filter.mp hwU).2
        · intro v hv
          obtain ⟨w, hwU, hb⟩ := hcov v hv
          exact ⟨w, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwU, v, hv, hb⟩), hb⟩
      have ht''P : t'' ∈ P :=
        hconv'.out hs₀P hUP (Set.mem_Icc.mpr
          ⟨Finset.subset_union_left,
           Finset.union_subset (hsubU s₀ hs₀P) (Finset.filter_subset _ _)⟩)
      exact (hbisim t'' t hbis).mp ht''P

/-- **BSML is expressively complete** for the convex, union-closed,
    bounded-bisimulation-closed team properties ([anttila-2025] Ch 3, in
    within-model finite-atom form). -/
theorem expressivelyComplete [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) :
    ExpressivelyCompleteFor (support M)
      (convexProperties ∩ unionClosedProperties ∩ bisimClosedProperties M) :=
  Set.Subset.antisymm (expressiveSoundness M) (expressiveCompleteness_converse M)

end BSML
