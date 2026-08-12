import Linglib.Logic.Team.BSML.Bridge
import Linglib.Logic.Team.BSML.Bisimulation

/-!
# Characteristic (Hintikka) formulas for BSML — foundation

[aloni-anttila-yang-2024] [anttila-2025]

The expressive-completeness converse for BSML (`expressiveCompleteness_converse`
in `BSML/ExpressiveCompleteness.lean`) needs **characteristic formulas**: for
each world `w` and depth `k`, an NE-free formula `χ_w^k` such that a singleton
`{v}` supports it exactly when `v` is `k`-bisimilar to `w`. This file builds the
foundation — finite conjunction over an NE-free language and the **depth-0
(atomic type)** characterisation — and proves it against the classical
single-world evaluation `classicalEval` (`BSML/Bridge.lean`).

Working through `classicalEval` is the simplification that makes this tractable:
characteristic formulas are NE-free, so by `Bridge.neFree_flat_eq` their team
support reduces to pointwise `classicalEval`, and the construction becomes the
standard *classical* modal Hintikka characterisation.

## Main declarations

* `verum`, `bigConj` — `⊤` (as `p ∨ ¬p`) and finite conjunction, both NE-free.
* `atomicType M w` — the depth-0 Hintikka formula: the conjunction of atomic
  literals true at `w`.
* `charFormula M k w` — the depth-`k` Hintikka formula: atomic type, `◇` of
  each successor type, and `□` of the successor-type disjunction.
* `classicalEval_charFormula_iff_bisim` — the characterisation: `v`
  classically satisfies `χ_w^k` iff `w` and `v` are `k`-bisimilar.
* `support_charFormula_singleton_iff_bisim` — the team-semantic face:
  singleton support of `χ_w^k` is `k`-bisimilarity.

## Todo

* Team characteristic formulas (`θ_s^k = ⋁_{w ∈ s} (χ_w^k ∧ NE)`,
  Definition 3.10 of [aloni-anttila-yang-2024]) and the convex,
  union-closed normal form that discharges
  `expressiveCompleteness_converse`.
-/

namespace BSML

open ModalLogic

variable {W : Type*} {Atom : Type*}

/-! ### `⊤` and finite conjunction -/

/-- `⊤` as an NE-free BSML formula: `p ∨ ¬p` for the default atom. Classically
    evaluates to `true` at every world; supported by every team. Requires an
    atom (`[Inhabited Atom]`): BSML has no atom-free closed `⊤`. -/
def verum [Inhabited Atom] : Formula Atom :=
  .disj (.atom default) (.neg (.atom default))

@[simp] theorem classicalEval_verum [Inhabited Atom] (M : KripkeModel W Atom) (w : W) :
    classicalEval M verum w = true := by
  simp [verum, classicalEval, Bool.or_not_self]

@[simp] theorem neFree_verum [Inhabited Atom] : (verum : Formula Atom).NEFree :=
  ⟨trivial, trivial⟩

/-- Finite conjunction of a list of formulas; the empty conjunction is `⊤`. -/
def bigConj [Inhabited Atom] : List (Formula Atom) → Formula Atom
  | [] => verum
  | φ :: rest => .conj φ (bigConj rest)

theorem classicalEval_bigConj [Inhabited Atom] (M : KripkeModel W Atom) (w : W)
    (l : List (Formula Atom)) :
    classicalEval M (bigConj l) w = true ↔ ∀ φ ∈ l, classicalEval M φ w = true := by
  induction l with
  | nil => simp [bigConj]
  | cons φ rest ih =>
    simp only [bigConj, classicalEval, Bool.and_eq_true, List.forall_mem_cons, ih]

theorem neFree_bigConj [Inhabited Atom] (l : List (Formula Atom))
    (h : ∀ φ ∈ l, φ.NEFree) : (bigConj l).NEFree := by
  induction l with
  | nil => exact neFree_verum
  | cons φ rest ih =>
    exact ⟨h φ (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun ψ hψ => h ψ (List.mem_cons.mpr (Or.inr hψ)))⟩

/-! ### Atomic type (depth-0 Hintikka formula) -/

/-- The **atomic type** of `w`: the conjunction over all atoms `p` of the literal
    `p` (when `w ⊨ p`) or `¬p` (when `w ⊭ p`). The depth-0 characteristic
    formula. -/
noncomputable def atomicType [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (w : W) : Formula Atom :=
  bigConj ((Finset.univ : Finset Atom).toList.map
    (fun p => if M.val p w then .atom p else .neg (.atom p)))

theorem neFree_atomicType [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (w : W) : (atomicType M w).NEFree := by
  apply neFree_bigConj
  intro φ hφ
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
  cases M.val p w <;> simp [Formula.NEFree]

/-- The atomic type of `w` is classically satisfied at `v` exactly when `v` and
    `w` assign every atom the same value. -/
theorem classicalEval_atomicType [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (w v : W) :
    classicalEval M (atomicType M w) v = true ↔ ∀ p : Atom, M.val p v = M.val p w := by
  rw [atomicType, classicalEval_bigConj]
  constructor
  · intro h p
    have hp := h _ (List.mem_map.mpr
      ⟨p, Finset.mem_toList.mpr (Finset.mem_univ p), rfl⟩)
    cases hb : M.val p w with
    | false => simp [hb, classicalEval] at hp; simp [hp]
    | true => simp [hb, classicalEval] at hp; simp [hp]
  · intro h φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    cases hb : M.val p w with
    | false => simp [hb, classicalEval, h p]
    | true => simp [hb, classicalEval, h p]

/-- **Depth-0 characterisation**: `w`'s atomic type is classically satisfied at
    `v` iff `v` and `w` are 0-bisimilar. The base case of the characteristic-
    formula characterisation. -/
theorem classicalEval_atomicType_iff_bisim0 [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (w v : W) :
    classicalEval M (atomicType M w) v = true ↔ WorldBisim 0 M w M v := by
  rw [classicalEval_atomicType]
  constructor
  · intro h p; exact (h p).symm
  · intro h p; exact (h p).symm

/-! ### `⊥` and finite disjunction -/

/-- `⊥` as an NE-free BSML formula: `p ∧ ¬p` for the default atom. Classically
    false at every world. -/
def falsum [Inhabited Atom] : Formula Atom :=
  .conj (.atom default) (.neg (.atom default))

@[simp] theorem classicalEval_falsum [Inhabited Atom] (M : KripkeModel W Atom) (w : W) :
    classicalEval M falsum w = false := by
  simp [falsum, classicalEval]

@[simp] theorem neFree_falsum [Inhabited Atom] : (falsum : Formula Atom).NEFree :=
  ⟨trivial, trivial⟩

/-- Finite disjunction of a list of formulas; the empty disjunction is `⊥`. -/
def bigDisj [Inhabited Atom] : List (Formula Atom) → Formula Atom
  | [] => falsum
  | φ :: rest => .disj φ (bigDisj rest)

theorem classicalEval_bigDisj [Inhabited Atom] (M : KripkeModel W Atom) (w : W)
    (l : List (Formula Atom)) :
    classicalEval M (bigDisj l) w = true ↔ ∃ φ ∈ l, classicalEval M φ w = true := by
  induction l with
  | nil => simp [bigDisj]
  | cons φ rest ih => simp [bigDisj, classicalEval, ih]

theorem neFree_bigDisj [Inhabited Atom] (l : List (Formula Atom))
    (h : ∀ φ ∈ l, φ.NEFree) : (bigDisj l).NEFree := by
  induction l with
  | nil => exact neFree_falsum
  | cons φ rest ih =>
    exact ⟨h φ (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun ψ hψ => h ψ (List.mem_cons.mpr (Or.inr hψ)))⟩

/-! ### Modal clauses of classical evaluation -/

theorem classicalEval_poss_iff (M : KripkeModel W Atom) (ψ : Formula Atom) (w : W) :
    classicalEval M (.poss ψ) w = true ↔ ∃ v ∈ M.access w, classicalEval M ψ v = true := by
  simp [classicalEval]

theorem classicalEval_nec_iff (M : KripkeModel W Atom) (ψ : Formula Atom) (w : W) :
    classicalEval M (Formula.nec ψ) w = true ↔ ∀ v ∈ M.access w, classicalEval M ψ v = true := by
  simp [Formula.nec, classicalEval]

/-! ### Characteristic formulas -/

/-- The depth-`k` characteristic (Hintikka) formula of `w`: at depth `0` the
    atomic type; at depth `k + 1` the atomic type, conjoined with `◇χ_v^k`
    for each `R`-successor `v` and with `□` of the disjunction of the
    successor types. -/
noncomputable def charFormula [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) : ℕ → W → Formula Atom
  | 0, w => atomicType M w
  | k + 1, w =>
      .conj (atomicType M w)
        (.conj
          (bigConj ((M.access w).toList.map fun v => .poss (charFormula M k v)))
          (Formula.nec (bigDisj ((M.access w).toList.map fun v => charFormula M k v))))

theorem neFree_charFormula [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (k : ℕ) (w : W) : (charFormula M k w).NEFree := by
  induction k generalizing w with
  | zero => exact neFree_atomicType M w
  | succ k ih =>
    refine ⟨neFree_atomicType M w, ?_, ?_⟩
    · refine neFree_bigConj _ (fun φ hφ => ?_)
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hφ
      exact ih v
    · refine neFree_bigDisj _ (fun φ hφ => ?_)
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hφ
      exact ih v

/-- **Depth-`k` characterisation** (the Hintikka half of Theorem 3.3 of
    [aloni-anttila-yang-2024]): `w`'s depth-`k` characteristic formula is
    classically satisfied at `v` iff `w` and `v` are `k`-bisimilar. -/
theorem classicalEval_charFormula_iff_bisim [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (k : ℕ) (w v : W) :
    classicalEval M (charFormula M k w) v = true ↔ WorldBisim k M w M v := by
  induction k generalizing w v with
  | zero => exact classicalEval_atomicType_iff_bisim0 M w v
  | succ k ih =>
    constructor
    · intro h
      simp only [charFormula, classicalEval, Bool.and_eq_true] at h
      obtain ⟨hA, hB, hC⟩ := h
      refine ⟨fun p => ((classicalEval_atomicType M w v).mp hA p).symm, ?_, ?_⟩
      · intro u hu
        have hposs := (classicalEval_bigConj M v _).mp hB (.poss (charFormula M k u))
          (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩)
        obtain ⟨u', hu', hchar⟩ := (classicalEval_poss_iff M _ v).mp hposs
        exact ⟨u', hu', (ih u u').mp hchar⟩
      · intro u' hu'
        have hd := (classicalEval_nec_iff M _ v).mp hC u' hu'
        obtain ⟨φ, hφ, hval⟩ := (classicalEval_bigDisj M u' _).mp hd
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hφ
        exact ⟨u, Finset.mem_toList.mp hu, (ih u u').mp hval⟩
    · intro hbisim
      simp only [charFormula, classicalEval, Bool.and_eq_true]
      refine ⟨(classicalEval_atomicType M w v).mpr (fun p => (hbisim.1 p).symm), ?_, ?_⟩
      · refine (classicalEval_bigConj M v _).mpr (fun φ hφ => ?_)
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hφ
        obtain ⟨u', hu', hb⟩ := hbisim.2.1 u (Finset.mem_toList.mp hu)
        exact (classicalEval_poss_iff M _ v).mpr ⟨u', hu', (ih u u').mpr hb⟩
      · refine (classicalEval_nec_iff M _ v).mpr (fun u' hu' => ?_)
        obtain ⟨u, hu, hb⟩ := hbisim.2.2 u' hu'
        exact (classicalEval_bigDisj M u' _).mpr
          ⟨charFormula M k u, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩,
           (ih u u').mpr hb⟩

/-! ### Team support of the auxiliary connectives -/

variable [DecidableEq W]

theorem support_verum [Inhabited Atom] (M : KripkeModel W Atom) (t : Finset W) :
    support M (verum (Atom := Atom)) t := by
  refine ⟨t.filter (fun w => M.val default w = true),
          t.filter (fun w => M.val default w = false), ?_, ?_, ?_⟩
  · show t.filter _ ∪ t.filter _ = t
    ext w
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro hw
      cases hb : M.val default w
      · exact Or.inr ⟨hw, rfl⟩
      · exact Or.inl ⟨hw, rfl⟩
  · exact fun w hw => (Finset.mem_filter.mp hw).2
  · exact fun w hw => (Finset.mem_filter.mp hw).2

theorem support_bigConj_iff [Inhabited Atom] (M : KripkeModel W Atom)
    (l : List (Formula Atom)) (t : Finset W) :
    support M (bigConj l) t ↔ ∀ φ ∈ l, support M φ t := by
  induction l with
  | nil => simpa [bigConj] using support_verum M t
  | cons φ rest ih =>
    simp only [bigConj, support_conj, ih, List.forall_mem_cons]

/-- Team support of a flat disjunction of characteristic formulas: every
    world of the team is `k`-bisimilar to some representative in `S`. -/
theorem support_charDisj_iff [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (k : ℕ) (S : Finset W) (t : Finset W) :
    support M (bigDisj (S.toList.map (charFormula M k))) t ↔
      ∀ v ∈ t, ∃ w ∈ S, WorldBisim k M w M v := by
  have hNE : (bigDisj (S.toList.map (charFormula M k))).NEFree := by
    refine neFree_bigDisj _ (fun φ hφ => ?_)
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hφ
    exact neFree_charFormula M k w
  rw [neFree_flat M _ t hNE]
  constructor
  · intro h v hv
    obtain ⟨φ, hφ, hval⟩ := (classicalEval_bigDisj M v _).mp (h v hv)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hφ
    exact ⟨w, Finset.mem_toList.mp hw,
      (classicalEval_charFormula_iff_bisim M k w v).mp hval⟩
  · intro h v hv
    obtain ⟨w, hw, hb⟩ := h v hv
    exact (classicalEval_bigDisj M v _).mpr
      ⟨charFormula M k w, List.mem_map.mpr ⟨w, Finset.mem_toList.mpr hw, rfl⟩,
       (classicalEval_charFormula_iff_bisim M k w v).mpr hb⟩

/-- On singleton teams, support of the characteristic formula is exactly
    `k`-bisimilarity — the team-semantic face of the characterisation, via
    the NE-free classical collapse. -/
theorem support_charFormula_singleton_iff_bisim [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (k : ℕ) (w v : W) :
    support M (charFormula M k w) {v} ↔ WorldBisim k M w M v :=
  (classicalCollapse M _ v (neFree_charFormula M k w)).trans
    (classicalEval_charFormula_iff_bisim M k w v)

end BSML
