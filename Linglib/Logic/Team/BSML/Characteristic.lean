module

public import Linglib.Logic.Team.BSML.Classical
public import Linglib.Logic.Team.BSML.Bisimulation

/-!
# Characteristic formulas for BSML

The depth-`k` characteristic (Hintikka) formula `χ_w^k` of a world `w` is an `NE`-free formula
true at exactly the worlds `k`-bisimilar to `w`. Being `NE`-free, it is supported by a team iff it
is classically true at each world of the team (`support_iff_forall_realize`), so the construction
is the classical one. The expressive completeness proof of `ExpressiveCompleteness.lean` uses it.

## Main definitions

* `verum`, `bigConj`, `bigDisj`: `⊤` as `p ∨ ¬p`, and finite conjunction and disjunction.
* `atomicType M w`: the conjunction of the atomic literals true at `w`.
* `charFormula M k w`: the depth-`k` characteristic formula of `w`.

## Main results

* `realize_charFormula_iff_bisim`: `χ_w^k` holds at `v` iff `w` and `v` are `k`-bisimilar.
* `support_charFormula_singleton_iff_bisim`: the same for singleton teams.

## References

* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
-/

@[expose] public section

namespace BSML

open ModalLogic

variable {W : Type*} {Atom : Type*}

/-! ### `⊤` and finite conjunction -/

/-- The tautology `p ∨ ¬p` for the default atom is `NE`-free, true at every world and
    supported by every team. BSML has no tautology without atoms. -/
def verum [Inhabited Atom] : Formula Atom :=
  .disj (.atom default) (.neg (.atom default))

@[simp] theorem realize_verum [Inhabited Atom] (M : KripkeModel W Atom) (w : W) :
    Realize M verum w := by
  cases M.val default w <;> simp [verum, Realize]

@[simp] theorem neFree_verum [Inhabited Atom] : (verum : Formula Atom).NEFree :=
  ⟨trivial, trivial⟩

/-- Finite conjunction of a list of formulas; the empty conjunction is `⊤`. -/
def bigConj [Inhabited Atom] : List (Formula Atom) → Formula Atom
  | [] => verum
  | φ :: rest => .conj φ (bigConj rest)

theorem realize_bigConj [Inhabited Atom] (M : KripkeModel W Atom) (w : W)
    (l : List (Formula Atom)) :
    Realize M (bigConj l) w ↔ ∀ φ ∈ l, Realize M φ w := by
  induction l with
  | nil => simp [bigConj]
  | cons φ rest ih => simp only [bigConj, Realize, List.forall_mem_cons, ih]

theorem neFree_bigConj [Inhabited Atom] (l : List (Formula Atom))
    (h : ∀ φ ∈ l, φ.NEFree) : (bigConj l).NEFree := by
  induction l with
  | nil => exact neFree_verum
  | cons φ rest ih =>
    exact ⟨h φ (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun ψ hψ => h ψ (List.mem_cons.mpr (Or.inr hψ)))⟩

/-! ### Atomic type (depth-0 Hintikka formula) -/

/-- The atomic type of `w` conjoins, over all atoms `p`, the literal `p` if `p` holds at `w`
    and `¬p` otherwise. It is the depth-0 characteristic formula. -/
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
theorem realize_atomicType [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (w v : W) :
    Realize M (atomicType M w) v ↔ ∀ p : Atom, M.val p v = M.val p w := by
  rw [atomicType, realize_bigConj]
  constructor
  · intro h p
    have hp := h _ (List.mem_map.mpr
      ⟨p, Finset.mem_toList.mpr (Finset.mem_univ p), rfl⟩)
    cases hb : M.val p w <;> simp [hb, Realize] at hp <;> simp [hp]
  · intro h φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    cases hb : M.val p w <;> simp [hb, Realize, h p]

/-- The atomic type of `w` holds at `v` iff `w` and `v` are 0-bisimilar. -/
theorem realize_atomicType_iff_bisim0 [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (w v : W) :
    Realize M (atomicType M w) v ↔ WorldBisim 0 M w M v := by
  rw [realize_atomicType]
  constructor
  · intro h p; exact (h p).symm
  · intro h p; exact (h p).symm

/-! ### Finite disjunction -/

@[simp] theorem not_realize_falsum [Inhabited Atom] (M : KripkeModel W Atom) (w : W) :
    ¬ Realize M .falsum w := by
  simp [Formula.falsum, Realize]

/-- Finite disjunction of a list of formulas; the empty disjunction is `⊥`. -/
def bigDisj [Inhabited Atom] : List (Formula Atom) → Formula Atom
  | [] => .falsum
  | φ :: rest => .disj φ (bigDisj rest)

theorem realize_bigDisj [Inhabited Atom] (M : KripkeModel W Atom) (w : W)
    (l : List (Formula Atom)) :
    Realize M (bigDisj l) w ↔ ∃ φ ∈ l, Realize M φ w := by
  induction l with
  | nil => simp [bigDisj]
  | cons φ rest ih => simp [bigDisj, ih]

theorem neFree_bigDisj [Inhabited Atom] (l : List (Formula Atom))
    (h : ∀ φ ∈ l, φ.NEFree) : (bigDisj l).NEFree := by
  induction l with
  | nil => exact Formula.neFree_falsum
  | cons φ rest ih =>
    exact ⟨h φ (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun ψ hψ => h ψ (List.mem_cons.mpr (Or.inr hψ)))⟩

/-! ### Characteristic formulas -/

/-- The depth-`k` characteristic (Hintikka) formula of `w` is its atomic type at depth `0`. At
    depth `k + 1` it conjoins the atomic type with `◇χ_v^k` for each successor `v` and with `□`
    of the disjunction of the successors' formulas. -/
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

/-- The depth-`k` characteristic formula of `w` holds at `v` iff `w` and `v` are `k`-bisimilar
    ([aloni-anttila-yang-2024] Theorem 3.3). -/
theorem realize_charFormula_iff_bisim [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (k : ℕ) (w v : W) :
    Realize M (charFormula M k w) v ↔ WorldBisim k M w M v := by
  induction k generalizing w v with
  | zero => exact realize_atomicType_iff_bisim0 M w v
  | succ k ih =>
    constructor
    · intro h
      simp only [charFormula, Realize] at h
      obtain ⟨hA, hB, hC⟩ := h
      refine ⟨fun p => ((realize_atomicType M w v).mp hA p).symm, ?_, ?_⟩
      · intro u hu
        have hposs := (realize_bigConj M v _).mp hB (.poss (charFormula M k u))
          (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩)
        obtain ⟨u', hu', hchar⟩ := realize_poss.mp hposs
        exact ⟨u', hu', (ih u u').mp hchar⟩
      · intro u' hu'
        have hd := realize_nec.mp hC u' hu'
        obtain ⟨φ, hφ, hval⟩ := (realize_bigDisj M u' _).mp hd
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hφ
        exact ⟨u, Finset.mem_toList.mp hu, (ih u u').mp hval⟩
    · intro hbisim
      simp only [charFormula, Realize]
      refine ⟨(realize_atomicType M w v).mpr (fun p => (hbisim.1 p).symm), ?_, ?_⟩
      · refine (realize_bigConj M v _).mpr (fun φ hφ => ?_)
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hφ
        obtain ⟨u', hu', hb⟩ := hbisim.2.1 u (Finset.mem_toList.mp hu)
        exact realize_poss.mpr ⟨u', hu', (ih u u').mpr hb⟩
      · refine realize_nec.mpr (fun u' hu' => ?_)
        obtain ⟨u, hu, hb⟩ := hbisim.2.2 u' hu'
        exact (realize_bigDisj M u' _).mpr
          ⟨charFormula M k u, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩,
           (ih u u').mpr hb⟩

/-! ### Team support of the auxiliary connectives -/

variable [DecidableEq W]

theorem support_verum [Inhabited Atom] (M : KripkeModel W Atom) (t : Finset W) :
    support M (verum (Atom := Atom)) t :=
  (support_iff_forall_realize neFree_verum).mpr fun w _ => realize_verum M w

theorem support_bigConj_iff [Inhabited Atom] (M : KripkeModel W Atom)
    (l : List (Formula Atom)) (t : Finset W) :
    support M (bigConj l) t ↔ ∀ φ ∈ l, support M φ t := by
  induction l with
  | nil => simpa [bigConj] using support_verum M t
  | cons φ rest ih =>
    simp only [bigConj, support_conj, ih, List.forall_mem_cons]

/-- A team supports the disjunction of the characteristic formulas of the worlds in `S` iff each
    of its worlds is `k`-bisimilar to one in `S`. -/
theorem support_charDisj_iff [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (k : ℕ) (S : Finset W) (t : Finset W) :
    support M (bigDisj (S.toList.map (charFormula M k))) t ↔
      ∀ v ∈ t, ∃ w ∈ S, WorldBisim k M w M v := by
  have hNE : (bigDisj (S.toList.map (charFormula M k))).NEFree := by
    refine neFree_bigDisj _ (fun φ hφ => ?_)
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hφ
    exact neFree_charFormula M k w
  rw [support_iff_forall_realize hNE]
  constructor
  · intro h v hv
    obtain ⟨φ, hφ, hval⟩ := (realize_bigDisj M v _).mp (h v hv)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hφ
    exact ⟨w, Finset.mem_toList.mp hw,
      (realize_charFormula_iff_bisim M k w v).mp hval⟩
  · intro h v hv
    obtain ⟨w, hw, hb⟩ := h v hv
    exact (realize_bigDisj M v _).mpr
      ⟨charFormula M k w, List.mem_map.mpr ⟨w, Finset.mem_toList.mpr hw, rfl⟩,
       (realize_charFormula_iff_bisim M k w v).mpr hb⟩

/-- On singleton teams, support of the characteristic formula is exactly
    `k`-bisimilarity — the team-semantic face of the characterisation, via
    the NE-free classical collapse. -/
theorem support_charFormula_singleton_iff_bisim [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) (k : ℕ) (w v : W) :
    support M (charFormula M k w) {v} ↔ WorldBisim k M w M v :=
  (support_singleton_iff_realize (neFree_charFormula M k w)).trans
    (realize_charFormula_iff_bisim M k w v)

end BSML
