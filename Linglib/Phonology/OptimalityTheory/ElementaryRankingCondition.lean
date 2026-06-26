import Linglib.Phonology.Constraints.Profile
import Linglib.Phonology.OptimalityTheory.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Elementary ranking conditions for Optimality Theory

Pure types and operations for OT's algebraic ranking-inference layer
([prince-2002]; [riggle-2009-complexity]). An ERC value is a **sign**, so the
alphabet is mathlib's `SignType`: `W` (`+1`, winner-preferring), `L` (`-1`,
loser-preferring), `e` (`0`, neutral). This buys, for free:

* `ercOfProfiles` is the coordinatewise `SignType.sign` of the violation
  difference;
* the *antithetical* ERC ([prince-2002] §2 negation) is pointwise `-`;
* per-coordinate **entailment** `L ≤ e ≤ W` is `SignType`'s own order;
* `DecidableEq` and the `LinearOrder` are inherited.

Satisfaction is grounded in the lexicographic order: a ranking satisfies an ERC
iff its sign vector, read in the ranking's priority order, is lex-nonnegative —
equivalently (`satisfiedBy_iff_dominance`), every `L`-constraint is outranked by
some `W`-constraint ([prince-2002] §0 (3)/(4)).

## Main declarations

* `ERCVal` — `SignType`, with `W`/`L`/`e` notation.
* `ERC n` — an ERC over `n` constraints, a sign vector `Fin n → ERCVal`.
* `Ranking n` — a constraint ranking, a permutation of `Fin n`.
* `ercOfProfiles` — the sign of a winner/loser violation-profile difference.
* `ERC.satisfiedBy`, `ERCSet.consistent`, `ERCSet.entails` — the
  satisfaction/consistency/entailment algebra.
* `satisfiedBy_ercOfProfiles_iff_le` — the bridge to the Core lex order.
* `tableauERC` — the ERC of a winner-loser pair in a tableau.
* `simpleERC` — a single-`W`/single-`L` ERC, one Hasse edge `i ≫ j`.

## References

* [prince-2002]
* [riggle-2009-complexity]
* [merchant-riggle-2016]
-/

open Core.Optimization.Evaluation

namespace OptimalityTheory
open Constraints

variable {n : ℕ}

/-! ### The three-valued alphabet `ERCVal` -/

/-- An ERC value is a sign ([prince-2002] §0): `W` (winner-preferring), `L`
(loser-preferring), `e` (neutral). This is mathlib's `SignType` — see `ERCVal.W`,
`ERCVal.L`, `ERCVal.e`. -/
abbrev ERCVal := SignType

namespace ERCVal

/-- Winner-preferring value (`+1`). -/
@[match_pattern] abbrev W : ERCVal := .pos
/-- Loser-preferring value (`-1`). -/
@[match_pattern] abbrev L : ERCVal := .neg
/-- Neutral / indifferent value (`0`). -/
@[match_pattern] abbrev e : ERCVal := .zero

end ERCVal

/-! ### Elementary ranking conditions -/

/-- An elementary ranking condition over `n` constraints: a sign vector
`Fin n → ERCVal` ([prince-2002] §0). -/
abbrev ERC (n : ℕ) := Fin n → ERCVal

/-- An ERC is *trivial* if it has no `L`-constraint, so every ranking
satisfies it. (Prince's "trivial" also includes the all-`L`/no-`W`
case, captured here by `isContradictory`.) -/
def ERC.isTrivial (α : ERC n) : Prop := ∀ k, α k ≠ .L

instance (α : ERC n) : Decidable α.isTrivial := Fintype.decidableForallFintype

/-- An ERC is *contradictory* if it has an `L`-constraint but no
`W`-constraint, so no ranking satisfies it — Prince's class `𝓛⁺`. -/
def ERC.isContradictory (α : ERC n) : Prop :=
  (∀ k, α k ≠ .W) ∧ (∃ k, α k = .L)

instance (α : ERC n) : Decidable α.isContradictory :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Rankings as permutations -/

/-- A ranking of `n` constraints: a permutation of `Fin n` ([prince-2002]'s
total domination order `≫`). `r i` is the constraint at rank position `i`
(position `0` is most dominant); `r.symm k` is the rank position of `k`. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)

/-- Constraint `i` *dominates* constraint `j` under `r`: it sits at a lower
(more dominant) rank position. -/
def Ranking.dominates (r : Ranking n) (i j : Fin n) : Prop :=
  r.symm i < r.symm j

instance (r : Ranking n) (i j : Fin n) : Decidable (r.dominates i j) :=
  inferInstanceAs (Decidable (r.symm i < r.symm j))

/-- The identity ranking: rank position equals constraint index. -/
def Ranking.id (n : ℕ) : Ranking n := Equiv.refl _

/-! ### Bridge: violation profiles to ERCs -/

/-- The ERC of a winner/loser violation-profile pair: the coordinatewise sign of
the violation difference ([prince-2002] §0; [riggle-2009-complexity] Def. 3). `W`
where the winner has fewer violations, `L` where more, `e` where equal. -/
def ercOfProfiles (winner loser : ViolationProfile n) : ERC n :=
  fun k => SignType.sign ((loser k : ℤ) - (winner k : ℤ))

/-- `ercOfProfiles` is `W` exactly where the winner has strictly fewer
violations. -/
theorem ercOfProfiles_eq_W_iff (w l : ViolationProfile n) (k : Fin n) :
    ercOfProfiles w l k = .W ↔ w k < l k := by
  show SignType.sign ((l k : ℤ) - (w k : ℤ)) = SignType.pos ↔ w k < l k
  rw [SignType.pos_eq_one, sign_eq_one_iff]; omega

/-- `ercOfProfiles` is `L` exactly where the winner has strictly more
violations. -/
theorem ercOfProfiles_eq_L_iff (w l : ViolationProfile n) (k : Fin n) :
    ercOfProfiles w l k = .L ↔ l k < w k := by
  show SignType.sign ((l k : ℤ) - (w k : ℤ)) = SignType.neg ↔ l k < w k
  rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff]; omega

/-- `ercOfProfiles` is `e` exactly where violations are equal. -/
theorem ercOfProfiles_eq_e_iff (w l : ViolationProfile n) (k : Fin n) :
    ercOfProfiles w l k = .e ↔ w k = l k := by
  show SignType.sign ((l k : ℤ) - (w k : ℤ)) = SignType.zero ↔ w k = l k
  rw [SignType.zero_eq_zero, sign_eq_zero_iff]; omega

/-- The *antithetical* ERC ([prince-2002] §2): swapping winner and loser negates
the ERC, `erc(l, w) = -erc(w, l)`. -/
theorem ercOfProfiles_swap (w l : ViolationProfile n) :
    ercOfProfiles l w = -ercOfProfiles w l := by
  funext k
  rw [Pi.neg_apply]
  rcases lt_trichotomy (w k) (l k) with h | h | h
  · rw [(ercOfProfiles_eq_L_iff l w k).mpr h, (ercOfProfiles_eq_W_iff w l k).mpr h]; decide
  · rw [(ercOfProfiles_eq_e_iff l w k).mpr h.symm, (ercOfProfiles_eq_e_iff w l k).mpr h]; decide
  · rw [(ercOfProfiles_eq_W_iff l w k).mpr h, (ercOfProfiles_eq_L_iff w l k).mpr h]; decide

/-- Construct an ERC from a list of `ERCVal`, with a length proof discharged by
`decide` for literals: `def myERC : ERC 4 := ercOfList [.W, .e, .L, .e]`. -/
def ercOfList (vs : List ERCVal) (h : vs.length = n := by decide) : ERC n :=
  fun i => vs[i.val]'(by omega)

/-! ### ERC satisfaction -/

private theorem ERCVal.lt_zero_iff (x : ERCVal) : x < 0 ↔ x = .L := by revert x; decide
private theorem ERCVal.zero_lt_iff (x : ERCVal) : 0 < x ↔ x = .W := by revert x; decide

/-- A ranking `r` *satisfies* ERC `α` iff its sign vector, read in `r`'s priority
order, is lexicographically nonnegative — the leading nonzero entry is `W`.
Equivalently (`satisfiedBy_iff_dominance`, [prince-2002] §0 (3)), every
`L`-constraint is outranked by some `W`-constraint. -/
def ERC.satisfiedBy (r : Ranking n) (α : ERC n) : Prop :=
  toLex (fun _ : Fin n => (0 : ERCVal)) ≤ toLex (fun p => α (r p))

/-- [prince-2002] §0 (3): satisfaction unfolds to the `∀∃` dominance form — every
loser-preferring constraint is dominated by some winner-preferring one. -/
theorem ERC.satisfiedBy_iff_dominance (r : Ranking n) (α : ERC n) :
    α.satisfiedBy r ↔ ∀ c, α c = .L → ∃ w, α w = .W ∧ r.dominates w c := by
  unfold ERC.satisfiedBy
  rw [lex_le_iff_forall]
  constructor
  · intro h c hc
    have hp : α (r (r.symm c)) < 0 := by rw [Equiv.apply_symm_apply, hc]; decide
    obtain ⟨p', hp'lt, hp'pos⟩ := h (r.symm c) hp
    exact ⟨r p', (ERCVal.zero_lt_iff _).mp hp'pos,
      by unfold Ranking.dominates; rwa [Equiv.symm_apply_apply]⟩
  · intro h p hp
    obtain ⟨w, hwW, hwdom⟩ := h (r p) ((ERCVal.lt_zero_iff _).mp hp)
    refine ⟨r.symm w,
      by unfold Ranking.dominates at hwdom; rwa [Equiv.symm_apply_apply] at hwdom, ?_⟩
    rw [Equiv.apply_symm_apply, hwW]; decide

instance (r : Ranking n) (α : ERC n) : Decidable (α.satisfiedBy r) :=
  decidable_of_iff _ (ERC.satisfiedBy_iff_dominance r α).symm

/-- [prince-2002] §0 (4): the `∀∃` form is equivalent to the `∃∀` form — *some*
`W`-constraint dominates *every* `L`-constraint — because the ranking is total
(Prince's footnote 3). Requires a nonempty constraint set. -/
theorem ERC.satisfiedBy_iff_exists_dominant [NeZero n] (r : Ranking n) (α : ERC n) :
    α.satisfiedBy r ↔ ∃ d, ∀ c, α c = .L → (α d = .W ∧ r.dominates d c) := by
  rw [ERC.satisfiedBy_iff_dominance]
  constructor
  · intro h
    by_cases hL : ∃ c, α c = .L
    · obtain ⟨c0, hc0⟩ := hL
      have hSne : (Finset.univ.filter (fun c => α c = .L)).Nonempty :=
        ⟨c0, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc0⟩
      obtain ⟨cstar, hcstar_mem, hcstar_min⟩ :=
        Finset.exists_min_image _ (fun c => (r.symm c : ℕ)) hSne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcstar_mem
      obtain ⟨w, hwW, hwdom⟩ := h cstar hcstar_mem
      refine ⟨w, fun c hc => ⟨hwW, ?_⟩⟩
      have hmin : (r.symm cstar : ℕ) ≤ (r.symm c : ℕ) :=
        hcstar_min c (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc)
      unfold Ranking.dominates at hwdom ⊢
      omega
    · simp only [not_exists] at hL
      exact ⟨(0 : Fin n), fun c hc => absurd hc (hL c)⟩
  · rintro ⟨d, hd⟩ c hc
    exact ⟨d, hd c hc⟩

/-- A trivial ERC is satisfied by every ranking. -/
theorem ERC.trivial_satisfiedBy {α : ERC n} (htriv : α.isTrivial) (r : Ranking n) :
    α.satisfiedBy r :=
  (ERC.satisfiedBy_iff_dominance r α).mpr (fun l hl => absurd hl (htriv l))

/-! ### Sets of ERCs -/

/-- A set of ERCs, carrying the satisfaction/consistency/entailment algebra of
OT grammars. Represented as a `List` so that `decide` can search the finitely
many rankings; entailment is invariant under reordering and duplication. -/
abbrev ERCSet (n : ℕ) := List (ERC n)

/-- A ranking satisfies an ERC set iff it satisfies every member. -/
def ERCSet.satisfiedBy (r : Ranking n) (E : ERCSet n) : Prop :=
  ∀ α ∈ E, ERC.satisfiedBy r α

instance (r : Ranking n) (E : ERCSet n) : Decidable (ERCSet.satisfiedBy r E) :=
  List.decidableBAll _ E

/-- An ERC set is *consistent* iff some ranking satisfies all its members. The
definition searches over all `n!` rankings; for large `n` use ERC fusion. -/
def ERCSet.consistent (E : ERCSet n) : Prop :=
  ∃ r : Ranking n, ERCSet.satisfiedBy r E

instance (E : ERCSet n) : Decidable (ERCSet.consistent E) :=
  Fintype.decidableExistsFintype

/-- The rankings consistent with an ERC set — its *linear extensions* in the
terminology of [merchant-riggle-2016]. -/
def ERCSet.linearExtensions (E : ERCSet n) : Set (Ranking n) :=
  { r | ERCSet.satisfiedBy r E }

/-! ### Entailment -/

/-- `E` *entails* `E'` iff every ranking satisfying `E` also satisfies `E'` —
equivalently, the linear extensions of `E` are contained in those of `E'`.
This is the natural preorder on ERC sets; mutual entailment means the two sets
describe the same OT grammar. (At the single-coordinate level, entailment is just
`SignType`'s order `L ≤ e ≤ W`.) -/
def ERCSet.entails (E E' : ERCSet n) : Prop :=
  ∀ r : Ranking n, ERCSet.satisfiedBy r E → ERCSet.satisfiedBy r E'

theorem ERCSet.entails_refl (E : ERCSet n) : ERCSet.entails E E := fun _ h => h

theorem ERCSet.entails_trans {E₁ E₂ E₃ : ERCSet n}
    (h₁₂ : ERCSet.entails E₁ E₂) (h₂₃ : ERCSet.entails E₂ E₃) :
    ERCSet.entails E₁ E₃ := fun r hr => h₂₃ r (h₁₂ r hr)

/-- Adding an ERC strengthens the set: `α :: E` entails `E` (more requirements,
fewer satisfying rankings). -/
theorem ERCSet.entails_of_cons (α : ERC n) (E : ERCSet n) :
    ERCSet.entails (α :: E) E :=
  fun _ hr β hβ => hr β (List.mem_cons_of_mem α hβ)

/-- Pointwise characterization: `E` entails `E'` if it entails each member
singleton. -/
theorem ERCSet.entails_of_forall_mem {E E' : ERCSet n}
    (h : ∀ α ∈ E', ERCSet.entails E [α]) : ERCSet.entails E E' :=
  fun r hr α hα => h α hα r hr α (List.mem_cons.mpr (Or.inl rfl))

/-! ### Bridge: tableaux and the Core lex order -/

/-- ERC satisfaction *is* lexicographic domination: `r` satisfies the ERC of a
winner/loser pair iff the winner's profile, read in `r`'s priority order, is
lex-≤ the loser's ([prince-2002]: an ERC holds of a ranking iff `a ≥ b` holds of
the candidates). This grounds ERC inference in the Core lex evaluation order. -/
theorem satisfiedBy_ercOfProfiles_iff_le (r : Ranking n) (w l : ViolationProfile n) :
    (ercOfProfiles w l).satisfiedBy r ↔
      toLex (fun p => w (r p)) ≤ toLex (fun p => l (r p)) := by
  rw [ERC.satisfiedBy_iff_dominance, lex_le_iff_forall]
  constructor
  · intro h p hp
    obtain ⟨c', hW, hdom⟩ := h (r p) ((ercOfProfiles_eq_L_iff w l (r p)).mpr hp)
    refine ⟨r.symm c',
      by unfold Ranking.dominates at hdom; rwa [Equiv.symm_apply_apply] at hdom, ?_⟩
    have := (ercOfProfiles_eq_W_iff w l c').mp hW
    rwa [Equiv.apply_symm_apply]
  · intro h c hc
    obtain ⟨p', hp'lt, hwin⟩ :=
      h (r.symm c) (by rw [Equiv.apply_symm_apply]; exact (ercOfProfiles_eq_L_iff w l c).mp hc)
    exact ⟨r p', (ercOfProfiles_eq_W_iff w l (r p')).mpr hwin,
      by unfold Ranking.dominates; rwa [Equiv.symm_apply_apply]⟩

/-- The ERC of a winner-loser pair `(w, l)` in tableau `t`: the ranking
requirements for `w` to beat `l`. Every tableau that selects a winner implicitly
generates one of these for each winner-loser pair. -/
def tableauERC {C : Type*} [DecidableEq C] (t : Tableau C n) (w l : C) : ERC n :=
  ercOfProfiles (t.profile w) (t.profile l)

/-- Tableau form of the bridge: the winner-loser ERC is satisfied by `r` iff `r`
ranks the winner at-or-above the loser under the tableau's lex evaluation. -/
theorem tableauERC_satisfiedBy_iff {C : Type*} [DecidableEq C]
    (t : Tableau C n) (r : Ranking n) (w l : C) :
    (tableauERC t w l).satisfiedBy r ↔
      toLex (fun p => t.profile w (r p)) ≤ toLex (fun p => t.profile l (r p)) :=
  satisfiedBy_ercOfProfiles_iff_le r (t.profile w) (t.profile l)

/-- At the identity ranking, ERC satisfaction is exactly the tableau's own lex
comparison — connecting ERC inference to `LexMinProblem`. -/
theorem tableauERC_satisfiedBy_id_iff {C : Type*} [DecidableEq C]
    (t : Tableau C n) (w l : C) :
    (tableauERC t w l).satisfiedBy (Ranking.id n) ↔ t.profile w ≤ t.profile l := by
  rw [tableauERC_satisfiedBy_iff]; exact Iff.rfl

/-- A candidate is the tableau's optimum iff, under the identity ranking, its ERC
against every competitor is satisfied — ERC consistency *is* optimality. -/
theorem isOptimal_iff_forall_satisfiedBy {C : Type*} [DecidableEq C]
    (t : Tableau C n) (w : C) :
    t.IsOptimal w ↔
      w ∈ t.candidates ∧
        ∀ l ∈ t.candidates, (tableauERC t w l).satisfiedBy (Ranking.id n) := by
  constructor
  · rintro ⟨hmem, hmin⟩
    exact ⟨hmem, fun l hl => (tableauERC_satisfiedBy_id_iff t w l).mpr (hmin l hl)⟩
  · rintro ⟨hmem, hsat⟩
    exact ⟨hmem, fun l hl => (tableauERC_satisfiedBy_id_iff t w l).mp (hsat l hl)⟩

/-! ### Simple ERCs -/

/-- A *simple* ERC has exactly one `W` and one `L`: a single dominance
requirement `i ≫ j`. Simple ERCs are the Hasse edges of the ranking partial
order; sets of them describe exactly the rankings representable as partial
orders ([merchant-riggle-2016]). -/
def ERC.isSimple (α : ERC n) : Prop :=
  (∃! w, α w = .W) ∧ (∃! l, α l = .L)

/-- The simple ERC asserting constraint `i` must dominate constraint `j`; all
other constraints are `e`. -/
def simpleERC (i j : Fin n) : ERC n :=
  fun k => if k = i then .W else if k = j then .L else .e

/-- The only `W` of `simpleERC i j` is at `i`. -/
theorem simpleERC_eq_W_iff {i j : Fin n} (k : Fin n) :
    simpleERC i j k = .W ↔ k = i := by
  simp only [simpleERC]; split_ifs with h₁ h₂ <;> simp_all

/-- The only `L` of `simpleERC i j` (with `i ≠ j`) is at `j`. -/
theorem simpleERC_eq_L_iff {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    simpleERC i j k = .L ↔ k = j := by
  simp only [simpleERC]; split_ifs with h₁ h₂ <;> simp_all

@[simp] theorem simpleERC_apply_W {i j : Fin n} : simpleERC i j i = .W :=
  (simpleERC_eq_W_iff i).mpr rfl

theorem simpleERC_apply_L {i j : Fin n} (hij : i ≠ j) : simpleERC i j j = .L :=
  (simpleERC_eq_L_iff hij j).mpr rfl

/-- A simple ERC `i ≫ j` (with `i ≠ j`) is satisfied by `r` iff `i` dominates
`j` under `r`. -/
theorem simpleERC_satisfiedBy_iff {i j : Fin n} (hij : i ≠ j) (r : Ranking n) :
    (simpleERC i j).satisfiedBy r ↔ r.dominates i j := by
  rw [ERC.satisfiedBy_iff_dominance]
  constructor
  · intro h
    obtain ⟨w, hw, hdom⟩ := h j ((simpleERC_eq_L_iff hij j).mpr rfl)
    rwa [(simpleERC_eq_W_iff w).mp hw] at hdom
  · intro hdom l hl
    rw [(simpleERC_eq_L_iff hij l).mp hl]
    exact ⟨i, simpleERC_apply_W, hdom⟩

/-- A simple ERC `i ≫ j` (with `i ≠ j`) is consistent: the identity ranking
witnesses it when `i < j`, and the transposition `(i, j)` otherwise. -/
theorem simpleERC_consistent {i j : Fin n} (hij : i ≠ j) :
    ERCSet.consistent [simpleERC i j] := by
  by_cases hlt : i.val < j.val
  · refine ⟨Ranking.id n, fun α hα => ?_⟩
    rw [List.mem_singleton.mp hα]
    refine (simpleERC_satisfiedBy_iff hij _).mpr ?_
    show (Ranking.id n).symm i < (Ranking.id n).symm j
    simpa [Ranking.id, Equiv.refl] using hlt
  · have hgt : j.val < i.val :=
      lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Fin.val_injective.ne hij.symm)
    refine ⟨(Equiv.swap i j : Ranking n), fun α hα => ?_⟩
    rw [List.mem_singleton.mp hα]
    refine (simpleERC_satisfiedBy_iff hij _).mpr ?_
    show (Equiv.swap i j).symm i < (Equiv.swap i j).symm j
    rw [Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact hgt

end OptimalityTheory
