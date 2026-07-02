import Linglib.Phonology.Constraints.Profile
import Linglib.Phonology.OptimalityTheory.Tableau
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Elementary ranking conditions

OT's algebraic ranking-inference layer ([prince-2002]; [riggle-2009-complexity]). An
ERC value is a *sign*, so the alphabet is mathlib's `SignType` — `W` (`+1`,
winner-preferring), `L` (`-1`, loser-preferring), `e` (`0`, neutral) — which buys
`ercOfProfiles` as a coordinatewise `SignType.sign`, the antithetical ERC as pointwise
negation, per-coordinate entailment as `SignType`'s own order `L ≤ e ≤ W`, and the
decidability instances for free.

A ranking satisfies an ERC iff its sign vector, read in the ranking's priority order,
is lex-nonnegative — equivalently (`ERC.satisfiedBy_iff_dominance`), every
`L`-constraint is outranked by some `W`-constraint ([prince-2002] §0 (3)/(4)).

## Main declarations

* `ERCVal`, `ERC n` — the sign alphabet and sign vectors `Fin n → ERCVal`.
* `ERC.SatisfiedBy`, `ERCSet.Consistent`, `ERCSet.Entails` — the
  satisfaction/consistency/entailment algebra; `ERCSet.linearExtensions` the
  satisfying rankings as a `Finset`.
* `ercOfProfiles`, `tableauERC` — ERCs from violation profiles and winner–loser
  pairs; `satisfiedBy_ercOfProfiles_iff_le` bridges to the Core lex order.
* `simpleERC` — a single-`W`/single-`L` ERC, one Hasse edge `i ≫ j`
  ([merchant-riggle-2016]).
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

namespace ERC

variable (α : ERC n)

/-- An ERC is *trivial* if it has no `L`-constraint, so every ranking satisfies it. -/
def IsTrivial : Prop := ∀ k, α k ≠ .L

instance : Decidable α.IsTrivial := Fintype.decidableForallFintype

/-- An ERC is *contradictory* if it has an `L`-constraint but no
`W`-constraint, so no ranking satisfies it — Prince's class `𝓛⁺`. -/
def IsContradictory : Prop := (∀ k, α k ≠ .W) ∧ (∃ k, α k = .L)

instance : Decidable α.IsContradictory := inferInstanceAs (Decidable (_ ∧ _))

/-- A *simple* ERC has exactly one `W` and one `L`. -/
def IsSimple : Prop := (∃! w, α w = .W) ∧ (∃! l, α l = .L)

end ERC

/-! ### ERC satisfaction -/

@[simp] private theorem ERCVal.lt_zero_iff (x : ERCVal) : x < 0 ↔ x = .L := by
  revert x; decide

@[simp] private theorem ERCVal.zero_lt_iff (x : ERCVal) : 0 < x ↔ x = .W := by
  revert x; decide

namespace ERC

variable (r : Ranking n) (α : ERC n)

/-- A ranking `r` *satisfies* ERC `α` iff its sign vector, read in `r`'s priority
order, is lexicographically nonnegative. -/
def SatisfiedBy : Prop :=
  toLex (fun _ : Fin n => (0 : ERCVal)) ≤ toLex (fun p => α (r p))

/-- **Prince's leading-entry characterization** ([prince-2002] §0): a ranking
satisfies an ERC iff the `r`-earliest non-neutral constraint, when one exists, is
winner-preferring. -/
theorem satisfiedBy_iff_lead :
    α.SatisfiedBy r ↔ ∀ he : ∃ p, α (r p) ≠ .e, α (r (Fin.find _ he)) = .W :=
  ⟨fun h he => (ERCVal.zero_lt_iff _).mp ((lex_le_iff_lead _ _).mp h he),
   fun h => (lex_le_iff_lead _ _).mpr fun he => (ERCVal.zero_lt_iff _).mpr (h he)⟩

private theorem eq_L_of_ne {x : ERCVal} (h1 : x ≠ .e) (h2 : x ≠ .W) : x = .L := by
  cases x <;> simp_all

/-- A loser-preferring constraint witnesses a non-neutral position. -/
private theorem exists_ne_of_L {c : Fin n} (hc : α c = .L) : ∃ p, α (r p) ≠ .e :=
  ⟨r.symm c, by rw [Equiv.apply_symm_apply, hc]; decide⟩

/-- The leading constraint dominates every loser-preferring one. -/
private theorem lead_dominates {c : Fin n} (he : ∃ p, α (r p) ≠ .e)
    (hlead : α (r (Fin.find _ he)) = .W) (hc : α c = .L) :
    r.Dominates (r (Fin.find _ he)) c := by
  have hle : Fin.find _ he ≤ r.symm c :=
    Fin.find_le_of_pos he (by rw [Equiv.apply_symm_apply, hc]; decide)
  have hne : Fin.find _ he ≠ r.symm c := fun h => by
    rw [h, Equiv.apply_symm_apply, hc] at hlead
    exact absurd hlead (by decide)
  simpa [Ranking.Dominates] using hle.lt_of_ne hne

/-- [prince-2002] §0 (3): satisfaction unfolds to the `∀∃` dominance form — every
loser-preferring constraint is dominated by some winner-preferring one. -/
theorem satisfiedBy_iff_dominance :
    α.SatisfiedBy r ↔ ∀ c, α c = .L → ∃ w, α w = .W ∧ r.Dominates w c :=
  (satisfiedBy_iff_lead r α).trans
    ⟨fun hlead c hc =>
      have he := exists_ne_of_L r α hc
      ⟨r (Fin.find _ he), hlead he, lead_dominates r α he (hlead he) hc⟩,
     fun h he => Classical.byContradiction fun hW =>
      have ⟨w, hwW, hdom⟩ := h _ (eq_L_of_ne (Fin.find_spec he) hW)
      Fin.find_min he (by simpa [Ranking.Dominates] using hdom)
        (by rw [Equiv.apply_symm_apply, hwW]; decide)⟩

instance : Decidable (α.SatisfiedBy r) :=
  decidable_of_iff _ (satisfiedBy_iff_dominance r α).symm

/-- [prince-2002] §0 (4): the `∀∃` form is equivalent to the `∃∀` form — *some*
`W`-constraint dominates *every* `L`-constraint — because the ranking is total:
the leading constraint is the single witness. -/
theorem satisfiedBy_iff_exists_dominant [NeZero n] :
    α.SatisfiedBy r ↔ ∃ d, ∀ c, α c = .L → (α d = .W ∧ r.Dominates d c) := by
  refine ⟨fun hsat => ?_,
    fun ⟨d, hd⟩ => (satisfiedBy_iff_dominance r α).mpr fun c hc => ⟨d, hd c hc⟩⟩
  have hlead := (satisfiedBy_iff_lead r α).mp hsat
  by_cases he : ∃ p, α (r p) ≠ .e
  · exact ⟨r (Fin.find _ he), fun c hc => ⟨hlead he, lead_dominates r α he (hlead he) hc⟩⟩
  · exact ⟨0, fun c hc => (he (exists_ne_of_L r α hc)).elim⟩

/-- A trivial ERC is satisfied by every ranking. -/
theorem trivial_satisfiedBy {α : ERC n} (htriv : α.IsTrivial) (r : Ranking n) :
    α.SatisfiedBy r :=
  (satisfiedBy_iff_dominance r α).mpr fun l hl => absurd hl (htriv l)

end ERC

/-! ### Sets of ERCs -/

/-- A set of ERCs, carrying the satisfaction/consistency/entailment algebra of
OT grammars. Represented as a `List` so that `decide` can search the finitely
many rankings; entailment is invariant under reordering and duplication. -/
abbrev ERCSet (n : ℕ) := List (ERC n)

namespace ERCSet

variable (r : Ranking n) (E E' : ERCSet n)

/-- A ranking satisfies an ERC set iff it satisfies every member. -/
def SatisfiedBy : Prop :=
  ∀ α ∈ E, ERC.SatisfiedBy r α

instance : Decidable (SatisfiedBy r E) :=
  List.decidableBAll _ E

/-- An ERC set is *consistent* iff some ranking satisfies all its members. -/
def Consistent : Prop := ∃ r : Ranking n, SatisfiedBy r E

instance : Decidable (Consistent E) :=
  Fintype.decidableExistsFintype

/-- The rankings consistent with an ERC set, as a `Finset` — its *linear extensions*
([merchant-riggle-2016]). -/
def linearExtensions : Finset (Ranking n) :=
  Finset.univ.filter (fun r => SatisfiedBy r E)

@[simp] theorem mem_linearExtensions {E : ERCSet n} {r : Ranking n} :
    r ∈ E.linearExtensions ↔ SatisfiedBy r E := by
  simp [linearExtensions]

/-! ### Entailment -/

/-- `E` *entails* `E'` iff every ranking satisfying `E` also satisfies `E'`. -/
def Entails : Prop := ∀ r : Ranking n, SatisfiedBy r E → SatisfiedBy r E'

theorem entails_refl : Entails E E := fun _ h => h

theorem entails_trans {E₁ E₂ E₃ : ERCSet n}
    (h₁₂ : Entails E₁ E₂) (h₂₃ : Entails E₂ E₃) : Entails E₁ E₃ :=
  fun r hr => h₂₃ r (h₁₂ r hr)

/-- Adding an ERC strengthens the set: `α :: E` entails `E`. -/
theorem entails_of_cons (α : ERC n) : Entails (α :: E) E :=
  fun _ hr β hβ => hr β (List.mem_cons_of_mem α hβ)

/-- Pointwise characterization: `E` entails `E'` if it entails each member
singleton. -/
theorem entails_of_forall_mem {E E' : ERCSet n}
    (h : ∀ α ∈ E', Entails E [α]) : Entails E E' :=
  fun r hr α hα => h α hα r hr α (List.mem_cons.mpr (Or.inl rfl))

/-- An ERC set is *simple* if every member is a simple ERC — a set of Hasse edges
([merchant-riggle-2016]). -/
def IsSimpleSet (E : ERCSet n) : Prop := ∀ α ∈ E, α.IsSimple

end ERCSet

/-! ### Simple ERCs -/

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
    (simpleERC i j).SatisfiedBy r ↔ r.Dominates i j := by
  rw [ERC.satisfiedBy_iff_dominance]
  constructor
  · intro h
    obtain ⟨w, hw, hdom⟩ := h j ((simpleERC_eq_L_iff hij j).mpr rfl)
    rwa [(simpleERC_eq_W_iff w).mp hw] at hdom
  · intro hdom l hl
    rw [(simpleERC_eq_L_iff hij l).mp hl]
    exact ⟨i, simpleERC_apply_W, hdom⟩

/-- A simple ERC `i ≫ j` (with `i ≠ j`) is consistent. -/
theorem simpleERC_consistent {i j : Fin n} (hij : i ≠ j) :
    ERCSet.Consistent [simpleERC i j] := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨Ranking.id n, fun α hα => List.mem_singleton.mp hα ▸
      (simpleERC_satisfiedBy_iff hij _).mpr (Ranking.id_dominates_iff.mpr h)⟩
  · refine ⟨Equiv.swap i j, fun α hα => List.mem_singleton.mp hα ▸
      (simpleERC_satisfiedBy_iff hij _).mpr ?_⟩
    show (Equiv.swap i j).symm i < (Equiv.swap i j).symm j
    rw [Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact h

/-- `simpleERC i j` (with `i ≠ j`) is a simple ERC. -/
theorem simpleERC_isSimple {i j : Fin n} (hij : i ≠ j) : (simpleERC i j).IsSimple :=
  ⟨⟨i, simpleERC_apply_W, fun y hy => (simpleERC_eq_W_iff y).mp hy⟩,
   ⟨j, simpleERC_apply_L hij, fun y hy => (simpleERC_eq_L_iff hij y).mp hy⟩⟩

/-! ### Bridges: profiles, tableaux, and the Core lex order -/

/-- The ERC of a winner/loser violation-profile pair: the coordinatewise sign of
the violation difference ([prince-2002] §0; [riggle-2009-complexity] Def. 3). -/
def ercOfProfiles (winner loser : ViolationProfile n) : ERC n :=
  fun k => SignType.sign ((loser k : ℤ) - (winner k : ℤ))

/-- `ercOfProfiles` is `W` exactly where the winner has strictly fewer
violations. -/
theorem ercOfProfiles_eq_W_iff (w l : ViolationProfile n) (k : Fin n) :
    ercOfProfiles w l k = .W ↔ w k < l k := by
  simp only [ercOfProfiles, SignType.pos_eq_one, sign_eq_one_iff]; omega

/-- `ercOfProfiles` is `L` exactly where the winner has strictly more
violations. -/
theorem ercOfProfiles_eq_L_iff (w l : ViolationProfile n) (k : Fin n) :
    ercOfProfiles w l k = .L ↔ l k < w k := by
  simp only [ercOfProfiles, SignType.neg_eq_neg_one, sign_eq_neg_one_iff]; omega

/-- `ercOfProfiles` is `e` exactly where violations are equal. -/
theorem ercOfProfiles_eq_e_iff (w l : ViolationProfile n) (k : Fin n) :
    ercOfProfiles w l k = .e ↔ w k = l k := by
  simp only [ercOfProfiles, SignType.zero_eq_zero, sign_eq_zero_iff]; omega

/-- The *antithetical* ERC ([prince-2002] §2): swapping winner and loser negates it. -/
theorem ercOfProfiles_swap (w l : ViolationProfile n) :
    ercOfProfiles l w = -ercOfProfiles w l := by
  funext k
  rw [Pi.neg_apply, ercOfProfiles, ercOfProfiles, ← neg_sub, Left.sign_neg]

/-- Construct an ERC from a list of `ERCVal`, with a length proof discharged by
`decide` for literals: `def myERC : ERC 4 := ercOfList [.W, .e, .L, .e]`. -/
def ercOfList (vs : List ERCVal) (h : vs.length = n := by decide) : ERC n :=
  fun i => vs[i.val]'(by omega)

/-- ERC satisfaction *is* lexicographic domination: `r` satisfies the ERC of a
winner/loser pair iff the winner's profile, read in `r`'s priority order, is lex-≤
the loser's ([prince-2002]). -/
theorem satisfiedBy_ercOfProfiles_iff_le (r : Ranking n) (w l : ViolationProfile n) :
    (ercOfProfiles w l).SatisfiedBy r ↔
      toLex (fun p => w (r p)) ≤ toLex (fun p => l (r p)) := by
  rw [ERC.satisfiedBy_iff_dominance, lex_le_iff_forall]
  constructor
  · intro h p hp
    obtain ⟨c', hW, hdom⟩ := h (r p) ((ercOfProfiles_eq_L_iff w l (r p)).mpr hp)
    refine ⟨r.symm c', by simpa [Ranking.Dominates] using hdom, ?_⟩
    have := (ercOfProfiles_eq_W_iff w l c').mp hW
    rwa [Equiv.apply_symm_apply]
  · intro h c hc
    obtain ⟨p', hp'lt, hwin⟩ :=
      h (r.symm c) (by rw [Equiv.apply_symm_apply]; exact (ercOfProfiles_eq_L_iff w l c).mp hc)
    exact ⟨r p', (ercOfProfiles_eq_W_iff w l (r p')).mpr hwin,
      by simpa [Ranking.Dominates] using hp'lt⟩

/-- The ERC of a winner-loser pair `(w, l)` in tableau `t`: the ranking requirements
for `w` to beat `l`. -/
def tableauERC {C : Type*} [DecidableEq C] (t : Tableau C n) (w l : C) : ERC n :=
  ercOfProfiles (t.profile w) (t.profile l)

/-- Tableau form of the bridge: the winner-loser ERC is satisfied by `r` iff `r`
ranks the winner at-or-above the loser under the tableau's lex evaluation. -/
theorem tableauERC_satisfiedBy_iff {C : Type*} [DecidableEq C]
    (t : Tableau C n) (r : Ranking n) (w l : C) :
    (tableauERC t w l).SatisfiedBy r ↔
      toLex (fun p => t.profile w (r p)) ≤ toLex (fun p => t.profile l (r p)) :=
  satisfiedBy_ercOfProfiles_iff_le r (t.profile w) (t.profile l)

/-- At the identity ranking, ERC satisfaction is exactly the tableau's own lex
comparison — connecting ERC inference to `LexMinProblem`. -/
theorem tableauERC_satisfiedBy_id_iff {C : Type*} [DecidableEq C]
    (t : Tableau C n) (w l : C) :
    (tableauERC t w l).SatisfiedBy (Ranking.id n) ↔ t.profile w ≤ t.profile l := by
  rw [tableauERC_satisfiedBy_iff]; exact Iff.rfl

/-- A candidate is the tableau's optimum iff, under the identity ranking, its ERC
against every competitor is satisfied — ERC consistency *is* optimality. -/
theorem mem_optimal_iff_forall_satisfiedBy {C : Type*} [DecidableEq C]
    (t : Tableau C n) (w : C) :
    w ∈ t.optimal ↔
      w ∈ t.candidates ∧
        ∀ l ∈ t.candidates, (tableauERC t w l).SatisfiedBy (Ranking.id n) :=
  Tableau.mem_optimal_iff.trans <| and_congr_right fun _ =>
    forall₂_congr fun l _ => (tableauERC_satisfiedBy_id_iff t w l).symm

/-- **The `Sₙ` action on a fixed `CON` is the ERC theory**: `w` is optimal in
`Tableau.ofPerm con r` iff every winner–loser ERC of the identity-ranked tableau is
satisfied by `r` — factorial typology and ERC consistency are two readouts of one
symmetric-group action. -/
theorem Tableau.ofPerm_mem_optimal_iff_satisfiedBy {C : Type*} [DecidableEq C] {n : ℕ}
    (con : CON C n) (r : Ranking n) (candidates : List C) (h : candidates ≠ [])
    (w : C) :
    w ∈ (Tableau.ofPerm con r candidates h).optimal ↔
      w ∈ candidates.toFinset ∧
        ∀ l ∈ candidates.toFinset,
          (tableauERC (Tableau.ofPerm con (Equiv.refl _) candidates h) w l).SatisfiedBy r :=
  Tableau.mem_optimal_iff.trans <| and_congr_right fun _ => forall₂_congr fun l _ =>
    ⟨fun hle => (tableauERC_satisfiedBy_iff _ r w l).mpr hle,
     fun hsat => (tableauERC_satisfiedBy_iff _ r w l).mp hsat⟩

end OptimalityTheory
