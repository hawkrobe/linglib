import Linglib.Studies.ChristopoulosZompi2023
import Linglib.Core.Optimization.Evaluation
import Mathlib.Data.Finset.Powerset

/-!
# Zompì 2023: *ABA in multidimensional paradigms, Max/Dep Eval
[zompi-2023]

Exponent selection as ranked violable faithfulness: per-dimension `Max` and
`Dep` constraints ([wolf-2008], after [mccarthy-prince-1995]) under
strict-domination Eval ([prince-smolensky-1993]). An exponent may be both
underspecified and overspecified for its context, each departure penalized
but neither fatal — the midpoint between DM's Underspecification and
nanosyntax's Overspecification ([starke-2009]).

Contexts are the cumulative case × number decompositions (the dissertation's
(163)): NOM ∅ ⊂ ACC {κ_dep} ⊂ DAT {κ_dep, κ_dat} on one dimension
([smith-moskal-xu-kang-bobaljik-2019], [caha-2009]), SG ∅ ⊂ PL {#pl} on the
other — realized here over `ChristopoulosZompi2023.K`, with specs carried by
the same rule type the Subset-Principle study runs on. What changes is only
the competition.

Main results:

* `mem_eval_iff` / `mem_eval_iff_lexMins` — the strict-domination Eval cut
  cascade is exactly lexicographic minimization: an Eval survivor is a
  `LexMinProblem.lexMins` optimum (the shared core `OptimalityTheory.Tableau`
  aliases), so this Max/Dep competition and phonological OT are one engine.
* `eastFrisian_pattern` / `malayalam_pattern` — the two minimally compliant
  Russian-doll patterns of §4.1.3: East Frisian 3M (*h-äi, z-äi; h-um, h-ör*)
  puts ABA on ⟨NOM.SG, NOM.PL, ACC.PL⟩ with AAA on ⟨NOM.SG, ACC.SG, ACC.PL⟩;
  Malayalam 1EX (*ñān, ñaŋŋaḷ; enne, ñaŋŋaḷe*) the reverse — same two
  candidate specifications, opposite rankings of the Dep pair and of the Max
  pair.
* `checkerboard_excluded` — the system's novel exclusion: over every ranking
  of the four relativized constraints and every two-candidate vocabulary on
  the paradigm's feature space, a candidate winning NOM.SG and ACC.PL also
  wins ACC.SG or NOM.PL (kernel-checked exhaustively);
  `checkerboard_excluded_general` states the vocabulary-general claim (the
  dissertation's W/T/L leftmost-column argument), left as a `sorry` TODO.
* `unidimensional_ABA_excluded` — *ABA down the singular case column survives
  the move to violable constraints, over every ranking (§4.1.4).
* `depTop_eq_subsetPrinciple` — [wolf-2008]'s mimicry, connecting the two
  engines: with global `Dep` outranking global `Max`, whenever some candidate
  is subset-applicable, unique Max/Dep winners are exactly the
  Subset-Principle-with-feature-counting winners of
  `ChristopoulosZompi2023.pattern` ([halle-1997]'s counting formulation). The
  dual corner (`Max ≫ Dep`) is nanosyntax's least-specified
  non-underspecified choice.
-/

namespace Zompi2023

open Morphology Morphology.Decomposition ChristopoulosZompi2023

/-- The inflectional dimensions the constraints are relativized to. -/
inductive Dim | kase | num | gen
  deriving DecidableEq, Repr

/-- Which dimension each feature of `ChristopoulosZompi2023.K` belongs to. -/
def dimOf : K → Dim
  | .k0 | .k1 | .k2 | .k3 => .kase
  | .s0 | .p0 => .num
  | .m0 | .f0 => .gen

/-- A case-number cell. -/
structure ZCell where
  case : Case3
  num : LNum
  deriving DecidableEq, Fintype, Repr

/-- The cumulative two-dimensional decomposition ((163)): SCC-style case
(NOM ∅ ⊂ ACC {k₁} ⊂ DAT {k₁,k₂}) crossed with cumulative number
(SG ∅ ⊂ PL {p₀}). -/
def zdecomp (c : ZCell) : Finset K :=
  scc c.case ∪ (match c.num with | .sg => ∅ | .pl => {.p0})

variable {F : Type*}

/-- A candidate: the Subset-Principle study's rule carrier, re-read as an OT
candidate — the spec may now be unfaithful to the context in both
directions. -/
abbrev Cand (F : Type*) := Rule ZCell zdecomp F

/-- The constraint inventory: `Max`/`Dep` relativized to a dimension ((162)),
plus the unrelativized globals of (161) used for the corner rankings. -/
inductive Con | maxD (d : Dim) | depD (d : Dim) | maxG | depG
  deriving DecidableEq, Repr

/-- Violation counts: `Max`-type stars for expected features the spec lacks,
`Dep`-type stars for spurious features the spec adds, counted on one
dimension or globally. -/
def viol : Con → ZCell → Cand F → ℕ
  | .maxD d, c, r => ((zdecomp c \ r.feats).filter (fun k => dimOf k = d)).card
  | .depD d, c, r => ((r.feats \ zdecomp c).filter (fun k => dimOf k = d)).card
  | .maxG, c, r => (zdecomp c \ r.feats).card
  | .depG, c, r => (r.feats \ zdecomp c).card

/-- One Eval cut: keep the candidates with fewest violations of `C`. -/
def cut (c : ZCell) (cands : List (Cand F)) (C : Con) : List (Cand F) :=
  match (cands.map (viol C c)).min? with
  | none => cands
  | some m => cands.filter (fun r => viol C c r = m)

/-- Strict-domination Eval: successive cuts down the ranking, top constraint
first. -/
def eval (rk : List Con) (v : List (Cand F)) (c : ZCell) : List (Cand F) :=
  rk.foldl (cut c) v

/-- `r` is the unique survivor of Eval at `c`. -/
def Wins (rk : List Con) (v : List (Cand F)) (c : ZCell) (r : Cand F) : Prop :=
  eval rk v c = [r]

instance [DecidableEq F] {rk : List Con} {v : List (Cand F)} {c : ZCell}
    {r : Cand F} : Decidable (Wins rk v c r) :=
  inferInstanceAs (Decidable (eval rk v c = [r]))

/-! ### The shared lexicographic-minimization core

`eval` is the strict-domination filter cascade; the phonology OT engine is
lexicographic arg-min over a fixed-length violation profile. Its foundation is
`Core.Optimization.Evaluation.LexMinProblem` — a finite candidate set scored by
a `Lex (Fin n → ℕ)` profile, exposing the winner set `LexMinProblem.lexMins`;
`OptimalityTheory.Tableau` is a definitional alias for it (`Tableau := LexMinProblem`,
`Tableau.optimal := lexMins`). `eval` and this engine are one object, not two
parallel engines: `mem_eval_iff` characterizes an Eval survivor as a
lexicographic minimizer of the ranked violation vector, and
`mem_eval_iff_lexMins` reads that off the `LexMinProblem` whose candidates are
`v` and whose profile is that vector. So morphological Max/Dep Eval and
phonological OT provably share the same lexicographic core. -/

section SharedCore
open Core.Optimization.Evaluation LexMinProblem

/-- The candidate's violation vector at a cell, ordered by the ranking — the
`List ℕ` reading of the OT `ViolationProfile`. -/
def rankedViols (rk : List Con) (c : ZCell) (r : Cand F) : List ℕ :=
  rk.map (fun C => viol C c r)

@[simp] theorem rankedViols_nil (c : ZCell) (r : Cand F) : rankedViols [] c r = [] :=
  rfl

@[simp] theorem rankedViols_cons (C : Con) (rk : List Con) (c : ZCell) (r : Cand F) :
    rankedViols (C :: rk) c r = viol C c r :: rankedViols rk c r := rfl

/-- A candidate survives one Eval cut iff it minimises that constraint over the
field: the cut keeps exactly the constraint's arg-min. -/
theorem mem_cut_iff {C : Con} {c : ZCell} {v : List (Cand F)} {r : Cand F} :
    r ∈ cut c v C ↔ r ∈ v ∧ ∀ s ∈ v, viol C c r ≤ viol C c s := by
  unfold cut
  cases hm : (v.map (viol C c)).min? with
  | none =>
    have hv : v = [] := by simpa using List.min?_eq_none_iff.mp hm
    subst hv; simp
  | some m =>
    obtain ⟨hmem, hmin⟩ := List.min?_eq_some_iff (α := ℕ) |>.mp hm
    obtain ⟨s₀, hs₀v, hs₀⟩ := List.mem_map.mp hmem
    rw [List.mem_filter]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hrv, hrm⟩
      exact ⟨hrv, fun s hs => hrm ▸ hmin _ (List.mem_map_of_mem hs)⟩
    · rintro ⟨hrv, hle⟩
      exact ⟨hrv, le_antisymm ((hle _ hs₀v).trans_eq hs₀)
        (hmin _ (List.mem_map_of_mem hrv))⟩

/-- **Eval is lexicographic minimization.** A candidate survives the whole cut
cascade iff its ranked violation vector is lexicographically ≤ every rival's:
the strict-domination cut sequence computes exactly the lex-min set. -/
theorem mem_eval_iff {rk : List Con} {v : List (Cand F)} {c : ZCell} {r : Cand F} :
    r ∈ eval rk v c ↔ r ∈ v ∧ ∀ s ∈ v, LexLE (rankedViols rk c r) (rankedViols rk c s) := by
  induction rk generalizing v with
  | nil => simp [eval, LexLE]
  | cons C rk ih =>
    rw [show eval (C :: rk) v c = eval rk (cut c v C) c from rfl, ih]
    constructor
    · rintro ⟨hrcut, htail⟩
      obtain ⟨hrv, hrmin⟩ := mem_cut_iff.mp hrcut
      refine ⟨hrv, fun s hs => ?_⟩
      rw [rankedViols_cons, rankedViols_cons, lexLE_cons_cons_iff]
      rcases lt_or_eq_of_le (hrmin s hs) with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, htail s (mem_cut_iff.mpr ⟨hs, fun t ht => heq ▸ hrmin t ht⟩)⟩
    · rintro ⟨hrv, hcons⟩
      have hrmin : ∀ s ∈ v, viol C c r ≤ viol C c s := fun s hs => by
        have := hcons s hs
        rw [rankedViols_cons, rankedViols_cons, lexLE_cons_cons_iff] at this
        rcases this with hlt | ⟨heq, _⟩
        · exact le_of_lt hlt
        · exact le_of_eq heq
      refine ⟨mem_cut_iff.mpr ⟨hrv, hrmin⟩, fun s hs => ?_⟩
      obtain ⟨hsv, hsmin⟩ := mem_cut_iff.mp hs
      have := hcons s hsv
      rw [rankedViols_cons, rankedViols_cons, lexLE_cons_cons_iff] at this
      rcases this with hlt | ⟨_, htail⟩
      · exact absurd (hsmin r hrv) (not_le_of_gt hlt)
      · exact htail

private theorem map_eq_ofFn_get {α β : Type*} (l : List α) (f : α → β) :
    l.map f = List.ofFn (fun i : Fin l.length => f (l.get i)) := by
  apply List.ext_getElem <;> simp

/-- The ranked violation vector is the fixed-length OT profile spelled out as a
list. -/
theorem rankedViols_eq_ofFn (rk : List Con) (c : ZCell) (r : Cand F) :
    rankedViols rk c r = List.ofFn (fun i : Fin rk.length => viol (rk.get i) c r) :=
  map_eq_ofFn_get rk (fun C => viol C c r)

/-- The Eval competition as a `LexMinProblem` — the engine `OptimalityTheory.Tableau`
aliases: candidate set `v`, profile the ranked violation vector (rank position `i`
reading the `i`-th constraint as a violation count via `lexFinNatOf`). This is a
phonological OT tableau with morphological Max/Dep constraints. -/
def zTableau [DecidableEq F] (rk : List Con) (v : List (Cand F)) (c : ZCell)
    (hv : v ≠ []) : LexMinProblem (Cand F) rk.length where
  candidates := v.toFinset
  profile := lexFinNatOf (fun i => viol (rk.get i) c)
  nonempty := let ⟨x, hx⟩ := List.exists_mem_of_ne_nil v hv; ⟨x, List.mem_toFinset.mpr hx⟩

/-- **Eval and OT are one engine.** An Eval survivor is exactly a lex-minimizer
of the OT tableau `zTableau`: the morphological Max/Dep competition *is* a
phonological OT tableau (`LexMinProblem`) over the shared
lexicographic-minimization core. -/
theorem mem_eval_iff_lexMins [DecidableEq F] {rk : List Con} {v : List (Cand F)}
    {c : ZCell} {r : Cand F} (hv : v ≠ []) :
    r ∈ eval rk v c ↔ r ∈ (zTableau rk v c hv).lexMins := by
  rw [mem_eval_iff, LexMinProblem.mem_lexMins_iff]
  simp only [LexMinProblem.IsLexMin]
  refine and_congr List.mem_toFinset.symm (forall_congr' fun s => ?_)
  refine imp_congr List.mem_toFinset.symm ?_
  rw [rankedViols_eq_ofFn, rankedViols_eq_ofFn, lexLE_ofFn]
  rfl

end SharedCore

/-- The 24 rankings of the four dimension-relativized constraints of the
case-number paradigm, enumerated (kernel-reducible, unlike
`List.permutations`). -/
def rankings : List (List Con) :=
  let M : Con := .maxD .kase; let N : Con := .maxD .num
  let D : Con := .depD .kase; let E : Con := .depD .num
  [[M,N,D,E],[M,N,E,D],[M,D,N,E],[M,D,E,N],[M,E,N,D],[M,E,D,N],
   [N,M,D,E],[N,M,E,D],[N,D,M,E],[N,D,E,M],[N,E,M,D],[N,E,D,M],
   [D,M,N,E],[D,M,E,N],[D,N,M,E],[D,N,E,M],[D,E,M,N],[D,E,N,M],
   [E,M,N,D],[E,M,D,N],[E,N,M,D],[E,N,D,M],[E,D,M,N],[E,D,N,M]]

/-- The candidate feature space of the case-number paradigm. -/
def featSpace : Finset K := {.k1, .k2, .p0}

/-- The possible context specifications ((163)): feature-structural
entailments hold inside specs too — κ_dat only alongside κ_dep. The
dissertation makes this well-formedness an entry condition on candidates and
flags it as crucial for unidimensional *ABA. -/
def specSpace : List (Finset K) :=
  [∅, {.k1}, {.k1, .k2}, {.p0}, {.k1, .p0}, {.k1, .k2, .p0}]

/-! ### The two minimally compliant patterns (§4.1.3) -/

/-- East Frisian 3M candidates ((165)): *z-* specified for plural, *h-* for
accusative. -/
def eastFrisian : List (Cand String) := [⟨{.p0}, "z"⟩, ⟨{.k1}, "h"⟩]

/-- East Frisian ((164), (166)): ranking `Dep(#) ≫ Dep(K)` and
`Max(K) ≫ Max(#)` yields *h-* in NOM.SG, ACC.SG, ACC.PL and *z-* in NOM.PL —
ABA along ⟨NOM.SG, NOM.PL, ACC.PL⟩, AAA along ⟨NOM.SG, ACC.SG, ACC.PL⟩. -/
theorem eastFrisian_pattern :
    Wins [.depD .num, .depD .kase, .maxD .kase, .maxD .num] eastFrisian
        ⟨.nom, .sg⟩ ⟨{.k1}, "h"⟩ ∧
      Wins [.depD .num, .depD .kase, .maxD .kase, .maxD .num] eastFrisian
        ⟨.nom, .pl⟩ ⟨{.p0}, "z"⟩ ∧
      Wins [.depD .num, .depD .kase, .maxD .kase, .maxD .num] eastFrisian
        ⟨.acc, .sg⟩ ⟨{.k1}, "h"⟩ ∧
      Wins [.depD .num, .depD .kase, .maxD .kase, .maxD .num] eastFrisian
        ⟨.acc, .pl⟩ ⟨{.k1}, "h"⟩ := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Malayalam 1EX candidates ((168)): same two specifications, exponents
*ñan-* and *enn-*. -/
def malayalam : List (Cand String) := [⟨{.p0}, "ñan"⟩, ⟨{.k1}, "enn"⟩]

/-- Malayalam ((167), (169)): swapping both relative rankings —
`Dep(K) ≫ Dep(#)`, `Max(#) ≫ Max(K)` — reverses both diagonals: *ñan-* in
NOM.SG, NOM.PL, ACC.PL and *enn-* in ACC.SG. -/
theorem malayalam_pattern :
    Wins [.depD .kase, .depD .num, .maxD .num, .maxD .kase] malayalam
        ⟨.nom, .sg⟩ ⟨{.p0}, "ñan"⟩ ∧
      Wins [.depD .kase, .depD .num, .maxD .num, .maxD .kase] malayalam
        ⟨.nom, .pl⟩ ⟨{.p0}, "ñan"⟩ ∧
      Wins [.depD .kase, .depD .num, .maxD .num, .maxD .kase] malayalam
        ⟨.acc, .sg⟩ ⟨{.k1}, "enn"⟩ ∧
      Wins [.depD .kase, .depD .num, .maxD .num, .maxD .kase] malayalam
        ⟨.acc, .pl⟩ ⟨{.p0}, "ñan"⟩ := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ### The checkerboard exclusion -/

/-- **The novel multidimensional generalization, exhaustively**: over all 24
rankings and all two-candidate vocabularies on the paradigm's feature space, a
candidate that uniquely wins both NOM.SG and ACC.PL also uniquely wins ACC.SG
or NOM.PL — the non-compliant "checkerboard" is ungenerable while either
Russian-doll ABA remains available (`eastFrisian_pattern`,
`malayalam_pattern`). -/
theorem checkerboard_excluded :
    ∀ rk ∈ rankings, ∀ fa ∈ featSpace.powerset, ∀ fb ∈ featSpace.powerset,
      Wins rk [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] ⟨.nom, .sg⟩ ⟨fa, Ex.A⟩ →
      Wins rk [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] ⟨.acc, .pl⟩ ⟨fa, Ex.A⟩ →
      Wins rk [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] ⟨.acc, .sg⟩ ⟨fa, Ex.A⟩ ∨
        Wins rk [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] ⟨.nom, .pl⟩ ⟨fa, Ex.A⟩ := by
  decide

/-- The vocabulary-general checkerboard exclusion, for any candidate list and
any ranking of the four relativized constraints.

TODO: the shared-core `mem_eval_iff` reduces `Wins` to strict lexicographic
domination of the ranked violation vector (`eval rk v c = [a]` iff `a`'s vector
lex-dominates every rival's, strictly since a tying rival would also survive).
On that footing the dissertation's argument ((170) and §4.1.4's continuation)
runs: (i) dimension-relativized counts factor through the dimension slice of the
context (`viol (maxD d)`/`viol (depD d)` at `⟨κ,ν⟩` depend only on the `d`-part
of `zdecomp`), so each constraint's field-level W/T/L verdict at NOM.SG and
ACC.PL transfers to the cell sharing its dimension; (ii) `Wins` at a cell is
equivalent to the leftmost non-tie column of the ranking (over the *original*
field, cascade-eliminations included) being a strict win; (iii) a three-way case
analysis on the relative rank of the leftmost strict-win columns at NOM.SG and
ACC.PL then forces a strict win at ACC.SG or NOM.PL. Step (ii) — the
column-scan characterization of the filter cascade — is the load-bearing lemma
still to be formalized. -/
theorem checkerboard_excluded_general {rk : List Con} {v : List (Cand F)}
    {a : Cand F}
    (hperm : rk.Perm [Con.maxD .kase, Con.maxD .num, Con.depD .kase,
      Con.depD .num])
    (hns : Wins rk v ⟨.nom, .sg⟩ a) (hap : Wins rk v ⟨.acc, .pl⟩ a) :
    Wins rk v ⟨.acc, .sg⟩ a ∨ Wins rk v ⟨.nom, .pl⟩ a := by
  sorry

/-- Unidimensional *ABA survives the move to violable constraints (§4.1.4):
down the singular case column, no ranking and no two-candidate vocabulary of
**well-formed** specs lets one candidate win NOM and DAT while the other takes
ACC. -/
theorem unidimensional_ABA_excluded :
    ∀ rk ∈ rankings, ∀ fa ∈ specSpace, ∀ fb ∈ specSpace,
      Wins rk [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] ⟨.nom, .sg⟩ ⟨fa, Ex.A⟩ →
      Wins rk [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] ⟨.dat, .sg⟩ ⟨fa, Ex.A⟩ →
      ¬ Wins rk [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] ⟨.acc, .sg⟩ ⟨fb, Ex.B⟩ := by
  decide

/-- The well-formedness entry condition is **necessary**, not merely
convenient: admit the entailment-violating spec {κ_dat} (κ_dat without κ_dep)
and case-column ABA becomes derivable — {κ_dat} takes NOM and DAT while
{κ_dep, #pl} takes ACC under `Max(K) ≫ Dep(K) ≫ Max(#) ≫ Dep(#)`. The
dissertation asserts the assumption "will play a crucial role in allowing the
current theory to derive unidimensional *ABA"; this witness confirms the
system cannot do without it. -/
theorem illformed_spec_breaks_unidimensional_ABA :
    Wins [.maxD .kase, .depD .kase, .maxD .num, .depD .num]
        [(⟨{.k2}, Ex.A⟩ : Cand Ex), ⟨{.k1, .p0}, Ex.B⟩] ⟨.nom, .sg⟩
        ⟨{.k2}, Ex.A⟩ ∧
      Wins [.maxD .kase, .depD .kase, .maxD .num, .depD .num]
        [(⟨{.k2}, Ex.A⟩ : Cand Ex), ⟨{.k1, .p0}, Ex.B⟩] ⟨.acc, .sg⟩
        ⟨{.k1, .p0}, Ex.B⟩ ∧
      Wins [.maxD .kase, .depD .kase, .maxD .num, .depD .num]
        [(⟨{.k2}, Ex.A⟩ : Cand Ex), ⟨{.k1, .p0}, Ex.B⟩] ⟨.dat, .sg⟩
        ⟨{.k2}, Ex.A⟩ := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### The corner rankings: Wolf's mimicry -/

/-- **`Dep ≫ Max` is the Subset Principle with feature counting**
([wolf-2008] on [halle-1997]; the dissertation's §4.1.1): whenever some
candidate is subset-applicable, the unique winner under the global corner
ranking is exactly what `ChristopoulosZompi2023.pattern` — the Elsewhere
engine the companion study runs — selects. Inviolable-`Max` is the dual,
nanosyntax's least-specified non-underspecified choice ([starke-2009]). -/
theorem depTop_eq_subsetPrinciple :
    ∀ fa ∈ featSpace.powerset, ∀ fb ∈ featSpace.powerset, ∀ c : ZCell,
      ∀ r ∈ [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩],
      (fa ⊆ zdecomp c ∨ fb ⊆ zdecomp c) →
      Wins [.depG, .maxG] [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] c r →
      pattern [(⟨fa, Ex.A⟩ : Cand Ex), ⟨fb, Ex.B⟩] c = some r.exponent := by
  decide

end Zompi2023
