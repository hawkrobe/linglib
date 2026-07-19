import Linglib.Studies.ChristopoulosZompi2023
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

TODO: formalize the dissertation's W/T/L argument ((170) and §4.1.4's
continuation): dimension-relativized violation counts factor through the
dimension components of context and spec, so a constraint's win/tie/lose
verdict for the NOM.SG winner transfers along the row or column that keeps its
dimension constant; a case analysis on the leftmost strictly-winning columns
at NOM.SG and ACC.PL then forces a win at ACC.SG or NOM.PL. -/
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
