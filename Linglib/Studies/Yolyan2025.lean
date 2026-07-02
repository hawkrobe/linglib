import Linglib.Core.Computability.Subregular.Function.Bimachine
import Linglib.Core.Computability.Subregular.Logic.BMRS
import Linglib.Phonology.Tone.Plateauing
import Linglib.Studies.McCollumEtAl2020

/-!
# Yolyan 2025: Weak Determinism as Simultaneous Application

[yolyan-2025]: weakly deterministic functions are those expressible as the
*simultaneous application* `P^L ⊙ P^R` of a backward and a forward BMRS program
(Def. 5.1) — a definition inside the program formalism, which for the first time makes
*non*-membership provable. `IsBmrsWeaklyDeterministic` renders it via the value-level
⊙ of `Logic/BMRS.lean`: `SimulModels` asks each output symbol to be the ⊙-combination
of the two programs' output predicates against the input (Defs. 4.1/4.3), sparing the
combined-head-space construction.

The engine is `not_isBmrsWeaklyDeterministic_of_requiresBothSides`: the paper's §5.3
template (Thms. 5.2–5.5), consuming the same `Subregular.RequiresBothSides` witness
that excludes the *bimachine* rendering of weak determinism
(`not_isBimachineWeaklyDeterministic_of_requiresBothSides`). Whether the two
definitions coincide is the paper's own open question (§6.3, against
[meinhardt-mai-bakovic-mccollum-2024]); feeding both exclusions one witness object
states it structurally without resolving it. The proof here streamlines the paper's:
on either perturbation the input value is unchanged, so ⊙ collapses to conjunction and
*both* one-sided outputs are forced true; each transports to the base word by one-sided
locality (`Eval.congr_agreeUpto`/`congr_agreeFrom`), and recombining forces the base
unchanged — no case-split through Prop. 4.2 needed. Only the `d = 0` instance of the
witness is used: one-sidedness is global, not window-bounded.

Instances: Sour Grapes harmony (Thm. 5.2 — the first proof of the [heinz-lai-2013]
conjecture, via [padgett-1995]/[wilson-2003]'s pathology), and — through the shared
witnesses already in the library — Tutrugbu ATR harmony (Prop. 5.5,
[mccollum-bakovic-mai-meinhardt-2020]), Luganda unbounded tonal plateauing
([jardine-2016]), and Copperbelt Bemba high-tone spreading (Prop. 5.4), the latter
formalized here as a second `Tone.Surfacing` instance. The positive
side: with no underlying stress the input predicate is constantly `⊥` and ⊙ collapses
to disjunction — (5.15), recovering [koser-jardine-2020]'s LHOL program as the
simultaneous application of its two one-sided halves. §6.3's conjunctive dual ⊘ is
exact on Sour Grapes: `sourGrapes_conjunctive` shows the map *is* the ⊘ of its
one-sided licensing conditions.
-/

namespace Yolyan2025

open Subregular Subregular.Logic Subregular.Logic.BMRS

/-- The single BMRS index variable. -/
private abbrev x : Term Unit := .var ()

variable {α : Type*} [DecidableEq α]

/-! ### Weak determinism as simultaneous application (Defs. 4.1, 4.3, 5.1) -/

/-- The value of the ⊙-combined output predicate for `σ` at `i` ([yolyan-2025]
Def. 4.1): the two programs' output values combined against the input value. -/
def SimulEval {L R : Type} (PL : Program α L) (PR : Program α R) (hL : L) (hR : R)
    (w : WordModel α) (i : ℕ) (σ : α) (b : Bool) : Prop :=
  ∃ bL bR, Eval PL w i (.call hL x) bL ∧ Eval PR w i (.call hR x) bR ∧
    b = combine (decide (w[i]? = some σ)) bL bR

/-- The simultaneous application `P^L ⊙ P^R` models `f` (Def. 4.3, restricted to the
length-preserving maps of §5): each output symbol is the one whose ⊙-combined output
predicate holds. -/
def SimulModels {L R : Type} (PL : Program α L) (PR : Program α R)
    (outL : α → L) (outR : α → R) (f : List α → List α) : Prop :=
  ∀ w : WordModel α, (f w).length = w.length ∧
    ∀ i < w.length, ∀ σ : α,
      ((f w)[i]? = some σ ↔ SimulEval PL PR (outL σ) (outR σ) w i σ true)

/-- **Def. 5.1**: `f` is weakly deterministic when it is the simultaneous application
of a backward (`BMRSᵖ`) and a forward (`BMRSˢ`) program. Head types are unconstrained
(the paper's are finite), which only strengthens the negative results below. -/
def IsBmrsWeaklyDeterministic (f : List α → List α) : Prop :=
  ∃ (L R : Type) (PL : Program α L) (PR : Program α R) (outL : α → L) (outR : α → R),
    PL.Backward ∧ PR.Forward ∧ SimulModels PL PR outL outR f

/-! ### The exclusion template (§5.3) -/

/-- **The §5.3 template, proven once**: a map that requires both sides is not weakly
deterministic. On the far-left perturbation the target is unchanged, so ⊙ is
conjunction and both one-sided outputs are true; the forward one transports to the
base by locality. Symmetrically the far-right perturbation delivers the backward one.
Recombining in the base forces the target unchanged — contradiction. Thms. 5.2, 5.3
and Props. 5.4, 5.5 are instances. -/
theorem not_isBmrsWeaklyDeterministic_of_requiresBothSides {f : List α → List α}
    (hf : RequiresBothSides f) : ¬ IsBmrsWeaklyDeterministic f := by
  rintro ⟨L, R, PL, PR, outL, outR, hPL, hPR, hm⟩
  obtain ⟨base, i, hi, hchange, hw⟩ := hf 0
  obtain ⟨uL, ⟨hLlen, hLag⟩, hLsym, hLrev⟩ := hw .left
  obtain ⟨uR, ⟨hRlen, hRag⟩, hRsym, hRrev⟩ := hw .right
  simp only [Nat.sub_zero] at hLag
  simp only [Nat.add_zero] at hRag
  set σ := base[i]'hi with hσ
  have hbase : base[i]? = some σ := List.getElem?_eq_getElem hi
  -- the far-left run: the target is unchanged, so both components are forced true
  have hLboth : Eval PL uL i (.call (outL σ) x) true ∧
      Eval PR uL i (.call (outR σ) x) true := by
    obtain ⟨bL, bR, hevL, hevR, hcomb⟩ :=
      ((hm uL).2 i (hLlen ▸ hi) σ).mp (hLrev.trans (hLsym.trans hbase))
    rw [decide_eq_true (hLsym.trans hbase), combine_true, eq_comm,
      Bool.and_eq_true] at hcomb
    exact ⟨hcomb.1 ▸ hevL, hcomb.2 ▸ hevR⟩
  -- the far-right run, symmetrically
  have hRboth : Eval PL uR i (.call (outL σ) x) true ∧
      Eval PR uR i (.call (outR σ) x) true := by
    obtain ⟨bL, bR, hevL, hevR, hcomb⟩ :=
      ((hm uR).2 i (hRlen ▸ hi) σ).mp (hRrev.trans (hRsym.trans hbase))
    rw [decide_eq_true (hRsym.trans hbase), combine_true, eq_comm,
      Bool.and_eq_true] at hcomb
    exact ⟨hcomb.1 ▸ hevL, hcomb.2 ▸ hevR⟩
  -- transport each one-sided output to the base word and recombine
  have hevL : Eval PL base i (.call (outL σ) x) true :=
    hRboth.1.congr_agreeUpto hPL hRlen trivial fun k hk => (hRag k hk).symm
  have hevR : Eval PR base i (.call (outR σ) x) true :=
    hLboth.2.congr_agreeFrom hPR hLlen trivial fun k hk => (hLag k hk).symm
  exact hchange ((((hm base).2 i hi σ).mpr
    ⟨true, true, hevL, hevR, by rw [decide_eq_true hbase]; rfl⟩).trans hbase.symm)

/-! ### Sour Grapes harmony is not weakly deterministic (Thm. 5.2)

The pathology of [padgett-1995]/[wilson-2003]: `−` becomes `+` iff a `+` lies anywhere
to its left and no blocker `⊟` anywhere to its right — spreading happens only when it
can reach the end of the word. -/

/-- The schematic Sour Grapes alphabet: trigger `+`, target `−`, blocker `⊟`. -/
inductive SG
  | plus | minus | blk
  deriving DecidableEq, Repr

/-- Sour Grapes harmony, by the paper's own characterization: a `−` surfaces `+` iff a
trigger precedes it and no blocker follows it. -/
def sourGrapes (w : List SG) : List SG :=
  w.mapIdx fun i σ =>
    if σ = .minus ∧ .plus ∈ w.take i ∧ .blk ∉ w.drop i then .plus else σ

/-- The witness family: a mutable middle flanked by `d`-margins, with an editable head
(trigger site) and tail (blocker site). -/
private def sg (u v : SG) (d : ℕ) : List SG :=
  u :: (List.replicate (2 * d + 1) .minus ++ [v])

private theorem sg_length {u v : SG} {d : ℕ} : (sg u v d).length = 2 * d + 3 := by
  simp [sg]

private theorem sg_getElem? {u v : SG} {d k : ℕ} :
    (sg u v d)[k]? = if k = 0 then some u else if k = 2 * d + 2 then some v
      else if k < 2 * d + 2 then some .minus else none := by
  rcases k with _ | k
  · rfl
  · simp only [sg, List.getElem?_cons_succ, List.getElem?_append, List.getElem?_replicate,
      List.length_replicate, List.getElem?_cons, List.getElem?_nil]
    split_ifs <;> first | rfl | omega | (exfalso; omega)

/-- The head is the only trigger site: `+` precedes the middle iff the head is `+`. -/
private theorem sg_plus_mem_take {u v : SG} {d : ℕ} :
    .plus ∈ (sg u v d).take (d + 1) ↔ u = .plus := by
  rw [sg, List.take_succ_cons, List.take_append_of_le_length (by simp; omega),
    List.take_replicate]
  simp [eq_comm, List.mem_replicate]

/-- The tail is the only blocker site: `⊟` follows the middle iff the tail is `⊟`. -/
private theorem sg_blk_mem_drop {u v : SG} {d : ℕ} :
    .blk ∈ (sg u v d).drop (d + 1) ↔ v = .blk := by
  rw [sg, List.drop_succ_cons, List.drop_append_of_le_length (by simp; omega),
    List.drop_replicate]
  simp [eq_comm, List.mem_replicate]

/-- The middle of the witness: spreads iff the head triggers and the tail is clear. -/
private theorem sourGrapes_sg_mid {u v : SG} {d : ℕ} :
    (sourGrapes (sg u v d))[d + 1]? =
      some (if u = .plus ∧ v ≠ .blk then .plus else .minus) := by
  have hmid : (sg u v d)[d + 1]? = some .minus := by
    rw [sg_getElem?]
    split_ifs <;> first | rfl | omega | (exfalso; omega)
  rw [sourGrapes, List.getElem?_mapIdx, hmid, Option.map_some]
  by_cases h : u = .plus ∧ v ≠ .blk
  · rw [if_pos h, if_pos ⟨rfl, sg_plus_mem_take.mpr h.1, fun hb => h.2 (sg_blk_mem_drop.mp hb)⟩]
  · rw [if_neg h, if_neg fun ⟨_, ht, hd⟩ =>
      h ⟨sg_plus_mem_take.mp ht, fun hv => hd (sg_blk_mem_drop.mpr hv)⟩]

/-- Sour Grapes requires both sides: the middle of `+ −…− −` spreads, but neither the
triggerless `− −…− −` (far-left perturbation) nor the blocked `+ −…− ⊟` (far-right)
changes it. -/
theorem sourGrapes_requiresBothSides : RequiresBothSides sourGrapes :=
  RequiresBothSides.of_flanks (fill := SG.minus) (on := SG.plus) (xOn := SG.plus)
    (yOn := SG.minus) (xOff := SG.minus) (yOff := SG.blk) (n := fun d => 2 * d + 1)
    (t := fun d => d + 1) (by decide) (fun d => ⟨by omega, by omega⟩)
    (fun d => by
      rw [show flankWord SG.plus SG.minus SG.minus (2 * d + 1) = sg .plus .minus d from
        rfl, sourGrapes_sg_mid]
      simp)
    (fun d => by
      rw [show flankWord SG.minus SG.minus SG.minus (2 * d + 1) = sg .minus .minus d from
        rfl, sourGrapes_sg_mid]
      simp)
    (fun d => by
      rw [show flankWord SG.plus SG.minus SG.blk (2 * d + 1) = sg .plus .blk d from
        rfl, sourGrapes_sg_mid]
      simp)

/-- **Thm. 5.2** — the first proof of the [heinz-lai-2013] conjecture. -/
theorem sourGrapes_not_bmrsWeaklyDeterministic :
    ¬ IsBmrsWeaklyDeterministic sourGrapes :=
  not_isBmrsWeaklyDeterministic_of_requiresBothSides sourGrapes_requiresBothSides

/-- The same witness excludes the *bimachine* rendering of weak determinism — the two
exclusions consume one object, which is the sharpest formal statement available of the
paper's §6.3 open question (are the two definitions equivalent?). -/
theorem sourGrapes_not_bimachineWeaklyDeterministic :
    ¬ IsBimachineWeaklyDeterministic sourGrapes :=
  not_isBimachineWeaklyDeterministic_of_requiresBothSides sourGrapes_requiresBothSides

/-! ### The library's unbounded-circumambient maps, through the same template -/

/-- **Prop. 5.5** (Tutrugbu ATR harmony is not weakly deterministic), riding the
witness already formalized for the bimachine side in `Studies/McCollumEtAl2020`. -/
theorem tutrugbu_not_bmrsWeaklyDeterministic :
    ¬ IsBmrsWeaklyDeterministic McCollumEtAl2020.tutrugbuATR :=
  not_isBmrsWeaklyDeterministic_of_requiresBothSides
    McCollumEtAl2020.tutrugbu_requiresBothSides

/-- Luganda unbounded tonal plateauing is not weakly deterministic: [jardine-2016]'s
flagship pattern (the class of the paper's Prop. 5.4 Bemba case), through
`Phonology/Tone/Plateauing`'s witness. -/
theorem utp_not_bmrsWeaklyDeterministic :
    ¬ IsBmrsWeaklyDeterministic Tone.Plateauing.utp.map :=
  not_isBmrsWeaklyDeterministic_of_requiresBothSides
    Tone.Plateauing.utp.requiresBothSides

/-! ### Bemba high-tone spreading is not weakly deterministic (Prop. 5.4)

Copperbelt Bemba ([jardine-2016]; the paper's bounded/unbounded spreading data): a high
tone spreads to the end of the word when no high follows it, and only onto the next two
TBUs when one does. A second `Tone.Surfacing` instance — and a cautionary one: unlike
plateauing, the surface set is not convex and the map is neither monotone nor
idempotent, so only the shared surfacing API transfers. -/

/-- The Bemba tonal alphabet. -/
inductive BTone
  | H | L
  deriving DecidableEq, Repr

/-- Position `i` surfaces H: an underlying H, within the two-TBU bounded spread of a
preceding H, or at-or-after the last H (unbounded spread to the word end). -/
def bembaSurfaces (w : List BTone) (i : ℕ) : Prop :=
  i < w.length ∧ (w[i]? = some .H
    ∨ (∃ j < i, w[j]? = some .H ∧ i ≤ j + 2)
    ∨ ∃ j ≤ i, w[j]? = some .H ∧ ∀ k < w.length, w[k]? = some .H → k ≤ j)

instance (w : List BTone) (i : ℕ) : Decidable (bembaSurfaces w i) := by
  unfold bembaSurfaces
  infer_instance

/-- Bemba high-tone spreading as a surfacing process. -/
def bemba : Tone.Surfacing BTone where
  hi := .H
  lo := .L
  Surfaces := bembaSurfaces
  hi_ne_lo := by decide
  lt_length h := h.1
  surfaces_of_hi h := ⟨(List.getElem?_eq_some_iff.mp h).1, .inl h⟩
  decSurfaces _ _ := inferInstance

/-- The witness family: flanks `x`, `y` around a toneless fill wide enough that the
bounded two-TBU spread never reaches the middle. -/
private def bw (x y : BTone) (d : ℕ) : List BTone :=
  x :: (List.replicate (2 * d + 4) .L ++ [y])

private theorem bw_length {x y : BTone} {d : ℕ} : (bw x y d).length = 2 * d + 6 := by
  simp [bw]

private theorem bw_getElem? {x y : BTone} {d k : ℕ} :
    (bw x y d)[k]? = if k = 0 then some x else if k = 2 * d + 5 then some y
      else if k < 2 * d + 5 then some .L else none := by
  rcases k with _ | k
  · rfl
  · simp only [bw, List.getElem?_cons_succ, List.getElem?_append, List.getElem?_replicate,
      List.length_replicate, List.getElem?_cons, List.getElem?_nil]
    split_ifs <;> first | rfl | exact ‹False›.elim | omega

/-- In the lone-trigger word, the middle surfaces: the initial H is the last H, so the
unbounded spread reaches it. -/
private theorem bembaSurfaces_bw_HL {d : ℕ} : bembaSurfaces (bw .H .L d) (d + 3) := by
  refine ⟨by rw [bw_length]; omega, .inr (.inr ⟨0, by omega, ?_, fun k hk hkH => ?_⟩)⟩
  · rw [bw_getElem?]
    split_ifs <;> first | rfl | omega
  · rw [bw_length] at hk
    rw [bw_getElem?] at hkH
    split_ifs at hkH <;> first | omega | exact BTone.noConfusion (Option.some.inj hkH)

/-- With a second H at the end, the middle does not surface: the bounded spread stops
two TBUs in, and the unbounded spread now belongs to the final H. -/
private theorem not_bembaSurfaces_bw_HH {d : ℕ} : ¬ bembaSurfaces (bw .H .H d) (d + 3) := by
  rintro ⟨-, h | ⟨j, hj, hjH, hspread⟩ | ⟨j, hj, hjH, hlast⟩⟩
  · rw [bw_getElem?] at h
    split_ifs at h <;> first | omega | exact BTone.noConfusion (Option.some.inj h)
  · rw [bw_getElem?] at hjH
    split_ifs at hjH <;> first | omega | exact BTone.noConfusion (Option.some.inj hjH)
  · have hj0 : j = 0 := by
      rw [bw_getElem?] at hjH
      split_ifs at hjH <;> first | omega | exact BTone.noConfusion (Option.some.inj hjH)
    have := hlast (2 * d + 5) (by rw [bw_length]; omega) (by
      rw [bw_getElem?]
      split_ifs <;> first | rfl | omega)
    omega

/-- With no trigger at all, the middle does not surface. -/
private theorem not_bembaSurfaces_bw_LL {d : ℕ} : ¬ bembaSurfaces (bw .L .L d) (d + 3) := by
  have hnoH : ∀ k, (bw .L .L d)[k]? ≠ some BTone.H := fun k => by
    rw [bw_getElem?]
    split_ifs <;> first | exact fun h => BTone.noConfusion (Option.some.inj h) | simp
  rintro ⟨-, h | ⟨j, -, hjH, -⟩ | ⟨j, -, hjH, -⟩⟩
  exacts [hnoH _ h, hnoH _ hjH, hnoH _ hjH]

/-- Bemba spreading requires both sides: the middle of `H L…L L` spreads (unbounded, no
blocker), but neither the triggerless far-left flip nor the far-right H (which bounds
the spread to two TBUs) changes it. -/
theorem bemba_requiresBothSides : RequiresBothSides bemba.map :=
  RequiresBothSides.of_flanks (fill := BTone.L) (on := BTone.H) (xOn := BTone.H)
    (yOn := BTone.L) (xOff := BTone.L) (yOff := BTone.H) (n := fun d => 2 * d + 4)
    (t := fun d => d + 3) (by decide) (fun d => ⟨by omega, by omega⟩)
    (fun d => bemba.map_getElem?_hi_iff.mpr bembaSurfaces_bw_HL)
    (fun d => bemba.map_getElem?_lo_iff.mpr
      ⟨by rw [flankWord_length]; omega, not_bembaSurfaces_bw_LL⟩)
    (fun d => bemba.map_getElem?_lo_iff.mpr
      ⟨by rw [flankWord_length]; omega, not_bembaSurfaces_bw_HH⟩)

/-- **Prop. 5.4**: Bemba high-tone spreading is not weakly deterministic. -/
theorem bemba_not_bmrsWeaklyDeterministic : ¬ IsBmrsWeaklyDeterministic bemba.map :=
  not_isBmrsWeaklyDeterministic_of_requiresBothSides bemba_requiresBothSides

/-- The bimachine twin, off the same witness. -/
theorem bemba_not_bimachineWeaklyDeterministic :
    ¬ IsBimachineWeaklyDeterministic bemba.map :=
  not_isBimachineWeaklyDeterministic_of_requiresBothSides bemba_requiresBothSides

/-! ### The positive side: LHOL stress as a simultaneous application (§5.2)

Leftmost-heavy-otherwise-leftmost stress ([koser-jardine-2020]; Lushootseed): stress
the leftmost heavy syllable, else the leftmost syllable. The backward program finds a
heavy with no heavy to its left; the forward program stresses an initial light with no
heavy to its right. No syllable is underlyingly stressed, so the input predicate is
constantly `⊥` and ⊙ collapses to disjunction — (5.15), the Koser–Jardine program. -/

/-- Syllable weight. -/
inductive Syll
  | H | L
  deriving DecidableEq, Repr

/-- Heads of the backward stress program: `noHL` = no heavy anywhere left (5.8). -/
inductive LHead
  | noHL | stressL
  deriving DecidableEq

/-- Heads of the forward stress program: `noHR` = no heavy anywhere right (5.9). -/
inductive RHead
  | noHR | stressR
  deriving DecidableEq

/-- (5.8), (5.12): stress a heavy with no heavy to its left. -/
def lholL : Program Syll LHead
  | .noHL => .ite (.initial x) .tru (.ite (.label {.H} x.pred) .fls (.call .noHL x.pred))
  | .stressL => (Expr.label {.H} x).and (.call .noHL x)

/-- (5.9), (5.11): stress an initial light with no heavy to its right. -/
def lholR : Program Syll RHead
  | .noHR => .ite (.final x) .tru (.ite (.label {.H} x.succ) .fls (.call .noHR x.succ))
  | .stressR => (Expr.label {.L} x).and ((Expr.initial x).and (.call .noHR x))

theorem lholL_backward : lholL.Backward := by
  intro f
  cases f <;> decide

theorem lholR_forward : lholR.Forward := by
  intro f
  cases f <;> decide

/-- With no underlying stress, ⊙ is the disjunction of the two programs — (5.15). On
LHLLH the backward program stresses the leftmost heavy alone. -/
theorem lhol_LHLLH :
    (List.range 5).map (fun i =>
      (evalFuel lholL [Syll.L, .H, .L, .L, .H] 32 i (.call .stressL x)).bind fun bL =>
      (evalFuel lholR [Syll.L, .H, .L, .L, .H] 32 i (.call .stressR x)).map fun bR =>
        combine false bL bR) =
    [some false, some true, some false, some false, some false] := by
  decide

/-- On all-light LLLL the forward program stresses the initial syllable alone. -/
theorem lhol_LLLL :
    (List.range 4).map (fun i =>
      (evalFuel lholL [Syll.L, .L, .L, .L] 32 i (.call .stressL x)).bind fun bL =>
      (evalFuel lholR [Syll.L, .L, .L, .L] 32 i (.call .stressR x)).map fun bR =>
        combine false bL bR) =
    [some true, some false, some false, some false] := by
  decide

/-! ### §6.3: Sour Grapes is *conjunctively* simultaneous -/

/-- Sour Grapes **is** the conjunctive simultaneous application ⊘ (Def. 6.5) of its
two one-sided licensing conditions: at a target, spreading happens iff the backward
condition (a trigger left) and the forward condition (no blocker right) *both* fire.
The disjunctive ⊙ cannot express this (Thm. 5.2); ⊘ does so exactly — the paper's
§6.3 route toward characterizing unbounded circumambience. -/
theorem sourGrapes_conjunctive {w : List SG} {i : ℕ} (hm : w[i]? = some .minus) :
    (sourGrapes w)[i]? = some (if combineC false
      (decide (.plus ∈ w.take i)) (decide (.blk ∉ w.drop i)) then .plus else .minus) := by
  rw [sourGrapes, List.getElem?_mapIdx, hm, Option.map_some, combineC_false]
  by_cases hL : .plus ∈ w.take i <;> by_cases hR : .blk ∉ w.drop i <;>
    simp [hL, hR]

end Yolyan2025
