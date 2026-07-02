/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy
import Linglib.Core.Computability.Subregular.Function.Bimachine

/-!
# McCollum, Baković, Mai & Meinhardt (2020): Tutrugbu ATR harmony is circumambient

[mccollum-bakovic-mai-meinhardt-2020] (Phonology 37:215-255) show that Tutrugbu
(Kwa, Ghana) regressive ATR harmony is an **unbounded circumambient** segmental
pattern (their def. 13): the surface ATR of a prefix vowel depends on information
arbitrarily far away on *both* sides — the [ATR] value of the root (to the right)
and the [high] value of the initial-syllable vowel (to the left). Circumambient
patterns require **non-deterministic** regular power (above the weakly-deterministic
upper bound of [heinz-lai-2013]); Tutrugbu is, in the authors' words, "a variation
on the **sour grapes** pattern" — i.e. a *non-myopic* harmony ([wilson-2003],
[wilson-2006]). It is thus a robustly attested counterexample to the claim that
unbounded spreading is always myopic: [walker-2010] argued (from Romance metaphony)
that nonmyopic harmony exists; [kimper-2012] and [mascaro-2019] replied that harmony
is myopic; Tutrugbu is the segmental case the myopic-side replies do not dissolve.

## The pattern (paper §2.1)

[+ATR] is dominant; affixes are underlyingly [−ATR]; harmony is regressive
(root → prefix). The conditional-blocking generalisation (paper §2.1, exx. (6)-(8)):

* a [−high] prefix vowel **blocks** harmony **iff** the initial-syllable vowel is
  [+high] (exx. (6)); two [+high] prefixes (3) or two [−high] prefixes (4)-(5) never
  block; harmony spreads as far as the blocking [−high] vowel and stops (7);
* the [+high] initial and the [−high] blocker may be separated by an **unbounded**
  number of syllables (ex. (8), 0–4-syllable gaps shown). So a medial vowel's ATR
  depends on the root (right) and the initial-σ height (left), both unbounded.

## What this file does

`Seg` is a toy alphabet (prefix vowels ±high × ±ATR-surface; root ±ATR). `tutrugbuATR`
implements the conditional-blocking rule faithfully; the paper's exx. (3)-(8) are
decide-checked as stimulus contrasts. `tutrugbu_isUnboundedCircumambient` and
`tutrugbu_nonmyopic` connect it to the substrate predicates in `SideDeterminacy.lean`.

The machine-level classification (circumambient ⟹ non-deterministic, *not* weakly
deterministic) needs bimachine substrate and is deferred; the co-located
circumambience proved here is exactly what that argument consumes.
-/

namespace McCollumEtAl2020

open Subregular
open Subregular (Direction)

/-! ### Alphabet and the conditional-blocking rule -/

/-- Toy Tutrugbu segment alphabet. Prefix vowels carry [±high] and a surface [±ATR];
the root carries [±ATR] (the harmony trigger). Underlying prefixes are [−ATR]
(`vHi`/`vLo`); harmony raises them to the [+ATR] surface forms (`vHiA`/`vLoA`). -/
inductive Seg
  | vHi   -- [+high] prefix vowel, surface [−ATR]
  | vLo   -- [−high] prefix vowel, surface [−ATR]
  | vHiA  -- [+high] prefix vowel, surface [+ATR]
  | vLoA  -- [−high] prefix vowel, surface [+ATR]
  | rP    -- root, [+ATR]  (e.g. 'grow')
  | rM    -- root, [−ATR]  (e.g. 'come')
  deriving DecidableEq, Repr

namespace Seg
/-- A [+high] prefix vowel. -/
def isHiPfx : Seg → Bool | .vHi | .vHiA => true | _ => false
/-- Raise a prefix vowel to its [+ATR] surface form (root vowels unchanged). -/
def raisePfx : Seg → Seg | .vHi => .vHiA | .vLo => .vLoA | s => s
end Seg

open Seg

/-- Regressive spread over the prefixes, scanned **root-side first** (the list is the
reversed prefix sequence). `spreading` tracks whether [+ATR] still propagates;
`initialHi` is whether the initial-syllable vowel is [+high] (the blocking condition).
A [−high] vowel is a *conditional blocker*: it halts spread only when `initialHi`. -/
def spreadRTL (initialHi : Bool) : Bool → List Seg → List Seg
  | _, [] => []
  | spreading, v :: rest =>
    if spreading then
      if v.isHiPfx then raisePfx v :: spreadRTL initialHi true rest
      else if initialHi then v :: spreadRTL initialHi false rest        -- blocker
      else raisePfx v :: spreadRTL initialHi true rest
    else v :: spreadRTL initialHi false rest

@[simp] theorem spreadRTL_nil (ih sp : Bool) : spreadRTL ih sp [] = [] := rfl

theorem spreadRTL_cons (ih sp : Bool) (v : Seg) (rest : List Seg) :
    spreadRTL ih sp (v :: rest) =
      if sp then
        (if v.isHiPfx then raisePfx v :: spreadRTL ih true rest
         else if ih then v :: spreadRTL ih false rest
         else raisePfx v :: spreadRTL ih true rest)
      else v :: spreadRTL ih false rest := rfl

/-- Once spreading has stopped, the scan leaves the list unchanged. -/
theorem spreadRTL_stopped (ih : Bool) : ∀ L, spreadRTL ih false L = L
  | [] => rfl
  | v :: rest => by rw [spreadRTL_cons, if_neg (by decide), spreadRTL_stopped ih rest]

/-- With an initial [−high] vowel (`ih = false`), nothing blocks: every prefix raises. -/
theorem spreadRTL_false_true : ∀ L, spreadRTL false true L = L.map raisePfx
  | [] => rfl
  | v :: rest => by
      rw [spreadRTL_cons, if_pos rfl]
      have ih := spreadRTL_false_true rest
      cases h : v.isHiPfx <;> simp [ih]

/-- A `replicate`-block of [+high] fillers raises and keeps spreading. -/
theorem spreadRTL_replicate_vHi (ih : Bool) (rest : List Seg) :
    ∀ n, spreadRTL ih true (List.replicate n .vHi ++ rest)
       = List.replicate n .vHiA ++ spreadRTL ih true rest
  | 0 => by simp
  | n + 1 => by
      rw [List.replicate_succ, List.cons_append, spreadRTL_cons, if_pos rfl,
          if_pos (by decide : (Seg.vHi).isHiPfx = true),
          spreadRTL_replicate_vHi ih rest n, List.replicate_succ, List.cons_append]
      rfl

/-- Tutrugbu ATR harmony on `[prefix vowels…] ++ [root]`. Harmony applies only with a
[+ATR] root; the initial-syllable height gates conditional blocking. -/
def tutrugbuATR (xs : List Seg) : List Seg :=
  match xs.getLast? with
  | some .rP =>
    let prefixes := xs.dropLast
    let initialHi := match prefixes.head? with | some p => p.isHiPfx | none => false
    (spreadRTL initialHi true prefixes.reverse).reverse ++ [.rP]
  | _ => xs

/-! ### Stimulus contrasts (paper §2.1, exx. (3)-(8)) -/

-- (3) all [+high] prefixes + [+ATR] root: full harmony.  /ɪ-tɔ-ʃɣ/ analogue
example : tutrugbuATR [.vHi, .vHi, .rP] = [.vHiA, .vHiA, .rP] := by decide
-- (4) all [−high] prefixes + [+ATR] root: full harmony.  /a-ba-ʃɣ/ → [ebeʃɣ]
example : tutrugbuATR [.vLo, .vLo, .rP] = [.vLoA, .vLoA, .rP] := by decide
-- (4a) [−ATR] root: no harmony.  /a-ba-bá/ → [ababá]
example : tutrugbuATR [.vLo, .vLo, .rM] = [.vLo, .vLo, .rM] := by decide
-- (6) [+high] initial + [−high] medial + [+ATR] root: BLOCKED.  /ɪ-ba-ʃɣ/ → [ɪbaʃɣ]
example : tutrugbuATR [.vHi, .vLo, .rP] = [.vHi, .vLo, .rP] := by decide
-- (7c) harmony spreads up to the blocker.  /ɪ-ba-dɪ-wu/ → [ɪbadiwu]
example : tutrugbuATR [.vHi, .vLo, .vHi, .rP] = [.vHi, .vLo, .vHiA, .rP] := by decide

/-- **The circumambient contrast** (paper §2.1): at a fixed medial [−high] target, the
surface ATR depends on BOTH the initial-σ height (left) AND the root ATR (right). -/
example : -- initial [−high], root [+ATR] → target harmonises
    tutrugbuATR [.vLo, .vLo, .rP] = [.vLoA, .vLoA, .rP] := by decide
example : -- vary the LEFT (initial → [+high]): target blocked
    tutrugbuATR [.vHi, .vLo, .rP] = [.vHi, .vLo, .rP] := by decide
example : -- vary the RIGHT (root → [−ATR]): target unharmonised
    tutrugbuATR [.vLo, .vLo, .rM] = [.vLo, .vLo, .rM] := by decide

/-- **Unbounded conditional blocking** (paper exx. (8c)/(8d); longer gaps schematised):
the [+high] initial and the [−high] blocker keep interacting across arbitrarily many
intervening [+high] vowels — the rule licenses an unbounded gap. -/
example : tutrugbuATR [.vHi, .vLo, .rP] = [.vHi, .vLo, .rP] := by decide            -- (8c)
example : tutrugbuATR [.vHi, .vHi, .vLo, .rP] = [.vHi, .vHi, .vLo, .rP] := by decide -- (8d)
example : tutrugbuATR [.vHi, .vHi, .vHi, .vLo, .rP]
        = [.vHi, .vHi, .vHi, .vLo, .rP] := by decide                               -- gap 2 (schem.)
-- contrast: drop the [+high] initial (→ [−high]) and the SAME word harmonises fully
example : tutrugbuATR [.vLo, .vHi, .vHi, .vLo, .rP]
        = [.vLoA, .vHiA, .vHiA, .vLoA, .rP] := by decide

/-! ### Subregular classification -/

/-- The prefix sequence of the witness: a [−high]/[+high] initial, then `d` [+high]
fillers, the [−high] target, and `d` more [+high] fillers. -/
def pre (init : Seg) (d : ℕ) : List Seg :=
  init :: List.replicate d .vHi ++ .vLo :: List.replicate d .vHi

/-- The unbounded-circumambience witness at distance `d`: a [−high] target flanked by
`d` [+high] fillers on each side, a [−high] initial, and a [+ATR] root. -/
def base (d : ℕ) : List Seg := pre .vLo d ++ [.rP]
/-- Far-LEFT perturbation: flip the initial to [+high] (blocks the target). -/
def baseL (d : ℕ) : List Seg := pre .vHi d ++ [.rP]
/-- Far-RIGHT perturbation: flip the root to [−ATR] (removes the trigger). -/
def baseR (d : ℕ) : List Seg := pre .vLo d ++ [.rM]

/-- `tutrugbuATR` on `base d`: with a [−high] initial nothing blocks, so every prefix
raises; the target at index `d+1` surfaces [+ATR] (`.vLoA`). -/
theorem tutrugbuATR_base (d : ℕ) :
    tutrugbuATR (base d)
      = .vLoA :: List.replicate d .vHiA ++ .vLoA :: List.replicate d .vHiA ++ [.rP] := by
  have hLast : (base d).getLast? = some .rP := by simp [base]
  have hDrop : (base d).dropLast = pre .vLo d := by simp [base]
  have hHead : (pre .vLo d).head? = some .vLo := by simp [pre]
  -- With ih=false, spreading raises every prefix
  have hSpread : (spreadRTL false true (pre .vLo d).reverse).reverse = (pre .vLo d).map .raisePfx :=
    by rw [spreadRTL_false_true, List.map_reverse, List.reverse_reverse]
  -- First reduce tutrugbuATR using the computed pieces
  rw [show tutrugbuATR (base d) =
      (spreadRTL false true (pre .vLo d).reverse).reverse ++ [.rP] from by
    simp only [tutrugbuATR, hLast, hDrop, hHead, Seg.isHiPfx]]
  -- Now substitute the spread result and expand pre
  rw [hSpread]
  simp only [pre, List.map_cons, List.map_append, List.map_replicate, Seg.raisePfx,
    List.cons_append, List.append_assoc]

/-- `tutrugbuATR` on `baseL d`: a [+high] initial makes the [−high] target a blocker, so
[+ATR] reaches only the root-side fillers; the target at index `d+1` stays [−ATR]. -/
theorem tutrugbuATR_baseL (d : ℕ) :
    tutrugbuATR (baseL d)
      = List.replicate (d + 1) .vHi ++ .vLo :: List.replicate d .vHiA ++ [.rP] := by
  have hLast : (baseL d).getLast? = some .rP := by simp [baseL]
  have hDrop : (baseL d).dropLast = pre .vHi d := by simp [baseL]
  have hHead : (pre .vHi d).head? = some .vHi := by simp [pre]
  -- (pre .vHi d).reverse = replicate d .vHi ++ .vLo :: replicate (d+1) .vHi
  have hRev : (pre .vHi d).reverse =
      List.replicate d .vHi ++ .vLo :: List.replicate (d + 1) .vHi := by
    simp only [pre, List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ']
  -- spreadRTL result: replicate d .vHiA ++ .vLo :: replicate (d+1) .vHi
  have hSpread : spreadRTL true true ((pre .vHi d).reverse) =
      List.replicate d .vHiA ++ .vLo :: List.replicate (d + 1) .vHi := by
    rw [hRev, spreadRTL_replicate_vHi, spreadRTL_cons]
    simp only [Seg.isHiPfx, if_true, if_false, Bool.false_eq_true, spreadRTL_stopped]
  -- Reduce tutrugbuATR to the spread expression
  rw [show tutrugbuATR (baseL d) =
      (spreadRTL true true (pre .vHi d).reverse).reverse ++ [.rP] from by
    simp only [tutrugbuATR, hLast, hDrop, hHead, Seg.isHiPfx]]
  -- Substitute hSpread and reverse the result
  rw [hSpread]
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.nil_append,
    List.append_assoc, List.cons_append]

/-- `tutrugbuATR` on `baseR d`: a [−ATR] root provides no trigger, so the map is the
identity; the target at index `d+1` stays [−ATR]. -/
theorem tutrugbuATR_baseR (d : ℕ) : tutrugbuATR (baseR d) = baseR d := by
  have hLast : (baseR d).getLast? = some .rM := by simp [baseR]
  simp only [tutrugbuATR, hLast]

/-- The base output at the target index is [+ATR]. -/
theorem base_get_target (d : ℕ) : (tutrugbuATR (base d))[d + 1]? = some .vLoA := by
  rw [tutrugbuATR_base]
  simp

/-- The `baseL` output at the target index is [−ATR] (blocked). -/
theorem baseL_get_target (d : ℕ) : (tutrugbuATR (baseL d))[d + 1]? = some .vLo := by
  rw [tutrugbuATR_baseL]
  simp

/-- The `baseR` output at the target index is [−ATR] (no trigger). -/
theorem baseR_get_target (d : ℕ) : (tutrugbuATR (baseR d))[d + 1]? = some .vLo := by
  rw [tutrugbuATR_baseR]
  simp [baseR, pre]

/-- **Tutrugbu ATR harmony is unbounded circumambient**
([mccollum-bakovic-mai-meinhardt-2020] §3, def. 13). At the medial target (index
`d+1`): the base harmonises it ([+ATR]); flipping the initial-σ height `d` syllables
to the left blocks it; flipping the root `d` syllables to the right removes the
trigger — both from the one base word. -/
theorem tutrugbu_isUnboundedCircumambient : IsUnboundedCircumambient tutrugbuATR := by
  intro d
  refine ⟨base d, d + 1, ?_, fun s => ?_⟩
  · -- the target is in-domain: d + 1 < (base d).length  (= 2d+3)
    simp only [base, pre, List.length_cons, List.length_append, List.length_replicate,
      List.length_nil]; omega
  match s with
  | .left =>
    refine ⟨baseL d, ⟨?_, ?_⟩, ?_⟩
    · simp only [baseL, base, pre, List.length_cons, List.length_append,
        List.length_replicate, List.length_nil]
    · -- AgreeFrom (base d) (baseL d) 1: they share the tail from index 1
      intro k hk
      cases k with
      | zero => omega
      | succ k' =>
        simp only [base, baseL, pre, List.cons_append, List.getElem?_cons_succ]
    · rw [base_get_target, baseL_get_target]; decide
  | .right =>
    refine ⟨baseR d, ⟨?_, ?_⟩, ?_⟩
    · simp only [baseR, base, pre, List.length_cons, List.length_append,
        List.length_replicate, List.length_nil]
    · -- AgreeUpto (base d) (baseR d) ((d+1)+d): differ only at the root index
      intro k hk
      have hpre_len : (pre Seg.vLo d).length = 2 * d + 2 := by
        simp only [pre, List.length_cons, List.length_append, List.length_replicate]
        omega
      rw [show base d = pre Seg.vLo d ++ [.rP] from rfl,
          show baseR d = pre Seg.vLo d ++ [.rM] from rfl,
          List.getElem?_append_left (by omega : k < (pre Seg.vLo d).length),
          List.getElem?_append_left (by omega : k < (pre Seg.vLo d).length)]
    · rw [base_get_target, baseR_get_target]; decide

/-- **Tutrugbu ATR harmony is non-myopic** — the attested "variation on sour grapes"
([mccollum-bakovic-mai-meinhardt-2020]; [wilson-2006]). A segmental counterexample to
the myopia generalisation defended by [kimper-2012] and [mascaro-2019], on the
nonmyopic side argued by [walker-2010]. -/
theorem tutrugbu_nonmyopic (s : Direction) : ¬ IsMyopicTowards tutrugbuATR s :=
  tutrugbu_isUnboundedCircumambient.not_myopic s

/-- The input symbol at the target index is the recessive `.vLo` (for any initial and
root): the prefix sequence places a `[−high]` vowel there. -/
theorem pre_get_target (init : Seg) (d : ℕ) : (pre init d)[d + 1]? = some .vLo := by
  simp only [pre, List.cons_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- **Tutrugbu ATR harmony requires both sides** ([meinhardt-mai-bakovic-mccollum-2024]
Def. 2): at the medial target the base spreads ([+ATR]), but flipping the initial height
to the far left *or* the root ATR to the far right reverts it to its [−ATR] input — the
suppression structure no union of one-sided rules can produce. -/
theorem tutrugbu_requiresBothSides : RequiresBothSides tutrugbuATR := by
  intro d
  have hpl : (pre Seg.vLo d).length = 2 * d + 2 := by
    simp only [pre, List.length_cons, List.length_append, List.length_replicate]; omega
  have hplH : (pre Seg.vHi d).length = 2 * d + 2 := by
    simp only [pre, List.length_cons, List.length_append, List.length_replicate]; omega
  have hbin : (base d)[d + 1]? = some .vLo := by
    rw [show base d = pre Seg.vLo d ++ [.rP] from rfl,
        List.getElem?_append_left (by omega : d + 1 < (pre Seg.vLo d).length), pre_get_target]
  have hLin : (baseL d)[d + 1]? = some .vLo := by
    rw [show baseL d = pre Seg.vHi d ++ [.rP] from rfl,
        List.getElem?_append_left (by omega : d + 1 < (pre Seg.vHi d).length), pre_get_target]
  have hRin : (baseR d)[d + 1]? = some .vLo := by
    rw [show baseR d = pre Seg.vLo d ++ [.rM] from rfl,
        List.getElem?_append_left (by omega : d + 1 < (pre Seg.vLo d).length), pre_get_target]
  refine ⟨base d, d + 1, ?_, ?_, fun s => ?_⟩
  · simp only [base, pre, List.length_cons, List.length_append, List.length_replicate,
      List.length_nil]; omega
  · rw [base_get_target, hbin]; decide
  match s with
  | .left =>
    refine ⟨baseL d, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [baseL, base, pre, List.length_cons, List.length_append,
        List.length_replicate, List.length_nil]
    · intro k hk
      cases k with
      | zero => omega
      | succ k' => simp only [base, baseL, pre, List.cons_append, List.getElem?_cons_succ]
    · rw [hLin, hbin]
    · rw [baseL_get_target, hLin]
  | .right =>
    refine ⟨baseR d, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [baseR, base, pre, List.length_cons, List.length_append,
        List.length_replicate, List.length_nil]
    · intro k hk
      rw [show base d = pre Seg.vLo d ++ [.rP] from rfl,
          show baseR d = pre Seg.vLo d ++ [.rM] from rfl,
          List.getElem?_append_left (by omega : k < (pre Seg.vLo d).length),
          List.getElem?_append_left (by omega : k < (pre Seg.vLo d).length)]
    · rw [hRin, hbin]
    · rw [baseR_get_target, hRin]

/-- **Tutrugbu ATR harmony is not weakly deterministic** — it needs the full
non-deterministic regular power, above the weakly-deterministic upper bound of
[heinz-lai-2013]. The capstone: the conjunctive blocking (`tutrugbu_requiresBothSides`)
cannot be a union of one-sided rules, so no non-interacting bimachine computes it. -/
theorem tutrugbu_not_weaklyDeterministic : ¬ IsBimachineWeaklyDeterministic tutrugbuATR :=
  not_isBimachineWeaklyDeterministic_of_requiresBothSides tutrugbu_requiresBothSides

end McCollumEtAl2020
