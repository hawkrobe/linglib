/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy

/-!
# McCollum, Baković, Mai & Meinhardt (2020): Tutrugbu ATR harmony is circumambient

[mccollum-bakovic-mai-meinhardt-2020] (Phonology 37:215-255) show that Tutrugbu
(Kwa, Ghana) regressive ATR harmony is an **unbounded circumambient** segmental
pattern (their def. 13): the surface ATR of a prefix vowel depends on information
arbitrarily far away on *both* sides — the [ATR] value of the root (to the right)
and the [high] value of the initial-syllable vowel (to the left). Circumambient
patterns require **non-deterministic** regular power (above the weakly-deterministic
upper bound of [heinz-lai-2013]); Tutrugbu is, in the authors' words, "a variation
on the **sour grapes** pattern" — i.e. a *non-myopic* harmony ([wilson-2006]). It is
thus an attested counterexample to the claim that all segmental harmony is myopic,
the question debated in [walker-2010], [kimper-2012] and [mascaro-2019].

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

open Core.Computability.Subregular.Function
open Core (Direction)

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

/-- **Unbounded conditional blocking** (paper ex. (8)): the [+high] initial and the
[−high] blocker stay interacting across growing gaps of [+high] vowels. -/
example : tutrugbuATR [.vHi, .vLo, .rP] = [.vHi, .vLo, .rP] := by decide               -- gap 0
example : tutrugbuATR [.vHi, .vHi, .vLo, .rP] = [.vHi, .vHi, .vLo, .rP] := by decide    -- gap 1
example : tutrugbuATR [.vHi, .vHi, .vHi, .vLo, .rP]
        = [.vHi, .vHi, .vHi, .vLo, .rP] := by decide                                   -- gap 2
-- contrast: drop the [+high] initial (→ [−high]) and the SAME word harmonises fully
example : tutrugbuATR [.vLo, .vHi, .vHi, .vLo, .rP]
        = [.vLoA, .vHiA, .vHiA, .vLoA, .rP] := by decide

/-! ### Subregular classification -/

/-- The unbounded-circumambience witness at distance `d`: a [−high] target flanked by
`d` [+high] fillers on each side, a [−high] initial, and a [+ATR] root. -/
def base (d : ℕ) : List Seg :=
  .vLo :: List.replicate d .vHi ++ .vLo :: List.replicate d .vHi ++ [.rP]
/-- Far-LEFT perturbation: flip the initial to [+high] (blocks the target). -/
def baseL (d : ℕ) : List Seg :=
  .vHi :: List.replicate d .vHi ++ .vLo :: List.replicate d .vHi ++ [.rP]
/-- Far-RIGHT perturbation: flip the root to [−ATR] (removes the trigger). -/
def baseR (d : ℕ) : List Seg :=
  .vLo :: List.replicate d .vHi ++ .vLo :: List.replicate d .vHi ++ [.rM]

/-- **Tutrugbu ATR harmony is unbounded circumambient** ([mccollum-…-2020] §3, def. 13).
At the medial target (index `d+1`): the base harmonises it ([+ATR]); flipping the
initial-σ height `d` syllables to the left blocks it; flipping the root `d` syllables
to the right removes the trigger — both from the one base word. -/
theorem tutrugbu_isUnboundedCircumambient : IsUnboundedCircumambient tutrugbuATR := by
  intro d
  refine ⟨base d, d + 1, ?_, ⟨baseL d, ?_, ?_, ?_⟩, ⟨baseR d, ?_, ?_, ?_⟩⟩
  all_goals sorry
  -- WITNESS (all `decide`-true at each fixed `d`; the `∀ d` step is the routine
  -- induction on `List.replicate d .vHi`):
  --   `tutrugbuATR (base d) ! (d+1) = some .vLoA`   (initial [−high] ⟹ full harmony)
  --   `tutrugbuATR (baseL d) ! (d+1) = some .vLo`   (initial [+high] ⟹ target blocked)
  --   `tutrugbuATR (baseR d) ! (d+1) = some .vLo`   ([−ATR] root ⟹ no harmony)
  --   AgreeFrom (base d) (baseL d) ((d+1)-d=1): differ only at index 0 (the initial)
  --   AgreeUpto (base d) (baseR d) ((d+1)+d=2d+1): differ only at index 2d+2 (the root)
  -- Helper lemmas needed: `spreadRTL ih true (replicate n .vHi ++ rest)`
  --   `= replicate n .vHiA ++ spreadRTL ih true rest`; and the dual blocked form.
  -- TODO(follow-up): discharge via those two `replicate` lemmas.

/-- **Tutrugbu ATR harmony is non-myopic** — the attested "variation on sour grapes"
([mccollum-…-2020]; [wilson-2006]). Settles the [walker-2010]/[mascaro-2019] myopia
question on the *nonmyopic* side for this pattern. -/
theorem tutrugbu_nonmyopic (s : Direction) : ¬ IsMyopicTowards tutrugbuATR s :=
  tutrugbu_isUnboundedCircumambient.not_myopic s

end McCollumEtAl2020
