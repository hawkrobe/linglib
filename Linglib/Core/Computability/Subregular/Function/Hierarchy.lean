/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.ISL
import Linglib.Core.Computability.Subregular.Function.OSL
import Linglib.Core.Computability.Subregular.Function.Subsequential

/-!
# Function-Level Subregular Hierarchy: Inclusion Theorems

Inclusion theorems for the function-level subregular hierarchy
@cite{aksenova-rawski-graf-heinz-2020} @cite{meinhardt-mai-bakovic-mccollum-2024}.
This is the function-level analogue of `Subregular/Hierarchy.lean` (which
proves `IsStrictlyLocal → IsLocallyTestable → IsLocallyThresholdTestable`
for languages).

The 2024 hierarchy figure (Meinhardt et al Fig. 1) places these classes
as proper inclusions:

```
Non-Deterministic (rational / regular relations)
       ↓
Weakly Deterministic (Heinz-Lai 2013, patched by Meinhardt et al 2024)
       ↓
Left-Subsequential ─────────────── Right-Subsequential
       ↓                                  ↓
Left-OSL                          Right-OSL
       ↘                                ↙
        Input Strictly Local
              ↓
            Finite
```

## What this file proves

* **`isInputStrictlyLocal_left_subsequential`**: every k-ISL function is
  Left-Subsequential. Constructive: exhibits the SFST whose state is the
  bounded input window. The standard FST simulation argument
  (@cite{chandlee-heinz-2018} §4).
* **`isLeftOutputStrictlyLocal_left_subsequential`**: every k-Left-OSL
  function is Left-Subsequential. Same shape: state = bounded output
  window.

## Deferred (sorry'd or not stated)

* **ISL ⊊ Left-OSL** (proper inclusion): every ISL function is also
  some-k Left-OSL, but the construction goes through Subsequential
  rather than directly between the rule types (the windows track
  different things — input vs output). Stated as a TODO.
* **k-monotonicity** (`ISLRule k → ISLRule (k+1)`): tractable for
  functions (no boundary-padding asymmetry, unlike the language case),
  but deferred to the next PR.
* **Strict separation witnesses** (proper containment): require concrete
  counterexamples (e.g. iterative spreading function in OSL but not
  ISL). Deferred per audit recommendation.
* **Right-Subsequential ⊃ Right-OSL** etc.: mirror image of the left
  proofs via `List.reverse` conjugation.
-/

namespace Core.Computability.Subregular.Function

variable {α β : Type}

/-! ### ISL → Left-Subsequential -/

/-- Construction: every ISL rule induces an SFST whose state is the
input window (length ≤ k − 1) and whose `finalOutput` is empty. -/
def ISLRule.toSFST {k : ℕ} (r : ISLRule k α β) : SFST (List α) α β where
  initial := []
  step window x := (lastN (k - 1) (window ++ [x]), r.windowOutput window x)
  finalOutput _ := []

/-- The SFST induced by an ISL rule computes the same string function. -/
theorem ISLRule.toSFST_run_eq_apply {k : ℕ} (r : ISLRule k α β) :
    r.toSFST.run = r.apply := by
  funext input
  show SFST.runFrom r.toSFST [] input = ISLRule.applyAux r [] input
  suffices h : ∀ window : List α,
      SFST.runFrom r.toSFST window input = ISLRule.applyAux r window input from h []
  intro window
  induction input generalizing window with
  | nil => rfl
  | cons x xs ih =>
    change r.windowOutput window x
              ++ SFST.runFrom r.toSFST (lastN (k - 1) (window ++ [x])) xs
         = r.windowOutput window x
              ++ ISLRule.applyAux r (lastN (k - 1) (window ++ [x])) xs
    rw [ih]

/-- **Left-ISL ⊆ Left-Subsequential**: every Left-ISL function is
computed by some SFST scanning left-to-right (@cite{chandlee-heinz-2018}
§4). -/
theorem isLeftInputStrictlyLocal_left_subsequential {k : ℕ}
    {f : List α → List β} (h : IsLeftInputStrictlyLocal k f) :
    IsLeftSubsequential f := by
  obtain ⟨r, hr⟩ := h
  exact ⟨List α, r.toSFST, hr ▸ r.toSFST_run_eq_apply⟩

/-- Direction-parameterised: ISL_d ⊆ Subseq_d for both directions. -/
theorem isInputStrictlyLocal_isSubsequential {d : Direction} {k : ℕ}
    {f : List α → List β} (h : IsInputStrictlyLocal d k f) :
    IsSubsequential d f := by
  cases d with
  | left => exact isLeftInputStrictlyLocal_left_subsequential h
  | right =>
    -- Reduce Right-ISL → Left-ISL of reverse-conjugate (via reverse-conjugation
    -- lemma), get Left-Subseq of conjugate, then back to Right-Subseq.
    rw [isSubsequential_right]
    rw [isInputStrictlyLocal_right] at h
    rw [isRightInputStrictlyLocal_iff_left_reverse] at h
    rw [isRightSubsequential_iff_left_reverse]
    exact isLeftInputStrictlyLocal_left_subsequential h

/-! ### Left-OSL → Left-Subsequential -/

/-- Construction: every Left-OSL rule induces an SFST whose state is the
output window (length ≤ k − 1) and whose `finalOutput` is empty.

The `windowOutput` call is repeated in the two tuple components rather
than `let`-bound so that `(step ow x).2` reduces definitionally to
`r.windowOutput ow x` for the `simp` proof of `toSFST_run_eq_apply`. -/
def OSLRule.toSFST {k : ℕ} (r : OSLRule k α β) : SFST (List β) α β where
  initial := []
  step outputWindow x :=
    (lastN (k - 1) (outputWindow ++ r.windowOutput outputWindow x),
     r.windowOutput outputWindow x)
  finalOutput _ := []

/-- The SFST induced by an OSL rule computes the same string function. -/
theorem OSLRule.toSFST_run_eq_apply {k : ℕ} (r : OSLRule k α β) :
    r.toSFST.run = r.apply := by
  funext input
  show SFST.runFrom r.toSFST [] input = OSLRule.applyAux r [] input
  suffices h : ∀ outputWindow : List β,
      SFST.runFrom r.toSFST outputWindow input
        = OSLRule.applyAux r outputWindow input from h []
  intro outputWindow
  induction input generalizing outputWindow with
  | nil => rfl
  | cons x xs ih =>
    change r.windowOutput outputWindow x
              ++ SFST.runFrom r.toSFST
                  (lastN (k - 1) (outputWindow ++ r.windowOutput outputWindow x)) xs
         = r.windowOutput outputWindow x
              ++ OSLRule.applyAux r
                  (lastN (k - 1) (outputWindow ++ r.windowOutput outputWindow x)) xs
    rw [ih]

/-- **Left-OSL ⊆ Left-Subsequential**: every Left-OSL function is
computed by some SFST scanning left-to-right. -/
theorem isLeftOutputStrictlyLocal_left_subsequential {k : ℕ}
    {f : List α → List β} (h : IsLeftOutputStrictlyLocal k f) :
    IsLeftSubsequential f := by
  obtain ⟨r, hr⟩ := h
  exact ⟨List β, r.toSFST, hr ▸ r.toSFST_run_eq_apply⟩

/-! ### Composition Closure (Mohri 1997 §3) -/

/-- **Compose's `runFrom` agrees with sequential `runFrom`s**. The product
SFST `compose Tg Tf` walks `Tf` over the input from `s.1`, threading
each emitted block through `Tg` from `s.2`. -/
theorem SFST.compose_runFrom {σf σg α β γ : Type*}
    (Tg : SFST σg β γ) (Tf : SFST σf α β) (s : σf × σg) (xs : List α) :
    (Tg.compose Tf).runFrom s xs = Tg.runFrom s.2 (Tf.runFrom s.1 xs) := by
  induction xs generalizing s with
  | nil =>
    -- Both sides reduce to the final-output handling.
    show (Tg.compose Tf).finalOutput s = Tg.runFrom s.2 (Tf.finalOutput s.1)
    show (Tg.runOnList s.2 (Tf.finalOutput s.1)).2
            ++ Tg.finalOutput (Tg.runOnList s.2 (Tf.finalOutput s.1)).1
         = Tg.runFrom s.2 (Tf.finalOutput s.1)
    rw [SFST.runFrom_eq_runOnList]
  | cons x xs ih =>
    show (Tg.compose Tf).runFrom s (x :: xs) = Tg.runFrom s.2 (Tf.runFrom s.1 (x :: xs))
    rw [SFST.runFrom_cons, SFST.runFrom_cons]
    -- LHS: ((Tg.compose Tf).step s x).2 ++ (Tg.compose Tf).runFrom ((Tg.compose Tf).step s x).1 xs
    -- RHS: Tg.runFrom s.2 ((Tf.step s.1 x).2 ++ Tf.runFrom (Tf.step s.1 x).1 xs)
    show (Tg.runOnList s.2 (Tf.step s.1 x).2).2
           ++ (Tg.compose Tf).runFrom
                ((Tf.step s.1 x).1, (Tg.runOnList s.2 (Tf.step s.1 x).2).1) xs
         = Tg.runFrom s.2
              ((Tf.step s.1 x).2 ++ Tf.runFrom (Tf.step s.1 x).1 xs)
    rw [SFST.runFrom_append, ih]

/-- **Subsequential functions are closed under composition** (Mohri 1997
§3, originally Schützenberger and Choffrut). The load-bearing fact that
makes the Heinz-Lai 2013 Weakly Deterministic class definition work as
the composition of two subsequential functions reading from opposite
directions. -/
theorem IsLeftSubsequential.comp {α β γ : Type}
    {g : List β → List γ} (hg : IsLeftSubsequential g)
    {f : List α → List β} (hf : IsLeftSubsequential f) :
    IsLeftSubsequential (g ∘ f) := by
  obtain ⟨σf, Tf, hTf⟩ := hf
  obtain ⟨σg, Tg, hTg⟩ := hg
  refine ⟨σf × σg, Tg.compose Tf, ?_⟩
  funext xs
  show (Tg.compose Tf).run xs = g (f xs)
  show (Tg.compose Tf).runFrom (Tf.initial, Tg.initial) xs = g (f xs)
  rw [SFST.compose_runFrom]
  show Tg.runFrom Tg.initial (Tf.runFrom Tf.initial xs) = g (f xs)
  show Tg.run (Tf.run xs) = g (f xs)
  rw [hTf, hTg]

end Core.Computability.Subregular.Function
