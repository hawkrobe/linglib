import Mathlib.Data.Set.Subsingleton
import Mathlib.Data.Set.Image
import Linglib.Syntax.Anaphora.Basic

/-!
# Diagnostic tests

A **diagnostic** is an abductive test for a latent classification `C` from an
observed outcome `Ω`: each outcome is *consistent with* a set of latent values —
the values that could have produced it. From that single datum everything else
follows:

* the test is **conclusive** at an outcome when the consistent set is a
  `Set.Subsingleton` (it pins the latent value to at most one);
* it is **sound** against a ground-truth outcome model `truth : C → Ω` when the
  true value is always among the consistent ones (the test never rules out the
  truth);
* it **decides** `C` when, on every true value, the outcome's consistent set is
  exactly that value — sound *and* conclusive everywhere it matters;
* one test **refines** another when its consistent sets are pointwise smaller (it
  rules out at least as much), a preorder under which conclusiveness is monotone.

`ofCauses` builds a diagnostic from named *causes* (each entailing a latent value)
— the faithful Hankamer–Sag picture, where a test outcome is explained by a set of
causes and the consistent latent values are what those causes entail.

The structure is domain-general (any `Ω`, `C`); the anaphora specialisation
(`Anaphor.DepthCause`, the ground-truth `Depth.testOutcome`) instantiates it for
Hankamer & Sag depth, and the per-test instances (EIR, extraction) live in the
paper that draws the comparison.
-/

universe u v w

/-- An abductive diagnostic: each observed outcome `o : Ω` is consistent with the
    set `consistent o` of latent values in `C` that could have produced it. -/
@[ext]
structure Diagnostic (Ω : Type u) (C : Type v) where
  /-- The latent values consistent with an outcome (the verdict it licenses). -/
  consistent : Ω → Set C

namespace Diagnostic

variable {Ω : Type u} {C : Type v} {γ : Type w}

/-- `t` is conclusive at `o` when the outcome pins the latent value to at most one
    possibility. -/
def IsConclusiveAt (t : Diagnostic Ω C) (o : Ω) : Prop := Set.Subsingleton (t.consistent o)

/-- `t` is conclusive when every outcome is. -/
def Conclusive (t : Diagnostic Ω C) : Prop := ∀ o, t.IsConclusiveAt o

/-- `t` is sound for a ground-truth outcome model `truth : C → Ω` when the true
    latent value is always among the explanations of the outcome it yields — the
    test never rules out the truth. -/
def SoundFor (t : Diagnostic Ω C) (truth : C → Ω) : Prop :=
  ∀ c, c ∈ t.consistent (truth c)

/-- `t` decides `C` against `truth` when, on every true value, the outcome's
    consistent set is exactly that value: a sound, conclusive verdict everywhere
    it is exercised. -/
def Decides (t : Diagnostic Ω C) (truth : C → Ω) : Prop :=
  ∀ c, t.consistent (truth c) = {c}

/-- `t` refines `s` when every outcome's consistent set under `t` is contained in
    `s`'s — `t` rules out at least as much. This is the pointwise-`⊆` informativeness
    order on tests; a finer (more informative) test is `≤`. -/
def Refines (t s : Diagnostic Ω C) : Prop := ∀ o, t.consistent o ⊆ s.consistent o

@[refl] theorem Refines.refl (t : Diagnostic Ω C) : t.Refines t := fun _ => Set.Subset.rfl

theorem Refines.trans {t s r : Diagnostic Ω C} (h₁ : t.Refines s) (h₂ : s.Refines r) :
    t.Refines r := fun o => (h₁ o).trans (h₂ o)

/-- Tests are preordered by refinement: `t ≤ s` iff `t.Refines s` (`t` is finer,
    ruling out at least as much). -/
instance : Preorder (Diagnostic Ω C) where
  le := Refines
  le_refl := Refines.refl
  le_trans _ _ _ := Refines.trans

/-- Refinement is monotone in conclusiveness: a refinement of a conclusive test is
    conclusive (a subset of a subsingleton is a subsingleton). -/
theorem Conclusive.mono {t s : Diagnostic Ω C} (h : t.Refines s) (hs : s.Conclusive) :
    t.Conclusive := fun o => Set.Subsingleton.anti (hs o) (h o)

/-- Deciding is exactly soundness plus conclusiveness on the truth outcomes. -/
theorem decides_iff {t : Diagnostic Ω C} {truth : C → Ω} :
    t.Decides truth ↔ t.SoundFor truth ∧ ∀ c, t.IsConclusiveAt (truth c) := by
  constructor
  · intro h
    refine ⟨fun c => ?_, fun c => ?_⟩
    · simp [h c]
    · show Set.Subsingleton (t.consistent (truth c))
      rw [h c]; exact Set.subsingleton_singleton
  · rintro ⟨hsound, hsub⟩ c
    exact Set.eq_singleton_iff_unique_mem.mpr ⟨hsound c, fun x hx => hsub c hx (hsound c)⟩

/-- A deciding test is sound. -/
theorem Decides.soundFor {t : Diagnostic Ω C} {truth : C → Ω} (h : t.Decides truth) :
    t.SoundFor truth := (decides_iff.mp h).1

/-! ### Building a diagnostic from causes -/

/-- Build a diagnostic from named *causes*: each outcome is explained by a set of
    causes, and the consistent latent values are exactly what those causes entail
    (`Set.image`). The verdict is inconclusive at an outcome precisely when its
    causes entail more than one latent value — so ambiguity is *derived* from the
    cause structure, not stipulated. -/
def ofCauses (causes : Ω → Set γ) (entails : γ → C) : Diagnostic Ω C :=
  ⟨fun o => entails '' causes o⟩

@[simp] theorem ofCauses_consistent (causes : Ω → Set γ) (entails : γ → C) (o : Ω) :
    (ofCauses causes entails).consistent o = entails '' causes o := rfl

/-- Fewer causes ⇒ a refinement: shrinking the cause sets pointwise rules out at
    least as much. -/
theorem ofCauses_refines {c₁ c₂ : Ω → Set γ} (entails : γ → C)
    (h : ∀ o, c₁ o ⊆ c₂ o) : (ofCauses c₁ entails).Refines (ofCauses c₂ entails) :=
  fun o => Set.image_mono (h o)

end Diagnostic

/-! ### Anaphoric-depth specialisation

The latent classification for an anaphora diagnostic is `Anaphor.Depth`; the
causes are the Hankamer–Sag / Landau reasons a depth test can pass or fail. -/

namespace Anaphor

/-- The causes of a depth-test outcome ([hankamer-sag-1976], [landau-2026], the
    (42c)/(42d) "two reasons for the star" analysis): a site passes because it
    `hostsVariable` (has surface structure for the resumptive or trace); it fails
    because it is a `deepAnaphor` (no structure → (42d)), or — for movement-based
    tests only — because a *surface* site's dependency is `derivationalBleeding`
    (bled by ellipsis timing → (42c)) or `islandBlocking` (an inherent barrier;
    resumption is "indifferent to island constraints"). Only `deepAnaphor` entails
    `deep`; the surface-site confounds (`derivationalBleeding`/`islandBlocking`)
    entail `surface`. The asymmetry between EIR (failure = `deepAnaphor` only) and
    extraction (all three) is exactly which confounds each test admits. -/
inductive DepthCause where
  | hostsVariable
  | deepAnaphor
  | derivationalBleeding
  | islandBlocking
  deriving DecidableEq, Repr

/-- The depth each cause entails. -/
def DepthCause.entails : DepthCause → Depth
  | .deepAnaphor => .deep
  | _            => .surface

/-- The ground-truth test outcome on a site of known depth: a surface anaphor
    passes (it has internal structure to host the variable/trace), a deep one
    fails. This is the `truth` model every depth diagnostic is judged against. -/
def Depth.testOutcome : Depth → Bool
  | .surface => true
  | .deep    => false

end Anaphor
