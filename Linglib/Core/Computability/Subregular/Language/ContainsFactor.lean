/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.StarFree
import Linglib.Core.Computability.Subregular.Language.Aperiodicity

/-!
# Containing (and avoiding) a fixed factor is star-free

For any list `c` over an *arbitrary* alphabet `α`, the language of words that contain `c` as a
contiguous factor (`{x | c <:+: x}`) is star-free, as is its complement (the words that *avoid*
`c`). This is the workhorse fact behind forbidden-substring constraints: each forbidden factor
cuts out a star-free set, and `SF` is closed under the finite Boolean operations.

Over a *finite* alphabet `c` avoidance is plainly strictly local (`SL_{|c|}` with the single
forbidden factor `c`), hence star-free by `Language.IsStrictlyLocal.isStarFree`. The substance
here is removing the finiteness hypothesis: an arbitrary `α` is collapsed onto the finite
alphabet `Fin |c| → Bool` by the **diagonal encoding** `enc a i = (a = c[i])`, which records, for
each position of `c`, whether `a` matches it. This loses almost all information about `α` yet is
faithful enough to detect occurrences of `c`: `c <:+: x ↔ (c.map enc) <:+: (x.map enc)`
(`containsFactor_iff_map`), because at a matched window the diagonal forces `x[j] = c[i]`. The
finite-alphabet result then transfers back by inverse homomorphism (`Language.IsStarFree.comap`).

Star-free = `FO[<]`-definable = counter-free ([schutzenberger-1965] [mcnaughton-papert-1971]).

## Main results

* `Language.isStarFree_containsFactor` — `{x | c <:+: x}` is star-free, `α` arbitrary.
* `Language.isStarFree_avoidsFactor` — `{x | ¬ c <:+: x}` is star-free, `α` arbitrary.
-/

open Subregular

namespace Language.ContainsFactor

/-! ### Generic list lemmas (no alphabet assumptions) -/

variable {α β : Type*}

/-- Window decomposition: a list splits at offsets `a` and `a + b` into prefix, window, suffix. -/
private theorem window_decomp (a b : ℕ) (t : List α) :
    t = t.take a ++ (t.drop a).take b ++ t.drop (a + b) := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- Infix is reflected by an injective map (and preserved by `List.IsInfix.map`). -/
private theorem infix_map_iff {f : α → β} (hf : Function.Injective f) (s t : List α) :
    s.map f <:+: t.map f ↔ s <:+: t := by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  obtain ⟨u, v, huv⟩ := h
  have hlent : u.length + s.length + v.length = t.length := by
    simpa [Nat.add_assoc] using congrArg List.length huv
  set p := t.take u.length with hp
  set mid := (t.drop u.length).take s.length with hmid
  set q := t.drop (u.length + s.length) with hq
  have hdecomp : t = p ++ mid ++ q := window_decomp _ _ t
  have hpl : p.length = u.length := by rw [hp, List.length_take]; omega
  have hmidl : mid.length = s.length := by rw [hmid, List.length_take, List.length_drop]; omega
  rw [show t.map f = p.map f ++ mid.map f ++ q.map f by
    rw [← List.map_append, ← List.map_append, ← hdecomp]] at huv
  have hul : u.length = (p.map f).length := by simp [hpl]
  have h2 : u ++ s.map f = p.map f ++ mid.map f :=
    List.append_inj_left huv (by simp [hpl, hmidl])
  have : mid = s := List.map_injective_iff.mpr hf (List.append_inj_right h2 hul).symm
  rw [hdecomp, this]; exact ⟨p, q, rfl⟩

/-- Stripping `some`: an infix relation is reflected by `List.map some`. -/
private theorem mapSome_infix_iff (s t : List α) :
    s.map some <:+: t.map some ↔ s <:+: t :=
  infix_map_iff (Option.some_injective α) s t

/-- Filtering the boundary form to its `some` positions recovers the core. -/
private theorem filter_isSome_boundary (m : ℕ) (y : List α) :
    (boundary m y).filter (fun b => b.isSome) = y.map some := by
  simp [boundary, List.filter_append, List.filter_map, Function.comp_def]

/-- Boundary stripping: an all-`some` factor of the boundary-augmented form sits in the core. -/
private theorem mapSome_infix_boundary_iff (m : ℕ) (y d : List α) :
    d.map some <:+: boundary m y ↔ d <:+: y := by
  rw [← mapSome_infix_iff d y]
  refine ⟨fun h => ?_, fun h => h.trans (List.infix_append _ _ _)⟩
  have := h.filter (fun b => b.isSome)
  rwa [filter_isSome_boundary, List.filter_map, Function.comp_def,
    show (fun a : α => (some a).isSome) = fun _ => true from rfl, List.filter_true] at this

/-! ### Containment over a finite alphabet -/

variable {γ : Type*} [Finite γ]

omit [Finite γ] in
/-- The `SL` grammar forbidding the single factor `d.map some` generates the avoidance language:
its forbidden window can only complete on an all-`some` occurrence of `d`. -/
private theorem ofForbidden_language_eq (d : List γ) :
    (SLGrammar.ofForbidden {d.map some}).language d.length
      = ({y : List γ | ¬ d <:+: y} : Language γ) := by
  ext y
  simp only [SLGrammar.mem_ofForbidden_language, Set.mem_singleton_iff]
  refine ⟨fun h hc => ?_, fun h f hf heq => ?_⟩
  · exact h (d.map some)
      (List.mem_kFactors.mpr ⟨(mapSome_infix_boundary_iff _ _ d).mpr hc, by simp⟩) rfl
  · subst heq
    exact h ((mapSome_infix_boundary_iff _ _ d).mp (List.mem_kFactors.mp hf).1)

/-- Over a finite alphabet, containing the fixed factor `d` is star-free: it is the complement of
the strictly-local avoidance language. -/
private theorem isStarFree_containsFactor_finite (d : List γ) :
    Language.IsStarFree ({y : List γ | d <:+: y} : Language γ) := by
  have hsl : Language.IsStarFree ({y : List γ | ¬ d <:+: y} : Language γ) :=
    Language.IsStrictlyLocal.isStarFree ⟨_, ofForbidden_language_eq d⟩
  rw [show ({y : List γ | d <:+: y} : Language γ)
    = ({y : List γ | ¬ d <:+: y} : Language γ)ᶜ from by ext y; simp]
  exact hsl.compl

/-! ### The diagonal encoding onto a finite alphabet -/

variable [DecidableEq α] (c : List α)

/-- The **diagonal encoding** `enc c a i = (a = c[i])`: faithful enough to detect `c`. -/
private def enc : α → (Fin c.length → Bool) := fun a i => decide (a = c.get i)

/-- Diagonal injectivity: same-length lists with equal `enc`-images are equal — at each position
`enc` records whether the symbol matches `c` there, which pins it down on the diagonal. -/
private theorem map_enc_eq_iff (m : List α) (hlen : m.length = c.length) :
    m.map (enc c) = c.map (enc c) ↔ m = c := by
  refine ⟨fun h => List.ext_getElem hlen fun i h1 h2 => ?_, fun h => h ▸ rfl⟩
  have hi : enc c m[i] = enc c c[i] := by
    simpa [List.getElem?_map, h1, h2] using congrArg (·[i]?) h
  have := congrFun hi ⟨i, h2⟩
  simpa [enc, List.get_eq_getElem] using this

/-- **K1**: containment over `α` transfers to and from containment of the diagonal-encoded factor
over the finite alphabet `Fin |c| → Bool`. -/
private theorem containsFactor_iff_map (x : List α) :
    c <:+: x ↔ c.map (enc c) <:+: x.map (enc c) := by
  refine ⟨fun h => h.map (enc c), fun h => ?_⟩
  obtain ⟨s, t, hst⟩ := h
  have hlenx : s.length + c.length + t.length = x.length := by
    simpa [Nat.add_assoc] using congrArg List.length hst
  set p := x.take s.length with hp
  set mid := (x.drop s.length).take c.length with hmid
  set q := x.drop (s.length + c.length) with hq
  have hdecomp : x = p ++ mid ++ q := window_decomp _ _ x
  have hpl : p.length = s.length := by rw [hp, List.length_take]; omega
  have hmidl : mid.length = c.length := by rw [hmid, List.length_take, List.length_drop]; omega
  rw [show x.map (enc c) = p.map (enc c) ++ mid.map (enc c) ++ q.map (enc c) by
    rw [← List.map_append, ← List.map_append, ← hdecomp]] at hst
  have hsl : s.length = (p.map (enc c)).length := by simp [hpl]
  have h2 : s ++ c.map (enc c) = p.map (enc c) ++ mid.map (enc c) :=
    List.append_inj_left hst (by simp [hpl, hmidl])
  have : mid = c := (map_enc_eq_iff c mid hmidl).mp (List.append_inj_right h2 hsl).symm
  rw [hdecomp, this]; exact ⟨p, q, rfl⟩

end Language.ContainsFactor

namespace Language

open Language.ContainsFactor

variable {α : Type*}

/-- **Containing a fixed factor is star-free** over an arbitrary alphabet ([schutzenberger-1965]
[mcnaughton-papert-1971]). For any `c`, the words containing `c` as a contiguous factor form a
star-free language. Over a finite alphabet this is strictly local; the diagonal encoding
`enc c a i = (a = c[i])` collapses an arbitrary alphabet onto the finite `Fin |c| → Bool` while
preserving occurrences of `c`, and `SF` is closed under inverse homomorphism. -/
theorem isStarFree_containsFactor (c : List α) :
    Language.IsStarFree {x : List α | c <:+: x} := by
  classical
  rw [show ({x : List α | c <:+: x} : Language α) = {w : List α |
      (FreeMonoid.map (enc c)) (FreeMonoid.ofList w) ∈ ({y | c.map (enc c) <:+: y} : Language _)}
    from by
      ext x
      simp only [Set.mem_setOf_eq, ← FreeMonoid.ofList_map]
      exact containsFactor_iff_map c x]
  exact (isStarFree_containsFactor_finite (c.map (enc c))).comap (FreeMonoid.map (enc c))

/-- **Avoiding a fixed factor is star-free** over an arbitrary alphabet ([schutzenberger-1965]
[mcnaughton-papert-1971]) — the complement of `isStarFree_containsFactor`. -/
theorem isStarFree_avoidsFactor (c : List α) :
    Language.IsStarFree {x : List α | ¬ c <:+: x} := by
  rw [show ({x : List α | ¬ c <:+: x} : Language α) = ({x : List α | c <:+: x} : Language α)ᶜ
    from by ext x; simp]
  exact (isStarFree_containsFactor c).compl

end Language
