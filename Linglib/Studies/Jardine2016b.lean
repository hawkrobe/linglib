/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Correspondence

/-!
# Jardine (2016): intervocalic voicing as a local string relation

[jardine-2016b] (Ch. 7) presents a phonological process as a **relation** between input and
output strings: a set of correspondence graphs, carved out of GEN by banned-subgraph
constraints. §7.2 runs the idea on intervocalic voicing, (7.1). Over Σ = ∆ = {a, b, p} the
primitives Γ = {aa, pb, pp, bb} of (7.14) — an input symbol over its output — generate
GEN = CG(Γ) by concatenation ((7.15); `g`), and five banned subgraphs cut the voicing
relation out of it: φ_apa (7.19) forbids a surface `apa`, and the four of (7.21) forbid a
`p` surfacing as `b` word-initially, word-finally, after a `p`, and before a `p`. The
grammar is φ_apba (7.22), and the relation it presents is R(CG(φ_apba)) (Def. 25).

## Main definitions

* `Pair`, `g`, `gen` — Γ with the boundary primitives, Jardine's `g : Γ* → CG(Γ)`, and a
  Γ-string's graph wrapped in the boundaries ⋊, ⋉ that (7.21) reads.
* `voicingGrammar` — φ_apba, the five banned subgraphs of (7.22).
* `voicing` — R(CG(φ_apba)) on boundary-augmented strings.

## Main results

* `voicing_iff` — Def. 25 unwound: `(w, v)` is in the relation iff some Γ-string spells
  both and its graph is free of the grammar — after which each data point decides.
* The data of (7.5), (7.17) and (7.20): `apa ↦ aba` and `pa ↦ pa` are in; `apa ↦ apa`,
  `pa ↦ ba` and `appa ↦ abpa` are out.
* `voicing_bpa_bba` — the grammar also admits `bpa ↦ bba`: no subgraph of (7.22) mentions
  a `b` beside the target, so the identity R(CG(φ_apba)) = Rvoice that the text leaves to
  the reader holds only on inputs with no `b` adjacent to a `p`.
-/

namespace Jardine2016b

open Autosegmental Correspondence

/-- Σ = ∆ = {a, b, p} of (7.1), with the word boundaries ⋊ (`lb`) and ⋉ (`rb`) that the
subgraphs of (7.21) read. -/
inductive Seg | a | b | p | lb | rb
  deriving DecidableEq, Repr

/-- The correspondence primitives Γ = {aa, pb, pp, bb} of (7.14) — an input symbol over its
output — with the boundary primitives ⋊ over ⋊ and ⋉ over ⋉. -/
inductive Pair | aa | pb | pp | bb | lb | rb
  deriving DecidableEq, Repr

namespace Pair

/-- The input symbol of a primitive. -/
def input : Pair → Seg
  | aa => .a | pb => .p | pp => .p | bb => .b | lb => .lb | rb => .rb

/-- The output symbol of a primitive. -/
def output : Pair → Seg
  | aa => .a | pb => .b | pp => .p | bb => .b | lb => .lb | rb => .rb

/-- A primitive is its input–output pair. -/
theorem ext {x y : Pair} (hi : x.input = y.input) (ho : x.output = y.output) : x = y := by
  cases x <;> cases y <;> simp_all [input, output]

/-- A Γ-string is determined by the strings it spells. -/
theorem map_injective {γs γs' : List Pair} (hi : γs.map input = γs'.map input)
    (ho : γs.map output = γs'.map output) : γs = γs' := by
  induction γs generalizing γs' with
  | nil => exact (List.map_eq_nil_iff.mp hi.symm).symm
  | cons x xs ih =>
    cases γs' with
    | nil => simp at hi
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hi ho
      rw [ext hi.1 ho.1, ih hi.2 ho.2]

end Pair

/-- Jardine's `g` on Γ-strings ((7.15)): the correspondence graph spelling the input and
output symbols position by position. -/
def g (γs : List Pair) : Strings Seg Seg := ⟨γs.map Pair.input, γs.map Pair.output, (· = ·)⟩

/-- A Γ-string's graph between the boundaries ⋊ and ⋉. -/
def gen (γs : List Pair) : Strings Seg Seg := g (.lb :: γs ++ [.rb])

/-! ### The grammar φ_apba -/

/-- φ_apa (7.19): a surface `apa` — output-only, the markedness constraint *VTV. -/
def banApa : Strings Seg Seg := ⟨[], [.a, .p, .a], fun _ _ => False⟩

/-- φ_⋊pb (7.21): a `p` surfacing as `b` word-initially. -/
def banInitialPb : Strings Seg Seg := ⟨[.p], [.lb, .b], fun i o => i = 0 ∧ o = 1⟩

/-- φ_pb⋉ (7.21): a `p` surfacing as `b` word-finally. -/
def banFinalPb : Strings Seg Seg := ⟨[.p], [.b, .rb], fun i o => i = 0 ∧ o = 0⟩

/-- φ_ppb (7.21): a `p` surfacing as `b` after a surface `p`. -/
def banPbAfterP : Strings Seg Seg := ⟨[.p], [.p, .b], fun i o => i = 0 ∧ o = 1⟩

/-- φ_pbp (7.21): a `p` surfacing as `b` before a surface `p`. -/
def banPbBeforeP : Strings Seg Seg := ⟨[.p], [.b, .p], fun i o => i = 0 ∧ o = 0⟩

/-- φ_apba (7.22). -/
def voicingGrammar : List (Strings Seg Seg) :=
  [banApa, banInitialPb, banFinalPb, banPbAfterP, banPbBeforeP]

/-! ### The relation R(CG(φ_apba)) -/

/-- CG(φ_apba): the graphs of GEN = CG(Γ) free of the grammar. -/
def CG (G : Rep Seg Seg) : Prop :=
  (∃ γs, G = (gen γs).toRep) ∧ specifiedByRep (voicingGrammar.map Strings.toRep) G

/-- R(CG(φ_apba)) (Def. 25), on boundary-augmented strings. -/
def voicing (w v : List Seg) : Prop := relRep CG (.lb :: w ++ [.rb]) (.lb :: v ++ [.rb])

/-- Def. 25 unwound: `(w, v)` is in the relation iff some Γ-string spells both and its
graph is free of the grammar. -/
theorem voicing_iff {w v : List Seg} :
    voicing w v ↔ ∃ γs, γs.map Pair.input = w ∧ γs.map Pair.output = v ∧
      Strings.SpecifiedBy voicingGrammar (gen γs) := by
  constructor
  · rintro ⟨G, ⟨⟨γs, rfl⟩, hφ⟩, hi, ho⟩
    refine ⟨γs, ?_, ?_, (Strings.specifiedByRep_map_toRep _ _).mp hφ⟩
    · simpa [gen, g, Pair.input] using hi
    · simpa [gen, g, Pair.output] using ho
  · rintro ⟨γs, rfl, rfl, hφ⟩
    exact ⟨(gen γs).toRep, ⟨⟨γs, rfl⟩, (Strings.specifiedByRep_map_toRep _ _).mpr hφ⟩,
      by simp [gen, g, Pair.input], by simp [gen, g, Pair.output]⟩

/-! ### The data of (7.5), (7.17) and (7.20) -/

/-- An intervocalic `p` voices: `apa ↦ aba` ((7.18a)). -/
theorem voicing_apa_aba : voicing [.a, .p, .a] [.a, .b, .a] :=
  voicing_iff.mpr ⟨[.aa, .pb, .aa], rfl, rfl, by decide⟩

/-- It must: the faithful `apa ↦ apa` contains φ_apa ((7.18b)). -/
theorem not_voicing_apa_apa : ¬ voicing [.a, .p, .a] [.a, .p, .a] := fun h => by
  obtain ⟨γs, hi, ho, hφ⟩ := voicing_iff.mp h
  obtain rfl := Pair.map_injective (γs' := [.aa, .pp, .aa]) hi ho
  exact absurd hφ (by decide)

/-- A non-intervocalic `p` stays: `pa ↦ pa`. -/
theorem voicing_pa_pa : voicing [.p, .a] [.p, .a] :=
  voicing_iff.mpr ⟨[.pp, .aa], rfl, rfl, by decide⟩

/-- And may not voice: `pa ↦ ba` contains φ_⋊pb ((7.20a)). -/
theorem not_voicing_pa_ba : ¬ voicing [.p, .a] [.b, .a] := fun h => by
  obtain ⟨γs, hi, ho, hφ⟩ := voicing_iff.mp h
  obtain rfl := Pair.map_injective (γs' := [.pb, .aa]) hi ho
  exact absurd hφ (by decide)

/-- `appa ↦ abpa` contains φ_pbp ((7.20b)). -/
theorem not_voicing_appa_abpa : ¬ voicing [.a, .p, .p, .a] [.a, .b, .p, .a] := fun h => by
  obtain ⟨γs, hi, ho, hφ⟩ := voicing_iff.mp h
  obtain rfl := Pair.map_injective (γs' := [.aa, .pb, .pp, .aa]) hi ho
  exact absurd hφ (by decide)

/-- The grammar also admits `bpa ↦ bba`: none of the subgraphs of (7.22) mentions a `b`
beside the target, so Rvoice's `bpa ↦ bpa` is not the only image of `bpa`. -/
theorem voicing_bpa_bba : voicing [.b, .p, .a] [.b, .b, .a] :=
  voicing_iff.mpr ⟨[.bb, .pb, .aa], rfl, rfl, by decide⟩

end Jardine2016b
