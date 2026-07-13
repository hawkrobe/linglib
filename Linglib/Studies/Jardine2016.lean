/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Correspondence

/-!
# Jardine (2016): transformations as correspondence-graph relations

[jardine-2016] (Ch. 7) presents a phonological process as a **relation** between input
and output, given by correspondence graphs carved out of GEN by banned-subgraph
constraints. This file exercises the `Autosegmental.Correspondence` substrate on the
intervocalic-voicing schema (Jardine's running example): a faithfulness constraint
`*[p↔p]` — forbidding a `p` that corresponds to a `p` — admits the voicing
correspondence `apa ↔ aba` and rejects the faithful `apa ↔ apa`.

## Scope

This demonstrates the constraint mechanism at the correspondence-graph level. The full
relation-level result `R(CG(φ)) = R_voice` additionally requires GEN (`CG(Γ)`, the
correspondence graphs built from primitives), which fixes the correspondence structure;
and Jardine's *output-only* markedness `*VTV` needs the arc-labelled-subgraph refinement
(Ch. 7 fn. 7). Both are deferred — see `Autosegmental/Correspondence.lean`.
-/

namespace Jardine2016

open Autosegmental Correspondence

/-- Toy alphabet for intervocalic voicing: a vowel `a`, voiceless `p`, voiced `b`. -/
inductive Seg | a | p | b
  deriving DecidableEq, Repr

open Autosegmental Autosegmental.Correspondence in
/-- A correspondence representation over the one alphabet. -/
abbrev CRep := Rep Seg Seg

/-- The faithfulness banned subgraph `*[pⁱ↔p]`: a `p` corresponding to a `p`.
    Forbidding it forces an intervocalic `p` to change. -/
def noPP : CRep :=
  ⟨Autosegmental.AR.ofData
    (fun b => match b with
      | true => ([Seg.p] : List (Autosegmental.TwoTier Seg Seg true))
      | false => [Seg.p])
    (fun i j p q => i = true ∧ j = false ∧ p = 0 ∧ q = 0),
    inferInstanceAs (Finite ((_ : Bool) × Fin _))⟩

/-- The voicing correspondence `apa ↔ aba`: identity positions, the medial `p`
    corresponding to a `b`. -/
def gVoice : CRep :=
  ⟨Autosegmental.AR.ofData
    (fun b => match b with
      | true => ([Seg.a, .p, .a] : List (Autosegmental.TwoTier Seg Seg true))
      | false => [Seg.a, .b, .a])
    (fun i j p q => i = true ∧ j = false ∧ p = q),
    inferInstanceAs (Finite ((_ : Bool) × Fin _))⟩

/-- The faithful correspondence `apa ↔ apa`: the medial `p` stays `p`. -/
def gFaithful : CRep :=
  ⟨Autosegmental.AR.ofData
    (fun b => match b with
      | true => ([Seg.a, .p, .a] : List (Autosegmental.TwoTier Seg Seg true))
      | false => [Seg.a, .p, .a])
    (fun i j p q => i = true ∧ j = false ∧ p = q),
    inferInstanceAs (Finite ((_ : Bool) × Fin _))⟩

open Autosegmental Autosegmental.Correspondence

instance : Finite (noPP : CRep).val.obj.V :=
  inferInstanceAs (Finite ((_ : Bool) × Fin _))

instance : Finite (gVoice : CRep).val.obj.V :=
  inferInstanceAs (Finite ((_ : Bool) × Fin _))

instance : Finite (gFaithful : CRep).val.obj.V :=
  inferInstanceAs (Finite ((_ : Bool) × Fin _))

/-- `gVoice` reads input `apa`, output `aba`. -/
theorem gVoice_io :
    gVoice.input = [Seg.a, .p, .a] ∧ gVoice.output = [Seg.a, .b, .a] :=
  ⟨AR.tierWord_ofData true, AR.tierWord_ofData false⟩

/-- The faithful correspondence is **rejected** — it contains a `p↔p`,
    embedded at position 1 of both tiers. -/
theorem gFaithful_rejected : ¬ specifiedByRep [noPP] gFaithful := by
  intro h
  refine h noPP (List.mem_singleton.mpr rfl) ⟨fun _ => 1, ?_, ?_⟩
  · intro i p hp
    have hp' : p < (AR.ofData
        (fun b => match b with
          | true => ([Seg.p] : List (Autosegmental.TwoTier Seg Seg true))
          | false => [Seg.p])
        (fun i j p q => i = true ∧ j = false ∧ p = 0 ∧ q = 0)).tierLength i := hp
    rw [AR.tierLength_ofData] at hp'
    have hp0 : p = 0 := by cases i <;> simpa using Nat.lt_one_iff.mp (by simpa using hp')
    subst hp0
    show ((gFaithful : CRep).val.tierWord i)[0 + 1]? = ((noPP : CRep).val.tierWord i)[0]?
    rw [show (gFaithful : CRep).val.tierWord i
        = _ from AR.tierWord_ofData i,
      show (noPP : CRep).val.tierWord i = _ from AR.tierWord_ofData i]
    cases i <;> rfl
  · intro i j p q hl
    rcases (AR.link_ofData i j p q).mp hl with
      ⟨-, -, -, ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact (AR.link_ofData true false 1 1).mpr
        ⟨by decide, by decide, by decide, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact (AR.link_ofData false true 1 1).mpr
        ⟨by decide, by decide, by decide, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- The voicing correspondence is **admitted** by the `*[p↔p]` grammar: the
    `p↔p` link would have to land on the output `b`. -/
theorem gVoice_specified : specifiedByRep [noPP] gVoice := by
  intro F hF
  rw [List.mem_singleton] at hF
  subst hF
  rintro ⟨o, hw, hl⟩
  have hbt : (0 : ℕ) < (noPP : CRep).val.tierLength true := by
    rw [show (noPP : CRep).val.tierLength true
      = _ from AR.tierLength_ofData true]
    simp
  have hbf : (0 : ℕ) < (noPP : CRep).val.tierLength false := by
    rw [show (noPP : CRep).val.tierLength false
      = _ from AR.tierLength_ofData false]
    simp
  have hwt := hw true 0 hbt
  have hwf := hw false 0 hbf
  rw [show (gVoice : CRep).val.tierWord true
      = _ from AR.tierWord_ofData true,
    show (noPP : CRep).val.tierWord true
      = _ from AR.tierWord_ofData true] at hwt
  rw [show (gVoice : CRep).val.tierWord false
      = _ from AR.tierWord_ofData false,
    show (noPP : CRep).val.tierWord false
      = _ from AR.tierWord_ofData false] at hwf
  have hlink := hl true false 0 0 ((AR.link_ofData true false 0 0).mpr
    ⟨by decide, by decide, by decide, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩)
  rcases (AR.link_ofData true false (0 + o true) (0 + o false)).mp hlink with
    ⟨-, hpb, hqb, ⟨-, -, hpq⟩ | ⟨h1, -⟩⟩
  · have h3' : o false < 3 := by
      have := AR.tierLength_ofData
        (ws := fun b => match b with
          | true => ([Seg.a, .p, .a] : List (Autosegmental.TwoTier Seg Seg true))
          | false => [Seg.a, .b, .a])
        (L := fun i j p q => i = true ∧ j = false ∧ p = q) false
      simp only [Nat.zero_add] at hqb
      omega
    simp only [Nat.zero_add] at hpq
    rw [hpq] at hwt
    match hof : o false, h3' with
    | 0, _ =>
      rw [hof] at hwt
      exact Seg.noConfusion (Option.some.inj hwt)
    | 1, _ =>
      rw [hof] at hwf
      exact Seg.noConfusion (Option.some.inj hwf)
    | 2, _ =>
      rw [hof] at hwt
      exact Seg.noConfusion (Option.some.inj hwt)
  · exact absurd h1 (by decide)

/-- Hence `apa ↔ aba` lies in the relation presented by the local grammar
    `*[p↔p]`, witnessed by `gVoice` ([jardine-2016] Def. 25). -/
theorem voicing_local :
    relRep (specifiedByRep [noPP]) [Seg.a, .p, .a] [Seg.a, .b, .a] :=
  ⟨gVoice, gVoice_specified, gVoice_io.1, gVoice_io.2⟩

end Jardine2016
