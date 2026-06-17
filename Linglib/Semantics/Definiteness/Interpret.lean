import Linglib.Semantics.Definiteness.Description
import Linglib.Semantics.Definiteness.Maximality

/-!
# Interpretation of Nominal Descriptions
[coppock-beaver-2015] [hanink-2021] [schwarz-2009]
[patel-grosz-grosz-2017] [sharvy-1980]

Maps `Description E W` to a referent in `Option E`, relative to a
(entity, situation) bi-assignment. `none` represents either presupposition
failure (no unique satisfier; no satisfying antecedent at the discourse
index) or inapplicability (indefinites do not denote a single entity at
this layer — they need separate existential-closure machinery).

The interpretation composes the operators in `Semantics/Definiteness/Maximality.lean`:

- `bare` and `unique` ↦ `russellIota` (order-free uniqueness; languages with
  mereological structure can opt into `sharvyMax` instead by providing a
  `[PartialOrder E]` instance and using a separate plural-aware
  interpreter)
- `anaphoric` and `demonstrative` ↦ entity-assignment lookup, accepted iff
  the restrictor holds of the indexed entity
- `possessive` ↦ `russellIota` of the restrictor conjoined with the
  possession relation applied to the possessor

A handful of agreement theorems wire the constructors together: bare and
unique collapse on a shared restrictor (the default Core reading is weak/
uniqueness); demonstrative and anaphoric agree when they share restrictor
and discourse index (the deictic feature is for presupposition checking,
not referent selection).
-/

namespace Semantics.Definiteness

open Intensional
open Intensional.Variables
open Core (Assignment)

variable {E W : Type}

-- ════════════════════════════════════════════════════════════════
-- § The Interpretation Function
-- ════════════════════════════════════════════════════════════════

/-- Denotation of a `Description` at a bi-assignment, as `Option E`.
    `none` is presupposition failure or inapplicability. -/
noncomputable def interpret (k : Description E W)
    (g : Assignment E) (gs : SitAssignment W) : Option E :=
  match k with
  | .bare R                     => russellIota (fun x => R g gs x)
  | .indefinite _               => none
  | .unique R _                 => russellIota (fun x => R g gs x)
  | .anaphoric R d              =>
      letI := Classical.dec (R g gs (g d))
      if R g gs (g d) then some (g d) else none
  | .demonstrative R _ _ d      =>
      letI := Classical.dec (R g gs (g d))
      if R g gs (g d) then some (g d) else none
  | .possessive R possessor rel =>
      russellIota (fun x => R g gs x ∧ rel g gs (possessor g gs) x)

-- ════════════════════════════════════════════════════════════════
-- § Per-Constructor Reductions
-- ════════════════════════════════════════════════════════════════

@[simp]
theorem interpret_bare (R : DenotGS E W .et)
    (g : Assignment E) (gs : SitAssignment W) :
    interpret (.bare R) g gs = russellIota (fun x => R g gs x) := rfl

@[simp]
theorem interpret_indefinite (R : DenotGS E W .et)
    (g : Assignment E) (gs : SitAssignment W) :
    interpret (E := E) (W := W) (.indefinite R) g gs = none := rfl

@[simp]
theorem interpret_unique (R : DenotGS E W .et) (sIdx : Nat)
    (g : Assignment E) (gs : SitAssignment W) :
    interpret (.unique R sIdx) g gs = russellIota (fun x => R g gs x) := rfl

theorem interpret_anaphoric (R : DenotGS E W .et) (d : Nat)
    (g : Assignment E) (gs : SitAssignment W) :
    interpret (.anaphoric R d) g gs =
      (letI := Classical.dec (R g gs (g d))
       if R g gs (g d) then some (g d) else none) := rfl

theorem interpret_demonstrative
    (R : DenotGS E W .et) (deictic : Features.Deixis.Feature)
    (sIdx d : Nat) (g : Assignment E) (gs : SitAssignment W) :
    interpret (.demonstrative R deictic sIdx d) g gs =
      (letI := Classical.dec (R g gs (g d))
       if R g gs (g d) then some (g d) else none) := rfl

@[simp]
theorem interpret_possessive
    (R : DenotGS E W .et) (possessor : DenotGS E W .e) (rel : DenotGS E W .eet)
    (g : Assignment E) (gs : SitAssignment W) :
    interpret (.possessive R possessor rel) g gs =
      russellIota (fun x => R g gs x ∧ rel g gs (possessor g gs) x) := rfl

-- ════════════════════════════════════════════════════════════════
-- § Cross-Constructor Agreement Theorems
-- ════════════════════════════════════════════════════════════════

/-- Bare nouns and weak/uniqueness definites agree on referent selection
    when they share a restrictor — the default Core reading is uniqueness.
    Languages whose bare nouns shift to ∃ or kind readings override this
    via fragment-specific interpreters. -/
theorem interpret_bare_eq_unique
    (R : DenotGS E W .et) (sIdx : Nat)
    (g : Assignment E) (gs : SitAssignment W) :
    interpret (.bare R) g gs = interpret (.unique R sIdx) g gs := rfl

/-- The deictic feature on a demonstrative does not affect referent
    selection: demonstratives and anaphoric definites pick the same entity
    when they share restrictor and discourse index. The deictic content is
    a presupposition filter, not a selector. -/
theorem interpret_demonstrative_eq_anaphoric
    (R : DenotGS E W .et) (deictic : Features.Deixis.Feature)
    (sIdx d : Nat) (g : Assignment E) (gs : SitAssignment W) :
    interpret (.demonstrative R deictic sIdx d) g gs =
    interpret (.anaphoric R d) g gs := rfl

/-- The situation index on a `unique` description does not affect the
    interpretation as written: the restrictor `R` already takes the full
    situation assignment, so the index records *which* pronoun is bound
    but does not change what is computed by the operator. -/
theorem interpret_unique_index_irrelevant
    (R : DenotGS E W .et) (sIdx₁ sIdx₂ : Nat)
    (g : Assignment E) (gs : SitAssignment W) :
    interpret (.unique R sIdx₁) g gs = interpret (.unique R sIdx₂) g gs := rfl

-- ════════════════════════════════════════════════════════════════
-- § Witness Properties
-- ════════════════════════════════════════════════════════════════

/-- Whatever entity the interpretation returns, the restrictor holds of it.
    Stated for `.unique` (the operator-driven case); the analogue for
    `.bare` follows by `interpret_bare_eq_unique`. -/
theorem interpret_unique_witness_satisfies
    (R : DenotGS E W .et) (sIdx : Nat) (e : E)
    (g : Assignment E) (gs : SitAssignment W)
    (h : interpret (.unique R sIdx) g gs = some e) :
    R g gs e := by
  have : russellIota (fun x => R g gs x) = some e := by
    rw [← interpret_unique]; exact h
  exact russellIota_witness_satisfies _ e this

/-- Witness-extraction shortcut: when an entity satisfies the restrictor and
    is the unique satisfier, `.unique` returns it. Closes the standard
    Russellian-iota extraction in one line — without it, every concrete
    `interpret_*` instance needs the six-step ritual of
    `interpret_unique` → `russellIota_isSome_iff_existsUnique` → `Option.isSome_iff_exists` →
    `russellIota_witness_satisfies` → case analysis. -/
theorem interpret_unique_eq_some_of_existsUnique
    (R : DenotGS E W .et) (sIdx : Nat)
    (g : Assignment E) (gs : SitAssignment W) (e : E)
    (hSat : R g gs e) (hUniq : ∀ y, R g gs y → y = e) :
    interpret (.unique R sIdx) g gs = some e := by
  have hExU : existsUnique (fun x => R g gs x) :=
    ⟨⟨e, hSat⟩, fun x y hx hy => (hUniq x hx).trans (hUniq y hy).symm⟩
  rw [interpret_unique]
  obtain ⟨e', he'⟩ : ∃ e', russellIota (fun x => R g gs x) = some e' :=
    Option.isSome_iff_exists.mp ((russellIota_isSome_iff_existsUnique _).mpr hExU)
  rw [he']
  congr 1
  exact hUniq e' (russellIota_witness_satisfies _ _ he')

/-- Specialization of `interpret_unique_eq_some_of_existsUnique` to a packaged
    `existsUnique` hypothesis, with the witness extracted. The first projection
    of `existsUnique` gives the entity; the second proves uniqueness. -/
theorem interpret_unique_eq_some_choose
    (R : DenotGS E W .et) (sIdx : Nat)
    (g : Assignment E) (gs : SitAssignment W)
    (hExU : existsUnique (fun x => R g gs x)) :
    interpret (.unique R sIdx) g gs = some hExU.1.choose :=
  interpret_unique_eq_some_of_existsUnique R sIdx g gs hExU.1.choose
    hExU.1.choose_spec
    (fun y hy => hExU.2 y _ hy hExU.1.choose_spec)

/-- An anaphoric definite that returns a witness must return the indexed
    entity — it never picks anything else. -/
theorem interpret_anaphoric_witness_is_indexed
    (R : DenotGS E W .et) (d : Nat)
    (g : Assignment E) (gs : SitAssignment W) (e : E)
    (h : interpret (.anaphoric R d) g gs = some e) :
    e = g d := by
  classical
  rw [interpret_anaphoric] at h
  by_cases hR : R g gs (g d)
  · rw [if_pos hR] at h; exact (Option.some_inj.mp h).symm
  · rw [if_neg hR] at h; cases h

/-- An anaphoric definite returns a witness iff the restrictor holds of the
    indexed entity. -/
theorem interpret_anaphoric_isSome_iff
    (R : DenotGS E W .et) (d : Nat)
    (g : Assignment E) (gs : SitAssignment W) :
    (interpret (.anaphoric R d) g gs).isSome ↔ R g gs (g d) := by
  classical
  rw [interpret_anaphoric]
  by_cases h : R g gs (g d)
  · simp [h]
  · simp [h]

/-- [patel-grosz-grosz-2017]'s "DEM = PER + index": the **strong** article
    (`anaphoric` at index `i`) and the **weak** article (`unique`) over a shared
    restrictor pick the same referent exactly when the indexed entity `g i` is the
    unique satisfier of `R`. The hypotheses are load-bearing — off this condition
    the strong (the indexed entity) and weak (the unique satisfier) articles
    diverge, PG&G's point that the strong article is anaphoric in a way the weak
    one is not. -/
theorem interpret_anaphoric_eq_unique_of_existsUnique
    (R : DenotGS E W .et) (sIdx i : Nat)
    (g : Assignment E) (gs : SitAssignment W)
    (hSat : R g gs (g i)) (hUniq : ∀ y, R g gs y → y = g i) :
    interpret (.anaphoric R i) g gs = interpret (.unique R sIdx) g gs := by
  rw [interpret_unique_eq_some_of_existsUnique R sIdx g gs (g i) hSat hUniq,
      interpret_anaphoric, if_pos hSat]

end Semantics.Definiteness
