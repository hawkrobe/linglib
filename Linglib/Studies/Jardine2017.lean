/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Embedding
import Linglib.Phonology.Autosegmental.Junction

/-!
# Jardine (2017): tone-association patterns as forbidden subgraphs
[jardine-2017]

[jardine-2017] argues that tone-association patterns over
autosegmental representations are *computationally local* in a
well-defined sense: each pattern's well-formedness can be specified
by a finite set of forbidden connected subgraphs. An AR is
well-formed under a grammar `{¬ F₁, ..., ¬ Fₙ}` iff none of the
`Fᵢ` embeds into it.

This gives a restrictive theory of tonal well-formedness that:
* makes clear typological predictions (the paper covers Mende,
  Hausa, Northern Karanga Shona, Kukuya, Hirosaki Japanese);
* contrasts with derivational/global accounts (`*VαCVβ` constraints,
  directionality parameters) which can overgenerate;
* admits a learning algorithm based on "scanning window" inspection.

## Coverage

This file formalises §3.1 + §5.1 of [jardine-2017]: the Mende
right-edge multiple-association pattern and the contrasting Hausa
left-edge pattern. Hirosaki Japanese (§5.3), Northern Karanga Shona
(§5.1's second half), and Kukuya (§5.2) are sketched in the
docstring as future extensions — each follows the same `Graph`-
based forbidden-subgraph schema.

Second consumer of `Autosegmental.Graph` after
`Studies/LaoideKemp2026.lean`. Exercises the `SubgraphEmbeds`
predicate (precedence-preserving translation embedding), which
Laoide-Kemp doesn't touch.

## Main definitions

* `Tone`, `TBU` — label types for the tonal and timing tiers.
* `AR` — `Graph Tone TBU`, an autosegmental representation in
  Jardine's sense.
* `Mende.attested` — three worked Mende ARs from
  [jardine-2017] eq. (5): `mbû` ('owl', HL contour on 1σ),
  `ngìlà` ('dog', H L on 2σ), `félàmà` ('junction', HLL with
  L-spread on 3σ).
* `Mende.forbidden_*` — three forbidden subgraphs from eq. (21):
  non-final H spreading, non-final L spreading, non-final contour.
* `Hausa.attested` — Hausa ARs with left-edge multiple association
  (eq. 7).
* `Hausa.forbidden_*` — non-initial spreading + non-initial contour
  (eq. 22).
* Per-attested-form theorems: each attested AR does NOT contain any
  forbidden subgraph.

## Convention

Jardine 2017 draws forbidden subgraphs with explicit `H→L`
precedence arrows on the tone tier and `σ→σ` arrows on the TBU tier.
In `Graph Tone TBU`, precedence is implicit in list order: the upper
tier is `List Tone`, the lower is `List TBU`. The `SubgraphEmbeds`
predicate captures the paper's connected-subgraph embedding by
requiring a *translation* mapping (consecutive positions in F map
to consecutive positions in G).
-/

namespace Jardine2017

open Autosegmental Autosegmental.Graph

/-! ## §1 Label types

Jardine 2017 uses `H` and `L` for tones and `σ` (syllable) or `μ`
(mora) for tone-bearing units, plus `#` for tier boundaries.
Boundaries (`#`) appear in some grammars (e.g., Northern Karanga
Shona eq. (24)) but not in the Mende/Hausa grammars formalised here;
we include the constructor for future extensions.
-/

/-- Tonal-tier label. -/
inductive Tone
  | H
  | L
  /-- Word/tier boundary marker (#). Used by some grammars (e.g.,
      Northern Karanga Shona in [jardine-2017] eq. 24); not used
      in the Mende/Hausa formalisations below. -/
  | bdry
  deriving DecidableEq, Repr

/-- Tone-bearing unit label. Most patterns in [jardine-2017]
    use the syllable σ; Hirosaki Japanese (§5.3) uses the mora μ. -/
inductive TBU
  | σ
  | μ
  /-- TBU-tier boundary marker. -/
  | bdry
  deriving DecidableEq, Repr

/-- An autosegmental representation in Jardine 2017's sense, on the graph
    foundation: tones over TBUs (with implicit precedence by position),
    links as association lines. -/
abbrev ARep := Autosegmental.Representation
  (Sigma.fst : ((b : Bool) × Autosegmental.TwoTier Tone TBU b) → Bool)

/-- Link presentations from finite pair lists (melody position, TBU position). -/
def mkL (links : List (ℕ × ℕ)) (i j : Bool) (p q : ℕ) : Prop :=
  i = true ∧ j = false ∧ (p, q) ∈ links

instance (links : List (ℕ × ℕ)) (i j : Bool) (p q : ℕ) :
    Decidable (mkL links i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Build a representation from a tone melody, a TBU string, and links. -/
abbrev mk (tones : List Tone) (tbus : List TBU) (links : List (ℕ × ℕ)) : ARep :=
  Autosegmental.Representation.ofData
    (fun b => match b with
      | true => (tones : List (Autosegmental.TwoTier Tone TBU true))
      | false => tbus)
    (mkL links)

open Autosegmental in
/-- Non-embedding verdicts compute: the spec plus kernel evaluation. -/
theorem mk_embeds_iff {tF tX : List Tone} {bF bX : List TBU}
    {lF lX : List (ℕ × ℕ)} :
    (mk tF bF lF).FactorEmbeds (mk tX bX lX) ↔
      dataEmbeds
        (fun b => match b with
          | true => (tF : List (Autosegmental.TwoTier Tone TBU true))
          | false => bF)
        (fun b => match b with
          | true => (tX : List (Autosegmental.TwoTier Tone TBU true))
          | false => bX)
        (mkL lF) (mkL lX) :=
  Representation.factorEmbeds_ofData_iff

/-! ## §2 Mende: right-edge multiple association
[jardine-2017] §3.1, eq. (5)

In Mende, tonal *plateaus* (a single tone associated to multiple
syllables) and contour tones (multiple tones on one syllable) are
restricted to the right word edge. -/

namespace Mende

/-- `mbû` 'owl' (1σ, HL contour). -/
abbrev mbû : ARep := mk [Tone.H, Tone.L] [TBU.σ] [(0, 0), (1, 0)]

/-- `ngìlà` 'dog' (2σ, HL melody, one tone per syllable). -/
abbrev ngìlà : ARep := mk [Tone.H, Tone.L] [TBU.σ, TBU.σ] [(0, 0), (1, 1)]

/-- `félàmà` 'junction' (3σ, HL melody with L-spread to the right two
    syllables: HLL surface). The diagnostic case for Mende. -/
abbrev félàmà : ARep := mk [Tone.H, Tone.L] [TBU.σ, TBU.σ, TBU.σ] [(0, 0), (1, 1), (1, 2)]

/-- **(21a) non-final H spreading**: an H linked to two consecutive σs with an
    L following on the tonal tier. -/
abbrev forbidden_nonfinal_H : ARep := mk [Tone.H, Tone.L] [TBU.σ, TBU.σ] [(0, 0), (0, 1)]

/-- **(21b) non-final L spreading** (mirror). -/
abbrev forbidden_nonfinal_L : ARep := mk [Tone.L, Tone.H] [TBU.σ, TBU.σ] [(0, 0), (0, 1)]

/-- **(21c) non-final contour**: an HL contour on a σ with another σ
    following. -/
abbrev forbidden_nonfinal_contour : ARep :=
  mk [Tone.H, Tone.L] [TBU.σ, TBU.σ] [(0, 0), (1, 0)]

/-! ### §2.2 Attested forms satisfy the Mende grammar ([jardine-2017] §5.1) -/

theorem mbû_no_nonfinal_H : ¬ forbidden_nonfinal_H.FactorEmbeds mbû := by
  rw [mk_embeds_iff]; decide

theorem mbû_no_nonfinal_L : ¬ forbidden_nonfinal_L.FactorEmbeds mbû := by
  rw [mk_embeds_iff]; decide

theorem mbû_no_nonfinal_contour : ¬ forbidden_nonfinal_contour.FactorEmbeds mbû := by
  rw [mk_embeds_iff]; decide

theorem ngìlà_no_nonfinal_H : ¬ forbidden_nonfinal_H.FactorEmbeds ngìlà := by
  rw [mk_embeds_iff]; decide

theorem ngìlà_no_nonfinal_L : ¬ forbidden_nonfinal_L.FactorEmbeds ngìlà := by
  rw [mk_embeds_iff]; decide

theorem ngìlà_no_nonfinal_contour :
    ¬ forbidden_nonfinal_contour.FactorEmbeds ngìlà := by
  rw [mk_embeds_iff]; decide

theorem félàmà_no_nonfinal_H : ¬ forbidden_nonfinal_H.FactorEmbeds félàmà := by
  rw [mk_embeds_iff]; decide

theorem félàmà_no_nonfinal_L : ¬ forbidden_nonfinal_L.FactorEmbeds félàmà := by
  rw [mk_embeds_iff]; decide

theorem félàmà_no_nonfinal_contour :
    ¬ forbidden_nonfinal_contour.FactorEmbeds félàmà := by
  rw [mk_embeds_iff]; decide

end Mende

/-! ## §3 Hausa: left-edge multiple association ([jardine-2017] eq. (7), (22)) -/

namespace Hausa

/-- `fáadi` 'fall' (2σ, HL melody one-to-one). -/
abbrev fáadi : ARep := mk [Tone.H, Tone.L] [TBU.σ, TBU.σ] [(0, 0), (1, 1)]

/-- `háantúnàa` 'noses' (3σ, HHL — H spreads at the *left* edge). -/
abbrev háantúnàa : ARep :=
  mk [Tone.H, Tone.L] [TBU.σ, TBU.σ, TBU.σ] [(0, 0), (0, 1), (1, 2)]

/-- **(22a) non-initial H spreading**: an L preceding an H linked to two σs. -/
abbrev forbidden_noninitial_H : ARep :=
  mk [Tone.L, Tone.H] [TBU.σ, TBU.σ] [(1, 0), (1, 1)]

/-- **(22b) non-initial L spreading** (mirror). -/
abbrev forbidden_noninitial_L : ARep :=
  mk [Tone.H, Tone.L] [TBU.σ, TBU.σ] [(1, 0), (1, 1)]

/-- **(22c) non-initial contour**: a σ preceded by another σ, bearing an HL
    contour. -/
abbrev forbidden_noninitial_contour : ARep :=
  mk [Tone.H, Tone.L] [TBU.σ, TBU.σ] [(0, 1), (1, 1)]

/-! ### §3.2 Attested Hausa forms satisfy the Hausa grammar -/

theorem fáadi_no_noninitial_H : ¬ forbidden_noninitial_H.FactorEmbeds fáadi := by
  rw [mk_embeds_iff]; decide

theorem fáadi_no_noninitial_L : ¬ forbidden_noninitial_L.FactorEmbeds fáadi := by
  rw [mk_embeds_iff]; decide

theorem fáadi_no_noninitial_contour :
    ¬ forbidden_noninitial_contour.FactorEmbeds fáadi := by
  rw [mk_embeds_iff]; decide

theorem háantúnàa_no_noninitial_H :
    ¬ forbidden_noninitial_H.FactorEmbeds háantúnàa := by
  rw [mk_embeds_iff]; decide

theorem háantúnàa_no_noninitial_L :
    ¬ forbidden_noninitial_L.FactorEmbeds háantúnàa := by
  rw [mk_embeds_iff]; decide

theorem háantúnàa_no_noninitial_contour :
    ¬ forbidden_noninitial_contour.FactorEmbeds háantúnàa := by
  rw [mk_embeds_iff]; decide

end Hausa

/-! ## §4 The Mende/Hausa contrast: same shape, opposite edges
[jardine-2017] §3.1 and §5.1

Mende's `félàmà` (HLL on 3σ, L-spread at *right* edge) is exactly
the kind of pattern Hausa's grammar would forbid (its mirror is a
non-initial L spread). Conversely, Hausa's `háantúnàa` (HHL on 3σ,
H-spread at *left* edge) is exactly what Mende's grammar forbids.

This pair makes Jardine's locality thesis concrete: each language's
grammar is a finite set of forbidden subgraphs, and the difference
between Mende and Hausa is the *side* of the word edge to which the
prohibition applies.
-/

/-- The Hausa attested form `háantúnàa` (HHL = H-spread to first 2σ)
    contains exactly the structural pattern that Mende's grammar
    forbids: non-final H spreading. This makes Mende and Hausa
    mutually exclusive on their diagnostic forms. -/
theorem hausa_haantunaa_violates_mende :
    Mende.forbidden_nonfinal_H.FactorEmbeds Hausa.háantúnàa := by
  rw [mk_embeds_iff]; decide

/-- Symmetrically, Mende's `félàmà` (HLL = L-spread to last 2σ)
    contains Hausa's forbidden non-initial-L pattern. -/
theorem mende_felama_violates_hausa :
    Hausa.forbidden_noninitial_L.FactorEmbeds Mende.félàmà := by
  rw [mk_embeds_iff]; decide

/-! ## §5 Future extensions

The paper covers three further patterns not formalised here. Each
extends the same `Graph`-based forbidden-subgraph schema and would
be a natural addition to this file.

* **Northern Karanga Shona** (§5.1 second half, eq. 23-28): a
  *positional* pattern where the leftmost H of a verb stem spreads
  maximally as far as the third syllable; medial L blocks
  multiple-H association. Grammar (24) uses boundary symbols (`#`)
  on both tiers; the `Tone.bdry` and `TBU.bdry` constructors are in
  place for this extension.

* **Kukuya** (§5.2, eq. 30-33): a *quality-sensitive* pattern where
  H tones cannot multiply associate in the presence of L, while L
  can spread freely. Encoded as the conjunction of Mende-grammar
  forbidden subgraphs (for non-final H association) and
  Hausa-grammar forbidden subgraphs (for non-initial H association),
  plus a non-final-contour ban.

* **Hirosaki Japanese** (§5.3, eq. 35-38): a *culminativity*
  constraint: at most one H per word, F (falling) only word-finally,
  H never spreads to multiple TBUs (here moras `μ`, not syllables).
  Demonstrates that the `Graph` substrate handles arbitrary TBU
  types (the `TBU.μ` constructor is already in place).

The deferred items are all `≤ 100 LOC` each in the same shape as
the Mende/Hausa above: enumerate attested forms, enumerate forbidden
subgraphs, prove non-embedding by `decide`. They can be added
incrementally as needed.
-/

end Jardine2017
