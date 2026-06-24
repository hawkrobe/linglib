/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Subgraph

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

/-- An autosegmental representation in Jardine 2017's sense:
    `Graph Tone TBU`. Upper tier is tones (with implicit precedence
    by list order); lower tier is TBUs; links are association lines. -/
abbrev AR := Graph Tone TBU

/-! ## §2 Mende: right-edge multiple association
[jardine-2017] §3.1, eq. (5)

In Mende, tonal *plateaus* (a single tone associated to multiple
syllables) and contour tones (multiple tones on one syllable) are
restricted to the right word edge. The HLL melody surfacing on a
trisyllabic word like `félàmà` 'junction' arises from L's right-edge
spread to syllables 2 and 3.
-/

namespace Mende

/-- `mbû` 'owl' (1σ, HL contour). Both H and L associate to the
    single syllable. Contour at the right edge — the only edge. -/
def mbû : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ]
  links := {(0, 0), (1, 0)}

/-- `ngìlà` 'dog' (2σ, HL melody, one tone per syllable). -/
def ngìlà : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ, .σ]
  links := {(0, 0), (1, 1)}

/-- `félàmà` 'junction' (3σ, HL melody with L-spread to right two
    syllables: HLL surface). The diagnostic case for Mende: L
    spreads at the *right* edge. -/
def félàmà : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ, .σ, .σ]
  links := {(0, 0), (1, 1), (1, 2)}

/-! ### §2.1 Forbidden subgraphs ([jardine-2017] eq. 21)

The Mende grammar is the conjunction of three forbidden subgraphs.
Each subgraph captures one structural configuration that doesn't
appear in any well-formed Mende AR.
-/

/-- **(21a) non-final H spreading**: `¬ H→L : σ σ`. An H tone linked
    to two consecutive σs, with an L tone following on the tonal
    tier. The L's presence is what makes the H "non-final" — there's
    another tone to its right. -/
def forbidden_nonfinal_H : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ, .σ]
  links := {(0, 0), (0, 1)}

/-- **(21b) non-final L spreading**: `¬ L→H : σ σ`. An L tone linked
    to two consecutive σs, with an H tone following. -/
def forbidden_nonfinal_L : AR where
  upper := .ofList [.L, .H]
  lower := .ofList [.σ, .σ]
  links := {(0, 0), (0, 1)}

/-- **(21c) non-final contour**: `¬ H L : σ→σ`. A contour (H and L
    both linked to one σ), with another σ following on the TBU tier.
    The trailing σ makes the contour-bearing σ "non-final". -/
def forbidden_nonfinal_contour : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ, .σ]
  links := {(0, 0), (1, 0)}

/-- The Mende grammar's forbidden block patterns ([jardine-2017] (21a–c)): a
    form is well-formed iff it is `Graph.Free` of all three. -/
def mendeForbidden : List AR :=
  [forbidden_nonfinal_H, forbidden_nonfinal_L, forbidden_nonfinal_contour]

/-! ### §2.2 Attested forms satisfy the Mende grammar

Each attested form is well-formed under the Mende grammar iff it
does not contain any forbidden subgraph. By `SubgraphEmbeds`, this
is `decide`-checkable.
-/

/-- `mbû` (HL contour on 1σ) — well-formed. -/
theorem mbû_no_nonfinal_H : ¬ SubgraphEmbeds forbidden_nonfinal_H mbû := by decide
theorem mbû_no_nonfinal_L : ¬ SubgraphEmbeds forbidden_nonfinal_L mbû := by decide
theorem mbû_no_nonfinal_contour : ¬ SubgraphEmbeds forbidden_nonfinal_contour mbû := by decide

/-- `ngìlà` (HL on 2σ, one tone per σ) — well-formed. -/
theorem ngìlà_no_nonfinal_H : ¬ SubgraphEmbeds forbidden_nonfinal_H ngìlà := by decide
theorem ngìlà_no_nonfinal_L : ¬ SubgraphEmbeds forbidden_nonfinal_L ngìlà := by decide
theorem ngìlà_no_nonfinal_contour :
    ¬ SubgraphEmbeds forbidden_nonfinal_contour ngìlà := by decide

/-- `félàmà` (HLL on 3σ via L-spread to final two σs) — the key
    well-formedness check. L is multiply associated, but the spread
    is to the *right edge*; no forbidden subgraph embeds. -/
theorem félàmà_no_nonfinal_H : ¬ SubgraphEmbeds forbidden_nonfinal_H félàmà := by decide
theorem félàmà_no_nonfinal_L : ¬ SubgraphEmbeds forbidden_nonfinal_L félàmà := by decide
theorem félàmà_no_nonfinal_contour :
    ¬ SubgraphEmbeds forbidden_nonfinal_contour félàmà := by decide

/-- All three Mende attested forms satisfy the full Mende grammar: each is
    `Graph.Free` of `mendeForbidden` (none of the three forbidden subgraphs
    embeds into any of them). [jardine-2017] §5.1, the main empirical claim. -/
theorem mende_grammar_admits_attested :
    mbû.Free mendeForbidden ∧ ngìlà.Free mendeForbidden ∧ félàmà.Free mendeForbidden := by
  decide

end Mende

/-! ## §3 Hausa: left-edge multiple association
[jardine-2017] eq. (7), (22)

Hausa is the *mirror* of Mende: multiple association occurs only at
the left edge. `háantúnàa` 'noses' has HHL surface — the H spreads
*leftward* to the first two syllables.
-/

namespace Hausa

/-- `fáadi` 'fall' (2σ, HL melody one-to-one). -/
def fáadi : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ, .σ]
  links := {(0, 0), (1, 1)}

/-- `háantúnàa` 'noses' (3σ, HHL — H spreads at the *left* edge to
    the first two syllables). The Hausa diagnostic. -/
def háantúnàa : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ, .σ, .σ]
  links := {(0, 0), (0, 1), (1, 2)}

/-! ### §3.1 Forbidden subgraphs ([jardine-2017] eq. 22)

Hausa's grammar is the mirror of Mende's: non-*initial* multiple
association is forbidden. The first two subgraphs match an L
preceding an H linked to two σs (non-initial H spreading) and
mirror; the third forbids a non-initial contour.
-/

/-- **(22a) non-initial H spreading**: `¬ L→H : σ σ`. An L on the
    tonal tier followed by an H linked to two σs — the H is
    non-initial (preceded by L). -/
def forbidden_noninitial_H : AR where
  upper := .ofList [.L, .H]
  lower := .ofList [.σ, .σ]
  links := {(1, 0), (1, 1)}

/-- **(22b) non-initial L spreading** (mirror). -/
def forbidden_noninitial_L : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ, .σ]
  links := {(1, 0), (1, 1)}

/-- **(22c) non-initial contour**: a σ preceded by another σ on
    the TBU tier, with a contour H L linked to the second σ. -/
def forbidden_noninitial_contour : AR where
  upper := .ofList [.H, .L]
  lower := .ofList [.σ, .σ]
  links := {(0, 1), (1, 1)}

/-! ### §3.2 Attested Hausa forms satisfy the Hausa grammar -/

theorem fáadi_no_noninitial_H :
    ¬ SubgraphEmbeds forbidden_noninitial_H fáadi := by decide
theorem fáadi_no_noninitial_L :
    ¬ SubgraphEmbeds forbidden_noninitial_L fáadi := by decide
theorem fáadi_no_noninitial_contour :
    ¬ SubgraphEmbeds forbidden_noninitial_contour fáadi := by decide

theorem háantúnàa_no_noninitial_H :
    ¬ SubgraphEmbeds forbidden_noninitial_H háantúnàa := by decide
theorem háantúnàa_no_noninitial_L :
    ¬ SubgraphEmbeds forbidden_noninitial_L háantúnàa := by decide
theorem háantúnàa_no_noninitial_contour :
    ¬ SubgraphEmbeds forbidden_noninitial_contour háantúnàa := by decide

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
    SubgraphEmbeds Mende.forbidden_nonfinal_H Hausa.háantúnàa := by decide

/-- Symmetrically, Mende's `félàmà` (HLL = L-spread to last 2σ)
    contains Hausa's forbidden non-initial-L pattern. -/
theorem mende_felama_violates_hausa :
    SubgraphEmbeds Hausa.forbidden_noninitial_L Mende.félàmà := by decide

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
