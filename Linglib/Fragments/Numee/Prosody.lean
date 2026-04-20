import Linglib.Theories.Phonology.Autosegmental.RegisterTier

/-!
# Numèè Prosodic Fragment
@cite{lionnet-2025}

Lexical and utterance-level prosody for Numèè (Glottocode: numa1247),
a Southern Oceanic language of New Caledonia. Data here are drawn from
the Goro dialect as described and analysed by @cite{lionnet-2025}
(which cites earlier descriptive work by Rivierre).

The Numèè register system shares the same underlying inventory as
Drubea — registerless and downstepped morae as the only contrastive
units, with no tone features. The two languages diverge at the
**utterance-final boundary** (@cite{lionnet-2025} §3.3–3.4):

- **Drubea** (`Fragments/Drubea/Prosody.lean`): utterance-final raising
  `h%` on the final registerless syllable.
- **Numèè** (this file): utterance-final downstepping `⁺%` on the final
  **light CV** syllable, only when **preceded by a registerless syllable**.
  When the final is itself underlyingly downstepped, the boundary
  inserts an *extra* downstep — a stacked "double downstep" `⁺⁺` —
  preserving the registerless/downstepped contrast utterance-finally
  (@cite{lionnet-2025} ex. 24 vs 25).

This fragment models syllable structure explicitly (the `Drubea`
fragment works at the morpheme/spec-list level), because the Numèè
boundary phenomenon's eligibility conditions reference syllable weight
(light CV vs CVV) and the immediately preceding syllable's register
status — neither expressible in a flat `List TRN`.
-/

namespace Fragments.Numee.Prosody

open Phonology.Autosegmental.RegisterTier

-- ============================================================================
-- § 1: Syllable-Level Representation
-- ============================================================================

/-- A Numèè syllable: surface form (segmental, no register marks) plus
    one `TRN` per mora. The mora is the register-bearing unit
    (@cite{lionnet-2025} §4.2), so light CV is monomoraic and CVV is
    bimoraic. A downstep mark `⁺` on the leftmost mora of a syllable
    surfaces as `some .l` at the corresponding `specs` index. -/
structure Syllable where
  form  : String
  specs : List TRN
  deriving Repr, DecidableEq

namespace Syllable

/-- Number of morae in this syllable (one `TRN` per mora). -/
def morae (s : Syllable) : Nat := s.specs.length

/-- Light CV: a monomoraic short syllable (e.g. `ku`, `nĩ`, `kwɛ̃`).
    The Numèè boundary downstep `⁺%` only docks on light CV finals. -/
def isLightCV (s : Syllable) : Bool := s.morae == 1

/-- All morae of this syllable are registerless (no `l` or `h`). The
    Numèè `⁺%` boundary requires the *preceding* syllable to satisfy
    this. -/
def isRegisterless (s : Syllable) : Bool := s.specs.all (· == TRN.empty)

/-- The syllable carries an underlying downstep `l` on at least one mora. -/
def isDownstepped (s : Syllable) : Bool := s.specs.any (· == TRN.downstep)

end Syllable

/-- A Numèè utterance: an ordered sequence of syllables. -/
abbrev Utterance := List Syllable

-- ============================================================================
-- § 2: Boundary Downstep ⁺% (@cite{lionnet-2025} §3.4)
-- ============================================================================

/-- Realisation outcome for the Numèè utterance-final boundary downstep
    `⁺%` (@cite{lionnet-2025} §3.4):

    - `none`: eligibility conditions not met; the final syllable
      surfaces unchanged (heavy final, or final preceded by a
      downstepped syllable).
    - `single`: a registerless final acquires one extra downstep step
      (the canonical Goro pattern).
    - `double`: an already-downstepped final is realised with a stacked
      double downstep `⁺⁺`, lowering pitch *below* what an underlyingly
      downstepped non-final realisation would (@cite{lionnet-2025} ex. 24
      vs 25). This stacking preserves the registerless/downstepped
      contrast in utterance-final position. -/
inductive BoundaryEffect where
  | none
  | single
  | double
  deriving DecidableEq, Repr

/-- The Numèè utterance-final boundary downstep `⁺%`
    (@cite{lionnet-2025} §3.4).

    Eligibility: the final syllable must be **light CV** (monomoraic)
    AND **preceded by a registerless syllable**. When eligible, the
    outcome depends on the final syllable's underlying register:
    registerless → `single`, downstepped → `double` (stacking). -/
def numeeBoundaryEffect : Utterance → BoundaryEffect := fun utt =>
  match utt.reverse with
  | last :: penult :: _ =>
      if last.isLightCV && penult.isRegisterless then
        if last.isDownstepped then .double else .single
      else .none
  | _ => .none

-- ============================================================================
-- § 3: Lexical Data (@cite{lionnet-2025} §3.4 ex. 22–29)
-- ============================================================================

/-- /jaa/ 'juice' — bimoraic CVV, registerless (ex. 24, 25). -/
def jaa : Syllable := ⟨"jaa", [TRN.empty, TRN.empty]⟩

/-- /nĩ/ 'coconut' — monomoraic CV, registerless (ex. 24). -/
def niCoconut : Syllable := ⟨"nĩ", [TRN.empty]⟩

/-- /⁺nĩ/ 'breast' — monomoraic CV, downstepped (ex. 25). The
    minimal-pair partner of `niCoconut`. -/
def niBreast : Syllable := ⟨"nĩ", [TRN.downstep]⟩

/-- /mii/ 'low' — bimoraic CVV, registerless (ex. 26). Heavy finals
    block the boundary downstep. -/
def mii : Syllable := ⟨"mii", [TRN.empty, TRN.empty]⟩

/-- /ku/ 'yam' — monomoraic CV, registerless (ex. 28). Light, but in
    ex. 28 it is preceded by a downstepped syllable, so the boundary
    is blocked. -/
def ku : Syllable := ⟨"ku", [TRN.empty]⟩

/-- /⁺tĩĩ/ 'three' — bimoraic CVV, downstep on first mora (ex. 28).
    Whether or not light, what matters here is that it counts as
    *downstepped* and so blocks the boundary on the following `ku`. -/
def beTii : Syllable := ⟨"tĩĩ", [TRN.downstep, TRN.empty]⟩

/-- /kwɛ̃/ 'sand' — monomoraic CV, registerless (ex. 29). Like `ku`,
    light but preceded by a downstepped syllable in its example. -/
def kwe : Syllable := ⟨"kwɛ̃", [TRN.empty]⟩

/-- /⁺paa/ 'down' — bimoraic CVV with downstep on first mora (ex. 29). -/
def paa : Syllable := ⟨"paa", [TRN.downstep, TRN.empty]⟩

/-- A registerless filler syllable used to pad utterances (`a`, `nõ`,
    `dɛŋo`, etc. in the §3.4 examples — segmental detail varies but
    the prosodic content is just `[TRN.empty]` or `[TRN.empty, TRN.empty]`). -/
def regCV  : Syllable := ⟨"σ", [TRN.empty]⟩
def regCVV : Syllable := ⟨"σː", [TRN.empty, TRN.empty]⟩

end Fragments.Numee.Prosody
