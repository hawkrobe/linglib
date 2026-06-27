import Linglib.Phonology.Prosody.Syllable
import Linglib.Phonology.Prosody.Foot

/-!
# Accent assignment and tone derivation

Language-general accent-assignment rules and the accent-to-tone derivation
for pitch-accent systems such as Japanese. Default accent is derived from a
syllable-weight profile; surface tones are then fully determined by accent
location.

## Main definitions

* `defaultAccentAAR` — the Antepenultimate Accent Rule ([mccawley-1968]):
  accent the syllable holding the antepenultimate mora.
* `latinStressRule` — the Latin Stress Rule ([hayes-1995]): penult if heavy,
  else antepenult. [kubozono-2006] argues it fits Japanese loanword accent.
* `LevelTone`, `accentToTones` — surface tones derived from accent position
  and mora count via accentual HL, initial rise, and spreading
  ([kawahara-2015]).
* `nonFinalitySigma`, `nonFinalityFoot` — the two NonFinality constraints of
  [prince-smolensky-1993] (final syllable vs. final head foot).
* `shortN2CompoundAccent`, `longN2CompoundAccent` — Japanese compound accent,
  split by the length of the second member ([kawahara-2015]).
-/

namespace Prosody

/-! ### Syllable-from-mora lookup -/

/-- The 0-indexed syllable containing mora `targetMora` (0-indexed), or
    `none` if `targetMora` exceeds the total mora count. -/
def findSyllable (weights : List Syllable.Weight) (targetMora : Nat) : Option Nat :=
  go weights targetMora 0
where
  go : List Syllable.Weight → Nat → Nat → Option Nat
    | [], _, _ => none
    | w :: ws, target, idx =>
      if target < w then some idx
      else go ws (target - w) (idx + 1)

/-! ### Antepenultimate Accent Rule -/

/-- The Antepenultimate Accent Rule ([mccawley-1968]): accent the syllable
    containing the antepenultimate (3rd-from-last) mora. Words with fewer than
    three morae accent the initial syllable. Returns the 0-indexed syllable. -/
def defaultAccentAAR (weights : List Syllable.Weight) : Option Nat :=
  match weights with
  | [] => none
  | _ =>
    let totalMorae := weights.foldl (· + ·) 0
    let targetMora := if totalMorae ≥ 3 then totalMorae - 3 else 0
    findSyllable weights targetMora

/-! ### Latin Stress Rule -/

/-- The Latin Stress Rule ([hayes-1995]): accent the penult if it is heavy
    (≥ 2μ), otherwise the antepenult. Monosyllables accent the only syllable;
    disyllables accent the penult (= initial). [kubozono-2006] argues this
    rule fits Japanese default accentuation better than `defaultAccentAAR`. -/
def latinStressRule : List Syllable.Weight → Option Nat
  | [] => none
  | [_] => some 0
  | [_, _] => some 0                    -- disyllable → always penult (= initial)
  | [_, 0, _] | [_, 1, _] => some 0      -- light penult → antepenult
  | [_, _, _] => some 1                 -- heavy+ penult → penult
  | _ :: rest@(_ :: _ :: _) =>           -- peel front, recurse, add 1
    (latinStressRule rest).map (· + 1)

/-! ### Accent-to-tone derivation -/

/-- A level tone for pitch-accent systems. Japanese uses only `H` (high) and
    `L` (low) at the lexical level ([kawahara-2015]). -/
inductive LevelTone where
  | H
  | L
  deriving DecidableEq, Repr, BEq

/-- Derive the surface tone of each mora from accent position and mora count
    ([kawahara-2015]), returning one `LevelTone` per mora:
    1. accentual HL — `H` on the accented mora, `L` on the next;
    2. initial rise — `L` on mora 0, `H` on mora 1 (blocked by initial accent);
    3. spreading — unspecified moras copy the rightmost specified tone. -/
def accentToTones (accentMora : Option Nat) (nMorae : Nat) : List LevelTone :=
  -- Steps 1+2: accentual HL + initial rise (`none` = still unspecified).
  -- `nMorae = 0` needs no special case: `List.range 0 = []` flows through to `[]`.
  let specified : List (Option LevelTone) := (List.range nMorae).map λ i =>
    if accentMora == some i then some .H
    else if accentMora == some (i - 1) && i ≥ 1 then some .L
    else if i == 0 && accentMora != some 0 then some .L
    else if i == 1 && accentMora != some 1 && accentMora != some 0 then some .H
    else none
  -- Step 3: spreading — fill `none`s from the rightmost specified tone (mora 0
  -- is always specified, so the `.H` seed is never reached for well-formed input).
  spread specified .H
where
  spread : List (Option LevelTone) → LevelTone → List LevelTone
    | [], _ => []
    | some t :: rest, _ => t :: spread rest t
    | none :: rest, last => last :: spread rest last

/-! ### NonFinality constraints -/

/-- NonFinality(σ) ([prince-smolensky-1993]): `1` if accent is on the
    word-final syllable, else `0`. Drives the avoidance of final accent in
    Japanese compound formation and loanword adaptation ([kawahara-2015]). -/
def nonFinalitySigma (accentSyll : Option Nat) (nSyll : Nat) : Nat :=
  match accentSyll with
  | some pos => if pos + 1 == nSyll then 1 else 0
  | none => 0

/-- NonFinality(Ft) ([prince-smolensky-1993]): `1` if the rightmost foot of
    the parse is the head foot (contains the accent), else `0`. Distinct from
    `nonFinalitySigma`: accent on the final *syllable* may be tolerated if the
    final *foot* is not the head foot. -/
def nonFinalityFoot (parse : MetricalParse) (accentSyll : Option Nat) : Nat :=
  match parse.reverse.head? with
  | some (.foot ws) =>
    -- The final foot occupies syllables `[finalFootStart, syllableCount)`.
    let finalFootStart := parse.syllableCount - ws.length
    match accentSyll with
    | some pos => if pos ≥ finalFootStart ∧ pos < finalFootStart + ws.length
                  then 1 else 0
    | none => 0
  | _ => 0

/-! ### Compound accent -/

/-- Short-N2 compound accent ([kawahara-2015]): when the second member N2 is
    short (≤ 2μ), accent may pre-accent the last syllable of N1, or N2 retains
    its own accent. Pre-accenting N2s lose their accent to NonFinality(Ft) and
    receive a new one, like dominant pre-accenting suffixes. -/
def shortN2CompoundAccent (n1Morae : Nat) (n2Accent : Option Nat)
    (preAccenting : Bool) : Option Nat :=
  if preAccenting then
    -- Pre-accenting: accent on last mora of N1
    if n1Morae > 0 then some (n1Morae - 1) else none
  else
    -- Retain N2 accent (shifted by N1 length)
    n2Accent.map (· + n1Morae)

/-- Long-N2 compound accent ([kawahara-2015]): when N2 is long (≥ 3μ), an
    unaccented or final-accented N2 accents its initial syllable; otherwise
    N2's own accent is retained. -/
def longN2CompoundAccent (n1Morae : Nat) (n2Accent : Option Nat)
    (n2Morae : Nat) : Option Nat :=
  match n2Accent with
  | none => some n1Morae  -- unaccented N2 → accent N2-initial
  | some pos =>
    if pos + 1 == n2Morae then some n1Morae  -- final accent → accent N2-initial
    else some (pos + n1Morae)                 -- retain N2 accent

end Prosody
