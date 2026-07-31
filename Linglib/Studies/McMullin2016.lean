/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Studies.Hansson2010

/-!
# McMullin (2016) [mcmullin-2016]

Tier-based locality in long-distance phonotactics: learnability and typology.
PhD thesis, University of British Columbia.

A long-distance phonotactic can be stated over **subsequences** — a forbidden pair of
segments however far apart, the strictly piecewise (SP) description — or over a **tier
projection** — delete the transparent material, then forbid adjacent pairs, the
tier-based strictly local (TSL) description. [mcmullin-2016] argues for the tier-based
class: SP grammars cannot see a **blocker**, an intervening segment that halts harmony,
because deleting material can never turn an SP-legal word illegal.

Both halves are formalised here.

* **Transparent harmony: the classes coincide.** Navajo sibilant harmony — the
  [hansson-2010] case study formalised as TSL_2 in `Studies/Hansson2010.lean` — is the
  same stringset as an SP_2 grammar. This is not an artefact of the toy alphabet:
  *every* AGREE language is SP_2 (`Subregular.TSLGrammar.agree_lang_eq_sp`), because
  equality is transitive, so constraining tier-adjacent pairs already constrains pairs
  at arbitrary distance.
* **Opaque harmony: they come apart.** A blocking pattern is TSL_2 but SP at no width,
  since deleting the blocker leaves an illegal word and SP languages are
  subsequence-closed.

The blocking alphabet `BSeg` is schematic — one blocker, one transparent segment, and
the two harmonizing series — and stands in for no particular language. Opaque
consonant-harmony systems are rare; [hansson-2010] surveys the attested cases and none
is formalised here.
-/

namespace McMullin2016

open Subregular Phonology.Studies.Hansson2010

/-! ### Transparent harmony: Navajo is SP_2 as well as TSL_2 -/

/-- **Navajo sibilant harmony is strictly 2-piecewise.** The subject is the very
language `Studies/Hansson2010.lean` builds as TSL_2, not a parallel SP stipulation, so
the two classifications are of one stringset by construction. -/
theorem navajoSibilantHarmony_lang_isSP2 :
    navajoSibilantHarmony.lang.IsStrictlyPiecewise 2 :=
  TSLGrammar.agree_lang_isStrictlyPiecewise NSeg.onTier

/-- The tier-based and subsequence-based grammars for Navajo generate the same
language — the instance at `NSeg.onTier` of `TSLGrammar.agree_lang_eq_sp`. -/
theorem navajoSibilantHarmony_lang_eq_sp :
    navajoSibilantHarmony.lang = (SPGrammar.agree NSeg.onTier).language 2 :=
  TSLGrammar.agree_lang_eq_sp NSeg.onTier

/-- [hansson-2010]'s minimal pair under the SP_2 description: the pre-harmony
/si-dʒéːʔ/ is rejected and the surface [ʃidʒéːʔ] accepted. Both transfer along the
equality of languages rather than being recomputed. -/
theorem preSiDze_violates_sp :
    preSiDze ∉ (SPGrammar.agree NSeg.onTier).language 2 :=
  navajoSibilantHarmony_lang_eq_sp ▸ preSiDze_violates

theorem postShiDze_legal_sp :
    postShiDze ∈ (SPGrammar.agree NSeg.onTier).language 2 :=
  navajoSibilantHarmony_lang_eq_sp ▸ postShiDze_legal

/-! ### Opaque harmony: blocking is strictly piecewise at no width -/

/-- A schematic alphabet for an opaque long-distance pattern: the two harmonizing
series, a blocker, and transparent material. -/
inductive BSeg
  /-- Anterior member of the harmonizing series. -/
  | ant
  /-- Posterior member of the harmonizing series. -/
  | post
  /-- The blocker: it projects onto the tier, so it interrupts the harmony. -/
  | blocker
  /-- Transparent material: off-tier, hence invisible to the constraint. -/
  | transparent
  deriving DecidableEq

/-- Everything but the transparent segment projects. A blocker *is* a segment that the
tier keeps — that is the whole of its opacity. -/
def BSeg.onTier (s : BSeg) : Prop := s ≠ .transparent

instance : DecidablePred BSeg.onTier :=
  fun s => inferInstanceAs (Decidable (s ≠ .transparent))

/-- The forbidden tier-adjacent pairs: the two series may not be tier-adjacent. -/
def BSeg.Mixed : BSeg → BSeg → Prop
  | .ant, .post => True
  | .post, .ant => True
  | _, _ => False

instance : DecidableRel BSeg.Mixed :=
  fun a b => by cases a <;> cases b <;> simp only [BSeg.Mixed] <;> infer_instance

/-- The schematic blocking language: harmony across transparent material, halted by a
blocker. -/
def blockingLang : Language BSeg :=
  (TSLGrammar.ofForbiddenPairs BSeg.Mixed BSeg.onTier).lang

theorem blockingLang_isTSL2 : Language.IsTierStrictlyLocal 2 blockingLang :=
  ⟨_, rfl⟩

/-- Transparent material does not license a mixed pair: it is deleted by the
projection, leaving the two series tier-adjacent. -/
theorem transparent_not_mem : [BSeg.ant, .transparent, .post] ∉ blockingLang := by
  unfold blockingLang; decide

/-- A blocker does license it: the blocker projects, so the two series are no longer
tier-adjacent. -/
theorem blocked_mem : [BSeg.ant, .blocker, .post] ∈ blockingLang := by
  unfold blockingLang; decide

/-- Deleting the blocker leaves an illegal word — the configuration no subsequence
grammar can distinguish. -/
theorem unblocked_not_mem : [BSeg.ant, .post] ∉ blockingLang := by
  unfold blockingLang; decide

/-- **Blocking is not strictly piecewise, at any width** ([mcmullin-2016]). SP
languages are subsequence-closed, so a legal word whose blocker-deletion is illegal
rules out every SP grammar at once. -/
theorem blockingLang_not_isStrictlyPiecewise (k : ℕ) :
    ¬ blockingLang.IsStrictlyPiecewise k :=
  fun h => unblocked_not_mem (h.mem_of_sublist (by decide) blocked_mem)

/-- **The tier buys expressive power** ([mcmullin-2016]): some TSL_2 language is
strictly piecewise at no width. With `navajoSibilantHarmony_lang_isSP2` — where the two
descriptions do coincide — this is the thesis's typological argument in miniature: SP
suffices for transparency, and only for transparency. -/
theorem exists_isTierStrictlyLocal_not_isStrictlyPiecewise :
    ∃ L : Language BSeg,
      Language.IsTierStrictlyLocal 2 L ∧ ∀ k, ¬ L.IsStrictlyPiecewise k :=
  ⟨blockingLang, blockingLang_isTSL2, blockingLang_not_isStrictlyPiecewise⟩

end McMullin2016
