/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Equiv.Defs
import Linglib.Features.Basic

/-!
# Tonal root nodes and subtonal features

Tone is paradigmatic: a **tonal root node** (TRN) bundles the two subtonal features
`[±upper]` (which register half) and `[±raised]` (which target within it) of [yip-1980] and
[pulleyblank-1986], each possibly unspecified, and links to a tone-bearing unit. Following
[lionnet-2022], the features are paradigmatic targets, not [snider-1999]'s syntagmatic
shifts; the terracing reading of `[raised]` is `Tone.Register`.

## Main definitions

* `Subtonal`, `TRN` — the two feature dimensions and the root node; `TRN.bundleEquiv`
  identifies a root node with its feature bundle `Subtonal → Option Bool`
  (`Features.Bundle`).
* `TRN.H`, `TRN.M`, `TRN.L`, `TRN.superHigh` — the four full specifications;
  `TRN.empty`, `TRN.downstep`, `TRN.upstep` — the register-only nodes.
* `TRN.assimilate`, `TRN.merge`, `TRN.dock` — the feature operations, through the bundle.
* `TBUKind`, `WordProsody`, `IsRegisterOnly` — the tone-bearing unit, [hyman-2006]'s two
  word-prosodic dimensions, and [lionnet-2025]'s register-only inventories.
-/

namespace Tone

/-- The two subtonal feature dimensions ([lionnet-2022] ex. 51, after [yip-1980],
[pulleyblank-1986]): `upper`, which register half; `raised`, which target within it. A
value is `some true` (`+`), `some false` (`-`), or `none` (unspecified). -/
inductive Subtonal where
  | upper
  | raised
  deriving DecidableEq, Repr, Inhabited

/-- A **tonal root node**: a `[±upper]` and a `[±raised]` value, each possibly unspecified.
A structure rather than the bundle `Subtonal → Option Bool`, so that `DecidableEq` derives
and literals reduce; `TRN.bundleEquiv` is the bundle view. -/
structure TRN where
  upper : Option Bool
  raised : Option Bool
  deriving DecidableEq, Repr, Inhabited

namespace TRN

/-- The fully unspecified node: the registerless mora of Drubea and Numèè
([lionnet-2025]). -/
@[match_pattern] def empty : TRN := ⟨none, none⟩

/-- A floating `[-raised]`: the downstep node of a register-only system. -/
@[match_pattern] def downstep : TRN := ⟨none, some false⟩

/-- A floating `[+raised]`: the upstep node. -/
@[match_pattern] def upstep : TRN := ⟨none, some true⟩

/-- High, `[+upper, -raised]` ([lionnet-2022] ex. 51). -/
@[match_pattern] def H : TRN := ⟨some true, some false⟩

/-- Mid, `[-upper, +raised]` ([lionnet-2022] ex. 51). -/
@[match_pattern] def M : TRN := ⟨some false, some true⟩

/-- Low, `[-upper, -raised]` ([lionnet-2022] ex. 51). -/
@[match_pattern] def L : TRN := ⟨some false, some false⟩

/-- The fourth specification `[+upper, +raised]`: the gap of Laal's three-tone system
([lionnet-2022] ex. 51). -/
@[match_pattern] def superHigh : TRN := ⟨some true, some true⟩

/-- The feature bundle of a node. -/
def toBundle (t : TRN) : Subtonal → Option Bool
  | .upper => t.upper
  | .raised => t.raised

/-- The node of a feature bundle. -/
def ofBundle (b : Subtonal → Option Bool) : TRN := ⟨b .upper, b .raised⟩

@[simp] theorem toBundle_upper (t : TRN) : t.toBundle .upper = t.upper := rfl

@[simp] theorem toBundle_raised (t : TRN) : t.toBundle .raised = t.raised := rfl

@[simp] theorem ofBundle_toBundle (t : TRN) : ofBundle t.toBundle = t := rfl

@[simp] theorem toBundle_ofBundle (b : Subtonal → Option Bool) : (ofBundle b).toBundle = b := by
  funext f; cases f <;> rfl

/-- A root node is its feature bundle. -/
def bundleEquiv : TRN ≃ (Subtonal → Option Bool) where
  toFun := toBundle
  invFun := ofBundle
  left_inv := ofBundle_toBundle
  right_inv := toBundle_ofBundle

/-- **Subtonal assimilation** at `f`: the target takes its value at `f` from the source,
its other feature untouched. Laal M-lowering ([lionnet-2022] §5.2) is `assimilate .raised`:
a `[-raised]` value spreads onto M, `[-upper, +raised]`, giving L. -/
def assimilate (f : Subtonal) (src tgt : TRN) : TRN :=
  ofBundle (Features.Bundle.assimilate f src.toBundle tgt.toBundle)

/-- **Merger** of two nodes ([lionnet-2022] ex. 53–54): each feature from the left node
where it is specified, else from the right (`Features.Bundle.merge`) — the fusion of two
associated tones ([goldsmith-1976]); the tier-level merger of a run of identical tones is
`OCP.collapse`. -/
def merge (t₁ t₂ : TRN) : TRN := ofBundle (Features.Bundle.merge t₁.toBundle t₂.toBundle)

@[simp] theorem merge_self (t : TRN) : merge t t = t := by
  simp only [merge, Features.Bundle.merge_self, ofBundle_toBundle]

/-- **Docking** of a floating feature ([lionnet-2022] §5.3): a free `[±f]` lands on a node,
overwriting its value at `f`. -/
def dock (f : Subtonal) (v : Bool) (t : TRN) : TRN :=
  ofBundle (Features.Bundle.set f v t.toBundle)

end TRN

/-! ### Tone-bearing units and word-prosodic types -/

/-- The prosodic unit that carries a node: the syllable in most tone languages, the mora in
Drubea and Numèè ([lionnet-2025]). -/
inductive TBUKind where
  | mora
  | syllable
  deriving DecidableEq, Repr

/-- A language's word prosody: [hyman-2006]'s two independent dimensions — whether pitch
enters the lexical realization of morphemes (his definition (3) of tone) and whether words
carry an obligatory metrical head (his definition (5) of stress accent). -/
structure WordProsody where
  tone : Bool
  stressAccent : Bool
  deriving DecidableEq, Repr

/-- A **register-only** inventory ([lionnet-2025]): no node specifies `[upper]`, so only the
syntagmatic `[raised]` is contrastive. Lionnet's split of [hyman-2006]'s tone prototype —
register-based systems (Drubea, Numèè) against tone-based ones with paradigmatic `[upper]`
contrasts (Yoruba, Mandarin) and mixed ones (Paicî, Baga Pukur) — is read off the lexical
inventory rather than recorded. -/
def IsRegisterOnly (ts : List TRN) : Prop := ∀ t ∈ ts, t.upper = none

instance (ts : List TRN) : Decidable (IsRegisterOnly ts) := List.decidableBAll _ _

end Tone
