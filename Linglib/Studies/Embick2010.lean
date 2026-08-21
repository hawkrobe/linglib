import Linglib.Morphology.DistributedMorphology.Locality
import Linglib.Data.Examples.Embick2010

/-!
# Localism versus globalism in morphology and phonology

[embick-2010]: contextual allomorphy holds only between concatenated nodes
that are active in the same cycle of Spell-Out — the C₁-LIN theory. The
category-defining heads are cyclic; merging one spells out the cyclic domains
in its complement, so a cyclic head and the noncyclic heads attached to it
are realized in the cycle of the next cyclic head, with the complement of the
inner one inactive (the Domain and Activity Corollaries), and nodes with null
exponents are pruned from the concatenation statements. Latin perfect
agreement takes its special endings only when a null present tense is pruned
between it and Asp[perf] (§3.1.1); a theme vowel reads the conjugation class
of the node it is concatenated with — the root's across a null v, *-ess*'s
otherwise (§3.1.2); root-attached n has root-determined allomorphs and the
gerund's n none, while *-ity* and *-ation* are potentiated by the *-able* and
*-ize* they follow (§2.2, §3.3); past tense and plural see the root across
pruned categorizers (§2.2–2.3); and Hindi Voice shows root-determined
allomorphy in the transitive but only its default in the indirect causative,
two cycles up (§3.2.2).

## Main definitions

* `Head`, `Morpheme`, `cyclic`, `phonNull`: the heads of the case studies.
* `Row`, `rows`: each conditioning relation the book attests or excludes.

## Main results

* `root_rows`, `head_rows`: attested conditioning is predicted and blocked
  conditioning excluded, by the root and by a head.
* `perfect_one_cycle`: the Latin perfects share one cycle, so only linear
  intervention separates the perfect indicative from the rest.
-/

namespace Embick2010

open DistributedMorphology Data.Examples

/-- The heads of the case studies: the categorizers, active and passive Voice,
the theme position, and the inflectional heads. -/
inductive Head where
  | n | v | a | voice | voicePassive | theme | aspect | tense | agr | number
  deriving DecidableEq, Repr

/-- A head occurrence with its exponent, empty when null. -/
structure Morpheme where
  head : Head
  exponent : String
  deriving DecidableEq, Repr

/-- The category-defining heads are the cyclic heads. -/
def cyclic (m : Morpheme) : Prop := m.head = .n ∨ m.head = .v ∨ m.head = .a

/-- A null exponent, pruned from concatenation. -/
def phonNull (m : Morpheme) : Prop := m.exponent = ""

instance : DecidablePred cyclic := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))
instance : DecidablePred phonNull := fun _ => inferInstanceAs (Decidable (_ = _))

/-! ### The case studies -/

/-- Whether the book attests the conditioning or excludes it. -/
inductive Claim where
  | attested | blocked
  deriving DecidableEq, Repr, Fintype

/-- A word, the head whose realization is at issue, what conditions it — the
root, or another head — and the book's verdict. -/
structure Row where
  form : String
  spine : Spine Morpheme
  target : Fin spine.heads.length
  conditioner : Option (Fin spine.heads.length)
  claim : Claim
  deriving Repr

def Morpheme.ofLabel (exp : String) : String → Option Morpheme
  | "n" => some ⟨.n, exp⟩
  | "v" => some ⟨.v, exp⟩
  | "a" => some ⟨.a, exp⟩
  | "voice" => some ⟨.voice, exp⟩
  | "voicePassive" => some ⟨.voicePassive, exp⟩
  | "theme" => some ⟨.theme, exp⟩
  | "aspect" => some ⟨.aspect, exp⟩
  | "tense" => some ⟨.tense, exp⟩
  | "agr" => some ⟨.agr, exp⟩
  | "number" => some ⟨.number, exp⟩
  | _ => none

/-- A position among the heads, innermost first. -/
def positionOfLabel : String → Option ℕ
  | "1" => some 0
  | "2" => some 1
  | "3" => some 2
  | "4" => some 3
  | "5" => some 4
  | _ => none

def Claim.ofLabel : String → Option Claim
  | "attested" => some .attested
  | "blocked" => some .blocked
  | _ => none

/-- The roots of the pool, indexed by first occurrence. -/
def rootNames : List String := (Examples.all.filterMap (·.feature? "root")).eraseDups

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let root ← ex.feature? "root"
  let heads := [("h1", "h1exp"), ("h2", "h2exp"), ("h3", "h3exp"), ("h4", "h4exp"),
    ("h5", "h5exp")].filterMap
    fun (k, e) => (ex.feature? k).bind (Morpheme.ofLabel ((ex.feature? e).getD ""))
  let t ← (ex.feature? "target").bind positionOfLabel
  let c ← ex.feature? "conditioner"
  let claim ← (ex.feature? "claim").bind Claim.ofLabel
  if ht : t < heads.length then
    if c = "root" then
      pure ⟨ex.primaryText, ⟨⟨rootNames.idxOf root⟩, heads⟩, ⟨t, ht⟩, none, claim⟩
    else
      let j ← positionOfLabel c
      if hj : j < heads.length then
        pure ⟨ex.primaryText, ⟨⟨rootNames.idxOf root⟩, heads⟩, ⟨t, ht⟩, some ⟨j, hj⟩, claim⟩
      else none
  else none

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

/-- The conditioning relations of §2.2–2.3, §3.1–3.3. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-! ### Predictions -/

/-- Root-determined allomorphy is attested exactly where the target sees the
root: the first cycle, across pruned heads only. -/
theorem root_rows :
    ∀ r ∈ rows, r.conditioner = none →
      (r.spine.SeesRoot cyclic phonNull r.target ↔ r.claim = .attested) := by
  decide

/-- Head-determined allomorphy is attested exactly where the target sees the
conditioning head: present at its insertion and concatenated with it. -/
theorem head_rows :
    ∀ r ∈ rows, ∀ j, r.conditioner = some j →
      (r.spine.Sees cyclic phonNull r.target j ↔ r.claim = .attested) := by
  decide

/-- The Latin perfects share one cycle: agreement is coactive with Asp[perf]
throughout, and only the overt tense of the non-indicative forms intervenes
(§3.1.1). -/
theorem perfect_one_cycle :
    ∀ r ∈ rows, r.spine.root = ⟨rootNames.idxOf "AM"⟩ → ∀ j, r.conditioner = some j →
      r.spine.Coactive cyclic r.target j ∧
        (r.spine.Sees cyclic phonNull r.target j ↔
          ∀ k, j < k → k < r.target → phonNull r.spine.heads[k]) := by
  decide

end Embick2010
