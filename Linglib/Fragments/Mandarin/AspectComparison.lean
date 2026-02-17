import Linglib.Core.AtomicDistributivity

/-!
# Mandarin Cross-Domain Particles (Zhao 2026, Ch. 6) @cite{zhao-2026}

Lexical entries for Mandarin le, guo, and mei-you with cross-domain behavior.
These particles operate across temporal and degree domains:

| Particle   | Temporal gloss     | Degree gloss       | Licensing          |
|------------|--------------------|--------------------|---------------------|
| 了 le      | perfective         | exceed-threshold   | NOT-ATOM-DIST_α    |
| 没有 mei-you | neg-perfective   | not-exceed         | NOT-ATOM-DIST_α    |
| 过 guo     | experiential       | —                  | (none)             |

le and mei-you presuppose NOT-ATOM-DIST_α, explaining their incompatibility
with statives (temporal domain) and bare comparatives (degree domain).
guo has no such presupposition.

## Cross-Module Connections

- `Core.AtomicDistributivity`: ATOM-DIST and antiAtomDistLicensed
- `Fragments.Mandarin.Particles`: existing Mandarin particle pattern

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation, Ch. 6.
-/

namespace Fragments.Mandarin.AspectComparison

open Core.AtomicDistributivity
open Core.Time

-- ════════════════════════════════════════════════════
-- § 1. Cross-Domain Particle Entries
-- ════════════════════════════════════════════════════

/-- Semantic domain for cross-domain particles. -/
inductive SemanticDomain where
  | temporal   -- temporal domain (aspect)
  | degree     -- degree domain (comparison)
  deriving DecidableEq, Repr, BEq

/-- A cross-domain particle entry (Zhao 2026, Ch. 6).
    Encodes the particle's surface form, its temporal and degree glosses,
    and whether it requires NOT-ATOM-DIST_α licensing. -/
structure CrossDomainParticle where
  /-- Chinese character(s) -/
  hanzi : String
  /-- Pinyin romanization -/
  pinyin : String
  /-- Gloss in temporal domain -/
  temporalGloss : String
  /-- Gloss in degree domain (if applicable) -/
  degreeGloss : Option String
  /-- Whether the particle presupposes NOT-ATOM-DIST_α -/
  requiresAntiAtomDist : Bool
  deriving Repr

/-- 了 le — perfective / exceed-threshold.
    Presupposes NOT-ATOM-DIST_α in both domains (Zhao 2026, Ch. 6). -/
def le : CrossDomainParticle :=
  { hanzi := "了", pinyin := "le"
  , temporalGloss := "perfective"
  , degreeGloss := some "exceed-threshold"
  , requiresAntiAtomDist := true }

/-- 没有 mei-you — negative perfective / not-exceed.
    Presupposes NOT-ATOM-DIST_α (Zhao 2026, Ch. 6). -/
def meiyou : CrossDomainParticle :=
  { hanzi := "没有", pinyin := "méi-yǒu"
  , temporalGloss := "negative perfective"
  , degreeGloss := some "not-exceed"
  , requiresAntiAtomDist := true }

/-- 过 guo — experiential aspect.
    No NOT-ATOM-DIST_α presupposition (Zhao 2026, Ch. 6). -/
def guo : CrossDomainParticle :=
  { hanzi := "过", pinyin := "guò"
  , temporalGloss := "experiential"
  , degreeGloss := none
  , requiresAntiAtomDist := false }

-- ════════════════════════════════════════════════════
-- § 2. Licensing Predicate
-- ════════════════════════════════════════════════════

/-- Is a particle licensed by an event quantifier V (w.r.t. trace τ)?
    Licensed iff either (a) the particle doesn't require anti-ATOM-DIST, or
    (b) V fails ATOM-DIST_α. -/
def isLicensed {Event α : Type*} [LinearOrder α]
    (p : CrossDomainParticle) (τ : Event → Interval α) (V : EvQuant Event) : Prop :=
  p.requiresAntiAtomDist = false ∨ antiAtomDistLicensed τ V

-- ════════════════════════════════════════════════════
-- § 3. Per-Datum Verification Theorems
-- ════════════════════════════════════════════════════

/-- le requires NOT-ATOM-DIST_α. -/
theorem le_requires_antiAtomDist : le.requiresAntiAtomDist = true := rfl

/-- mei-you requires NOT-ATOM-DIST_α. -/
theorem meiyou_requires_antiAtomDist : meiyou.requiresAntiAtomDist = true := rfl

/-- guo does NOT require NOT-ATOM-DIST_α. -/
theorem guo_no_antiAtomDist : guo.requiresAntiAtomDist = false := rfl

/-- le is licensed iff NOT-ATOM-DIST_α holds. -/
theorem le_licensed_iff {Event α : Type*} [LinearOrder α]
    (τ : Event → Interval α) (V : EvQuant Event) :
    isLicensed le τ V ↔ antiAtomDistLicensed τ V := by
  simp [isLicensed, le]

/-- mei-you is licensed iff NOT-ATOM-DIST_α holds. -/
theorem meiyou_licensed_iff {Event α : Type*} [LinearOrder α]
    (τ : Event → Interval α) (V : EvQuant Event) :
    isLicensed meiyou τ V ↔ antiAtomDistLicensed τ V := by
  simp [isLicensed, meiyou]

/-- guo is always licensed (no anti-ATOM-DIST requirement). -/
theorem guo_always_licensed {Event α : Type*} [LinearOrder α]
    (τ : Event → Interval α) (V : EvQuant Event) :
    isLicensed guo τ V := by
  left; rfl

end Fragments.Mandarin.AspectComparison
