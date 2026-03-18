# Bibliography Content Audit — Findings Log

Each section corresponds to one audited paper. Findings are listed with:
- **File:line** — where the claim appears
- **Claim** — what the Lean file says
- **Reality** — what the PDF says
- **Severity** — WRONG / INACCURATE / UNVERIFIABLE
- **Resolution** — what was done (fixed, tagged UNVERIFIED, or left as-is with justification)

---

<!-- Template for new entries:

## @cite{key} — Author (Year)

**Audited**: YYYY-MM-DD
**Citation sites**: N files, M total instances
**Claims checked**: N
**Findings**: N (X WRONG, Y INACCURATE, Z UNVERIFIABLE)

### Findings

1. **File:line** `Linglib/Foo/Bar.lean:42`
   - Claim: "§3.1 defines ordering sources as..."
   - Reality: This is in §3.2, not §3.1
   - Severity: INACCURATE
   - Resolution: Fixed §3.1 → §3.2

-->
