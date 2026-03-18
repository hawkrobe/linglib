# Bibliography Content Audit — Session Prompt

Paste this at the start of a Claude Code session to run an audit pass.

---

## Prompt

```
We're doing a content audit of linglib's bibliography. The goal is to verify that claims made about cited papers in our Lean files actually match what the papers say. This catches hallucinated equation numbers, fabricated parameter values, misattributed claims, wrong example sentences, incorrect data, and inaccurate section references.

## How it works

The audit unit is the **paper** (identified by its @cite{key}). For each paper:

1. **Gather claims**: grep for all @cite{key} instances across Linglib/, extract ~10 lines of surrounding context for each, and categorize the claims being made:
   - LOCATION: section/equation/table/figure/theorem/definition numbers (§3.1, eq. (39), Table 1)
   - PARAMETER: specific numeric values attributed to the paper (α = 3, r² = 0.99, P(w) = 1/4)
   - DATA: reproduced data tables, experimental results, corpus counts
   - EXAMPLE: linguistic example sentences with judgments (*Who did you wonder whether left)
   - ATTRIBUTION: theoretical claims attributed to the paper ("X argues that...", "X defines Y as...")
   - QUOTATION: direct or near-direct quotes

2. **Check against PDF**: use the Zotero MCP tools to fetch the paper's full text or PDF annotations, or ask me to provide the PDF. Compare each claim against what the paper actually says.

3. **Log findings** in `blog/data/audit_log.md` under a section for that paper:
   - For each discrepancy: the file:line, what the Lean file says, what the paper says, and severity (WRONG / INACCURATE / UNVERIFIABLE)
   - WRONG = factually incorrect (wrong number, wrong claim)
   - INACCURATE = close but imprecise (right section but wrong subsection, paraphrased claim that shifts meaning)
   - UNVERIFIABLE = can't confirm from the PDF (e.g., page numbers for an unpaginated preprint)

4. **Fix in-place**: correct WRONG findings directly in the Lean files. For INACCURATE, fix if straightforward, otherwise add `-- UNVERIFIED:` tag. For UNVERIFIABLE, add `-- UNVERIFIED:` tag.

5. **Update the tracker**: after auditing a paper, add/update its entry in `blog/data/audit_tracker.md`.

## Picking papers to audit

Check `blog/data/audit_tracker.md` for what's already been audited. Then pick the next paper using this priority order:

1. Papers I (the user) specifically request
2. Papers with the most LOCATION-type claims (§, eq., Table, Figure references) — these are the highest hallucination risk
3. Papers with `role = formalized` in references.bib and a study file — load-bearing claims
4. Papers with many citation sites (high blast radius if wrong)
5. Papers from 2024+ (past typical training data, higher hallucination risk)

## Session structure

- Audit 1-3 papers per session depending on complexity
- Start by showing me which paper you're picking and why
- Show me the extracted claims before checking (so I can flag any I know are suspicious)
- After checking, show me a summary of findings before making fixes
- Commit fixes at the end with a message like: "Audit: fix N hallucinations in @cite{key} across M files"

## Important rules

- NEVER guess what the paper says. If you can't access the PDF, say so and we'll figure it out.
- When you find a wrong location reference (§, eq., Table), replace it with a content description unless you can verify the correct number from the PDF. "the ordering source semantics" is safer than "§3.2" if you're not sure about §3.2.
- Don't silently fix things — always show me what changed and why.
- If a paper has 50+ citation sites, focus on the ones with specific claims (LOCATION, PARAMETER, DATA) rather than generic attributions.
```

---

## Supporting files

The prompt references two files that will be created on first use:

- `blog/data/audit_tracker.md` — tracks which papers have been audited, with date and findings count
- `blog/data/audit_log.md` — detailed per-paper findings log
