# File Database — `docs/database/`

A per-file analytic catalogue of the whole Theory-of-Systems repo, built **bottom-up** to
surface where the project is genuinely distinctive. Two deliverables:

1. **The database** (this folder): one structured record per `.v` file — number, topic,
   role, full lemma inventory, E/R/R разбор, deep analysis of the key lemmas, and an honest
   **uniqueness** verdict. Source of truth = JSON; Markdown views are generated from it.
2. **`UNIQUENESS.md`** (derived, built last): the curated «what is unique about this system»
   document for external readers — assembled *from the database's `uniqueness` fields*, not
   written from the top down.

## Layout

```
docs/database/
  README.md          — this file (schema + rubric + workflow)
  _files.tsv         — master list: global file number ↔ path (stable, alpha by path)
  <cluster>.json     — one shard per top-level dir (cs.json, foundation.json, …) = SOURCE OF TRUTH
  <cluster>.md       — generated human-readable view of each shard
  INDEX.md           — generated master table (all files, sorted by number)
  generate.ps1       — JSON shards → <cluster>.md + INDEX.md
  UNIQUENESS.md      — (deliverable 2) curated, built last from the uniqueness fields
```

Regenerate the Markdown after editing any shard:
```powershell
pwsh docs/database/generate.ps1     # or: powershell -File docs\database\generate.ps1
```

## Record schema (one object per file, inside the cluster's JSON array)

| field | type | meaning |
|-------|------|---------|
| `num` | int | global file number (from `_files.tsv`, stable, alpha-by-path) |
| `path` | string | repo-relative path, forward slashes |
| `cluster` | string | shard key (top-level dir, e.g. `cs`, `foundation`, `process`) |
| `title` | string | ≤ ~80-char headline of what the file delivers |
| `topic` | string | 1–2 sentences: what it is about |
| `role` | string | role in the architecture — what it depends on, who reuses it |
| `qed` / `admitted` / `axioms` | int | counts (qed = actual `Qed.` count; **flag drift vs header in `notes`**) |
| `imports` | string[] | key imports (Stdlib / cs / ToS modules) |
| `err` | object | E/R/R разбор: `{elements, roles, rules, p4}` (P4 = the finite-actuality diagnostic) |
| `lemmas` | object[] | **full inventory**: `{name, kind, role}` for every named declaration (one line each) |
| `key_lemmas` | object[] | 2–5 deep dives: `{name, analysis, tags}` — where the uniqueness lives |
| `classical_counterpart` | string | named classical result(s) the file / its key lemmas mirror, and precisely WHAT differs here (honesty anchor + Task-2 raw material) |
| `uniqueness` | object | `{score, level, claim, caveat}` (see rubric) |
| `tags` | string[] | cross-cutting tags (e.g. `diagonal`, `no-AC`, `P4`, `lawvere`) |
| `notes` | string? | optional: header/actual drift, deps on a concurrent workstream, gaps |

### `uniqueness` rubric — judged on the **project's own honest scale**

Scale (descending): `new-theorem > synthesis+observation > new-framing > methods > exposition`.
This mirrors `memory/project-uniqueness-map.md`. **No overclaim**: `caveat` MUST state what is
classical / already known. A file is allowed to be plumbing — that is information, not a demerit.

| `score` | `level` | meaning |
|--------:|---------|---------|
| 5 | `new-theorem` / flagship | genuine new result, or a reused **root/flagship** of a unique vein |
| 4 | `synthesis+observation` | novel *unification* of known pieces; load-bearing foundation/bridge |
| 3 | `new-framing` | known result re-cast in the E/R/R / Element–role-limit ontology; useful grounding |
| 2 | `methods` | unusual *formalization* of standard content |
| 1 | `exposition` | standard content, cleanly exposed; examples |
| 0 | `infrastructure` | build/plumbing/deprecated/helpers only |

`level` enum: `new-theorem | synthesis+observation | new-framing | methods | exposition | infrastructure`.

## Granularity (chosen 2026-06-07)

**File-level rich record + flagged key lemmas.** Every lemma is *listed* (`lemmas[]`, complete
index) with a one-line role; only the 2–5 lemmas where distinctiveness actually lives get a
deep `analysis` (`key_lemmas[]`). Rationale: uniqueness lives at the file/theorem level, not in
the ~23 000 routine arithmetic/monotonicity helpers — this maximises signal per token while the
index stays complete.

## Status

Built incrementally, cluster by cluster. **546 files / 7,417 Qed catalogued so far** across
23 shards (see `INDEX.md` and `_uniqueness_ranked.md`).

Done: `cs`, `algebra`, `settheory`, `geometry`, `numbertheory`, `category`, `analysis`, `src`
(root), `lattice`, `zeta`, `physics`, `navier_stokes`, `experimental`, `projective`, `light`,
`linalg`, `fermions`, `process_qm`, `Architecture_of_Reasoning`, `smalldirs` (14 tiny dirs),
`foundation` (F-1..F-3, files #161–310 of 266), and `log2` (5 files #1830–1834: the
log2-as-process pair + the Mertens→exp_R→injectivity tower; see HIGHLIGHTS H58).

In progress / pending: `foundation` F-4..F-5 (#311–425), then the giants `process` (340),
`gauge` (114), `stdlib` (709+); final reconcile of `_files.tsv` numbering. See
`memory/file-database.md` for the running progress log. **`UNIQUENESS.md`** (deliverable 2) is
built LAST from the `uniqueness` fields once cataloguing is complete.
