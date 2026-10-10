# An Observation Plane for the Riemann Hypothesis — paper and machine-checked companion

Anonymous version, prepared for double-blind review.

## Contents

| Path | Description |
|---|---|
| `paper/riemann_observation_EN.tex`, `paper/riemann_observation_EN.pdf` | The manuscript: LaTeX source and compiled PDF (11 pages). |
| `formal/` | The machine-checked Lean 4 companion: `Formal/ZeroRelative/` (68 modules), `build.sh`, `check_selfcontained.sh`, `check_sorry.py`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`. |
| `探针_20261010/` | The independently placed probe item cited in the paper (§9, last row of the file table): `CommonLineCheck.lean`. |
| `LICENSE` | Apache License 2.0 (applies to the Lean sources in `formal/`). |
| `MANIFEST.sha256` | SHA-256 checksums of the files above. |

The formal companion carries the paper's constructions and equivalence chain as
Lean 4 declarations. The sources import only Mathlib and in-package modules;
no axioms beyond Mathlib's are introduced.

## Verification

All checks below were run on this exact tree at packaging time. Beyond the
sources, only Lean 4.32.2 and mathlib (revision per `lake-manifest.json`) are
required.

From `formal/`:

- `bash build.sh` — layered build (main chain, isolated files, migration layer,
  symmetric tool family): 0 errors.
- `bash check_selfcontained.sh` — import whitelist check (Mathlib and
  in-package modules only): all 68 files pass.
- `python3 check_sorry.py . ../探针_20261010` — text-level
  0 `sorry` / `admit` / `axiom` check: 0 hits in 69 files.
- `lake env lean ../探针_20261010/CommonLineCheck.lean` — the probe cited in
  §9: expected exit 0.

Declaration counts in §9 of the paper count public declarations (theorems,
lemmas, defs); `private` declarations are excluded. The full tree compiles from
source (68 modules, 0 errors, 0 `sorry`).

## Notes

- No `.lake` build cache is included; the first build fetches/builds mathlib.
- The manuscript's references to a published framework are cited in the third
  person, as is standard practice for double-blind review.
