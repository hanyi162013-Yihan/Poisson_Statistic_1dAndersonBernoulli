# Poisson statistics for the one-dimensional Anderson model

Lean 4 formalization of Poisson spectral statistics for the one-dimensional
Anderson model, including Bernoulli potentials. The project uses mathlib.

The initial snapshot contains 198 Lean modules, including the root import
module, and 1,734 public theorem or lemma declarations. A successful full
verification must be established by the check below; source availability or
individual module checks alone do not establish that result.

## Reproduce the verification

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
python3 check.py
```

The `lean-toolchain` file pins Lean to `leanprover/lean4:v4.33.0`.
`lakefile.toml` and `lake-manifest.json` pin mathlib and its dependencies;
mathlib's revision is `db584cd6d46c92f209a44c0f1c829460d327499d`.
The cache command retrieves dependency build artifacts. The project sources
are still compiled by `check.py`.

`check.py` builds the whole library, checks every public theorem's transitive
axiom dependencies, and separately audits the constructed Furstenberg input.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. It rejects
proof placeholders, new axiom or opaque declarations, and proof-checking
limit overrides. It also checks that the sources remain unchanged during
verification.

`main_status_guard.py` requires the exact final theorem signatures and their
compiled type-checking modules before reporting the main result. The expected
complete status is `PROVED_FOR_POTENTIAL_LAW`.

## Main statements

- `FixedCouplingPoisson/SpectralPoissonUnconditional.lean` contains the final
  IDS-normalized and linearly normalized Poisson convergence statements.
- `FixedCouplingPoisson/SpectralPoissonUnconditionalStatementTypes.lean`
  checks their exact signatures.
- `FixedCouplingPoisson/FurstenbergInputProved.lean` constructs the qualitative
  SL(2) input from the proved stationary-measure results.

The final statements do not require an external Furstenberg input. Their
mathematical conditions remain explicit: local strict increase of the IDS
for IDS normalization, or a positive IDS derivative for linear normalization.
The Bernoulli IDS statement assumes a nondegenerate Bernoulli law and an energy
in the interior of the specified spectral bands.

## Continuous verification

GitHub Actions runs `python3 check.py` on Ubuntu, with the same pinned Lean and
mathlib versions, then requires the complete main-result status. The workflow
does not restore a project build cache. Action versions are pinned to commits.
No heartbeat, recursion-depth, or proof-checking timeout limit is raised.

Each run uploads an artifact containing the build and axiom logs, audited
declaration inventory, generated `AxiomAudit.lean`, result JSON, committed
source hashes, and run identity. Failed runs preserve the available logs too.

The repository contains the reproducible formalization sources and verification
configuration. Original manuscript files and local working files are excluded.
