# Poisson spectral statistics for the one-dimensional Anderson model

Lean 4 formalization of unit-intensity Poisson local eigenvalue statistics for
the one-dimensional Anderson model, including nondegenerate Bernoulli
potentials. The project uses mathlib and the actual finite Dirichlet matrix
spectrum.

The verified snapshot contains **198 Lean modules**, including the root import
module, and **1,734 public theorem or lemma declarations**. Both the local
complete check and the
[GitHub Actions verification](https://github.com/hanyi162013-Yihan/Poisson_Statistic_1dAndersonBernoulli/actions/runs/38197193741)
**passed** on the same 203 source/configuration hashes. The checks include the
complete library build, all 1,734 public proof axiom closures, the constructed
Furstenberg input, and the exact final theorem signatures. The recorded main
status is `PROVED_FOR_POTENTIAL_LAW`. Both runs produced identical result JSON,
audited declaration inventories, and axiom logs. The cloud run verified source
commit `3abb1d03dbc390f371963f70c0cb78ec8c178715`; subsequent documentation-only
updates do not change that verified Lean snapshot.

## Mathematical statements

Let the single-site potential have an almost surely bounded probability law
that is not a point mass. Fixed coupling is included in this law. The model
uses the canonical iid sample space `ℕ → ℝ` with the actual infinite product
measure. Its finite-volume operator is the real symmetric tridiagonal
Dirichlet matrix with potential values on the diagonal and hopping coefficient
one.

Write $\lambda_{1,n},\ldots,\lambda_{n,n}$ for its eigenvalues. The function
$N$ is the proved limiting expected eigenvalue count per site, and its
continuity is proved in the project.

The final results give convergence in distribution to the unit-intensity
Poisson point process on $\mathbb R$:

- **IDS normalization:**
  $\sum_{j=1}^{n}\delta_{n[N(\lambda_{j,n})-N(E)]}$ converges whenever $N$ is
  strictly increasing on a neighborhood of $E$. No derivative or single-site
  density is assumed.
- **Linear normalization:**
  $\sum_{j=1}^{n}\delta_{n\rho(\lambda_{j,n}-E)}$ converges when $N$ has a finite
  derivative $\rho>0$ at the single point $E$. No density of states on a whole
  neighborhood is assumed; this version needs no separate local strictness
  hypothesis.
- **Bernoulli specialization:** for potential values $a<b$, probabilities
  $0<p<1$, and
  $E\in\operatorname{int}([a-2,a+2]\cup[b-2,b+2])$, the IDS conclusion follows
  without an additional IDS regularity hypothesis. The required local strict
  increase is proved.

Both normalizations are stated as ordinary weak convergence of probability
laws on the space of locally finite measures with the **vague topology**, and
also on its subspace of locally finite counting measures. The vague topology
uses all continuous compactly supported real test functions. The target is a
constructed counting-measure law whose counts in every finite family of
pairwise disjoint bounded half-open intervals are independent Poisson
variables with means equal to interval lengths.

The five final declarations are in
[`SpectralPoissonUnconditional.lean`](FixedCouplingPoisson/SpectralPoissonUnconditional.lean).
Their full signatures are checked in
[`SpectralPoissonUnconditionalStatementTypes.lean`](FixedCouplingPoisson/SpectralPoissonUnconditionalStatementTypes.lean).
The laws in these declarations are the actual iid pushforwards of the finite
Dirichlet spectra, not auxiliary crossing-process laws.

## Furstenberg input and proof scope

The final declarations have **no external `Furstenberg.Input` hypothesis**.
[`FurstenbergInputProved.lean`](FixedCouplingPoisson/FurstenbergInputProved.lean)
constructs the original qualitative interface for the actual Schrödinger
SL(2, ℝ) transfer law at every energy. It supplies forward and inverse
stationary probabilities, uniqueness, atomlessness, and strictly positive
stationary log-cocycle means.

This is the SL(2) theory used by the spectral proof. The project does not claim
a full Oseledets decomposition, a general-dimensional Lyapunov spectrum, or a
separate almost sure exponent-limit identification. The final API is stated
on the canonical product sample space; a general wrapper transporting the
result to every other realization of iid potentials is not included.

The proof develops the estimates needed for the final convergence statements.
It uses uniform occupation bounds rather than all finer initial-state bounds,
uniform convergence rather than unused explicit rate formulas, and exact
constant-block spectra with cutting estimates for the Bernoulli local
strictness argument. Unused stronger auxiliary statements are not claimed as
formalized. These choices do not weaken the five final convergence statements.

## Reproduce the verification

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
python3 check.py
```

`lean-toolchain` pins Lean to `leanprover/lean4:v4.33.0`.
`lakefile.toml` and `lake-manifest.json` pin mathlib and its dependencies;
mathlib's revision is `db584cd6d46c92f209a44c0f1c829460d327499d`.
The cache command retrieves dependency build artifacts. `check.py` compiles
the project sources.

The checker builds the entire library and audits the transitive axiom
dependencies of every public theorem or lemma, plus the named
`provedFurstenbergInput` construction. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. It rejects proof placeholders, new axiom or opaque
declarations, and proof-checking limit overrides, and verifies that the source
and configuration hashes remain unchanged during checking.

`main_status_guard.py` also requires the five exact final theorem signatures
and their compiled type-guard modules. Complete verification produces
`check_result.json` with status `checked_main_formalization` and main theorem
status `PROVED_FOR_POTENTIAL_LAW`, together with `checked_theorems.json`,
`check.log`, and `axiom_audit.log`.

## Continuous verification

GitHub Actions runs the same checker on Ubuntu with the pinned Lean and
mathlib versions, then requires the complete main-theorem status and the
committed source hashes. Dependency caches are allowed; the workflow clears
the project build directory before checking. Action versions are pinned to
commits. No heartbeat, recursion-depth, or proof-checking timeout limit is
raised.

Each run preserves the available build and axiom logs, audited declaration
inventory, generated `AxiomAudit.lean`, result JSON, source hashes, and run
identity as an artifact, including when a run fails.

The repository contains the reproducible formalization sources and
verification configuration. Original manuscript files and local working
files are excluded.
