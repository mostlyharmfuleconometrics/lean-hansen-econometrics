# lean-hansen-econometrics

A Lean 4 formalization of the mathematical results in Bruce E. Hansen's
*Econometrics*.

The project develops reusable probability, linear algebra, asymptotic, and
distribution theory while it formalizes the book chapter by chapter. It does
not translate the text line by line. The goal is a checked mathematical API
with an explicit crosswalk to the source.

## Current scope

- All 29 chapters have extracted text and a canonical inventory.
- Chapters 2--13 have Lean modules imported by the root library.
- Chapter 1 and Chapters 14--29 are inventory-only.
- No chapter is marked complete in the broad sense of covering every section,
  derivation, example, and exercise.

The source PDF, `HansenEconometrics.pdf`, is in the surrounding Hansen project.
Each `inventory/chN-inventory.md` file is the source of truth for theorem-level
coverage, assumptions, corrections, and open gaps.

## Coverage labels

- `inventory only`: the chapter text and crosswalk exist, but there is no
  chapter Lean module.
- `partial`: the chapter has compiled Lean results, but some source material or
  exact textbook endpoints remain open, conditional, corrected, or out of
  scope.

## Chapter coverage

| ch | title | status | current Lean surface |
|---:|---|---|---|
| [01](inventory/ch1-inventory.md) | Introduction | inventory only | Primarily expository material. |
| [02](inventory/ch2-inventory.md) | Conditional Expectation and Projection | partial | Conditional expectation, CEF errors, conditional variance, best prediction, linear projection, and potential-outcome/CIA bridges. |
| [03](inventory/ch3-inventory.md) | The Algebra of Least Squares | partial | OLS minimization and normal equations, projection and annihilator algebra, leverage, leave-one-out and influence formulas, and FWL results. |
| [04](inventory/ch4-inventory.md) | Least Squares Regression | partial | OLS and GLS algebra, unbiasedness and covariance, Gauss--Markov comparisons, residual variance, HC0--HC3, and clustered covariance. |
| [05](inventory/ch5-inventory.md) | Normal Regression | partial | Multivariate-normal support, exact Gaussian, chi-square, Student-t, and F laws, confidence intervals, and classical tests. |
| [06](inventory/ch6-inventory.md) | A Review of Large Sample Asymptotics | partial | WLLN and CLT interfaces, continuous mapping, Slutsky, stochastic order, Delta methods, moment transfer, and uniform-integrability bounds. |
| [07](inventory/ch7-inventory.md) | Asymptotic Theory for Least Squares | partial | OLS consistency and normality, feasible covariance estimators, functions of parameters, standard errors, confidence intervals, Wald inference, residual uniformity, and leverage rates. |
| [08](inventory/ch8-inventory.md) | Restricted Estimation | partial | Exact restricted-estimation results through Theorem 8.5 and minimum-distance, constrained-estimator, efficiency, misspecification, and nonlinear-restriction interfaces. |
| [09](inventory/ch9-inventory.md) | Hypothesis Testing | partial | Theorems 9.1--9.11 have theorem-facing endpoints for t, Wald, criterion, F, Hausman, consistency, and local-power results. |
| [10](inventory/ch10-inventory.md) | Resampling Methods | partial | Bootstrap WLLN and CLT, mapping and Delta methods, variance and quantiles, percentile and percentile-t intervals, tests, finite replication, higher-order interfaces, and regression bootstrap results through Theorem 10.20. |
| [11](inventory/ch11-inventory.md) | Multivariate Regression | partial | System regression, SUR, reduced-rank regression, PCA, factor models, matrix-normal, Wishart, inverse-Wishart, and Hotelling results for Theorems 11.1--11.12. |
| [12](inventory/ch12-inventory.md) | Instrumental Variables | partial | IV and 2SLS algebra and asymptotics, nonlinear functions and tests, bootstrap, generated regressors, control functions, overidentification, LIML, weak instruments, and many-instrument limits for Theorems 12.1--12.19. |
| [13](inventory/ch13-inventory.md) | Generalized Method of Moments | partial | All 17 numbered theorems and Proposition 13.1 have compiled endpoints covering linear and nonlinear GMM, efficiency, inference, constraints, and specification tests. |
| [14](inventory/ch14-inventory.md) | Time Series | inventory only | Extracted and crosswalked. |
| [15](inventory/ch15-inventory.md) | Multivariate Time Series | inventory only | Extracted and crosswalked. |
| [16](inventory/ch16-inventory.md) | Non-Stationary Time Series | inventory only | Extracted and crosswalked. |
| [17](inventory/ch17-inventory.md) | Panel Data | partial | For general (possibly unbalanced) panels: the individual dummy design and within transformation, both clauses of equation (17.19), and both clauses of Theorem 17.1 (fixed effects equals dummy variable estimator). |
| [18](inventory/ch18-inventory.md) | Difference in Differences | inventory only | Extracted and crosswalked. |
| [19](inventory/ch19-inventory.md) | Nonparametric Regression | inventory only | Extracted and crosswalked. |
| [20](inventory/ch20-inventory.md) | Series Regression | inventory only | Extracted and crosswalked. |
| [21](inventory/ch21-inventory.md) | Regression Discontinuity | inventory only | Extracted and crosswalked. |
| [22](inventory/ch22-inventory.md) | M-Estimators | inventory only | Extracted and crosswalked. |
| [23](inventory/ch23-inventory.md) | Nonlinear Least Squares | inventory only | Extracted and crosswalked. |
| [24](inventory/ch24-inventory.md) | Quantile Regression | inventory only | Extracted and crosswalked. |
| [25](inventory/ch25-inventory.md) | Binary Choice | inventory only | Extracted and crosswalked. |
| [26](inventory/ch26-inventory.md) | Multiple Choice | inventory only | Extracted and crosswalked. |
| [27](inventory/ch27-inventory.md) | Censoring and Selection | inventory only | Extracted and crosswalked. |
| [28](inventory/ch28-inventory.md) | Model Selection, Stein Shrinkage, and Model Averaging | inventory only | Extracted and crosswalked. |
| [29](inventory/ch29-inventory.md) | Machine Learning | inventory only | Extracted and crosswalked. |

## Important coverage qualifications

The inventories record all known differences between the printed statements
and the formal results. Important examples are:

- The exact random-design moment threshold in Theorem 5.5 remains deferred.
- Chapter 6 still has textbook-shaped convergence gaps, and the concrete
  high-moment Edgeworth expansion in Theorem 7.15 remains open.
- Some Chapter 8--10 asymptotic results are reusable interfaces whose
  model-specific premises must be supplied by a later theorem.
- The printed target in Theorem 11.6 is false in general. The repository proves
  consistency for the correct feasible-SUR covariance target and formalizes why
  the printed target would force an invalid OLS/SUR equality.
- Theorem 12.7 is false as printed. Theorems 12.17 and 12.19 also need corrected
  assumptions or domains. The Chapter 12 inventory separates literal,
  corrected, and diagnostic endpoints.
- Theorem 13.5 proves the valid weak covariance ordering; its printed strict
  claim needs a weight normalization. The nonlinear form of Theorem 13.12 needs
  a constrained-optimizer linearization. Theorems 13.16 and 13.17 need explicit
  maintained-relevance assumptions.

## Formalization architecture

The library uses a layered design:

1. `LinearAlgebraUtils`, `ProbabilityUtils`, and `AsymptoticUtils` provide
   reusable infrastructure.
2. Early chapter modules provide OLS, projection, distribution, and asymptotic
   results used by later chapters.
3. Larger chapters use umbrella modules with focused submodules. Chapters
   10--13 follow this pattern.
4. Canonical chapter-facing theorems wrap reusable proof engines and expose
   Hansen's notation when it is mathematically sound.

Finite-sample estimators use a consistent totalization policy. Base definitions
use invertibility assumptions. `Star` definitions use `Matrix.nonsingInv` as a
proof engine. Textbook-facing `OrZero` definitions make singular-design behavior
explicit. See [`AGENTS.md`](AGENTS.md) for the full API and proof policy.

## Repository structure

- `HansenEconometrics/`: Lean source modules.
- `HansenEconometrics.lean`: root library import; `lake build` checks this
  complete surface.
- `inventory/`: canonical chapter status notes and LaTeX/Lean crosswalks.
- `textbook/`: extracted chapter text and redirects to the canonical
  inventories.
- `review/`: adversarial review harness, prompt templates, schema, and reports.
- `site/`: Quarto sources for the documentation site.
- `docs/`: rendered site committed for GitHub Pages.
- `scripts/`: extraction, declaration export, site generation, and review tools.
- `tests/`: tests for the review and documentation tooling.
- `AGENTS.md`: contributor rules for theorem design, imports, documentation, and
  review gates.

## Build and validation

The project uses Lean `v4.29.0` and Mathlib `v4.29.0`, as specified by
`lean-toolchain` and `lakefile.toml`.

Run the local CI-equivalent check from the repository root:

```sh
lake build
lake build @mathlib/lint-style
lake env .lake/packages/mathlib/.lake/build/bin/lint-style HansenEconometrics
```

If [`just`](https://github.com/casey/just) is installed, `just ci` runs the same
three commands.

The main GitHub Actions workflow runs the same build and text-style checks for
pull requests and pushes to `main` or `master`. Lean's standard elaboration
linters are enabled in `lakefile.toml`. Existing warnings mean that the project
does not yet use `lake build --wfail` as a required gate.

Run the tooling tests with:

```sh
uv run --no-project --with markdown python -m unittest discover -s tests -p 'test_*.py'
```

## Review harness

The repository includes a four-part review harness for redundancy, hygiene,
textbook faithfulness, and proof quality. It resolves each Lean file to its
chapter excerpt and inventory, validates findings against a JSON schema, and
stores reports in `review/reports/`.

See [`review/README.md`](review/README.md) for the Codex, Claude Code, and manual
workflows.

## Documentation site

The Quarto site contains a packaged Lean crash course, a generated
statement-dependency graph, foldable important-result pages for Chapters
2--13, and hand-written proof deep dives for selected results in Chapters 3,
5, and 7. Each deep dive links to its canonical generated result card. The
generated result pages use the canonical inventory crosswalks and metadata
from the compiled Lean environment.

With Quarto and `just` installed, refresh and render the complete site to
`docs/`:

```sh
just site-render
```

Use `just site-preview` for local preview or `just site-render-fast` to reuse an
existing declaration export. [`site/README.md`](site/README.md) documents the
generation, test, crash-course refresh, and publishing workflow.

## Working method

For each chapter:

1. extract the source text;
2. record theorem candidates in the canonical inventory;
3. identify reusable dependencies;
4. prove the lowest-level results first;
5. add chapter-facing wrappers;
6. update the inventory and run the build and review gates.

The project prefers Mathlib reuse, narrow imports, private same-file proof
scaffolding, stable public theorem names, and explicit documentation of any
assumption that differs from the textbook.

## Philosophy

The objective is a usable formal skeleton of the mathematics in Hansen's book.
The library favors reusable results and mathematically correct statements over
a line-by-line encoding of the prose. It also records when a printed theorem is
false, incomplete, or needs a more precise assumption.
