# riemann

This repository contains two layers:

1. **The Lean formalization of the Riemann Hypothesis / GRH proof**
   announced by Levent Alpöge (Anthropic) on 2026-11-20 at `alpo.ge/remark.pdf`
   — 175,187 Lean files, 17,374,215 lines, 817,038 theorems, unmodified.
2. **`extended-research/`** — independent follow-up work building on that
   proof: machine-checked foundations toward the *Extended* Riemann
   Hypothesis (Hecke/Artin L-functions).

Everything in `extended-research/` is verified **on GitHub Actions only**
(no local builds), by the manual pipeline `.github/workflows/lean-manual.yml`.

---

## Status of the base proof (upstream, not this repo's work)

The Lean proof of RH and GRH for Dirichlet L-functions was independently
verified on 2026-11-21 by Andrew Sutherland (MIT)
(<https://math.mit.edu/~drew/grh>):

- all 175,187 modules compile (Lean v4.33.1, zero errors);
- `#print axioms` for the five headline theorems: `propext`,
  `Classical.choice`, `Quot.sound` only;
- Lean-kernel replay of every module (leanchecker: 175,187/175,187);
- two independently written kernels (`nanoda`, Rust; `con-leche`) accept the
  full exported proof, as does `lean4lean`;
- Mathlib oleans byte-identical to the official cache.

The final theorem is Mathlib's own statement:
`theorem riemannHypothesis : RiemannHypothesis := rhOfAll` in `src/Main.lean`.

## What was achieved and proven on CI (this repo's extended research)

All items below are in `extended-research/HorizonERH.lean`, elaborated by the
GitHub Actions pipeline against the **same toolchain and Mathlib revision as
the base proof** (Lean `v4.33.1`, mathlib `0df444a360ea`). Every one of them
has been printed by `#print axioms` in public CI logs with axiom footprint
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

### 1. A generic mirror adapter for any L-function

- **`mirror_lemma`** — zero-free right of the critical line + a completed
  functional equation (nonzero root number, zero-free gamma factor) ⟹ every
  critical-strip zero lies exactly on `Re = 1/2`. Works for *any* L-function
  (Dirichlet, Hecke, Artin, automorphic). This is the role of
  `Formalism.VW.critLine` in the base proof, isolated and generalized.

### 2. The ERH interface for Dedekind zeta functions

- **`DedekindZetaDatum K`** — packages the analytic continuation of `ζ_K`,
  its completion, gamma factor and functional equation as data (Mathlib
  defines `NumberField.dedekindZeta` only where the L-series converges).
- **`DedekindERH`** — the target statement of the ERH extension.
- **`dedekindZetaCriticalLine`** — the adapter instantiated for `ζ_K`.

### 3. The abelian rung, plugged into the *proven* Dirichlet GRH

- **`nonvanishing_right_of_product` / `abelianDedekindERH`** (pole-aware at
  `s = 1`) — a factorization of `ζ_K` into Dirichlet L-functions
  (Kronecker–Weber) turns nonvanishing of the factors into nonvanishing of
  `ζ_K` right of the critical line.
- **`DirichletGRH`** — the *exact* shape of the base project's proven theorem
  (`Main.lean`: `LFunction_ne_zero_of_half_lt_re := allChi`).
- **`nonvanishing_of_dirichlet_factorization`** — Kronecker–Weber
  factorization + proven Dirichlet GRH ⟹ `ζ_K` nonzero for `Re s > 1/2`.
  *What remains for the abelian case is only the factorization itself.*

### 4. The `ζ_ℚ` glue (new lemma, not previously in Mathlib)

- **`card_ideal_rat_absNorm`** — exactly one ideal of `𝓞 ℚ` per absolute norm
  (via `Rat.ringOfIntegersEquiv`, `Algebra.norm_eq_of_algEquiv`, and the PID
  structure of `ℤ` transported through `RingEquiv.idealComapOrderIso`).
- **`dedekindZeta_rat_eq_riemannZeta`** — Mathlib's Dedekind zeta of `ℚ`
  equals `riemannZeta` on the convergence half-plane.

### 5. The `K = ℚ` rung, closed in both directions

- **`riemannZetaDatum`** — a `DedekindZetaDatum ℚ` whose anchor field is
  *proved* from the glue (no hypotheses).
- **`dedekindERH_rat_of_RH`** — the machine-verified Riemann Hypothesis
  yields the ERH statement for `ℚ`.
- **`riemannHypothesis_of_dedekindERH_rat`** — the converse bridge (the base
  project's mirror step `rh_of_right` replayed on the datum).
- **`riemannHypothesis_iff_dedekindERH_rat`** — RH and ERH(ℚ) are
  **equivalent**, machine-checked in both directions.

### 6. The concrete character χ₄ (mod 4)

- **`chiFour`** — the primitive quadratic Dirichlet character mod 4, defined
  computationally by residue (`chi_4(1)=1`, `chi_4(3)=-1`, zero elsewhere),
  with verified values. (Mathlib already provides the ℤ-valued `ZMod.χ₄`;
  `chiFour` is the ℂ-valued `DirichletCharacter ℂ 4` needed by the statements,
  equivalent to `ZMod.χ₄` cast to ℂ.)
- **`chiFour_sq`** — χ₄ is quadratic (`χ₄ * χ₄ = 1`), by four-case evaluation.
- **`chiFour_isPrimitive`** — χ₄ is primitive: its conductor is 4 (it cannot
  factor through level 1 or 2 because every level-1/2 character takes value
  1 at 3 while χ₄(3) = −1; and the conductor divides 4).

### 7. The quadratic datum — ERH modulo two classical inputs

(The two remaining inputs for a concrete field: the two-squares coefficient
identity `hcoeff`, and the nonvanishing of the root number `hroot`.)

- **`gammaFactor_ne_zero_of_re_pos`** — Dirichlet gamma-factors are zero-free
  on the right half-plane.
- **`quadraticTwist_fe`** — the twisted product `N^(s²/2) · Λ_ζ · Λ_ψ`
  satisfies a functional equation with the *constant* root number inverted
  (the non-constant factor `N^(s-1/2)` of Dirichlet's FE is absorbed by the
  twist, via `(1-s)²/2 + (s - 1/2) = s²/2`).
- **`quadraticDatum`** — a complete `DedekindZetaDatum K` for any `K` whose
  zeta factors as `ζ · L(ψ)` with `ψ` primitive quadratic: the continuation
  *is* the product (strip identity by construction — no identity-theorem
  step), the anchor field is fed by the coefficient identity, the FE and
  gamma factor are fully verified.
- **`dedekindERH_quadratic_modulo_twoSquares`** — the rung closed: given the
  two-squares coefficient identity and the classical nonvanishing of the
  root number (|rootNumber| = 1 via Gauss sums — not yet in Mathlib), the
  proven Dirichlet GRH yields full `DedekindERH K` (e.g. `K = ℚ(i)`).

### 8. No Siegel zeros

- **`DirichletCriticalLine`** — the exact shape of the parent project's proven
  `DirichletLZerosOnLine` (`Main.lean`: `LFunction_eq_zero_re := claimAll.2.1`).
- **`no_siegel_zeros`** — under that (parent-proven) statement, there is no
  real `β ∈ (1/2, 1)` with `L(χ, β) = 0` for any Dirichlet character of any
  level: the "Siegel zeros" responsible for a century of ineffective constants
  (Landau–Siegel) cannot exist once the zeros are pinned on the line.
- **`LFunction_one_ne_zero`** — Dirichlet's nonvanishing `L(χ, 1) ≠ 0` for
  non-principal `χ`, as a corollary of the proven GRH shape.

### 9. The ℚ(i) / two-squares rung (the abelian gate, reduced)

- **`nonvanishing_of_dirichlet_family`** — mixed-level Dirichlet products:
  the factor family may combine L-functions of *different* conductors
  (e.g. `ζ · L(χ₄) = L(mod 1) · L(mod 4)`).
- **`dedekindZeta_eq_riemannZeta_mul_LFunction_of_convolution`** —
  coefficient identity ⟹ L-series factorization: if the ideal counts of `K`
  equal the Dirichlet convolution `1 ⍟ ψ`, then `ζ_K = ζ · L(ψ)` on the
  convergence half-plane (via Mathlib's `LSeries_convolution`). For
  `K = ℚ(i)`, `ψ = χ₄`, the coefficient identity is the classical
  two-squares count — the **unique remaining analytic input** of that rung.
- **`dedekindERH_quadratic_of_twoSquares`** — the rung assembled: given the
  strip-level equality `ζ_K = ζ · L(χ₄)` (coefficient identity + identity
  theorem), the proven Dirichlet GRH yields the full `DedekindERH` for `K`.

### 10. The Hecke and Artin rungs (interfaces and the Brauer reduction)

- **`ERHFamily` + `dedekindERH_of_heckeERH`** — `ζ_K` is the Hecke
  L-function of the trivial Grössencharakter; ERH for any family containing
  `ζ_K` gives `DedekindERH K`.
- **`ArtinBrauerDatum` + `nonvanishing_of_artin_brauer`** — an Artin
  L-function with Brauer decomposition data (finite product of Hecke-type
  factors with integer exponents, as supplied by Brauer induction) is
  nonvanishing right of the critical line as soon as its factors are.
  Together with the mirror adapter this is the complete logical bridge
  **"Hecke ERH + Brauer induction ⟹ Artin ERH"**; what remains is the
  analytic supply (Hecke L-theory; Brauer induction; the first concrete
  factorization `ζ_ℚ(i) = ζ·L(χ₄)`).

## The verification pipeline

`.github/workflows/lean-manual.yml` (GitHub Actions, manual
`workflow_dispatch`): installs elan + the pinned toolchain, fetches the
Mathlib binary cache per `lake-manifest.json`, elaborates
`extended-research/HorizonERH.lean` (or any files given as input) with
`lake env lean`, and **fails** on any compilation error or on `sorryAx`
appearing in `#print axioms` output. Optional input builds a lake target of
the base project (building all 175,187 modules takes ~1–2 CPU-weeks and is
out of reach for CI runners). Run it: *Actions → "Lean build (manual)" →
Run workflow* (~9 minutes).

## Repository layout

```
src/                    the base Lean proof (unmodified, 175,187 files)
lakefile.toml           Lake configuration of the base project
lean-toolchain          leanprover/lean4:v4.33.1
lake-manifest.json      pins mathlib @ 0df444a360ea
extended-research/      HorizonERH.lean + its own README (details, roadmap)
.github/workflows/      the manual Lean CI pipeline
```

## Credits

- **The proof, the direction, and the new concepts** (the family nonvanishing
  strategy, the functional-equation mirror, "manufactured multiplicity" via
  iterated theta-lift chains, the announced ERH trajectory): Levent Alpöge
  with Claude (Anthropic), `alpo.ge/remark.pdf`; verification by A. Sutherland
  (MIT). The present ladder only exists because that proof made its
  hypotheses true.
- **The concrete content of `extended-research/`** (glue lemmas, bridges,
  reductions): this repository, built on Mathlib (`leanprover-community`),
  compiled against the same pinned revision as the base proof.

## License / provenance

The base tree is redistributed as published at `alpo.ge/lean.tar.gz`
(parts 01–14). `extended-research/` is new work; see its README for the
research roadmap (abelian factorizations, Hecke L-theory, Brauer induction,
Artin ERH).
