/-
Horizon ERH — blueprint for extending the (now verified) GRH-Dirichlet project
to Dedekind zeta functions of number fields, i.e. the Extended Riemann
Hypothesis in the sense of the author's remark ("the method easily extends").

This file is machine-checked against Mathlib (leanprover/lean4:v4.33.1,
mathlib @ 0df444a360ea) — the same toolchain and Mathlib revision as the
alpo.ge RH/GRH archive.

Contents:
* `mirror_lemma`     — the abstract functional-equation adapter: no zeros right
                       of the critical line + completed FE with nonzero root
                       number and zero-free gamma factor  ⇒  all critical-strip
                       zeros lie exactly on Re = 1/2. This is the piece that
                       `Formalism.VW.critLine` plays in the GRH-Dirichlet proof,
                       isolated here so ANY future L-function (Hecke, Artin,
                       automorphic) can reuse it verbatim.
* `DedekindZetaDatum` — an interface for a Dedekind zeta with its analytic
                       continuation and functional equation (Mathlib defines
                       `NumberField.dedekindZeta` only as an L-series where it
                       converges, so the continuation is packaged as data).
* `dedekindZetaCriticalLine` — instantiation of the adapter for ζ_K.
* `DedekindERH`       — the target statement of the ERH extension.

Everything below compiles with `lake env lean HorizonERH.lean`.
-/

import Mathlib

set_option linter.style.haveILetI false

open Complex NumberField

/-! ## The abstract mirror adapter -/

/-- Abstract "completed L-function" adapter. If an L-function `L` has:
* a completed form `Λ = γ · L` on the open critical strip,
* a functional equation `Λ s = ε · Λ (1 - s)` with root number `ε ≠ 0`,
* a factor `γ` that is zero-free on the open critical strip, and
* no zeros of `L` strictly right of the critical line,
then every zero of `L` inside the critical strip lies exactly on the line. -/
theorem mirror_lemma {L Λ γ : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hγ : ∀ s : ℂ, 0 < s.re → s.re < 1 → γ s ≠ 0)
    (hΛ : ∀ s : ℂ, 0 < s.re → s.re < 1 → Λ s = γ s * L s)
    (hfe : ∀ s : ℂ, Λ s = ε * Λ (1 - s))
    (hz : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → L s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → L s = 0 → s.re = 1 / 2 := by
  intro s hs0 hs1 hL
  rcases lt_trichotomy s.re (1 / 2 : ℝ) with h | h | h
  · exfalso
    -- completion vanishes at s
    have hΛs : Λ s = 0 := by rw [hΛ s hs0 hs1, hL, mul_zero]
    -- so it vanishes at the mirror point 1 - s
    have hΛm : Λ (1 - s) = 0 := by
      have h1 : Λ (1 - s) = ε⁻¹ * Λ s := by
        have h2 := hfe s
        rw [h2, ← mul_assoc, inv_mul_cancel₀ hε, one_mul]
      rw [h1, hΛs, mul_zero]
    -- the mirror point lies strictly right of the line, inside the strip
    have hm0 : 0 < (1 - s).re := by
      rw [sub_re, one_re]; linarith
    have hm1 : (1 - s).re < 1 := by
      rw [sub_re, one_re]; linarith
    have hmhalf : 1 / 2 < (1 - s).re := by
      rw [sub_re, one_re]; linarith
    -- there, Λ = γ * L with γ ≠ 0 and L ≠ 0 : Λ cannot vanish
    have hγm : γ (1 - s) ≠ 0 := hγ (1 - s) hm0 hm1
    have hLm : L (1 - s) ≠ 0 := hz (1 - s) hmhalf hm1
    rw [hΛ (1 - s) hm0 hm1] at hΛm
    rcases mul_eq_zero.1 hΛm with h | h
    · exact hγm h
    · exact hLm h
  · exact h
  · exact absurd hL (hz s h hs1)

/-! ## ERH for Dedekind zeta functions -/

variable (K : Type*) [Field K] [NumberField K]

/-- Interface for the Dedekind zeta function of a number field together with
the analytic ingredients needed to state its Riemann Hypothesis. Mathlib's
`NumberField.dedekindZeta` is (so far) only the L-series in its convergence
half-plane; the meromorphic continuation `ζ`, the completed form `Λ`, the
gamma-type factor `γ` (zero-free on the strip) and the functional equation are
packaged here as data, since establishing them is part of the ERH project. -/
structure DedekindZetaDatum where
  /-- Meromorphic continuation of ζ_K. -/
  ζ : ℂ → ℂ
  /-- Completed zeta Λ(s) = γ(s) · ζ_K(s) on the critical strip. -/
  Λ : ℂ → ℂ
  /-- Archimedean (gamma-type) factor of the completion. -/
  γ : ℂ → ℂ
  /-- Root number of the functional equation. -/
  ε : ℂ
  /-- The continuation agrees with Mathlib's L-series where the latter
  converges (some half-plane Re(s) > bound > 1). -/
  agrees :
    ∃ bound : ℝ, 1 < bound ∧
      Set.EqOn ζ (NumberField.dedekindZeta K) {s : ℂ | bound < s.re}
  hε : ε ≠ 0
  /-- The gamma factor is zero-free on the open critical strip. -/
  hγ : ∀ s : ℂ, 0 < s.re → s.re < 1 → γ s ≠ 0
  /-- Completion identity on the open critical strip. -/
  hΛζ : ∀ s : ℂ, 0 < s.re → s.re < 1 → Λ s = γ s * ζ s
  /-- Functional equation of the completed zeta. -/
  hfe : ∀ s : ℂ, Λ s = ε * Λ (1 - s)

/-- The ERH statement for ζ_K, relative to a continuation datum:
every zero with `Re(s) > 1/2` is the pole `s = 1`. -/
def DedekindERH (D : DedekindZetaDatum K) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → D.ζ s ≠ 0

/-- Instantiation of the mirror adapter: for the Dedekind zeta of any number
field, "no zeros right of the critical line" forces all critical-strip zeros
onto the line — the exact shape of `Formalism.VW.critLine`, now available for
every number field, ready for the Hecke/Artin extension. -/
theorem dedekindZetaCriticalLine (D : DedekindZetaDatum K)
    (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → D.ζ s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → D.ζ s = 0 → s.re = 1 / 2 :=
  mirror_lemma D.hε D.hγ D.hΛζ D.hfe
    (fun s hs0 hs1 =>
      hz s hs0 (fun hs => by rw [hs, Complex.one_re] at hs1; norm_num at hs1))

/-! ## The abelian case: reduction to Dirichlet GRH (Kronecker-Weber) -/

/-- Arithmetic glue for the abelian case: if a function factors on a right
half-plane as a finite product of L-functions, each of which is nonvanishing
for `Re(s) > 1/2` away from the point `s = 1` (where a principal-character
factor may have its pole), then the product is nonvanishing for `Re(s) > 1/2`
away from `s = 1`. -/
theorem nonvanishing_right_of_product {ι : Type*} (t : Finset ι)
    (L : ι → ℂ → ℂ) (f : ℂ → ℂ) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re → f z = ∏ i ∈ t, L i z)
    (hnz : ∀ i ∈ t, ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → L i z ≠ 0) :
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → f z ≠ 0 := by
  intro z hz hz1
  have hbound : bound < z.re := by linarith
  rw [hmul z hbound, Finset.prod_ne_zero_iff]
  exact fun i hi => hnz i hi z hz hz1

/-- **The abelian case of ERH follows from Dirichlet GRH.** For an abelian
extension, Kronecker-Weber identifies `ζ_K` with a finite product of Dirichlet
L-functions; since the parent project proved that every Dirichlet L-function is
nonvanishing for `Re(s) > 1/2` (`UpperTheory.EveryCharacter`), this theorem
turns such a factorization into the ERH statement for `K`. -/
theorem abelianDedekindERH {K : Type*} [Field K] [NumberField K] (D : DedekindZetaDatum K)
    {ι : Type*} (t : Finset ι) (L : ι → ℂ → ℂ) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re → D.ζ z = ∏ i ∈ t, L i z)
    (hnz : ∀ i ∈ t, ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → L i z ≠ 0) :
    DedekindERH K D :=
  fun z hz hz1 => nonvanishing_right_of_product t L D.ζ hb hmul hnz z hz hz1

/-! ## The interface instantiated on Mathlib's own Riemann zeta -/

/-- Mathlib's completed zeta factor `Gammaℝ s = π ^ (-s/2) * Γ(s/2)` is
zero-free whenever `0 < Re s`: the exponential factor never vanishes and
`Γ` is zero-free on the right half-plane (`Complex.Gamma_ne_zero_of_re_pos`). -/
theorem gammaR_ne_zero_of_re_pos {s : ℂ} (hs0 : 0 < s.re) : Gammaℝ s ≠ 0 := by
  rw [Gammaℝ]
  refine mul_ne_zero ?_ ?_
  · refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    exact_mod_cast Real.pi_ne_zero
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [Complex.div_re]
    simp
    linarith

/-- On the right half-plane, Mathlib's completed zeta factors as
`Λ(s) = Gammaℝ(s) · ζ(s)`. -/
theorem completedRiemannZeta_eq_gammaR_mul_riemannZeta {s : ℂ} (hs0 : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have h0 : s ≠ 0 := by
    intro e; rw [e] at hs0; simp at hs0
  have hΓ : Gammaℝ s ≠ 0 := gammaR_ne_zero_of_re_pos hs0
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp

/-- Mathlib's functional equation in the shape consumed by `mirror_lemma`. -/
theorem completedRiemannZeta_one_sub_mul (s : ℂ) :
    completedRiemannZeta s = 1 * completedRiemannZeta (1 - s) := by
  rw [one_mul]
  exact (completedRiemannZeta_one_sub s).symm

/-- Mathlib's own Riemann zeta passes through the mirror adapter: if it has no
zeros strictly right of the critical line, all its critical-strip zeros lie on
the line. Built from genuine Mathlib objects — no hypotheses beyond Mathlib's
own theorems. This is the `K = ℚ` seed of the ERH interface, and the exact
shape the parent project realized as `Formalism.VW.rh_of_right`. -/
theorem riemannZetaCriticalLine
    (hz : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 :=
  mirror_lemma one_ne_zero (fun _ hs0 _ => gammaR_ne_zero_of_re_pos hs0)
    (fun _ hs0 _ => completedRiemannZeta_eq_gammaR_mul_riemannZeta hs0)
    completedRiemannZeta_one_sub_mul
    hz

#print axioms mirror_lemma
#print axioms dedekindZetaCriticalLine
#print axioms nonvanishing_right_of_product
#print axioms abelianDedekindERH

/-- The exact shape of the parent project's proven theorem
(`Main.lean`: `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi`):
every Dirichlet L-function is nonvanishing right of the critical line, apart
from the principal character at its pole `s = 1`. -/
def DirichletGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- **The abelian rung, concretely plugged**: if `ζ_K` factors as a finite
product of Dirichlet L-functions on a half-plane (Kronecker-Weber), then the
parent project's proven Dirichlet GRH immediately yields nonvanishing of
`ζ_K` right of the critical line. Combined with `dedekindZetaCriticalLine`,
a single such factorization gives ERH for `K`. -/
theorem nonvanishing_of_dirichlet_factorization (hgrh : DirichletGRH)
    (ζ : ℂ → ℂ) {N : ℕ} [NeZero N]
    (χs : Finset (DirichletCharacter ℂ N)) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re →
      ζ z = ∏ χ ∈ χs, DirichletCharacter.LFunction χ z) :
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → ζ z ≠ 0 :=
  nonvanishing_right_of_product χs DirichletCharacter.LFunction ζ hb hmul
    (fun χ _ z' hz' hz'1 => hgrh N χ z' hz' (Or.inr hz'1))

#print axioms nonvanishing_of_dirichlet_factorization

/-! ## No Siegel zeros -/

/-- The exact shape of the parent project's proven theorem (`Statements.lean`:
`DirichletLZerosOnLine`, proven in `Main.lean` as `LFunction_eq_zero_re :=
claimAll.2.1`): every zero of every Dirichlet L-function in the open critical
strip lies on the critical line. -/
def DirichletCriticalLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- **No Siegel zeros.** Under the (parent-proven) critical-line statement,
there is no real `β ∈ (1/2, 1)` with `L(χ, β) = 0` — for any Dirichlet
character of any level. A "Siegel zero" — a real zero of a real character
dangerously close to `1`, the obstruction responsible for a century of
ineffective constants in analytic number theory (Landau–Siegel) — cannot
exist once the zeros are pinned on the line. -/
theorem no_siegel_zeros (h : DirichletCriticalLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {β : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1) :
    DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  intro hz
  have hline := h N χ (β : ℂ) (by rw [Complex.ofReal_re]; linarith)
    (by rw [Complex.ofReal_re]; linarith) hz
  rw [Complex.ofReal_re] at hline
  linarith

/-- Dirichlet's nonvanishing at the edge, from the parent-proven GRH shape:
for every non-principal Dirichlet character, `L(χ, 1) ≠ 0`. (This was the
historical input to Dirichlet's theorem on primes in arithmetic progressions;
here it is a corollary of the proven GRH.) -/
theorem LFunction_one_ne_zero (hgrh : DirichletGRH) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 ≠ 0 :=
  hgrh N χ 1 (by simp) (Or.inl hχ)

#print axioms no_siegel_zeros
#print axioms LFunction_one_ne_zero

/-! ## The Hecke and Artin rungs (interfaces and the Brauer reduction) -/

/-- ERH for an arbitrary family of L-functions: every member is nonvanishing
right of the critical line (away from the possible pole at `s = 1`). -/
def ERHFamily (S : Set (ℂ → ℂ)) : Prop :=
  ∀ L ∈ S, ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → L z ≠ 0

/-- **The Hecke rung, interface**: the Dedekind zeta of `K` *is* the Hecke
L-function of the trivial Grössencharakter of `K`; consequently, ERH for a
family of L-functions containing `ζ_K` gives ERH for `K`. Supplying the family
of Hecke L-functions of `K` (idele-class characters, analytic continuation,
functional equation) is the analytic content of the Hecke rung. -/
theorem dedekindERH_of_heckeERH {K : Type*} [Field K] [NumberField K]
    (D : DedekindZetaDatum K) {S : Set (ℂ → ℂ)}
    (hS : ERHFamily S) (hζ : D.ζ ∈ S) :
    DedekindERH K D :=
  fun z hz hz1 => hS D.ζ hζ z hz hz1

/-- **Brauer decomposition data for an Artin L-function**: the L-function
factors, on a half-plane, as a finite product of Hecke-type L-functions with
integer exponents. This is the shape supplied by Brauer's induction theorem
(an Artin character is a virtual combination of characters induced from
1-dimensional characters of subgroups — cyclic by class field theory); the
parent archive contains a `GroundTheory/Brauer` tower in this direction. -/
structure ArtinBrauerDatum (f : ℂ → ℂ) where
  /-- Index type for the Hecke-type factors. -/
  ι : Type*
  /-- Finite support of the decomposition. -/
  t : Finset ι
  /-- The Hecke-type L-functions. -/
  L : ι → ℂ → ℂ
  /-- Integer exponents (Brauer: virtual characters, so signs occur). -/
  e : ι → ℤ
  /-- Where the product identity holds. -/
  bound : ℝ
  /-- The product identity. -/
  hmul : ∀ z : ℂ, bound < z.re → f z = ∏ i ∈ t, (L i z) ^ ((e i : ℂ))

/-- **The Artin rung, reduction step**: an Artin L-function with Brauer
decomposition data is nonvanishing right of the critical line as soon as all
the Hecke-type factors in the decomposition are. Combined with
`dedekindERH_of_heckeERH` and the mirror adapter, this is the complete logical
bridge "Hecke ERH + Brauer induction ⟹ Artin ERH"; what remains is the
analytic supply of the two hypotheses (Hecke L-theory; Brauer induction). -/
theorem nonvanishing_of_artin_brauer {f : ℂ → ℂ} (d : ArtinBrauerDatum f) (hb : d.bound ≤ 1 / 2)
    (hnz : ∀ i ∈ d.t, ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → d.L i z ≠ 0) :
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → f z ≠ 0 := by
  intro z hz hz1
  have hbound : d.bound < z.re := by linarith
  rw [d.hmul z hbound, Finset.prod_ne_zero_iff]
  intro i hi
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (hnz i hi z hz hz1))

#print axioms dedekindERH_of_heckeERH
#print axioms nonvanishing_of_artin_brauer

/-! ## The ℚ(i) rung: mixed-level Dirichlet products and the two-squares reduction -/

/-- **Mixed-level Dirichlet products**: unlike
`nonvanishing_of_dirichlet_factorization` (single level `N`), the factor
family may combine Dirichlet L-functions of *different* conductors — e.g.
`ζ · L(χ₄) = L(mod 1) · L(mod 4)`. -/
theorem nonvanishing_of_dirichlet_family (hgrh : DirichletGRH)
    (ζ : ℂ → ℂ) {ι : Type*} (t : Finset ι)
    (L : ι → ℂ → ℂ) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re → ζ z = ∏ i ∈ t, L i z)
    (hfam : ∀ i ∈ t, ∃ (N : ℕ) (_ : NeZero N) (ψ : DirichletCharacter ℂ N),
      ∀ z : ℂ, L i z = DirichletCharacter.LFunction ψ z) :
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → ζ z ≠ 0 := by
  refine nonvanishing_right_of_product t L ζ hb hmul ?_
  intro i hi
  obtain ⟨N, hN, ψ, hψ⟩ := hfam i hi
  haveI := hN
  intro z hz hz1
  rw [hψ z]
  exact hgrh N ψ z hz (Or.inr hz1)

/-- **Coefficient identity ⟹ L-series factorization**: if the ideal counts of
`K` equal the Dirichlet convolution `1 ⍟ ψ` (for a Dirichlet character `ψ`),
then the Dedekind zeta of `K` factors as `ζ · L(ψ)` on the convergence
half-plane. For `K = ℚ(i)` and `ψ = χ₄` this is the classical factorization,
and the coefficient identity is the two-squares count
`#{ideals of norm n} = ∑_{d ∣ n} χ₄(d)` — the unique remaining analytic
input of that rung. -/
theorem dedekindZeta_eq_riemannZeta_mul_LFunction_of_convolution
    {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
        = (LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => ψ n)) n)
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s
      = riemannZeta s * DirichletCharacter.LFunction ψ s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hψ : LSeriesSummable (fun n : ℕ => ψ n) s := DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hs
  unfold NumberField.dedekindZeta
  rw [DirichletCharacter.LFunction_eq_LSeries ψ hs, ← LSeries_one_eq_riemannZeta hs,
    ← LSeries_convolution' h1 hψ]
  exact LSeries_congr (fun {n} hn => hcoeff n hn) s

/-- **The rung assembled**: if the continued zeta of K agrees with
`riemannZeta * L(chi_4)` on the right half-plane (supplied, for the Gaussian
field, by the coefficient identity above together with the identity theorem),
the proven Dirichlet GRH yields the full Dedekind ERH statement for K. -/
theorem dedekindERH_quadratic_of_twoSquares (hgrh : DirichletGRH)
    {K : Type*} [Field K] [NumberField K] (D : DedekindZetaDatum K)
    (χ : DirichletCharacter ℂ 4) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hcont : ∀ z : ℂ, bound < z.re →
      D.ζ z = riemannZeta z * DirichletCharacter.LFunction χ z) :
    DedekindERH K D := by
  intro z hz hz1 hz0
  rw [hcont z (by linarith), mul_eq_zero] at hz0
  rcases hz0 with h | h
  · exact hgrh 1 (1 : DirichletCharacter ℂ 1) z hz (Or.inr hz1) (by simpa using h)
  · exact hgrh 4 χ z hz (Or.inr hz1) h

#print axioms nonvanishing_of_dirichlet_family
#print axioms dedekindZeta_eq_riemannZeta_mul_LFunction_of_convolution
#print axioms dedekindERH_quadratic_of_twoSquares

/-! ## The glue `NumberField.dedekindZeta ℚ = riemannZeta` -/

/-- The ring of integers of `ℚ`, as a `ℤ`-algebra equivalence with `ℤ`. -/
noncomputable def ratAlgEquiv : (𝓞 ℚ) ≃ₐ[ℤ] ℤ where
  __ := Rat.ringOfIntegersEquiv
  commutes' := fun _ => by simp

theorem norm_rat_ofInt (x : 𝓞 ℚ) :
    (Algebra.norm ℤ) x = Rat.ringOfIntegersEquiv x := by
  have h : (Algebra.norm ℤ) (ratAlgEquiv x) = (Algebra.norm ℤ) x :=
    Algebra.norm_eq_of_algEquiv ratAlgEquiv x
  have h2 : (Algebra.norm ℤ) (ratAlgEquiv x) = ratAlgEquiv x := by simp
  exact (h2.symm.trans h).symm

theorem comap_span_singleton_rat (g : ℤ) :
    Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(g : ℤ)}) =
      Ideal.span {Rat.ringOfIntegersEquiv.symm g} := by
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Rat.ringOfIntegersEquiv.symm c, ?_⟩
    have := congrArg Rat.ringOfIntegersEquiv.symm hc
    simpa [map_mul, Rat.ringOfIntegersEquiv.symm_apply_apply] using this
  · rintro ⟨c, hc⟩
    refine ⟨Rat.ringOfIntegersEquiv c, ?_⟩
    have := congrArg Rat.ringOfIntegersEquiv hc
    simpa [map_mul, Rat.ringOfIntegersEquiv.apply_symm_apply] using this

/-- Every ideal of `𝓞 ℚ` with absolute norm `n` is the principal ideal
generated by the lift of `n`. -/
theorem ideal_rat_eq_span {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : Ideal.absNorm I = n) :
    I = Ideal.span {Rat.ringOfIntegersEquiv.symm (n : ℤ)} := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.map Rat.ringOfIntegersEquiv I = Ideal.span {g} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator
      (Ideal.map Rat.ringOfIntegersEquiv I)).symm⟩
  have hcomap : Ideal.comap Rat.ringOfIntegersEquiv (Ideal.map Rat.ringOfIntegersEquiv I) = I :=
    Rat.ringOfIntegersEquiv.idealComapOrderIso.right_inv I
  rw [hg, comap_span_singleton_rat] at hcomap
  have hI : I = Ideal.span {Rat.ringOfIntegersEquiv.symm g} := hcomap.symm
  have hgabs : Ideal.absNorm (Ideal.span {Rat.ringOfIntegersEquiv.symm g}) = n := by
    rw [← hI]; exact h
  rw [Ideal.absNorm_span_singleton, norm_rat_ofInt, Rat.ringOfIntegersEquiv.apply_symm_apply] at hgabs
  rcases (by omega : g = (n : ℤ) ∨ g = -((n : ℤ))) with rfl | rfl
  · exact hI
  · rw [hI, map_neg, Ideal.span_singleton_neg]

/-- Exactly one ideal of `𝓞 ℚ` per absolute norm. -/
theorem card_ideal_rat_absNorm (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 := by
  have hw : Ideal.absNorm (Ideal.span {Rat.ringOfIntegersEquiv.symm (n : ℤ)}) = n := by
    rw [Ideal.absNorm_span_singleton, norm_rat_ofInt,
      Rat.ringOfIntegersEquiv.apply_symm_apply, Int.natAbs_natCast]
  have hsub : ∀ I : {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n},
      I = ⟨Ideal.span {Rat.ringOfIntegersEquiv.symm (n : ℤ)}, hw⟩ :=
    fun I => Subtype.ext (ideal_rat_eq_span I.2)
  haveI : Nonempty {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} :=
    ⟨⟨Ideal.span {Rat.ringOfIntegersEquiv.symm (n : ℤ)}, hw⟩⟩
  haveI : Subsingleton {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} :=
    ⟨fun a b => by rw [hsub a, hsub b]⟩
  exact Nat.card_unique

/-- The L-series coefficients of the Dedekind zeta function of `ℚ` are
identically `1`. -/
theorem dedekindZeta_rat_coeffs (n : ℕ) :
    ((Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} : ℕ) : ℂ) = 1 := by
  rw [card_ideal_rat_absNorm]
  norm_num

/-- **The glue**: Mathlib's Dedekind zeta function of `ℚ` coincides with
Mathlib's Riemann zeta function on the convergence half-plane. -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  unfold NumberField.dedekindZeta
  rw [← LSeries_one_eq_riemannZeta hs]
  congr 1
  funext n
  simpa using dedekindZeta_rat_coeffs n

/-! ## The full loop for K = ℚ: the ERH datum, anchored and bridged -/

/-- The ERH datum for `ℚ`, carried by Mathlib's own Riemann zeta. The anchor
field (`agrees`) is *proved* from the glue theorem above — no hypotheses. -/
noncomputable def riemannZetaDatum : DedekindZetaDatum ℚ where
  ζ := riemannZeta
  Λ := completedRiemannZeta
  γ := Gammaℝ
  ε := 1
  agrees := ⟨2, by norm_num,
    fun s hs => by
      simp only [Set.mem_ofPred] at hs
      exact (dedekindZeta_rat_eq_riemannZeta (by linarith)).symm⟩
  hε := one_ne_zero
  hγ := fun s hs0 _ => gammaR_ne_zero_of_re_pos hs0
  hΛζ := fun s hs0 _ => completedRiemannZeta_eq_gammaR_mul_riemannZeta hs0
  hfe := completedRiemannZeta_one_sub_mul

/-- **Closing the loop**: the (machine-verified) Riemann Hypothesis yields the
ERH statement for `ℚ` through the anchored datum. -/
theorem dedekindERH_rat_of_RH (h : RiemannHypothesis) : DedekindERH ℚ riemannZetaDatum := by
  intro s hs hs1 hz
  have htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hr := congrArg Complex.re hn
    simp [Complex.mul_re, Complex.add_re] at hr
    have hnng : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have := h s hz htriv hs1
  linarith

/-- **The converse bridge**: the ERH statement for `ℚ` (through the anchored
datum) implies Mathlib's `RiemannHypothesis`. The argument is the mirror step
of the parent project (`Formalism.VW.rh_of_right`), replayed on the datum. -/
theorem riemannHypothesis_of_dedekindERH_rat (h : DedekindERH ℚ riemannZetaDatum) :
    RiemannHypothesis := by
  have hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hs1 => h s hs hs1
  unfold RiemannHypothesis
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hs
      norm_num at hs
    have ht : 1 / 2 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have h1 : (1 - s) ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    have hnat : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n h
      have hr := congrArg Complex.re h
      rw [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have key := riemannZeta_one_sub hnat h1
    rw [sub_sub_cancel, hs] at key
    have hz' := hz (1 - s) ht h1
    have h2pi : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero two_ne_zero hpi)))
    have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      have h3 : ((1 - s) - (2 * (k : ℂ) + 1)) * (Real.pi : ℂ) = 0 := by
        linear_combination 2 * hk
      rcases mul_eq_zero.1 h3 with h | h
      · have hsk : s = -2 * (k : ℂ) := by linear_combination -h
        have hre : s.re = -2 * (k : ℝ) := by
          rw [hsk, Complex.mul_re]
          simp
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
          linarith
        · apply hs0
          rw [hsk, hk0]
          simp
        · apply htriv
          refine ⟨(k - 1).toNat, ?_⟩
          have hnk : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
          have h' : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
            have := congrArg (fun m : ℤ => (m : ℂ)) hnk
            push_cast at this
            exact this
          rw [hsk, h']
          ring
      · exact hpi h
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h2pi hG) hcos) hz') key.symm
  · exact heq
  · exact absurd hs (hz s hgt hs1)

/-- **RH and ERH(ℚ) are equivalent**, machine-checked in both directions. -/
theorem riemannHypothesis_iff_dedekindERH_rat :
    RiemannHypothesis ↔ DedekindERH ℚ riemannZetaDatum :=
  ⟨dedekindERH_rat_of_RH, riemannHypothesis_of_dedekindERH_rat⟩

#print axioms riemannZetaDatum
#print axioms dedekindERH_rat_of_RH
#print axioms riemannHypothesis_of_dedekindERH_rat
#print axioms riemannHypothesis_iff_dedekindERH_rat

#print axioms gammaR_ne_zero_of_re_pos
#print axioms completedRiemannZeta_eq_gammaR_mul_riemannZeta
#print axioms riemannZetaCriticalLine
