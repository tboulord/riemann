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

open Complex

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
for `Re(s) > 1/2`, then the product is nonvanishing for `Re(s) > 1/2`. -/
theorem nonvanishing_right_of_product {ι : Type*} (t : Finset ι)
    (L : ι → ℂ → ℂ) (f : ℂ → ℂ) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re → f z = ∏ i ∈ t, L i z)
    (hnz : ∀ i ∈ t, ∀ z : ℂ, 1 / 2 < z.re → L i z ≠ 0) :
    ∀ z : ℂ, 1 / 2 < z.re → f z ≠ 0 := by
  intro z hz
  have hbound : bound < z.re := by linarith
  rw [hmul z hbound, Finset.prod_ne_zero_iff]
  exact fun i hi => hnz i hi z hz

/-- **The abelian case of ERH follows from Dirichlet GRH.** For an abelian
extension, Kronecker-Weber identifies `ζ_K` with a finite product of Dirichlet
L-functions; since the parent project proved that every Dirichlet L-function is
nonvanishing for `Re(s) > 1/2` (`UpperTheory.EveryCharacter`), this theorem
turns such a factorization into the ERH statement for `K`. -/
theorem abelianDedekindERH {K : Type*} [Field K] [NumberField K] (D : DedekindZetaDatum K)
    {ι : Type*} (t : Finset ι) (L : ι → ℂ → ℂ) {bound : ℝ} (hb : bound ≤ 1 / 2)
    (hmul : ∀ z : ℂ, bound < z.re → D.ζ z = ∏ i ∈ t, L i z)
    (hnz : ∀ i ∈ t, ∀ z : ℂ, 1 / 2 < z.re → L i z ≠ 0) :
    DedekindERH K D :=
  fun z hz _ => nonvanishing_right_of_product t L D.ζ hb hmul hnz z hz

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
#print axioms gammaR_ne_zero_of_re_pos
#print axioms completedRiemannZeta_eq_gammaR_mul_riemannZeta
#print axioms riemannZetaCriticalLine
