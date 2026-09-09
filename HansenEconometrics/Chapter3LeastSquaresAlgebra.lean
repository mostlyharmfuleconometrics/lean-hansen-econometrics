import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.Chapter2LinearProjection

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]

/-- Hansen Definition 3.1: sum of squared errors, written in matrix notation. -/
noncomputable def sumSquaredErrors (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) : ℝ :=
  (y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b)

/-- Hansen Theorem 3.2: closed-form OLS coefficient under invertibility of `Xᵀ X`. -/
noncomputable def olsBeta (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : k → ℝ :=
  (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)

/-- **Star primitive**: totalized OLS coefficient that is defined on every design matrix.

Uses `Matrix.nonsingInv` in place of the typeclass inverse `⅟(Xᵀ * X)`, so it is a genuine
function with no typeclass precondition.  On **singular** designs `(Xᵀ * X)⁻¹ = 0` by
definition, so `olsBetaStar X y = 0`; on **nonsingular** designs it agrees with `olsBeta`
(see `olsBetaStar_eq_olsBeta`).

Role in the project architecture:
- **Chapters 3–5** use `olsBeta` (typeclass inverse) for finite-sample algebra.
- **Chapter 7+** use `olsBetaStar` as the proof engine for asymptotic results, where
  nonsingularity holds only a.s. and cannot be supplied as a global typeclass.
- Textbook-facing statements that a reader would want to cite use `olsBetaOrZero`
  (Chapter 7), which is provably equal to `olsBetaStar` (see `olsBetaOrZero_eq_olsBetaStar`). -/
noncomputable def olsBetaStar (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y)

/-- Under invertibility of `Xᵀ * X`, the total `olsBetaStar` agrees with `olsBeta`. -/
theorem olsBetaStar_eq_olsBeta
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBetaStar X y = olsBeta X y := by
  unfold olsBetaStar olsBeta
  rw [← invOf_eq_nonsing_inv]

/-- Hansen Section 3.10: fitted values `X β̂`. -/
noncomputable def fitted (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : n → ℝ :=
  X *ᵥ olsBeta X y

/-- Hansen Theorem 3.2: OLS residual vector `Y - X β̂`. -/
noncomputable def residual (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : n → ℝ :=
  y - fitted X y

/-- Hansen Theorem 3.2: normal equations in closed-form OLS notation. -/
theorem normal_equations
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    Xᵀ *ᵥ residual X y = 0 := by
  unfold residual fitted olsBeta
  rw [mulVec_sub]
  have hmul : Xᵀ *ᵥ (X *ᵥ (⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ y))) = (Xᵀ * (X * ⅟ (Xᵀ * X))) *ᵥ (Xᵀ *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc
    Xᵀ *ᵥ y - Xᵀ *ᵥ (X *ᵥ (⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ y)))
        = Xᵀ *ᵥ y - (Xᵀ * (X * ⅟ (Xᵀ * X))) *ᵥ (Xᵀ *ᵥ y) := by rw [hmul]
    _ = Xᵀ *ᵥ y - (((Xᵀ * X) * ⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)) := by rw [Matrix.mul_assoc]
    _ = Xᵀ *ᵥ y - (1 *ᵥ (Xᵀ *ᵥ y)) := by rw [mul_invOf_self]
    _ = 0 := by simp

/-- Hansen Theorem 3.2: the regressors are orthogonal to the OLS residual vector. -/
theorem regressors_orthogonal_to_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    Xᵀ *ᵥ residual X y = 0 :=
  normal_equations X y

/-- The closed-form OLS coefficient is the unique vector satisfying the normal equations. -/
theorem olsBeta_eq_of_normal_equations
    (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)]
    (hb : Xᵀ *ᵥ (y - X *ᵥ b) = 0) :
    olsBeta X y = b := by
  unfold olsBeta
  have hxy : Xᵀ *ᵥ y = (Xᵀ * X) *ᵥ b := by
    rw [Matrix.mulVec_sub] at hb
    have hmul : Xᵀ *ᵥ (X *ᵥ b) = (Xᵀ * X) *ᵥ b := by
      rw [Matrix.mulVec_mulVec]
    rw [hmul] at hb
    exact sub_eq_zero.mp hb
  rw [hxy]
  rw [Matrix.mulVec_mulVec b (⅟ (Xᵀ * X)) (Xᵀ * X)]
  rw [invOf_mul_self]
  simp

/-- Fitted values plus residuals recover the data vector. -/
theorem fitted_add_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X y + residual X y = y := by
  unfold residual
  simp [sub_eq_add_neg, add_left_comm]

/-- Hansen Definition 3.1 / Theorem 3.2: at `β̂`, SSE is the residual sum of squares. -/
theorem sumSquaredErrors_olsBeta
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    sumSquaredErrors X y (olsBeta X y) = residual X y ⬝ᵥ residual X y := by
  rfl

/-- Hansen equation (3.17): if the regressor matrix contains a constant column,
residuals sum to zero. -/
theorem residual_sum_zero_of_one_mem_colspan
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)]
    {c : k → ℝ} (hc : X *ᵥ c = 1) :
    ∑ i, residual X y i = 0 := by
  calc
    ∑ i, residual X y i = residual X y ⬝ᵥ 1 := by
      rw [dotProduct_one]
    _ = residual X y ⬝ᵥ (X *ᵥ c) := by
      rw [hc]
    _ = (Matrix.vecMul (residual X y) X) ⬝ᵥ c := by
      rw [Matrix.dotProduct_mulVec]
    _ = 0 := by
      have h : Matrix.vecMul (residual X y) X = 0 := by
        simpa [vecMul_eq_mulVec_transpose] using (normal_equations X y)
      rw [h]
      simp

omit [DecidableEq k] in
/-- Bridge lemma: the Chapter 3 sum-of-squared-errors equals the Chapter 2
`linearProjectionMSE` when the moment matrices are the sample Gram matrix and
cross-moment vector. This connects the two notations so we can reuse the
Chapter 2 minimization theorem. Private — internal to this file's proof of
`sumSquaredErrors_olsBeta_le`. -/
private lemma sumSquaredErrors_eq_linearProjectionMSE
    (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) :
    sumSquaredErrors X y b =
      linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b := by
  have hcross : y ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (Xᵀ *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]
  have hquad : (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b) := by
    rw [← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec b Xᵀ (X *ᵥ b),
        vecMul_eq_mulVec_transpose,
        Matrix.transpose_transpose]
  unfold sumSquaredErrors linearProjectionMSE
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_comm (X *ᵥ b) y, hcross, hquad]
  ring

/-- Hansen Theorem 3.1 (existence half): `olsBeta X y` attains the minimum of the sum
of squared errors. For any coefficient vector `b`, `SSE(olsBeta X y) ≤ SSE(b)`.

Uniqueness — `b = olsBeta X y` whenever `SSE(b) = SSE(olsBeta X y)` — requires strict
positive-definiteness of `Xᵀ * X` and is left to a follow-up. -/
theorem sumSquaredErrors_olsBeta_le
    (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
    sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b := by
  rw [sumSquaredErrors_eq_linearProjectionMSE X y b,
      sumSquaredErrors_eq_linearProjectionMSE X y (olsBeta X y),
      show olsBeta X y = linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y) from rfl]
  exact linearProjectionBeta_minimizes_MSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y)
    (gram_transpose X) (gram_quadratic_nonneg X) b

/-- Hansen Theorem 3.1 (existence half), packaged as `IsMinOn`: `olsBeta X y` is a
global minimizer of `sumSquaredErrors X y` over all of `k → ℝ`. -/
theorem olsBeta_isMinOn
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    IsMinOn (sumSquaredErrors X y) Set.univ (olsBeta X y) := by
  intro b _
  exact sumSquaredErrors_olsBeta_le X y b

/-- Hansen Theorem 3.1 (uniqueness half): if `b` attains the minimum of the SSE, then
`b = olsBeta X y`. Combined with `sumSquaredErrors_olsBeta_le` and `olsBeta_isMinOn`,
this completes Hansen's Theorem 3.1: `olsBeta X y` is the unique minimizer of
`sumSquaredErrors X y` over `k → ℝ` whenever `Xᵀ * X` is invertible. -/
theorem olsBeta_eq_of_minimizer
    (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)]
    (hb : sumSquaredErrors X y b = sumSquaredErrors X y (olsBeta X y)) :
    b = olsBeta X y := by
  rw [sumSquaredErrors_eq_linearProjectionMSE X y b,
      sumSquaredErrors_eq_linearProjectionMSE X y (olsBeta X y)] at hb
  exact linearProjectionBeta_eq_of_MSE_eq
    (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b
    (gram_transpose X) (fun v hv => gram_quadratic_pos X hv) hb

/-- Reusable helper: transport `olsBeta` across a propositional equality of design matrices.

`Invertible` is data rather than a `Prop`, so `congr` cannot cross the two different
`[Invertible (·ᵀ * ·)]` instances attached to `A` and `B`; `Subsingleton (Invertible _)`
can. Cite this whenever two spellings of the same design matrix have to be reconciled. -/
theorem olsBeta_congr {A B : Matrix n k ℝ} (h : A = B) (y : n → ℝ)
    [iA : Invertible (Aᵀ * A)] [iB : Invertible (Bᵀ * B)] :
    olsBeta A y = olsBeta B y := by
  subst h
  rw [Subsingleton.elim iA iB]

/-- Reusable helper: transport `residual` across a propositional equality of design
matrices. The `residual` companion of `olsBeta_congr`; see that lemma for why a plain
`congr` does not work. -/
theorem residual_congr {A B : Matrix n k ℝ} (h : A = B) (y : n → ℝ)
    [iA : Invertible (Aᵀ * A)] [iB : Invertible (Bᵀ * B)] :
    residual A y = residual B y := by
  subst h
  rw [Subsingleton.elim iA iB]

end HansenEconometrics
