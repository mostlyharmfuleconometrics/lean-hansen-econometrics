import HansenEconometrics.Chapter3FWL

/-!
# Chapter 17 — panel data: the within transformation and Theorem 17.1

This module opens Chapter 17 with the panel objects Hansen constructs in §17.8, §17.9
and §17.11, and
with his Theorem 17.1.

Observations are indexed by an arbitrary finite type `n`, and a **group map** `g : n → ι`
records which individual produced each observation. The panel need not be balanced:
individual `j` contributes `groupSize g j` observations — Hansen's `Tⱼ`, the cardinality of
the fibre of `g` over `j`, in bijection with Hansen's period set `Sⱼ` — and the dummy
Gram matrix is `DᵀD = diag(T₁, …, T_N)`. Hansen's
implicit requirement that every individual be observed at least once is carried here as
`Function.Surjective g`, and it is exactly what makes that Gram matrix invertible.

Public surface:

* `groupSize` — Hansen's `Tⱼ = |Sⱼ|`, and `groupSize_pos_of_surjective`;
* `panelDummies` — the individual dummy design `D` of §17.8, together with its Gram matrix
  `panelDummies_transpose_mul_self` and the `Invertible` witness `panelDummiesGramInvertible`;
* `individualMean`, `withinTransform`, `withinTransformMatrix` — the within (demeaning)
  operator `Ẏᵢₜ = Yᵢₜ − Ȳᵢ` of §17.8, for vectors and columnwise for design matrices;
* `annihilatorMatrix_panelDummies_mulVec` and `residualizedRegressors_panelDummies` — the
  two clauses of Hansen equation (17.19), `M_D Y = Ẏ` and `M_D X = Ẋ`;
* `fixedEffectsBeta` (§17.9) and `dummyVariableBeta` (§17.11);
* `fixedEffectsBeta_eq_dummyVariableBeta` and
  `fixedEffects_residual_eq_dummyVariable_residual` — the two clauses of Theorem 17.1.

The proof is Hansen's own argument. Equation (17.19) identifies the within transformation
with the residual from a regression on `D`, and the Frisch-Waugh-Lovell theorem of
[Chapter3FWL](./Chapter3FWL.lean) then identifies the `β` block of the `[D X]` regression
with least squares on the demeaned data.

Because `D` is not invertible-by-typeclass — surjectivity of `g` is a `Prop`, not an
instance — `panelDummiesGramInvertible` is a `def`, and results whose *statement* mentions
`annihilatorMatrix` or `residualizedRegressors` install it with a `letI` in the statement.
Both clauses of Theorem 17.1 avoid this: neither side of either statement mentions the
annihilator, so the instance stays confined to the proof.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n ι k : Type*}
variable [Fintype n] [Fintype ι] [DecidableEq ι]

/-- Hansen §17.8: the number of observations belonging to individual `j`, i.e. Hansen's `Tⱼ`,
the cardinality of the fibre `{p | g p = j}`, which is in bijection with Hansen's set of
observed periods `Sⱼ` (§17.2) — the module drops time labels, keeping only the grouping.

This is a fibre cardinality, spelled the way Mathlib spells the same thing in
`Finset.card_eq_sum_card_fiberwise`. In a balanced panel it is constant in `j`; nothing here
assumes that. -/
def groupSize (g : n → ι) (j : ι) : ℕ :=
  (Finset.univ.filter fun p => g p = j).card

/-- Hansen §17.8: the individual dummy design matrix `D`.

There is one column per individual, and the row of observation `p` is the indicator vector of
the individual `g p`. This is Hansen's `dᵢ` of §17.11 stacked into a matrix; his display
`D = diag{1_{T₁}, …, 1_{T_N}}` presumes the observations are sorted by individual, so
`panelDummies g` is that matrix up to a permutation of rows. Nothing below depends on the
row order. -/
def panelDummies (g : n → ι) : Matrix n ι ℝ :=
  Matrix.of fun p j => if g p = j then 1 else 0

omit [Fintype ι] in
/-- The dummy Gram matrix is `DᵀD = diag(T₁, …, T_N)`: the individuals' dummy columns are
orthogonal, and the `j`th has squared length `Tⱼ = groupSize g j`. In a balanced panel this
specializes to Hansen's `T · I`. -/
theorem panelDummies_transpose_mul_self (g : n → ι) :
    (panelDummies g)ᵀ * panelDummies g = Matrix.diagonal fun j => (groupSize g j : ℝ) := by
  ext j j'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, panelDummies, Matrix.of_apply]
  by_cases h : j = j'
  · subst h
    rw [Matrix.diagonal_apply_eq]
    have hsq : ∀ p : n, (if g p = j then (1 : ℝ) else 0) * (if g p = j then (1 : ℝ) else 0)
        = if g p = j then (1 : ℝ) else 0 := by
      intro p; by_cases hp : g p = j <;> simp [hp]
    simp only [hsq]
    rw [Finset.sum_boole]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hj : g p = j
    · subst hj
      simp [h]
    · simp [hj]

omit [Fintype ι] in
/-- Every individual contributes at least one observation, which is Hansen's implicit `Tᵢ ≥ 1`.
This is the content of surjectivity of the group map. -/
theorem groupSize_pos_of_surjective {g : n → ι} (hg : Function.Surjective g) (j : ι) :
    0 < groupSize g j := by
  obtain ⟨p, hp⟩ := hg j
  exact Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩⟩

omit [Fintype ι] in
/-- Each group size is invertible as a real scalar when every individual is observed.
Private: shared scaffolding for the two Gram-inverse results below. -/
private theorem groupSize_mul_inv_cancel {g : n → ι} (hg : Function.Surjective g) :
    (fun j => ((groupSize g j : ℝ)) * ((groupSize g j : ℝ))⁻¹) = fun _ : ι => (1 : ℝ) := by
  funext j
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (groupSize_pos_of_surjective hg j).ne')

/-- `DᵀD = diag(T₁, …, T_N)` is invertible as soon as every individual is observed, with
inverse `diag(T₁⁻¹, …, T_N⁻¹)`.

Surjectivity is a `Prop`, not a typeclass, so this is a `def` rather than a global instance:
use sites install it with `letI := panelDummiesGramInvertible hg` to discharge the Chapter 3
FWL hypothesis `[Invertible (X₁ᵀ * X₁)]` at `X₁ := panelDummies g`. -/
@[reducible] noncomputable def panelDummiesGramInvertible
    {g : n → ι} (hg : Function.Surjective g) :
    Invertible ((panelDummies g)ᵀ * panelDummies g) := by
  refine invertibleOfRightInverse _ (Matrix.diagonal fun j => ((groupSize g j : ℝ))⁻¹) ?_
  rw [panelDummies_transpose_mul_self, Matrix.diagonal_mul_diagonal,
    groupSize_mul_inv_cancel hg, Matrix.diagonal_one]

/-- The typeclass inverse of the dummy Gram matrix, in closed form:
`⅟(DᵀD) = diag(T₁⁻¹, …, T_N⁻¹)`. Private: pure scaffolding for equation (17.19). -/
private theorem invOf_panelDummies_gram {g : n → ι} (hg : Function.Surjective g) :
    letI := panelDummiesGramInvertible hg
    (⅟ ((panelDummies g)ᵀ * panelDummies g))
      = Matrix.diagonal fun j => ((groupSize g j : ℝ))⁻¹ := by
  letI := panelDummiesGramInvertible hg
  refine invOf_eq_right_inv ?_
  rw [panelDummies_transpose_mul_self, Matrix.diagonal_mul_diagonal,
    groupSize_mul_inv_cancel hg, Matrix.diagonal_one]

omit [Fintype n] in
/-- `D` broadcasts an individual-level vector to the observation level. Private
scaffolding for equation (17.19). -/
private theorem panelDummies_mulVec (g : n → ι) (v : ι → ℝ) :
    panelDummies g *ᵥ v = fun p => v (g p) := by
  ext p
  simp [panelDummies, Matrix.mulVec, dotProduct]

omit [Fintype ι] in
/-- `Dᵀ` sums an observation-level vector over each individual's observation set `Sⱼ`. Private
scaffolding for equation (17.19). -/
private theorem panelDummies_transpose_mulVec (g : n → ι) (y : n → ℝ) :
    (panelDummies g)ᵀ *ᵥ y = fun j => ∑ p ∈ Finset.univ.filter fun p => g p = j, y p := by
  ext j
  simp only [panelDummies, Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_filter]

/-- Hansen §17.8: the individual-specific mean `Ȳᵢ = (1/Tᵢ) ∑_{t ∈ Sᵢ} Yᵢₜ`.

An individual with no observations gets `Ȳᵢ = 0` by Mathlib's junk-value convention
(`(0 : ℝ)⁻¹ = 0`); every result below excludes that case via surjectivity of `g`. -/
noncomputable def individualMean (g : n → ι) (y : n → ℝ) : ι → ℝ :=
  fun j => (groupSize g j : ℝ)⁻¹ * ∑ p ∈ Finset.univ.filter fun p => g p = j, y p

/-- Hansen §17.8: the within transformation `Ẏᵢₜ = Yᵢₜ − Ȳᵢ`, which subtracts each
individual's own mean and so annihilates any individual-constant term. -/
noncomputable def withinTransform (g : n → ι) (y : n → ℝ) : n → ℝ :=
  fun p => y p - individualMean g y (g p)

/-- Hansen §17.8: the within transformation applied columnwise to a design matrix,
`Ẋ` in Hansen's notation. -/
noncomputable def withinTransformMatrix (g : n → ι) (X : Matrix n k ℝ) : Matrix n k ℝ :=
  Matrix.of fun p j => withinTransform g (fun q => X q j) p

variable [DecidableEq n]

/-- **Hansen equation (17.19)**, first clause: `M_D Y = Ẏ`. The residual from regressing
an outcome on the individual dummies is exactly its within transformation. -/
theorem annihilatorMatrix_panelDummies_mulVec {g : n → ι} (hg : Function.Surjective g)
    (y : n → ℝ) :
    letI := panelDummiesGramInvertible hg
    annihilatorMatrix (panelDummies g) *ᵥ y = withinTransform g y := by
  letI := panelDummiesGramInvertible hg
  rw [annihilator_mul_y_eq_closed_form_residual, invOf_panelDummies_gram hg,
    panelDummies_transpose_mulVec]
  have hdiag : (Matrix.diagonal fun j => ((groupSize g j : ℝ))⁻¹) *ᵥ
      (fun j => ∑ p ∈ Finset.univ.filter fun p => g p = j, y p) = individualMean g y := by
    ext j
    simp [individualMean, Matrix.mulVec_diagonal]
  rw [hdiag, panelDummies_mulVec]
  ext p
  simp [withinTransform]

/-- **Hansen equation (17.19)**, second clause: `M_D X = Ẋ`. The residualized regressors
of the Frisch-Waugh-Lovell decomposition, with the individual dummies partialled out, are
exactly the within-transformed regressors. -/
theorem residualizedRegressors_panelDummies {g : n → ι} (hg : Function.Surjective g)
    (X : Matrix n k ℝ) :
    letI := panelDummiesGramInvertible hg
    residualizedRegressors (panelDummies g) X = withinTransformMatrix g X := by
  letI := panelDummiesGramInvertible hg
  ext p j
  have h := congrFun (annihilatorMatrix_panelDummies_mulVec hg (fun q => X q j)) p
  simpa [residualizedRegressors, withinTransformMatrix, Matrix.mul_apply, Matrix.mulVec,
    dotProduct] using h

variable [Fintype k] [DecidableEq k]

/-- Hansen §17.9: the fixed effects (within) estimator `β̂_fe`, least squares of the
demeaned outcome `Ẏ` on the demeaned regressors `Ẋ`.

The `Invertible` hypothesis is Hansen's own caveat that `∑ᵢ Ẋᵢ' Ẋᵢ` be full rank, which
he notes "requires that all components of `Xᵢₜ` have time variation for at least some
individuals in the sample". -/
noncomputable def fixedEffectsBeta (g : n → ι) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible ((withinTransformMatrix g X)ᵀ * withinTransformMatrix g X)] : k → ℝ :=
  olsBeta (withinTransformMatrix g X) (withinTransform g y)

/-- Hansen §17.11, model (17.34): the dummy variable estimator of `β`, i.e. the `β` block
of the least squares regression of `Y` on the individuals' dummies together with `X`.

**Column ordering.** Hansen writes model (17.34) as `Y = Xβ + Du + ε`, i.e. with the
regressors first and the dummies second. This formalization regresses on `[D X]` instead,
because `Chapter3FWL` residualizes the *right* block against the left. The two designs
differ by a permutation of columns, so they produce the same `β` block and the same
residuals. (The *full* coefficient vectors live over `ι ⊕ k` and `k ⊕ ι` respectively and
are permutations of one another, not equal.) This equivalence is documented rather than
proved; see the chapter inventory for the follow-up that would close it.

Note also (Hansen §17.16) that `D` spans the constant vector, so an `X` that already
carries an intercept column makes `[D X]` rank deficient; the `Invertible` hypothesis
below is therefore doing real work. -/
noncomputable def dummyVariableBeta (g : n → ι) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible ((Matrix.fromCols (panelDummies g) X)ᵀ *
      Matrix.fromCols (panelDummies g) X)] : k → ℝ :=
  fromColsRightBeta (panelDummies g) X y

/-- Bridge lemma: transport invertibility of the within Gram matrix to the residualized
Gram matrix that `Chapter3FWL` states its hypotheses in. Private proof infrastructure; it
is a `def` rather than an `instance`, so each use site installs it with `letI`. -/
@[reducible] private noncomputable def residualizedGramInvertibleOfWithin
    {g : n → ι} (hg : Function.Surjective g) (X : Matrix n k ℝ)
    [hW : Invertible ((withinTransformMatrix g X)ᵀ * withinTransformMatrix g X)] :
    letI := panelDummiesGramInvertible hg
    Invertible ((residualizedRegressors (panelDummies g) X)ᵀ *
      residualizedRegressors (panelDummies g) X) :=
  letI := panelDummiesGramInvertible hg
  hW.copy _ (by rw [residualizedRegressors_panelDummies hg])

omit [DecidableEq n] in
/-- **Hansen Theorem 17.1**, coefficient clause: the fixed effects estimator of `β`
algebraically equals the dummy variable estimator of `β`.

No balancedness is assumed: the individuals may contribute different numbers of
observations, and the only panel hypothesis is that each contributes at least one.

Hansen's proof, followed here: by equation (17.19) the residuals from regressing on `D`
are the within transformations, so Frisch-Waugh-Lovell (Theorem 3.5) turns the `β` block
of the `[D X]` regression into least squares of `Ẏ` on `Ẋ`. -/
theorem fixedEffectsBeta_eq_dummyVariableBeta {g : n → ι} (hg : Function.Surjective g)
    (X : Matrix n k ℝ) (y : n → ℝ)
    [hW : Invertible ((withinTransformMatrix g X)ᵀ * withinTransformMatrix g X)]
    [Invertible ((Matrix.fromCols (panelDummies g) X)ᵀ *
      Matrix.fromCols (panelDummies g) X)] :
    fixedEffectsBeta g X y = dummyVariableBeta g X y := by
  classical
  letI := panelDummiesGramInvertible hg
  letI := residualizedGramInvertibleOfWithin hg X
  unfold fixedEffectsBeta dummyVariableBeta
  rw [fromColsRightBeta_eq_fwlBeta (panelDummies g) X y]
  unfold fwlBeta
  rw [annihilatorMatrix_panelDummies_mulVec hg]
  exact (olsBeta_congr (residualizedRegressors_panelDummies hg X) (withinTransform g y)).symm

omit [DecidableEq n] in
/-- **Hansen Theorem 17.1**, residual clause: the fixed effects and dummy variable
estimators have the same residuals. As with the coefficient clause, the panel need not be
balanced. -/
theorem fixedEffects_residual_eq_dummyVariable_residual {g : n → ι}
    (hg : Function.Surjective g) (X : Matrix n k ℝ) (y : n → ℝ)
    [hW : Invertible ((withinTransformMatrix g X)ᵀ * withinTransformMatrix g X)]
    [Invertible ((Matrix.fromCols (panelDummies g) X)ᵀ *
      Matrix.fromCols (panelDummies g) X)] :
    residual (withinTransformMatrix g X) (withinTransform g y) =
      residual (Matrix.fromCols (panelDummies g) X) y := by
  classical
  letI := panelDummiesGramInvertible hg
  letI := residualizedGramInvertibleOfWithin hg X
  have h := fwl_residual_eq_full_residual (panelDummies g) X y
  rw [annihilatorMatrix_panelDummies_mulVec hg] at h
  rw [← h]
  exact (residual_congr (residualizedRegressors_panelDummies hg X) (withinTransform g y)).symm

end HansenEconometrics
