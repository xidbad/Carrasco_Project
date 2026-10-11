import Mathlib.Algebra.Quaternion
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Section 2.3 — basic objects

Rotations about the `X`-axis in `SO(3)`, diagonal matrices in `SU(2)`, and unit quaternions,
all parametrised by points of the unit circle.
-/

open Matrix Complex

noncomputable section

namespace Section23

/-- `SU(2)`. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
/-- `SO(3)`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ
/-- The unit quaternions `U = {q ∈ ℍ : q q* = 1}`. -/
abbrev UnitQuat := unitary (Quaternion ℝ)

/-- The rotation about the `X`-axis through the angle `θ`. -/
def rotX (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos θ, -Real.sin θ; 0, Real.sin θ, Real.cos θ]

/-- The rotation about the `Z`-axis, written as in Step 2 (the matrix `g₂`). -/
def rotZ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, Real.sin θ, 0; -Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- The matrix of a rotation about the `X`-axis given by a point `z` of the unit circle. -/
def rotXMat (z : Circle) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, (z : ℂ).re, -(z : ℂ).im; 0, (z : ℂ).im, (z : ℂ).re]

lemma circle_re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have := Circle.normSq_coe z
  rw [Complex.normSq_apply] at this
  nlinarith [this]

lemma rotXMat_mem (z : Circle) : rotXMat z ∈ SO3 := by
  have h := circle_re_sq_add_im_sq z
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotXMat, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [h]
  · simp [rotXMat, Matrix.det_fin_three]; nlinarith [h]

/-- Rotations about the `X`-axis as a group homomorphism from the circle to `SO(3)`. -/
def rotHom : Circle →* SO3 where
  toFun z := ⟨rotXMat z, rotXMat_mem z⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotXMat]
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotXMat, Circle.coe_mul] <;> ring

lemma rotHom_injective : Function.Injective rotHom := by
  intro z w h
  have h1 := congrArg (fun g : SO3 => (g : Matrix (Fin 3) (Fin 3) ℝ) 1 1) h
  have h2 := congrArg (fun g : SO3 => (g : Matrix (Fin 3) (Fin 3) ℝ) 2 1) h
  simp [rotHom, rotXMat] at h1 h2
  exact Circle.ext (Complex.ext h1 h2)

lemma rotXMat_exp (θ : ℝ) : rotXMat (Circle.exp θ) = rotX θ := by
  simp [rotXMat, rotX, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- The diagonal matrix `diag(z, z̄)` in `SU(2)`. -/
def diagMat (z : Circle) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(z : ℂ), 0; 0, (starRingEnd ℂ) (z : ℂ)]

lemma diagMat_mem (z : Circle) : diagMat z ∈ SU2 := by
  have h := Circle.normSq_coe z
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
        Complex.mul_conj, h]
  · simp [diagMat, Matrix.det_fin_two, Complex.mul_conj, h]

/-- `z ↦ diag(z, z̄)` as a group homomorphism from the circle to `SU(2)`. -/
def diagHom : Circle →* SU2 where
  toFun z := ⟨diagMat z, diagMat_mem z⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagMat]
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagMat, Circle.coe_mul]

lemma diagHom_injective : Function.Injective diagHom := by
  intro z w h
  have h1 := congrArg (fun g : SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  sorry-- simpa? [diagHom, diagMat] using h1

lemma diagMat_eq_inv (z : Circle) : diagMat z = !![(z : ℂ), 0; 0, (z : ℂ)⁻¹] := by
  rw [diagMat, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

/-- The quaternion `re z + (im z) i`. -/
def quatOf (z : Circle) : Quaternion ℝ := ⟨(z : ℂ).re, (z : ℂ).im, 0, 0⟩

lemma quatOf_mem (z : Circle) : quatOf z ∈ UnitQuat := by
  have h := circle_re_sq_add_im_sq z
  rw [Unitary.mem_iff]
  constructor <;> ext <;> simp [quatOf] <;> sorry -- nlinarith [h]

/-- `z ↦ re z + (im z) i` as a group homomorphism from the circle to the unit quaternions. -/
def quatHom : Circle →* UnitQuat where
  toFun z := ⟨quatOf z, quatOf_mem z⟩
  map_one' := by
    apply Subtype.ext
    ext <;> simp [quatOf] <;> sorry
  map_mul' z w := by
    apply Subtype.ext
    ext <;> simp [quatOf, Circle.coe_mul]

end Section23

#min_imports
