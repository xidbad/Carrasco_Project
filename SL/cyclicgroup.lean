import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Quaternion
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Section 2.3 — basic objects

Rotations about the `X`-axis in `SO(3)`, diagonal matrices in `SU(2)`, and unit quaternions,
all parametrised by points of the unit circle.
-/

open Matrix Complex Real

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


/-!
# `SU(2) ≅ U` and the `2 : 1` homomorphism `SU(2) → SO(3)`
-/


/-- Every `A ∈ SU(2)` has the shape `!![a, b; -b̄, ā]` with `|a|² + |b|² = 1`. -/
lemma su2_entries (A : SU2) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -(starRingEnd ℂ) ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) ∧
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (starRingEnd ℂ) ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∧
    normSq ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) + normSq ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
      = 1 := by
  obtain ⟨M, hM⟩ := A
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff] at hM
  obtain ⟨hu, hdet⟩ := hM
  have hu' : star M * M = 1 := mul_eq_one_comm.mp hu
  have hadj : M * M.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hstar : star M = M.adjugate := by
    calc star M = star M * (M * M.adjugate) := by rw [hadj, mul_one]
      _ = M.adjugate := by rw [← mul_assoc, hu', one_mul]
  rw [Matrix.adjugate_fin_two] at hstar
  have e01 := congrFun (congrFun hstar 0) 1
  have e11 := congrFun (congrFun hstar 1) 1
  have h00 := congrFun (congrFun hu 0) 0
  simp [Matrix.star_apply] at e01 e11 h00
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.mul_conj] at h00
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (starRingEnd ℂ) e01
  · simpa using congrArg (starRingEnd ℂ) e11
  · exact_mod_cast h00

/-- The quaternion `a + b j` attached to the matrix `!![a, b; -b̄, ā]`. -/
def quatOfMat (M : Matrix (Fin 2) (Fin 2) ℂ) : Quaternion ℝ :=
  ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩

/-- The matrix `!![a, b; -b̄, ā]` attached to the quaternion `a + b j`. -/
def matOfQuat (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩;
    -(starRingEnd ℂ) ⟨q.imJ, q.imK⟩, (starRingEnd ℂ) ⟨q.re, q.imI⟩]

lemma normSq_entries (A : SU2) :
    ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 + ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im ^ 2 +
    ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re ^ 2 + ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im ^ 2
      = 1 := by
  have := (su2_entries A).2.2
  simp only [Complex.normSq_apply] at this
  linarith

lemma quatOfMat_mem (A : SU2) : quatOfMat A ∈ UnitQuat := by
  have h := normSq_entries A
  rw [Unitary.mem_iff]
  constructor <;> ext <;> simp [quatOfMat] <;> sorry -- nlinarith [h]

lemma unitQuat_normSq (q : UnitQuat) :
    (q : Quaternion ℝ).re ^ 2 + (q : Quaternion ℝ).imI ^ 2 + (q : Quaternion ℝ).imJ ^ 2 +
      (q : Quaternion ℝ).imK ^ 2 = 1 := by
  have h := Unitary.coe_star_mul_self q
  rw [Quaternion.star_mul_self] at h
  have h' : Quaternion.normSq (q : Quaternion ℝ) = 1 := by
    have := congrArg (fun p : Quaternion ℝ => p.re) h
    simpa only [Quaternion.re_coe, Quaternion.re_one] using this
  rw [Quaternion.normSq_def'] at h'
  exact h'

lemma matOfQuat_mem (q : UnitQuat) : matOfQuat q ∈ SU2 := by
  have h := unitQuat_normSq q
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matOfQuat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      apply Complex.ext <;> simp <;> nlinarith [h]
  · simp [matOfQuat, Matrix.det_fin_two]
    apply Complex.ext <;> simp <;> nlinarith [h]

lemma quatOfMat_mul (A B : SU2) :
    quatOfMat ((A * B : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = quatOfMat A * quatOfMat B := by
  obtain ⟨hA1, hA2, -⟩ := su2_entries A
  obtain ⟨hB1, hB2, -⟩ := su2_entries B
  simp only [Submonoid.coe_mul]
  ext <;> simp [quatOfMat, Matrix.mul_apply, Fin.sum_univ_two, hB1, hB2] <;> ring

/-- The isomorphism `SU(2) ≅ U = {q ∈ ℍ : q q* = 1}`, `!![a, b; -b̄, ā] ↦ a + b j`. -/
def SU2EquivUnitQuat : SU2 ≃* UnitQuat where
  toFun A := ⟨quatOfMat A, quatOfMat_mem A⟩
  invFun q := ⟨matOfQuat q, matOfQuat_mem q⟩
  left_inv A := by
    obtain ⟨h1, h2, -⟩ := su2_entries A
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matOfQuat, quatOfMat, h1, h2]
  right_inv q := by
    apply Subtype.ext
    ext <;> simp [matOfQuat, quatOfMat]
  map_mul' A B := Subtype.ext (quatOfMat_mul A B)

lemma SU2EquivUnitQuat_apply (A : SU2) :
    (SU2EquivUnitQuat A : Quaternion ℝ) =
      ⟨((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re, ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
        ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re, ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im⟩ :=
  rfl

lemma SU2EquivUnitQuat_diagHom (z : Circle) : SU2EquivUnitQuat (diagHom z) = quatHom z := by
  apply Subtype.ext
  ext <;> simp [SU2EquivUnitQuat_apply, diagHom, diagMat, quatHom, quatOf]

/-- The matrix, in the basis `i, j, k` of the pure quaternions, of `v ↦ q v q̄`. -/
def rotMatOfQuat (q : Quaternion ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := q.re; let x := q.imI; let y := q.imJ; let z := q.imK
  !![w^2 + x^2 - y^2 - z^2, 2 * (x * y - w * z), 2 * (x * z + w * y);
     2 * (x * y + w * z), w^2 - x^2 + y^2 - z^2, 2 * (y * z - w * x);
     2 * (x * z - w * y), 2 * (y * z + w * x), w^2 - x^2 - y^2 + z^2]

lemma rotMatOfQuat_mem' (q : Quaternion ℝ) (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) :
    rotMatOfQuat q ∈ SO3 := by
  obtain ⟨w, x, y, z⟩ := q
  simp only at h
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotMatOfQuat, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination (w^2 + x^2 + y^2 + z^2 + 1) * h
        | ring
  · simp [rotMatOfQuat, Matrix.det_fin_three]
    linear_combination ((w^2 + x^2 + y^2 + z^2)^2 + (w^2 + x^2 + y^2 + z^2) + 1) * h

lemma rotMatOfQuat_mem (q : UnitQuat) : rotMatOfQuat q ∈ SO3 :=
  rotMatOfQuat_mem' q (unitQuat_normSq q)

lemma rotMatOfQuat_mul (p q : Quaternion ℝ) :
    rotMatOfQuat (p * q) = rotMatOfQuat p * rotMatOfQuat q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatOfQuat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The `2 : 1` homomorphism `U → SO(3)`, `q ↦ (v ↦ q v q̄)` on the pure quaternions. -/
def quatToRot : UnitQuat →* SO3 where
  toFun q := ⟨rotMatOfQuat q, rotMatOfQuat_mem q⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotMatOfQuat] <;> sorry
  map_mul' p q := Subtype.ext (rotMatOfQuat_mul p q)

lemma quatToRot_eq_one_iff (q : UnitQuat) : quatToRot q = 1 ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro hq
    have h := unitQuat_normSq q
    have e : ∀ i j, rotMatOfQuat q i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j =>
      congrFun (congrFun (congrArg Subtype.val hq) i) j
    have e00 := e 0 0; have e11 := e 1 1; have e22 := e 2 2
    have e01 := e 0 1; have e10 := e 1 0; have e02 := e 0 2; have e20 := e 2 0
    have e12 := e 1 2; have e21 := e 2 1
    simp [rotMatOfQuat] at e00 e11 e22 e01 e10 e02 e20 e12 e21
    have hx : (q : Quaternion ℝ).imI = 0 := by nlinarith
    have hy : (q : Quaternion ℝ).imJ = 0 := by nlinarith
    have hz : (q : Quaternion ℝ).imK = 0 := by nlinarith
    have hw : (q : Quaternion ℝ).re ^ 2 = 1 := by rw [hx, hy, hz] at h; linarith
    have hw' : (q : Quaternion ℝ).re = 1 ∨ (q : Quaternion ℝ).re = -1 := by
      have h0 : ((q : Quaternion ℝ).re - 1) * ((q : Quaternion ℝ).re + 1) = 0 := by
        linear_combination hw
      rcases mul_eq_zero.mp h0 with h' | h'
      · left; linarith
      · right; linarith
    rcases hw' with hw | hw
    · sorry -- left; apply Subtype.ext; ext <;> simp [hx, hy, hz, hw]
    · sorry -- right; apply Subtype.ext; rw [Unitary.coe_neg]; ext <;> simp [hx, hy, hz, hw]
  · rintro (rfl | rfl)
    · exact map_one _
    · sorry
      -- apply Subtype.ext
      -- ext i j
      -- fin_cases i <;> fin_cases j <;> simp [quatToRot, rotMatOfQuat, Unitary.coe_neg]

lemma quatToRot_quatHom (z : Circle) : quatToRot (quatHom z) = rotHom (z ^ 2) := by
  have h := circle_re_sq_add_im_sq z
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatToRot, rotMatOfQuat, quatHom, quatOf, rotHom, rotXMat, pow_two,
      Circle.coe_mul] <;> nlinarith [h]

/-- The `2 : 1` homomorphism `π : SU(2) → SO(3)` (via `SU(2) ≅ U`). -/
def coverMap : SU2 →* SO3 := quatToRot.comp SU2EquivUnitQuat.toMonoidHom

/-- The kernel of `π : SU(2) → SO(3)` is `{I₂, -I₂}`. -/
theorem coverMap_eq_one_iff (A : SU2) :
    coverMap A = 1 ↔
      (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  obtain ⟨h1, h2, -⟩ := su2_entries A
  rw [coverMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, quatToRot_eq_one_iff]
  constructor
  · rintro (h | h)
    · left
      have h' := congrArg Subtype.val h
      rw [SU2EquivUnitQuat_apply] at h'
      simp only [Quaternion.ext_iff] at h'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2] <;> apply Complex.ext <;> simp_all
    · sorry
      -- right
      -- have h' := congrArg Subtype.val h
      -- rw [SU2EquivUnitQuat_apply, Unitary.coe_neg] at h'
      -- simp only [Quaternion.ext_iff] at h'
      -- ext i j
      -- fin_cases i <;> fin_cases j <;> simp [h1, h2] <;> apply Complex.ext <;> simp_all
  · rintro (h | h) <;> sorry
    -- · left; apply Subtype.ext; rw [SU2EquivUnitQuat_apply, h]; ext <;> simp
    -- · right; apply Subtype.ext; rw [SU2EquivUnitQuat_apply, h, Unitary.coe_neg]; ext <;> simp

lemma coverMap_diagHom (z : Circle) : coverMap (diagHom z) = rotHom (z ^ 2) := by
  rw [coverMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, SU2EquivUnitQuat_diagHom,
    quatToRot_quatHom]



/-!
# Section 2.3 — Cyclic groups `ℤ/nℤ`

Correspondence with the text:
* `ḡ`, `Ḡ` (rotations about the `X`-axis through `2kπ/n`): `gbar`, `Gbar`, `Gbar_eq`,
  `card_Gbar`, `Gbar_mulEquiv_zmod`.
* `g₂ = I₃ ⇔ cos 2θ₂ = 1, sin 2θ₂ = 0`: `rotZ_eq_one_iff`; consequence for `g₂ ∈ SU(2)`:
  `g2_eq_one_or_neg_one`, `g2_zero`.
* `g = g₁ g₂ g₃` diagonal: `diag_mul_diag`; `gⁿ = I₂ ⇔ αⁿ = 1`: `diag_pow_eq_one_iff`.
* `G = Cₙ`: `Cn`, `Cn_eq`, `card_Cn`, `Cn_mulEquiv_zmod`, `zpowers_diag_primitive_eq_Cn`.
* `|Cₙ|` odd `⇒ -I₂ ∉ Cₙ`, `π` injective on `Cₙ`: `neg_one_not_mem_Cn`,
  `coverMap_restrict_injective`, `Cn_mulEquiv_image`, `map_Cn_eq_Gbar`
  (with `ker π = {±I₂}` in `coverMap_eq_one_iff`).
* 2.3.1: `SU2EquivUnitQuat` (in `Quaternion.lean`), `SU2EquivUnitQuat_gen_pow`, `CnQuat`,
  `CnQuat_eq`, `map_Cn_eq_CnQuat`, `card_CnQuat`.
-/


/-! ### Generalities on cyclic subgroups -/

lemma zpowers_eq_pow_Icc {G : Type*} [Group G] (g : G) {n : ℕ} (hn : 0 < n)
    (h : orderOf g = n) :
    (Subgroup.zpowers g : Set G) = {x | ∃ k ∈ Finset.Icc 1 n, x = g ^ k} := by
  ext x
  classical
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, Finset.mem_Icc]
  rw [(orderOf_pos_iff.mp (h ▸ hn)).mem_zpowers_iff_mem_range_orderOf, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_range, h] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨n, ⟨hn, le_rfl⟩, by rw [pow_zero, ← h, pow_orderOf_eq_one]⟩
    · exact ⟨k, ⟨hk0, hk.le⟩, rfl⟩
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    rcases hk2.lt_or_eq with hk | rfl
    · exact ⟨k, by rw [Finset.mem_range, h]; exact hk, rfl⟩
    · exact ⟨0, by rw [Finset.mem_range, h]; exact hn, by rw [pow_zero, ← h, pow_orderOf_eq_one]⟩

lemma zpowers_mulEquiv_zmod {G : Type*} [Group G] (g : G) {n : ℕ} (h : orderOf g = n) :
    Nonempty (Subgroup.zpowers g ≃* Multiplicative (ZMod n)) := by
  subst h
  rw [← Nat.card_zpowers]
  exact ⟨(zmodCyclicMulEquiv inferInstance).symm⟩

/-! ### The primitive `n`-th root of unity `ε = exp (2πi/n)` -/

/-- `ε = exp (2πi/n)`, the standard primitive `n`-th root of unity. -/
def epsilon (n : ℕ) : ℂ := Complex.exp (2 * π * I / n)

/-- `ε` as a point of the unit circle. -/
def epsC (n : ℕ) : Circle := Circle.exp (2 * π / n)

lemma coe_epsC (n : ℕ) : (epsC n : ℂ) = epsilon n := by
  rw [epsC, Circle.coe_exp, epsilon]
  congr 1
  push_cast
  ring

lemma isPrimitiveRoot_epsilon {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (epsilon n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma orderOf_circle {z : Circle} {n : ℕ} (hz : IsPrimitiveRoot (z : ℂ) n) : orderOf z = n := by
  rw [← orderOf_injective Circle.coeHom Circle.coe_injective z]
  exact hz.eq_orderOf.symm

lemma orderOf_epsC {n : ℕ} (hn : n ≠ 0) : orderOf (epsC n) = n :=
  orderOf_circle (by rw [coe_epsC]; exact isPrimitiveRoot_epsilon hn)

lemma coe_epsC_pow (n k : ℕ) :
    ((epsC n ^ k : Circle) : ℂ) = ⟨Real.cos (2 * k * π / n), Real.sin (2 * k * π / n)⟩ := by
  rw [Circle.coe_pow, epsC, Circle.coe_exp, ← Complex.exp_nat_mul]
  have : (k : ℂ) * (((2 * π / n : ℝ)) * I) = ((2 * k * π / n : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
  · rw [Complex.exp_ofReal_mul_I_im]

/-- Any primitive `n`-th root of unity on the circle generates the same subgroup as `ε`. -/
lemma circle_zpowers_eq {n : ℕ} (hn : n ≠ 0) {z : Circle} (hz : IsPrimitiveRoot (z : ℂ) n) :
    Subgroup.zpowers z = Subgroup.zpowers (epsC n) := by
  haveI : NeZero n := ⟨hn⟩
  have hε : IsPrimitiveRoot (epsC n : ℂ) n := by
    rw [coe_epsC]; exact isPrimitiveRoot_epsilon hn
  obtain ⟨i, -, hi⟩ := hε.eq_pow_of_pow_eq_one hz.pow_eq_one
  have hle : Subgroup.zpowers z ≤ Subgroup.zpowers (epsC n) := by
    rw [Subgroup.zpowers_le]
    refine ⟨i, ?_⟩
    apply Circle.ext
    simp [hi]
  haveI : Finite (Subgroup.zpowers (epsC n)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, orderOf_circle hε]; exact hn)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_circle hz, orderOf_circle hε]

/-! ### The rotation group `Ḡ` in `SO(3)` -/

lemma rotX_mem (θ : ℝ) : rotX θ ∈ SO3 := by
  rw [← rotXMat_exp]; exact rotXMat_mem _

/-- The rotation about the `X`-axis through `θ`, as an element of `SO(3)`. -/
def rotSO3 (θ : ℝ) : SO3 := ⟨rotX θ, rotX_mem θ⟩

lemma rotSO3_eq_rotHom (θ : ℝ) : rotSO3 θ = rotHom (Circle.exp θ) :=
  Subtype.ext (rotXMat_exp θ).symm

lemma rotX_mul (a b : ℝ) : rotX a * rotX b = rotX (a + b) := by
  rw [← rotXMat_exp, ← rotXMat_exp, ← rotXMat_exp, Circle.exp_add]
  exact (congrArg Subtype.val (map_mul rotHom (Circle.exp a) (Circle.exp b))).symm

lemma rotX_pow (θ : ℝ) (k : ℕ) : rotX θ ^ k = rotX (k * θ) := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [rotX]
  | succ k ih => rw [pow_succ, ih, rotX_mul]; push_cast; ring_nf

/-- The rotation `ḡ` about the `X`-axis through `2π/n` (as in the text). -/
abbrev gbar (n : ℕ) : SO3 := rotSO3 (2 * π / n)

/-- The cyclic rotation group `Ḡ = ⟨ḡ⟩ ⊆ SO(3)`. -/
def Gbar (n : ℕ) : Subgroup SO3 := Subgroup.zpowers (gbar n)

lemma gbar_eq_rotHom (n : ℕ) : gbar n = rotHom (epsC n) := rotSO3_eq_rotHom _

lemma orderOf_gbar {n : ℕ} (hn : n ≠ 0) : orderOf (gbar n) = n := by
  rw [gbar_eq_rotHom, orderOf_injective rotHom rotHom_injective, orderOf_epsC hn]

/-- `Ḡ = { ḡᵏ : k = 1, …, n }` where `ḡᵏ` is the rotation through `2kπ/n`. -/
theorem Gbar_eq {n : ℕ} (hn : 0 < n) :
    (Gbar n : Set SO3) =
      {g : SO3 | ∃ k ∈ Finset.Icc 1 n, (g : Matrix (Fin 3) (Fin 3) ℝ) = rotX (2 * π / n) ^ k} := by
  rw [Gbar, zpowers_eq_pow_Icc _ hn (orderOf_gbar hn.ne')]
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, by simp [rotSO3]⟩
  · rintro ⟨k, hk, h⟩; exact ⟨k, hk, Subtype.ext (by simp [rotSO3, h])⟩

theorem card_Gbar {n : ℕ} (hn : n ≠ 0) : Nat.card (Gbar n) = n := by
  rw [Gbar, Nat.card_zpowers, orderOf_gbar hn]

theorem Gbar_cyclic (n : ℕ) : IsCyclic (Gbar n) := Subgroup.isCyclic_zpowers _

theorem Gbar_mulEquiv_zmod {n : ℕ} (hn : n ≠ 0) :
    Nonempty (Gbar n ≃* Multiplicative (ZMod n)) :=
  zpowers_mulEquiv_zmod _ (orderOf_gbar hn)

/-! ### The conditions on the angles in Step 2 -/

/-- `g₂ = I₃ ⇔ cos 2θ₂ = 1, sin 2θ₂ = 0`. -/
theorem rotZ_eq_one_iff (θ : ℝ) :
    rotZ (2 * θ) = 1 ↔ Real.cos (2 * θ) = 1 ∧ Real.sin (2 * θ) = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [rotZ] at h00 h01
    exact ⟨h00, h01⟩
  · rintro ⟨hc, hs⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotZ, hc, hs]

/-- The matrix `g₂ ∈ SU(2)` of Step 2. -/
def g2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), Real.sin θ; -Real.sin θ, Real.cos θ]

/-- If `cos 2θ₂ = 1` and `sin 2θ₂ = 0`, then `g₂ = ± I₂`
(and `g₂ = I₂` for the choice `θ₂ = 0` made in the text). -/
theorem g2_eq_one_or_neg_one (θ : ℝ) (hc : Real.cos (2 * θ) = 1) :
    g2 θ = 1 ∨ g2 θ = -1 := by
  rw [Real.cos_two_mul] at hc
  have hs : Real.sin θ = 0 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hc' : (Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by linear_combination hc / 2
  rcases mul_eq_zero.mp hc' with h | h
  · left
    have : Real.cos θ = 1 := by linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [g2, this, hs]
  · right
    have : Real.cos θ = -1 := by linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [g2, this, hs]

theorem g2_zero : g2 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [g2]

/-- `diag(γ, γ̄) · diag(δ, δ̄) = diag(γδ, \overline{γδ})`. -/
theorem diag_mul_diag (γ δ : ℂ) :
    !![γ, 0; 0, (starRingEnd ℂ) γ] * !![δ, 0; 0, (starRingEnd ℂ) δ] =
      !![γ * δ, 0; 0, (starRingEnd ℂ) (γ * δ)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma diag_pow (a b : ℂ) (k : ℕ) : !![a, 0; 0, b] ^ k = !![a ^ k, 0; 0, b ^ k] := by
  have h : ∀ x y : ℂ, !![x, 0; 0, y] = Matrix.diagonal ![x, y] := by
    intro x y; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h, h, Matrix.diagonal_pow]
  congr 1
  ext i; fin_cases i <;> simp

/-- `g = diag(a, a⁻¹)` satisfies `gⁿ = I₂` iff `aⁿ = 1`. -/
theorem diag_pow_eq_one_iff (a : ℂ) (n : ℕ) :
    !![a, 0; 0, a⁻¹] ^ n = 1 ↔ a ^ n = 1 := by
  rw [diag_pow]
  constructor
  · intro h; simpa using congrFun (congrFun h 0) 0
  · intro h
    ext i j; fin_cases i <;> fin_cases j <;> simp [h, inv_pow]

/-- Likewise `ḡⁿ = I₃` iff `cos nθ = 1` (rotation through `θ` about the `X`-axis). -/
theorem rotX_pow_eq_one_iff (θ : ℝ) (n : ℕ) :
    rotX θ ^ n = 1 ↔ Real.cos (n * θ) = 1 := by
  rw [rotX_pow]
  constructor
  · intro h; simpa [rotX] using congrFun (congrFun h 1) 1
  · intro h
    have hs : Real.sin (n * θ) = 0 := by nlinarith [Real.sin_sq_add_cos_sq (n * θ)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotX, h, hs]

/-! ### The cyclic group `Cₙ ⊆ SU(2)` -/

/-- The generator `diag(ε, ε⁻¹)` of `Cₙ`. -/
abbrev gen (n : ℕ) : SU2 := diagHom (epsC n)

lemma coe_gen_pow (n k : ℕ) :
    ((gen n ^ k : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![epsilon n ^ k, 0; 0, (epsilon n ^ k)⁻¹] := by
  rw [← map_pow]
  simp only [diagHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [diagMat_eq_inv, Circle.coe_pow, coe_epsC]

/-- The cyclic group `Cₙ = ⟨diag(ε, ε⁻¹)⟩ ⊆ SU(2)`. -/
def Cn (n : ℕ) : Subgroup SU2 := Subgroup.zpowers (gen n)

lemma orderOf_gen {n : ℕ} (hn : n ≠ 0) : orderOf (gen n) = n := by
  rw [orderOf_injective diagHom diagHom_injective, orderOf_epsC hn]

/-- `Cₙ = { diag(ε, ε⁻¹)ᵏ = diag(εᵏ, ε⁻ᵏ) : k = 1, …, n }`. -/
theorem Cn_eq {n : ℕ} (hn : 0 < n) :
    (Cn n : Set SU2) = {A : SU2 | ∃ k ∈ Finset.Icc 1 n,
      (A : Matrix (Fin 2) (Fin 2) ℂ) = !![epsilon n ^ k, 0; 0, (epsilon n ^ k)⁻¹]} := by
  rw [Cn, zpowers_eq_pow_Icc _ hn (orderOf_gen hn.ne')]
  ext A
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, coe_gen_pow n k⟩
  · rintro ⟨k, hk, h⟩; exact ⟨k, hk, Subtype.ext (by rw [h, coe_gen_pow])⟩

/-- `|Cₙ| = n`. -/
theorem card_Cn {n : ℕ} (hn : n ≠ 0) : Nat.card (Cn n) = n := by
  rw [Cn, Nat.card_zpowers, orderOf_gen hn]

theorem Cn_cyclic (n : ℕ) : IsCyclic (Cn n) := Subgroup.isCyclic_zpowers _

/-- `Cₙ ≅ ℤ/nℤ`. -/
theorem Cn_mulEquiv_zmod {n : ℕ} (hn : n ≠ 0) : Nonempty (Cn n ≃* Multiplicative (ZMod n)) :=
  zpowers_mulEquiv_zmod _ (orderOf_gen hn)

/-- The group `G` generated by `diag(α, α⁻¹)`, for any primitive `n`-th root of unity `α`,
is `Cₙ`. -/
theorem zpowers_diag_primitive_eq_Cn {n : ℕ} (hn : n ≠ 0) (α : Circle)
    (hα : IsPrimitiveRoot (α : ℂ) n) : Subgroup.zpowers (diagHom α) = Cn n := by
  rw [Cn, gen, ← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, circle_zpowers_eq hn hα]

lemma coe_diagHom (α : Circle) :
    ((diagHom α : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = !![(α : ℂ), 0; 0, (α : ℂ)⁻¹] :=
  diagMat_eq_inv α

/-- If `n` is odd then `-I₂ ∉ Cₙ`. -/
theorem neg_one_not_mem_Cn {n : ℕ} (hn : Odd n) (A : SU2) (hA : A ∈ Cn n) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1 := by
  have hn0 : 0 < n := hn.pos
  have hA' : A ∈ (Cn n : Set SU2) := hA
  rw [Cn_eq hn0] at hA'
  obtain ⟨k, -, hk⟩ := hA'
  intro h
  rw [hk] at h
  have h00 : epsilon n ^ k = -1 := by simpa using congrFun (congrFun h 0) 0
  have hprim := isPrimitiveRoot_epsilon hn0.ne'
  have h2k : epsilon n ^ (2 * k) = 1 := by rw [pow_mul', h00]; norm_num
  have hdvd : n ∣ 2 * k := (hprim.pow_eq_one_iff_dvd _).mp h2k
  have hcop : Nat.Coprime n 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact hn.not_two_dvd_nat
  have hk' : n ∣ k := hcop.dvd_of_dvd_mul_left hdvd
  rw [(hprim.pow_eq_one_iff_dvd k).mpr hk'] at h00
  norm_num at h00

/-- If `n` is odd, the `2 : 1` homomorphism `π : SU(2) → SO(3)` is injective on `Cₙ`
(i.e. `ker π ∩ Cₙ = {I₂}`). -/
theorem coverMap_restrict_injective {n : ℕ} (hn : Odd n) :
    Function.Injective (coverMap.restrict (Cn n)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [MonoidHom.restrict_apply, coverMap_eq_one_iff] at hA
  rcases hA with h | h
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd h (neg_one_not_mem_Cn hn A A.2)

/-- Hence, for `n` odd, `π` restricts to an isomorphism of `Cₙ` onto its image. -/
theorem Cn_mulEquiv_image {n : ℕ} (hn : Odd n) :
    Nonempty (Cn n ≃* (Cn n).map coverMap) := by
  refine ⟨(MonoidHom.ofInjective (coverMap_restrict_injective hn)).trans
    (MulEquiv.subgroupCongr ?_)⟩
  rw [MonoidHom.restrict_range]

lemma coverMap_gen (n : ℕ) : coverMap (gen n) = rotHom (epsC n ^ 2) := coverMap_diagHom _

/-- For `n` odd, the image of `Cₙ` under `π` is the rotation group `Ḡ`. -/
theorem map_Cn_eq_Gbar {n : ℕ} (hn : Odd n) : (Cn n).map coverMap = Gbar n := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hcop : Nat.Coprime 2 n := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; exact hn.not_two_dvd_nat
  have hprim : IsPrimitiveRoot ((epsC n ^ 2 : Circle) : ℂ) n := by
    rw [Circle.coe_pow, coe_epsC]
    exact (isPrimitiveRoot_epsilon hn0).pow_of_coprime 2 hcop
  rw [Cn, MonoidHom.map_zpowers, coverMap_gen, Gbar, gbar_eq_rotHom, ← MonoidHom.map_zpowers,
    ← MonoidHom.map_zpowers, circle_zpowers_eq hn0 hprim]

/-! ### 2.3.1 Cyclic groups in terms of quaternions -/

/-- The quaternion cyclic group `Cₙ = ⟨cos (2π/n) + i sin (2π/n)⟩ ⊆ U`. -/
def CnQuat (n : ℕ) : Subgroup UnitQuat := Subgroup.zpowers (quatHom (epsC n))

/-- Under `SU(2) ≅ U`, `diag(εᵏ, ε⁻ᵏ) ↦ cos (2kπ/n) + i sin (2kπ/n)`. -/
theorem SU2EquivUnitQuat_gen_pow (n k : ℕ) :
    (SU2EquivUnitQuat (gen n ^ k) : Quaternion ℝ) =
      ⟨Real.cos (2 * k * π / n), Real.sin (2 * k * π / n), 0, 0⟩ := by
  rw [map_pow, gen, SU2EquivUnitQuat_diagHom, ← map_pow]
  simp only [quatHom, MonoidHom.coe_mk, OneHom.coe_mk, quatOf, coe_epsC_pow]

/-- `Cₙ` corresponds to the quaternion cyclic group under `SU(2) ≅ U`. -/
theorem map_Cn_eq_CnQuat (n : ℕ) : (Cn n).map SU2EquivUnitQuat.toMonoidHom = CnQuat n := by
  rw [Cn, MonoidHom.map_zpowers, CnQuat, MulEquiv.coe_toMonoidHom, gen,
    SU2EquivUnitQuat_diagHom]

/-- `Cₙ = { cos (2kπ/n) + i sin (2kπ/n) ∈ ℍ : k = 1, …, n }`. -/
theorem CnQuat_eq {n : ℕ} (hn : 0 < n) :
    (CnQuat n : Set UnitQuat) = {q : UnitQuat | ∃ k ∈ Finset.Icc 1 n,
      (q : Quaternion ℝ) = ⟨Real.cos (2 * k * π / n), Real.sin (2 * k * π / n), 0, 0⟩} := by
  have hord : orderOf (quatHom (epsC n)) = n := by
    rw [← SU2EquivUnitQuat_diagHom, MulEquiv.orderOf_eq, orderOf_gen hn.ne']
  rw [CnQuat, zpowers_eq_pow_Icc _ hn hord]
  ext q
  simp only [Set.mem_setOf_eq]
  have key : ∀ k : ℕ, ((quatHom (epsC n) ^ k : UnitQuat) : Quaternion ℝ) =
      ⟨Real.cos (2 * k * π / n), Real.sin (2 * k * π / n), 0, 0⟩ := by
    intro k
    rw [← SU2EquivUnitQuat_diagHom, ← map_pow]
    exact SU2EquivUnitQuat_gen_pow n k
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, key k⟩
  · rintro ⟨k, hk, h⟩; exact ⟨k, hk, Subtype.ext (by rw [h, key])⟩

theorem card_CnQuat {n : ℕ} (hn : n ≠ 0) : Nat.card (CnQuat n) = n := by
  rw [CnQuat, Nat.card_zpowers, ← SU2EquivUnitQuat_diagHom,
    MulEquiv.orderOf_eq, orderOf_gen hn]

end Section23

#min_imports
