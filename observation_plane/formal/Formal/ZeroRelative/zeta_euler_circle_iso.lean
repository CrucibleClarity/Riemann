import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith

/-!
# 欧拉圆正交 × 零点 (分裂度量判据)

欧拉圆正交观测 (习题 XXV) 的零点连接: 分裂度量 normSq = Re²-Im² 下,
半径 1 圆 (normSq=1) 与半径 i 圆 (normSq=-1) 正交且不相交
(circles_disjoint)。ζ 的零点处 Re ζ = Im ζ = 0 ⟹ normSq(ζ) = 0:
零点不在两个正交欧拉圆上, 而在它们之间的锥面 (normSq=0) 上。

诚实边界 (观测 M 评估): 这给出的是"零点避开欧拉圆"的判据, 不排除
离线零点 — Re/Im 拆分不区分在线/离线 (离线零点同样 Re=Im=0,
区别在共轭轨道类型 2 点 vs 4 点)。RH 缺口不变。

English: Euler circles: the two orthogonal Euler circles; divergence/period observations -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- 零点判定: ζ(z) = 0 ⟺ Re ζ(z) = 0 ∧ Im ζ(z) = 0 (副本: proof.lean 同定理). 
English: Zero criterion: ζ(z) = 0 ⟺ Re ζ(z) = 0 ∧ Im ζ(z) = 0 (duplicate of the same theorem in proof.lean). -/
theorem zeta_eq_zero_iff_re_im (z : ℂ) :
    riemannZeta z = 0 ↔ (riemannZeta z).re = 0 ∧ (riemannZeta z).im = 0 := by
  constructor
  · intro h
    constructor <;> simp [h]
  · intro h
    apply Complex.ext
    · exact h.1
    · exact h.2

/-- 零点在分裂锥面上: ζ(z) = 0 ⟹ normSq(ζ(z)) = Re²-Im² = 0. 
English: Zeros lie on the split cone: ζ(z) = 0 ⟹ normSq(ζ(z)) = Re²-Im² = 0. -/
theorem zero_split_normSq (z : ℂ) (hz : riemannZeta z = 0) :
    (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 = 0 := by
  have hri := (zeta_eq_zero_iff_re_im z).mp hz
  rw [hri.1, hri.2]
  norm_num

/-- 零点避开两个正交欧拉圆: normSq(ζ(z)) = 0 ≠ ±1
    (半径 1 圆 normSq=1 与半径 i 圆 normSq=-1 均不含零点). 
English: Zeros avoid the two orthogonal Euler circles: normSq(ζ(z)) = 0 ≠ ±1 (neither the radius-1 circle normSq=1 nor the radius-i circle normSq=-1 contains a zero). -/
theorem zero_not_on_euler_circles (z : ℂ) (hz : riemannZeta z = 0) :
    (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 ≠ 1 ∧
      (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 ≠ -1 := by
  have h0 := zero_split_normSq z hz
  constructor <;> linarith

end RiemannUnifiedObservation
