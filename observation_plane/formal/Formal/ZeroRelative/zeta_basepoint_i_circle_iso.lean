import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# T 坐标 (基点 i): 临界线 = 单位圆 — 平移反演可消的 0pat 形式

观测 AB 的形式化: T(z) = 1/(z-i) - 1 (recip 中心 = 复平面基点 i,
平移 -1 消圆心) 把临界线映到单位圆:
  Re z = 1/2 ⟺ ‖1/(z-i) - 1‖ = 1

深层结构 (等距本质): 临界线 = i 与 1+i 的垂直平分线
  Re z = 1/2 ⟺ ‖z-i‖ = ‖z-(1+i)‖
recip 1/(z-i) 利用这个等距: |1/(z-i) - 1| = |(1+i)-z|/|z-i| = 1。

这是 recip_on_critical_circle_iff (1/z 版) 的基点 i 版本 —
recip 中心取虚轴上任意点 (Re c = 0) 时, 像恒为圆心 1 半径 1 的圆
(只依赖临界线 Re = 1/2 的平移不变性), 平移 -1 恰好把圆心消到 0。

English: i-basepoint circle: the unit circle centered at i, the image of the critical line -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- 临界线 = i 与 1+i 的垂直平分线 (基点 i 坐标的等距判据):
    Re z = 1/2 ⟺ ‖z-i‖ = ‖z-(1+i)‖。 
English: The critical line is the perpendicular bisector of i and 1+i (the equidistance criterion in basepoint-i coordinates): Re z = 1/2 ⟺ ‖z-i‖ = ‖z-(1+i)‖. -/
theorem critical_line_equidistant_basepoint_i (z : ℂ) :
    z.re = 1 / 2 ↔ ‖z - Complex.I‖ = ‖z - (1 + Complex.I)‖ := by
  constructor
  · intro hre
    -- 平方相等 (normSq 展开 + hre)
    have hsq : ‖z - Complex.I‖ ^ 2 = ‖z - (1 + Complex.I)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      rw [hre]
      ring
    -- 非负 ⟹ 平方等式到等式
    have habs : |‖z - Complex.I‖| = |‖z - (1 + Complex.I)‖| :=
      (sq_eq_sq_iff_abs_eq_abs ‖z - Complex.I‖ ‖z - (1 + Complex.I)‖).mp hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  · intro h
    -- 平方相等
    have hsq : ‖z - Complex.I‖ ^ 2 = ‖z - (1 + Complex.I)‖ ^ 2 := by rw [h]
    have hns : Complex.normSq (z - Complex.I) = Complex.normSq (z - (1 + Complex.I)) := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    -- 展开 re/im ⟹ (z.re-1)² = z.re² ⟹ z.re = 1/2
    rw [Complex.normSq_apply, Complex.normSq_apply] at hns
    simp at hns
    nlinarith

/-- T 坐标 (基点 i): 临界线 = 单位圆。T(z) = 1/(z-i) - 1
    (recip 中心 = 复平面基点 i, 平移 -1 消圆心):
    Re z = 1/2 ⟺ ‖1/(z-i) - 1‖ = 1。 
English: T coordinates (basepoint i): the critical line = the unit circle. T(z) = 1/(z-i) - 1 (recip center = the basepoint i of the complex plane, translation -1 removes the circle center): Re z = 1/2 ⟺ ‖1/(z-i) - 1‖ = 1. -/
theorem recip_basepoint_i_on_unit_circle (z : ℂ) (hz : z ≠ Complex.I) :
    ‖1 / (z - Complex.I) - 1‖ = 1 ↔ z.re = 1 / 2 := by
  -- 1/(z-i) - 1 = -(z-(1+i))/(z-i) (代数)
  have hrewrite : 1 / (z - Complex.I) - 1 = -((z - (1 + Complex.I)) / (z - Complex.I)) := by
    field_simp [sub_ne_zero.mpr hz]
    ring
  have hne : ‖z - Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  -- |1/(z-i)-1| = |z-(1+i)|/|z-i| = 1 ⟺ |z-(1+i)| = |z-i| (等距)
  rw [hrewrite, norm_neg, norm_div, div_eq_one_iff_eq hne]
  rw [eq_comm]
  exact (critical_line_equidistant_basepoint_i z).symm

end RiemannUnifiedObservation
