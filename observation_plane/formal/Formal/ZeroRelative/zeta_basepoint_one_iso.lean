import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# 反演对称中心作基点 — 基点 1 (临界线圆圆心) 坐标下的在线判据

用户方向 (2026-08-19): 反演 1/z 的对称中心 (不动点 ±1, 其中 +1 =
临界线圆圆心) 作为基点观测; 用临界线圆相关位置做基点。

基点 1 (w = z - 1) 坐标下的完整观测:
- 临界线圆 |z-1| = 1 变成单位圆 |w| = 1 (基点 = 圆心, 天然圆);
- 在线判据 Re z = 1/2 变成等距条件 ‖w‖ = ‖1+w‖ (w 到 0 与到 -1
  等距, 垂直平分线; 0 = 反演中心, -1 = 圆上点 0 的基点 1 像);
- 零点轨道 {z, z̄, 1-z, 1-z̄} 变成 {w, w̄, -w, -w̄} (关于基点 1 的
  中心对称 × 共轭; 在线 ⟺ 退化).

这是已有等价链 (|1-z| = |z| ⟺ Re z = 1/2, 观测 U) 在基点 1
坐标下的显式形式。等价重写, 不添加新信息 (反演保真), 但确认
"以临界线圆相关位置为基点" 是合法 0pat 观测。

English: basepoint one: off-line zeros force the left half-strip (T2) -/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- 基点 1 (临界线圆圆心) 坐标下的在线判据:
    z = 1+w 在临界线上 ⟺ w 到 0 (反演中心) 与到 -1 (圆上点) 等距.
    临界线圆 |z-1| = 1 在基点 1 坐标下 = 单位圆 |w| = 1. 
English: On-line criterion at basepoint 1 (the critical-line circle center): z = 1+w is on the critical line ⟺ w is equidistant from 0 (inversion center) and -1 (circle point); the critical-line circle |z-1| = 1 becomes the unit circle |w| = 1. -/
theorem on_line_iff_equidistant_base_one (w : ℂ) :
    (1 + w).re = 1 / 2 ↔ ‖w‖ = ‖1 + w‖ := by
  constructor
  · intro h
    have hre : w.re = -1 / 2 := by
      have : (1 + w).re = 1 + w.re := by simp [Complex.add_re, Complex.ofReal_re]
      linarith
    -- ‖w‖² = ‖1+w‖² (normSq 展开 + hre)
    have hsq : ‖w‖ ^ 2 = ‖1 + w‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      rw [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
      rw [hre]
      ring
    -- 非负 ⟹ 从平方等式到等式
    have habs : |‖w‖| = |‖1 + w‖| :=
      (sq_eq_sq_iff_abs_eq_abs ‖w‖ ‖1 + w‖).mp hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  · intro h
    have hsq : ‖w‖ ^ 2 = ‖1 + w‖ ^ 2 := by rw [h]
    have hns : Complex.normSq w = Complex.normSq (1 + w) := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    have hre : w.re = -1 / 2 := by
      rw [Complex.normSq_apply, Complex.normSq_apply,
        Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im] at hns
      nlinarith
    have : (1 + w).re = 1 + w.re := by simp [Complex.add_re, Complex.ofReal_re]
    linarith

end RiemannUnifiedObservation
