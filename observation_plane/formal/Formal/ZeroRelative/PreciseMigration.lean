/- 隔离文件 (Layer 14): 基点的精确迁移 T(z) = 1/(z-i) - 1。
    内容: 算子与逆压缩-平移分解 / 三分层模判据 (临界线 <-> 单位圆) / 函数方程反射变为单位圆对合 / 相位锁定位置。
    性质: mathlib-only, 0 error 0 sorry。

English: isolated file (Layer 14): the exact base-point migration T(z) = 1/(z-i) - 1 --- operator and inverse, three-tier modulus decision, reflection as the unit-circle involution, phase-locked positions-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped ComplexConjugate

-- MARKER_20260825: lean 读取验证

/-!
# PreciseMigration — 基点精确移动定理族 (黎曼方向后续组装件, 2026-08-25)

**角色**: 把 state/NetElementAssembly §6d 的"精确移动方法" (结构映射算子:
压缩 + 平移 + 相位中心, 参数全结构) 落成可复用定理族, 供黎曼方向组装。
**规范**: 允许全部自动化工具 (非零洞组装版; 组装链审计版见
PreciseMigrationDemo.lean)。全部 0pat (只引用 Mathlib)。

**算子**: T(z) = 1/(z−i) − 1 — recip(压缩) 中心 = 复平面基点 i (相位精确)
+ 平移 −1 (结构值)。性质:
  * 可逆 (TInv), 两基点距离比 = 模 (位置量 → 模量)
  * **三档判定**: |T(z)| 与 1 的关系 ⟺ Re z 与 1/2 的关系 (越上下界核心件)
  * 反射配对: T(1 − conj z) = 1/conj T(z) (对称映射在 T 坐标 = 圆反演)

**相位中心锁定** (辐角对消, 无漂移): log i = i·π/2, e^{iπ/2} = i。
**精确位置锁定**: i^i = e^{−π/2} (假实轴刻度), i^{1/(2i)} = e^{π/4}
(辐角对消: (1/(2i))·(i·π/2) = π/4), 半点 = e^{π/4}/2 ≈ 1.09664;
对偶对 e^{±π/4} 互逆 (上下界关于新 0 对称配对的精确成员)。

黎曼组装角色: 临界线 Re z = 1/2 ⟺ 单位圆 |T(z)| = 1 (观测 AB 已有);
左右半带 ⟺ 圆内/圆外 (本族新增); 函数方程对称 (1−conj) ⟺ 单位圆反演
(本族新增)。后续: 带内零点判定全部换成三档模判定 (一阶完备)。
-/

namespace ZeroRelative

noncomputable section

/-! ## §1 精确移动算子本体: T(z) = 1/(z−i) − 1 -/

/-- 精确移动算子: 压缩 (recip, 中心 = 基点 i) + 平移 (−1, 结构值)。 
English: Exact migration operator: compression (recip, center = basepoint i) + translation (−1, structural value). -/
def T (z : ℂ) : ℂ := 1 / (z - Complex.I) - 1

/-- 逆算子: 精确移动可逆 (组装件可反复使用, 不信息递减)。 
English: Inverse operator: exact migration is invertible (assembly piece reusable, no information loss). -/
def TInv (w : ℂ) : ℂ := Complex.I + 1 / (w + 1)

/-- 算子分解: T(z) + 1 = (z−i)⁻¹ — 压缩核 + 平移分离 (参数全结构)。 
English: Operator decomposition: T(z) + 1 = (z−i)⁻¹ — compression kernel and translation separated (full parameter structure). -/
theorem T_shift_recip (z : ℂ) : T z + 1 = (z - Complex.I)⁻¹ := by
  rw [T]
  ring

/-- 右逆: TInv ∘ T = id (z ≠ i) — 移动算子可逆, 坐标切换无损。 
English: Right inverse: TInv ∘ T = id (z ≠ i) — migration operator invertible, lossless coordinate change. -/
theorem T_inv_right (z : ℂ) (hz : z ≠ Complex.I) : TInv (T z) = z := by
  have hz' : z - Complex.I ≠ 0 := sub_ne_zero.mpr hz
  rw [TInv, T]
  field_simp [hz']
  ring

/-- 左逆: T ∘ TInv = id (w ≠ −1) — 双射对 (精确移动是坐标变换, 非数值逼近)。 
English: Left inverse: T ∘ TInv = id (w ≠ −1) — bijective pair (exact migration is a coordinate change, not a numerical approximation). -/
theorem T_inv_left (w : ℂ) (hw : w ≠ -1) : T (TInv w) = w := by
  rw [TInv, T]
  have hinner : Complex.I + 1 / (w + 1) - Complex.I = 1 / (w + 1) := by
    ring
  rw [hinner]
  have hw1 : w + 1 ≠ 0 := by
    intro h
    exact hw (add_eq_zero_iff_eq_neg.mp h)
  field_simp [hw1]
  ring

/-- 距离比 = 模: ‖T(z)‖² = (到 1+i 的距离)² / (到 i 的距离)²
— 精确移动把"位置量"换成"模量", 界换轨为结构判定。 
English: Distance ratio = modulus: ‖T(z)‖² = (distance to 1+i)² / (distance to i)² — exact migration swaps 'position quantity' for 'modulus quantity', converting bounds into structural criteria. -/
theorem T_normSq_ratio (z : ℂ) (hz : z ≠ Complex.I) :
    Complex.normSq (T z) = Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) := by
  have hz' : z - Complex.I ≠ 0 := sub_ne_zero.mpr hz
  rw [T]
  rw [← div_sub_same hz']
  rw [Complex.normSq_div]
  have hEq : 1 - (z - Complex.I) = -(z - 1 - Complex.I) := by ring
  rw [hEq, Complex.normSq_neg]

/-- normSq 差分: ‖z−1−i‖² − ‖z−i‖² = 1 − 2·Re z — 两基点距离平方差
= 位置线性量 (精确移动把二次模量压成一阶位置谓词)。 
English: normSq difference: ‖z−1−i‖² − ‖z−i‖² = 1 − 2·Re z — squared-distance difference of the two basepoints = linear position quantity (exact migration collapses the quadratic modulus into a first-order position predicate). -/
lemma T_normSq_diff (z : ℂ) :
    Complex.normSq (z - 1 - Complex.I) - Complex.normSq (z - Complex.I) = 1 - 2 * z.re := by
  rw [Complex.normSq_apply, Complex.normSq_apply]
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_im, Complex.sub_im]
  simp
  ring

/-- **三档判定 (等)**: |T(z)|² = 1 ⟺ Re z = 1/2 — 临界线 ⟺ 单位圆
(位置谓词 ⟺ 模谓词, 一阶判定)。 
English: Three-tier criterion (equality): |T(z)|² = 1 ⟺ Re z = 1/2 — critical line ⟺ unit circle (position predicate ⟺ modulus predicate, first-order criterion). -/
theorem T_normSq_eq_one_iff (z : ℂ) (hz : z ≠ Complex.I) :
    Complex.normSq (T z) = 1 ↔ z.re = 1 / 2 := by
  have hz' : z - Complex.I ≠ 0 := sub_ne_zero.mpr hz
  have hd : Complex.normSq (z - Complex.I) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hz')
  calc
    Complex.normSq (T z) = 1
        ↔ Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) = 1 := by
          rw [T_normSq_ratio z hz]
    _ ↔ Complex.normSq (z - 1 - Complex.I) = Complex.normSq (z - Complex.I) := by
          rw [div_eq_iff hd]
          rw [one_mul]
    _ ↔ 1 - 2 * z.re = 0 := by
          rw [← sub_eq_zero]
          rw [T_normSq_diff]
    _ ↔ z.re = 1 / 2 := by
          constructor
          · intro h
            rw [sub_eq_zero] at h
            rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
            rw [mul_comm]
            exact h.symm
          · intro h
            rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)] at h
            rw [mul_comm] at h
            rw [sub_eq_zero]
            exact h.symm

/-- **三档判定 (内)**: |T(z)|² < 1 ⟺ Re z > 1/2 — 左半带 (1+i 侧) ⟺ 单位圆内
(上下界换轨核心: 边界判定 → 模判定)。 
English: Three-tier criterion (interior): |T(z)|² < 1 ⟺ Re z > 1/2 — left half-strip (1+i side) ⟺ inside the unit circle (the core of bound-shifting: boundary criterion → modulus criterion). -/
theorem T_normSq_lt_one_iff (z : ℂ) (hz : z ≠ Complex.I) :
    Complex.normSq (T z) < 1 ↔ 1 / 2 < z.re := by
  have hz' : z - Complex.I ≠ 0 := sub_ne_zero.mpr hz
  have hd : 0 < Complex.normSq (z - Complex.I) := Complex.normSq_pos.mpr hz'
  calc
    Complex.normSq (T z) < 1
        ↔ Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) < 1 := by
          rw [T_normSq_ratio z hz]
    _ ↔ Complex.normSq (z - 1 - Complex.I) < Complex.normSq (z - Complex.I) := by
          rw [div_lt_one hd]
    _ ↔ 1 - 2 * z.re < 0 := by
          rw [← sub_lt_zero]
          rw [T_normSq_diff]
    _ ↔ 1 / 2 < z.re := by
          constructor
          · intro h
            rw [sub_lt_zero] at h
            rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
            rw [mul_comm]
            exact h
          · intro h
            rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)] at h
            rw [mul_comm] at h
            rw [sub_lt_zero]
            exact h

/-- **三档判定 (外)**: |T(z)|² > 1 ⟺ Re z < 1/2 — 右半带 (i 侧) ⟺ 单位圆外。 
English: Three-tier criterion (exterior): |T(z)|² > 1 ⟺ Re z < 1/2 — right half-strip (i side) ⟺ outside the unit circle. -/
theorem T_normSq_gt_one_iff (z : ℂ) (hz : z ≠ Complex.I) :
    Complex.normSq (T z) > 1 ↔ z.re < 1 / 2 := by
  have hz' : z - Complex.I ≠ 0 := sub_ne_zero.mpr hz
  have hd : 0 < Complex.normSq (z - Complex.I) := Complex.normSq_pos.mpr hz'
  calc
    Complex.normSq (T z) > 1
        ↔ Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) > 1 := by
          rw [T_normSq_ratio z hz]
    _ ↔ 0 < Complex.normSq (z - 1 - Complex.I) - Complex.normSq (z - Complex.I) := by
          constructor
          · intro h
            have h1 : 0 < Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) - 1 :=
              sub_pos.mpr h
            have : 0 < (Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) - 1) *
                Complex.normSq (z - Complex.I) := mul_pos h1 hd
            have hbm : Complex.normSq (z - 1 - Complex.I) - Complex.normSq (z - Complex.I) =
                (Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) - 1) *
                  Complex.normSq (z - Complex.I) := by
              field_simp [ne_of_gt hd]
            rw [← hbm] at this
            exact this
          · intro h
            have hbm' : Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) - 1 =
                (Complex.normSq (z - 1 - Complex.I) - Complex.normSq (z - Complex.I)) /
                  Complex.normSq (z - Complex.I) := by
              field_simp [ne_of_gt hd]
            have h1 : 0 < Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) - 1 := by
              rw [hbm']
              exact div_pos h hd
            exact sub_pos.mp h1
    _ ↔ 0 < 1 - 2 * z.re := by
          rw [T_normSq_diff]
    _ ↔ z.re < 1 / 2 := by
          constructor
          · intro h
            rw [sub_pos] at h
            rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
            rw [mul_comm]
            exact h
          · intro h
            rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h
            rw [mul_comm] at h
            rw [sub_pos]
            exact h

/-- 纯代数: 1/(1−u) − 1 = 1/(1/u − 1) (u ≠ 0, u ≠ 1) —
反射配对的 T 坐标代数核。 
English: Pure algebra: 1/(1−u) − 1 = 1/(1/u − 1) (u ≠ 0, u ≠ 1) — the algebraic kernel of the reflection pair in T coordinates. -/
private lemma inv_shift_identity (u : ℂ) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    1 / (1 - u) - 1 = 1 / (1 / u - 1) := by
  have h1m : 1 - u ≠ 0 := by
    intro h
    exact hu1 (sub_eq_zero.mp h).symm
  have hm : 1 / u - 1 ≠ 0 := by
    intro h
    apply hu1
    have hdiv : 1 / u = 1 := sub_eq_zero.mp h
    have hones : u * (1 / u) = u * 1 := congrArg (fun v : ℂ => u * v) hdiv
    rw [mul_one] at hones
    have huu : u * (1 / u) = 1 := by field_simp [hu0]
    rw [huu] at hones
    exact hones.symm
  field_simp [h1m, hu0, hm]
  ring

/-- **反射配对**: T(1 − conj z) = 1/conj(T(z)) — 函数方程对称
(z ↦ 1−conj z, 关于临界线) 在 T 坐标 = 单位圆反演 w ↦ 1/conj w 
(对合: 双侧相位对消, 对称配对件)。 
English: Reflection pair: T(1 − conj z) = 1/conj(T(z)) — functional equation symmetry (z ↦ 1−conj z, about the critical line) in T coordinates = unit-circle inversion w ↦ 1/conj w (involution: phase cancellation, symmetric pairing piece). -/
theorem T_reflect (z : ℂ) (hz : z ≠ Complex.I) (hz2 : z ≠ 1 + Complex.I) :
    T (1 - conj z) = 1 / conj (T z) := by
  rw [T]
  have hstar : conj (T z) = 1 / (conj z + Complex.I) - 1 := by
    rw [T]
    simp [Complex.conj_I]
  rw [show 1 - conj z - Complex.I = 1 - (conj z + Complex.I) by ring]
  rw [hstar]
  have hu0 : conj z + Complex.I ≠ 0 := by
    intro h
    apply hz
    have hre : z.re = (0 : ℝ) := by
      have := congrArg Complex.re h
      rw [Complex.add_re, Complex.conj_re, Complex.I_re] at this
      simpa using this
    have him : z.im = (1 : ℝ) := by
      have := congrArg Complex.im h
      rw [Complex.add_im, Complex.conj_im, Complex.I_im] at this
      have hz' : -z.im + 1 = 0 := by simpa using this
      linarith
    exact Complex.ext hre him
  have hu1 : conj z + Complex.I ≠ 1 := by
    intro h
    apply hz2
    have hre : z.re = (1 : ℝ) := by
      have := congrArg Complex.re h
      rw [Complex.add_re, Complex.conj_re, Complex.I_re] at this
      simpa using this
    have him : z.im = (1 : ℝ) := by
      have := congrArg Complex.im h
      rw [Complex.add_im, Complex.conj_im, Complex.I_im] at this
      have hz' : -z.im + 1 = 0 := by simpa using this
      linarith
    exact Complex.ext (by simpa using hre) (by simpa using him)
  exact inv_shift_identity (conj z + Complex.I) hu0 hu1

/-- **临界线上恒 1**: Re z = 1/2 ⟹ |T(z)|² = 1 — 临界线参数化下 T 恒在单位圆
(T 坐标: 临界线 = 圆, 无漂移)。  
English: Constantly 1 on the critical line: Re z = 1/2 ⟹ |T(z)|² = 1 — under critical-line parametrization T stays on the unit circle (in T coordinates: critical line = circle, no drift). -/
theorem T_on_critical_line (z : ℂ) (hz : z ≠ Complex.I) (hre : z.re = 1 / 2) :
    Complex.normSq (T z) = 1 :=
  (T_normSq_eq_one_iff z hz).2 hre

/-! ## §2 相位中心锁定 (基点 i 的辐角对消) -/

/-- 相位中心: e^{iπ/2} = i — i 是辐角锁定中心 (结构基准, 非数值近似)。 
English: Phase center: e^{iπ/2} = i — i is the argument-locking center (structural reference, not a numerical approximation). -/
theorem center_phase : Complex.exp (Complex.I * (Real.pi / 2)) = Complex.I := by
  rw [show Complex.I * (Real.pi / 2) = (Real.pi / 2) * Complex.I by ring]
  rw [Complex.exp_mul_I]
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

/-- 主分支对数: log i = i·π/2 — 辐角锁定 (arg i = π/2 主分支, 无分支漂移)。 
English: Principal branch logarithm: log i = i·π/2 — argument locking (arg i = π/2 principal branch, no branch drift). -/
theorem log_I_phase : Complex.log Complex.I = Complex.I * (Real.pi / 2) := by
  rw [Complex.log_I]
  ring

/-! ## §3 精确位置锁定 (假实轴刻度) -/

/-- **假实轴刻度**: i^i = e^{−π/2} — 辐角对消: (π/2)(−π/2)? 即
log i = i·π/2, i·log i = −π/2 (指数 i 的辐角与 log i 的辐角对消为纯实角)。 
English: Pseudo-real axis scale: i^i = e^{−π/2} — argument cancellation: log i = i·π/2, i·log i = −π/2 (the argument of exponent i cancels with that of log i into a purely real angle). -/
theorem i_pow_i : Complex.I ^ Complex.I = Complex.exp (-(Real.pi / 2)) := by
  have hI : Complex.I ≠ 0 := by simp
  rw [Complex.cpow_def_of_ne_zero hI]
  rw [Complex.log_I]
  have harg : ((Real.pi / 2) * Complex.I) * Complex.I = -((Real.pi / 2) : ℂ) := by
    rw [mul_assoc]
    simp [Complex.I_mul_I]
  rw [harg]

/-- **精确位置**: i^{1/(2i)} = e^{π/4} — 辐角对消: (1/(2i))·(i·π/2) = π/4
(纯实角; 主分支锁定 k=0; 任何小数近似 = 漂移源)。 
English: Exact position: i^{1/(2i)} = e^{π/4} — argument cancellation: (1/(2i))·(i·π/2) = π/4 (purely real angle; principal branch locked k=0; any decimal approximation = drift source). -/
theorem i_pow_half_inv_two_i :
    Complex.I ^ (1 / (2 * Complex.I)) = Complex.exp (Real.pi / 4) := by
  have hI : Complex.I ≠ 0 := by simp
  have h2I : (2 : ℂ) * Complex.I ≠ 0 := by simp
  rw [Complex.cpow_def_of_ne_zero hI]
  rw [Complex.log_I]
  have harg : ((Real.pi / 2) * Complex.I) * (1 / (2 * Complex.I)) = (Real.pi / 4 : ℂ) := by
    field_simp [h2I]
    ring_nf
  rw [harg]

/-- **半点精确位置**: (1/2)·i^{1/(2i)} = e^{π/4}/2 ≈ 1.09664 —
假实轴半点 (i 的 1/(2i) 次后继的一半, 复平面实轴上, 实部 = e^{π/4}/2)。 
English: Exact half-point position: (1/2)·i^{1/(2i)} = e^{π/4}/2 ≈ 1.09664 — the pseudo-real-axis half-point (half of i's 1/(2i)-th successor, on the real axis of the complex plane, real part = e^{π/4}/2). -/
theorem half_succ_position :
    (1 / 2 : ℂ) * (Complex.I ^ (1 / (2 * Complex.I))) =
      Complex.exp (Real.pi / 4) / 2 := by
  rw [i_pow_half_inv_two_i]
  ring

/-- **对偶对互逆**: e^{π/4}·e^{−π/4} = 1 — 上下界关于新 0 (临界线) 的
对称配对成员 (精确锁定, 非近似)。 
English: Inverse dual pair: e^{π/4}·e^{−π/4} = 1 — members of the symmetric pairing of the bounds about the new 0 (critical line) (exactly locked, not approximate). -/
theorem pair_inverse : Real.exp (Real.pi / 4) * Real.exp (-(Real.pi / 4)) = 1 := by
  rw [← Real.exp_add]
  ring_nf
  rw [Real.exp_zero]

/-- **假实轴刻度乘法律**: e^{−aπ/2}·e^{−bπ/2} = e^{−(a+b)π/2} —
刻度 (i^i)^n = e^{−nπ/2} 的乘法半群律 (对偶刻度加法对应相位偶数, 无漂移)。 
English: Pseudo-real axis scale multiplication law: e^{−aπ/2}·e^{−bπ/2} = e^{−(a+b)π/2} — multiplicative semigroup law of the scale (i^i)^n = e^{−nπ/2} (dual-scale addition matches even phases, no drift). -/
theorem imag_scale_mul (a b : ℝ) :
    Real.exp (-(a * Real.pi / 2)) * Real.exp (-(b * Real.pi / 2)) =
      Real.exp (-((a + b) * Real.pi / 2)) := by
  rw [← Real.exp_add]
  ring_nf

/-- **对偶刻度**: e^{π/4}·e^{π/4} = e^{π/2} — 半点自乘 = 半点对偶
(a = b = −1/2 刻度律实例: 两个 1/2 后继合成一个 1 后继)。 
English: Dual scale: e^{π/4}·e^{π/4} = e^{π/2} — half-point squared = half-point dual (instance of the scale law with a = b = −1/2: two 1/2 successors compose into one 1 successor). -/
theorem pair_square :
    Real.exp (Real.pi / 4) * Real.exp (Real.pi / 4) = Real.exp (Real.pi / 2) := by
  rw [← Real.exp_add]
  ring_nf

end

end ZeroRelative
