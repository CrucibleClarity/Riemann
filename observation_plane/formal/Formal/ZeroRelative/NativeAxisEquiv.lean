import Formal.ZeroRelative.EulerFoldImagAxis
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace ZeroRelative

/-!
# NativeAxisEquiv — 4 log 轴 ↔ 复数位置原生等价 (节点 0.6 前置, 2026-08-27)

u/v 正交轴 (两正交实轴旋转 45° 的"四 log 轴": 正侧 = 人类"无理数"侧,
负侧 90° 折线 = 人类虚轴侧 — `fold_imag_axis_diag` 已证虚轴 = u+v=0 对角线)
的原生等价: 常数 c = √2/2 = 2^{−1/2} 是 log2 轴值; 坐标代换
(u, v) = (c(re+im), c(re−im)) 的**全部代数性质与 I/π 无关** — "旋转 45°"
只是人类命名 (e^{iπ/4} 呈现), 原生版只用 c 常数与 re/im 数值投影。

本文件 = 等价的光机证: 原生还原 (u,v → re,im 纯实数) / 唯一性 (单射) /
保模 (2c² = 1) / 满射 (读回呈现 — 豁免原则见下)。证明体不引用任何含
I/π 的定理 (仅标准代数与 √2 手链 — 匹配 0 自动化纪律的风格)。

**呈现豁免 (构造侧)**: `axis_exists` 用 ↑re + ↑im·I 把实数对装入 Lean 的 ℂ
容器 (人类坐标读取层) — 无 i 的变换语义, 不依赖 ζ/相位/圈数任何定理 —
非自指 (0.6 判据: 自指 = 证明依赖待证结构; 此处仅容器组装)。

基点标尺: log2⁻¹ = 1/ln2 (因子周期 P = 2π/ln2 的单位刻度 — 本文件不含 π;
P 是结果不是构造输入)。
-/

open Complex

/-- √2 ≠ 0 (0 < √2 — 手写: ne_of_gt + sqrt_pos, 自动化禁). -/
lemma axis_sqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))

/-- **c = √2/2 = 1/√2** (div_eq_mul_inv + sq_sqrt + mul_inv_rev + ← mul_assoc
    + inv_mul_cancel₀ + one_mul — 零 field_simp). -/
lemma axis_c : (Real.sqrt 2 : ℝ) / 2 = 1 / Real.sqrt 2 := by
  have hsq : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := by
    rw [← pow_two]
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h2inv : (2 : ℝ)⁻¹ = ((Real.sqrt 2 : ℝ) * Real.sqrt 2)⁻¹ :=
    (congrArg Inv.inv hsq).symm
  rw [div_eq_mul_inv]
  rw [h2inv]
  rw [mul_inv_rev]
  rw [← mul_assoc]
  rw [mul_inv_cancel₀ axis_sqrt2_ne]
  rw [one_mul]
  rw [one_div]

/-- **c·2 = √2** ((√2/2)·2 = √2): 还原公式的核心系数 (2c = √2 → 2c² = 1). -/
lemma axis_c_mul_two : (Real.sqrt 2 / 2) * 2 = Real.sqrt 2 := by
  rw [div_eq_mul_inv]
  calc (Real.sqrt 2 * (2 : ℝ)⁻¹) * 2
      = Real.sqrt 2 * ((2 : ℝ)⁻¹ * 2) := by rw [mul_assoc]
    _ = Real.sqrt 2 * 1 := by rw [inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = Real.sqrt 2 := by rw [mul_one]

/-- **c·2 = √2 (乘数展开形)**: (√2·2⁻¹)·2 = √2 — hmain 展开匹配用. -/
lemma axis_c_mul_two_exp : (Real.sqrt 2 * (2 : ℝ)⁻¹) * 2 = Real.sqrt 2 := by
  calc (Real.sqrt 2 * (2 : ℝ)⁻¹) * 2
      = Real.sqrt 2 * ((2 : ℝ)⁻¹ * 2) := by rw [mul_assoc]
    _ = Real.sqrt 2 * 1 := by rw [inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = Real.sqrt 2 := by rw [mul_one]

/-- **√2·u·√2⁻¹ = u** (反商消去, 展开形). -/
lemma axis_mul_inv_two_u (u : ℝ) :
    (Real.sqrt 2 * u) * (Real.sqrt 2)⁻¹ = u := by
  calc (Real.sqrt 2 * u) * (Real.sqrt 2)⁻¹
      = u * ((Real.sqrt 2) * (Real.sqrt 2)⁻¹) := by ring
    _ = u * 1 := by rw [mul_inv_cancel₀ axis_sqrt2_ne]
    _ = u := by rw [mul_one]

/-- **c² = 1/2** (2c² = 1 ⟹ 保模). -/
lemma axis_c_sq : ((Real.sqrt 2 : ℝ) / 2) ^ 2 = 1 / 2 := by
  rw [div_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **原生还原 · 横坐标**: (u+v)/√2 = Re — 四 log 轴坐标纯实数恢复横坐标,
    无 I/π — 人类坐标的"实数侧" (人类强行把虚轴记为实部坐标 ⟹ 虚部进基点;
    原生侧从 u/v 直接恢复 re = (u+v)/√2). -/
theorem axis_recovery_re (z : ℂ) :
    (fold_u z + fold_v z) / (Real.sqrt 2 : ℝ) = z.re := by
  unfold fold_u fold_v
  have hmain : (Real.sqrt 2 / 2) * (z.re + z.im) + (Real.sqrt 2 / 2) * (z.re - z.im)
      = (Real.sqrt 2 / 2) * (2 * z.re) := by ring
  rw [hmain]
  rw [div_eq_mul_inv]
  calc ((Real.sqrt 2 / 2) * (2 * z.re)) * (Real.sqrt 2)⁻¹
      = ((Real.sqrt 2 / 2) * 2) * z.re * (Real.sqrt 2)⁻¹ := by ring
    _ = (Real.sqrt 2 * z.re) * (Real.sqrt 2)⁻¹ := by rw [axis_c_mul_two]
    _ = z.re := by
      calc (Real.sqrt 2 * z.re) * (Real.sqrt 2)⁻¹
          = z.re * ((Real.sqrt 2) * (Real.sqrt 2)⁻¹) := by ring
        _ = z.re * 1 := by rw [mul_inv_cancel₀ axis_sqrt2_ne]
        _ = z.re := by rw [mul_one]

/-- **原生还原 · 纵坐标**: (u−v)/√2 = Im — 同上 (差侧), 无 I/π. -/
theorem axis_recovery_im (z : ℂ) :
    (fold_u z - fold_v z) / (Real.sqrt 2 : ℝ) = z.im := by
  unfold fold_u fold_v
  have hmain : (Real.sqrt 2 / 2) * (z.re + z.im) - (Real.sqrt 2 / 2) * (z.re - z.im)
      = (Real.sqrt 2 / 2) * (2 * z.im) := by ring
  rw [hmain]
  rw [div_eq_mul_inv]
  calc ((Real.sqrt 2 / 2) * (2 * z.im)) * (Real.sqrt 2)⁻¹
      = ((Real.sqrt 2 / 2) * 2) * z.im * (Real.sqrt 2)⁻¹ := by ring
    _ = (Real.sqrt 2 * z.im) * (Real.sqrt 2)⁻¹ := by rw [axis_c_mul_two]
    _ = z.im := by
      calc (Real.sqrt 2 * z.im) * (Real.sqrt 2)⁻¹
          = z.im * ((Real.sqrt 2) * (Real.sqrt 2)⁻¹) := by ring
        _ = z.im * 1 := by rw [mul_inv_cancel₀ axis_sqrt2_ne]
        _ = z.im := by rw [mul_one]

/-- **唯一性 (单射)**: 四 log 轴坐标 (u,v) 唯一决定位置 — 位置等价的原生单向
    (由还原公式 + Complex.ext). -/
theorem axis_unique {z w : ℂ} (hu : fold_u z = fold_u w) (hv : fold_v z = fold_v w) :
    z = w := by
  have hre : z.re = w.re := by
    calc z.re = (fold_u z + fold_v z) / (Real.sqrt 2 : ℝ) := (axis_recovery_re z).symm
      _ = (fold_u w + fold_v w) / (Real.sqrt 2 : ℝ) := by rw [hu, hv]
      _ = w.re := axis_recovery_re w
  have him : z.im = w.im := by
    calc z.im = (fold_u z - fold_v z) / (Real.sqrt 2 : ℝ) := (axis_recovery_im z).symm
      _ = (fold_u w - fold_v w) / (Real.sqrt 2 : ℝ) := by rw [hu, hv]
      _ = w.im := axis_recovery_im w
  exact Complex.ext hre him

/-- **保模 (等价结构件)**: u² + v² = re² + im² — 四 log 轴坐标长度 = 复位置
    长度 (2c² = 1) — 位置等价保结构 (与折叠模 U²+V²=‖ζ‖² 平行, 但这是
    定义域侧, 无 ζ). -/
theorem axis_norm_sq_preserving (z : ℂ) :
    fold_u z ^ 2 + fold_v z ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  unfold fold_u fold_v
  calc ((Real.sqrt 2 / 2) * (z.re + z.im)) ^ 2 + ((Real.sqrt 2 / 2) * (z.re - z.im)) ^ 2
      = (Real.sqrt 2 / 2) ^ 2 * ((z.re + z.im) ^ 2 + (z.re - z.im) ^ 2) := by
        rw [mul_pow, mul_pow]
        ring
    _ = (1 / 2 : ℝ) * ((z.re + z.im) ^ 2 + (z.re - z.im) ^ 2) := by rw [axis_c_sq]
    _ = z.re ^ 2 + z.im ^ 2 := by ring

/-- **满射 (读回呈现 · 豁免)**: 每个四 log 轴坐标 (u,v) 都是某复数位置的坐标 —
    读回 = ↑re + ↑im·I 装入 Lean 的 ℂ 容器 (人类坐标读取层, 无 i 变换语义;
    不依赖 ζ/相位定理 — 非自指). -/
theorem axis_exists (u v : ℝ) : ∃ z : ℂ, fold_u z = u ∧ fold_v z = v := by
  let s : ℝ := Real.sqrt 2
  let z : ℂ := ((u + v) / s : ℝ) + (((u - v) / s : ℝ)) * Complex.I
  refine ⟨z, ?_, ?_⟩
  · unfold fold_u
    have hre : z.re = (u + v) / s := by
      dsimp [z, s]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_self, add_zero]
    have him : z.im = (u - v) / s := by
      dsimp [z, s]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    rw [hre, him]
    have hsum : (u + v) / s + (u - v) / s = (2 * u) / s := by
      rw [← add_div]
      ring
    rw [hsum]
    have hmain : (Real.sqrt 2 / 2) * ((2 * u) / Real.sqrt 2) = u := by
      rw [show (((2 * u) : ℝ) / Real.sqrt 2) = (2 * u) * (Real.sqrt 2)⁻¹ by
        rw [div_eq_mul_inv]]
      rw [div_eq_mul_inv]
      have hmid : (Real.sqrt 2 * (2 : ℝ)⁻¹) * ((2 * u) * (Real.sqrt 2)⁻¹)
          = ((Real.sqrt 2 * (2 : ℝ)⁻¹) * 2) * u * (Real.sqrt 2)⁻¹ := by ring
      rw [hmid]
      rw [axis_c_mul_two_exp]
      exact axis_mul_inv_two_u u
    exact hmain
  · unfold fold_v
    have hre : z.re = (u + v) / s := by
      dsimp [z, s]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_self, add_zero]
    have him : z.im = (u - v) / s := by
      dsimp [z, s]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    rw [hre, him]
    have hsum : (u + v) / s - (u - v) / s = (2 * v) / s := by
      rw [← sub_div]
      ring
    rw [hsum]
    have hmain : (Real.sqrt 2 / 2) * ((2 * v) / Real.sqrt 2) = v := by
      rw [show (((2 * v) : ℝ) / Real.sqrt 2) = (2 * v) * (Real.sqrt 2)⁻¹ by
        rw [div_eq_mul_inv]]
      rw [div_eq_mul_inv]
      have hmid : (Real.sqrt 2 * (2 : ℝ)⁻¹) * ((2 * v) * (Real.sqrt 2)⁻¹)
          = ((Real.sqrt 2 * (2 : ℝ)⁻¹) * 2) * v * (Real.sqrt 2)⁻¹ := by ring
      rw [hmid]
      rw [axis_c_mul_two_exp]
      exact axis_mul_inv_two_u v
    exact hmain

end ZeroRelative
