import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Ring

/-!
# 欧拉圆虚轴折线 (EulerFoldImagAxis) — 2026-08-27

用户主张 (原话要点, D102): "按欧拉圆把复数轴干成 90 度正交的折线: 复平面的
假实轴也是虚轴 (虚轴本身坐标是 1); 欧拉圆负侧 (−1) 处, 两个正交且与实轴
夹角 ±45° 的方向, 坐标值都是实数; 从负侧实轴取复数、从正交的另一根实轴取号;
这 90° 直角的两根半轴就是数学史上构造出来的虚数轴。不去证逻辑矛盾, 直接用
这个 90° 直角的轴构造假复平面。"

**净元组装 (负侧虚轴)**: 全部由标准复几何元组装, 零新公理 —
- 元1 欧拉恒等式: e^{iπ} = −1 (欧拉圆负侧基点, mathlib 引用)
- 元2 虚轴单位: e^{iπ/2} = i, e^{−iπ/2} = −i (1/4 圈, 用户"虚轴本身坐标是1"
  的 pat 表达: i 是相位锁定后的 1)
- 组装3 从负侧旋转: (−1)·e^{−iπ/2} = i, (−1)·e^{iπ/2} = −i (exp 乘法性
  exp_add + 周期 exp_two_pi_mul_I — 数学史 √−1 的几何化: 从 −1 转 90°)
- 元4 折线方向: arg(1+i) = π/4, arg(1−i) = −π/4 (从 −1 到 ±i 的连线)
- 元5 90° 正交: 内积 re((1+i)·conj(1−i)) = 0, 方向差 π/2 — "90 度正交的折线"
- 元6 长度: ‖1±i‖ = √2 (折线半段)
- 组装7 极坐标: e^{iπ/4} = (√2/2)(1+i), e^{−iπ/4} = (√2/2)(1−i)
  (极坐标元 norm_mul_exp_arg_mul_I: ‖z‖·e^{i·arg z} = z)
- 组装8 假复平面: 任意 z 唯一分解 z = u·e^{iπ/4} + v·e^{−iπ/4}, u,v ∈ ℝ
  (u = (√2/2)(re+im), v = (√2/2)(re−im)) — 两根 45° 实轴互相 90° 正交,
  坐标全实数 ("从负侧实轴取复数, 从正交的另一根实轴取号")

**诚实边界**: 本文件 = 标准复几何的重新呈现 (欧拉恒等式/极坐标/旋转的
推论), 不是新数学; "虚数轴 = 折线" 是几何叙述 (与数学史一致: 虚数轴 =
实轴旋转 90° 的像, Argand/Gauss), 不改变 ℂ 的代数结构 (i² = −1);
"数学界接受" 的判据 = 呈现与共识结构兼容 (每步可机证, 零新公理)。

English: Euler-circle imaginary-axis fold — the imaginary axis presented as
a 90°-orthogonal fold assembled from standard units: Euler identity
e^{iπ} = −1 (negative-side basepoint), quarter-turn units e^{±iπ/2} = ±i
(the imaginary-axis units; "the imaginary axis itself has coordinate 1"),
rotation from −1 (exp additivity + periodicity), segments from −1 to ±i
with arguments ±π/4 (real coordinates) and length √2, orthogonal segments,
and the unique real-coordinate decomposition z = u·e^{iπ/4} + v·e^{−iπ/4}
(the 45° real basis = the "fake plane" construction). All statements are
classical complex geometry, machine-verified, zero new axioms.
-/

noncomputable section

open Complex
open scoped Topology
open scoped Real
open scoped ComplexConjugate

namespace ZeroRelative

-- ===== 元1: 欧拉恒等式 (欧拉圆负侧基点) =====

/-- **欧拉恒等式**: e^{iπ} = −1 — 欧拉圆负侧基点 (虚数轴的出发点).
    English: Euler identity e^{iπ} = −1 — the negative-side basepoint of
    the Euler circle. -/
theorem euler_identity : exp (π * I) = -1 :=
  Complex.exp_pi_mul_I

-- ===== 元2: 虚轴单位 = 1/4 圈 =====

/-- **虚轴单位**: e^{iπ/2} = i — 虚轴本身坐标是 1 (用户: 假实轴也是虚轴,
    虚轴单位 = 相位锁定后的 1).
    English: the imaginary-axis unit: e^{iπ/2} = i — the imaginary axis
    itself has coordinate 1 (i is the phase-locked 1). -/
theorem I_eq_exp_half_pi : exp ((π / 2) * I) = I :=
  Complex.exp_pi_div_two_mul_I

/-- **对偶虚轴单位**: e^{−iπ/2} = −i.
    English: the dual unit: e^{−iπ/2} = −i. -/
theorem neg_I_eq_exp_neg_half_pi : exp (-π / 2 * I) = -I :=
  Complex.exp_neg_pi_div_two_mul_I

-- ===== 组装3: 从负侧旋转 90° (数学史 √−1 的几何化) =====

/-- **i = −1 旋转 90°**: (−1)·e^{−iπ/2} = i — 组装: 欧拉恒等式 (e^{iπ}=−1)
    接 exp 乘法性 (exp_add): e^{iπ}·e^{−iπ/2} = e^{i(π−π/2)} = e^{iπ/2} = i.
    English: i is −1 rotated by 90° — assembled from the Euler identity and
    exp additivity. -/
theorem I_from_neg_one_rotation : (-1 : ℂ) * exp (-π / 2 * I) = I := by
  calc
    (-1 : ℂ) * exp (-π / 2 * I) = exp (π * I) * exp (-π / 2 * I) := by
      rw [euler_identity]
    _ = exp ((π / 2) * I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = I := I_eq_exp_half_pi

/-- **−i = −1 旋转 −90°**: (−1)·e^{iπ/2} = −i — 组装: 欧拉恒等式 + exp 加法
    + 周期 (exp_two_pi_mul_I): e^{iπ}·e^{iπ/2} = e^{i3π/2} = e^{i(−π/2+2π)}
    = e^{−iπ/2} = −i.
    English: −i is −1 rotated by −90° — assembled via exp additivity and
    the 2π period. -/
theorem neg_I_from_neg_one_rotation : (-1 : ℂ) * exp ((π / 2) * I) = -I := by
  calc
    (-1 : ℂ) * exp ((π / 2) * I) = exp (π * I) * exp ((π / 2) * I) := by
      rw [euler_identity]
    _ = exp ((3 * π / 2) * I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = exp (-π / 2 * I) := by
      rw [show (3 * π / 2) * I = -π / 2 * I + 2 * π * I by ring]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I]
      ring
    _ = -I := neg_I_eq_exp_neg_half_pi

-- ===== 元4: 折线顶点与方向 (从 −1 到 ±i 的连线) =====

/-- **折线经过 ±i**: i−(−1) = 1+i 且 −i−(−1) = 1−i — 虚数轴的两个单位点
    恰在折线的两根半轴上 (连接 −1 与 ±i).
    English: the fold joins −1 to both i and −i: the imaginary axis units
    lie on the fold segments. -/
theorem imag_axis_units_on_fold : I - (-1) = 1 + I ∧ -I - (-1) = 1 - I := by
  constructor <;> ring

/-- **从 −1 到 i 的方向 = +45°**: arg(1+i) = π/4 — 折线第一段
    (向量 i−(−1) = 1+i 与实轴夹角 45°; tan(arg z) = im/re 元 + arctan).
    English: the direction from −1 to i has argument π/4 (45°). -/
theorem neg_one_to_I_direction : arg (1 + I) = π / 4 := by
  have hmem : (1 + I).arg ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    rw [Set.mem_Ioo, ← abs_lt]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by
      rw [Complex.add_re, Complex.one_re, Complex.I_re]
      norm_num))
  have htan : Real.tan ((1 + I).arg) = 1 := by
    rw [Complex.tan_arg]
    rw [Complex.add_im, Complex.one_im, Complex.I_im, Complex.add_re, Complex.one_re, Complex.I_re]
    norm_num
  have h1 : Real.arctan (Real.tan ((1 + I).arg)) = (1 + I).arg :=
    Real.arctan_tan (x := (1 + I).arg) hmem.1 hmem.2
  have h2 : Real.arctan (Real.tan ((1 + I).arg)) = π / 4 := by
    rw [htan, Real.arctan_one]
  exact h1.symm.trans h2

/-- **从 −1 到 −i 的方向 = −45°**: arg(1−i) = −π/4 — 折线第二段.
    English: the direction from −1 to −i has argument −π/4 (−45°). -/
theorem neg_one_to_neg_I_direction : arg (1 - I) = -(π / 4) := by
  have hmem : (1 - I).arg ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    rw [Set.mem_Ioo, ← abs_lt]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by
      rw [Complex.sub_re, Complex.one_re, Complex.I_re]
      norm_num))
  have htan : Real.tan ((1 - I).arg) = -1 := by
    rw [Complex.tan_arg]
    rw [Complex.sub_im, Complex.one_im, Complex.I_im, Complex.sub_re, Complex.one_re, Complex.I_re]
    norm_num
  have h1 : Real.arctan (Real.tan ((1 - I).arg)) = (1 - I).arg :=
    Real.arctan_tan (x := (1 - I).arg) hmem.1 hmem.2
  have h2 : Real.arctan (Real.tan ((1 - I).arg)) = -(π / 4) := by
    rw [htan]
    rw [← Real.arctan_one]
    rw [← Real.arctan_neg]
  exact h1.symm.trans h2

-- ===== 元5: 90° 正交 =====

/-- **两半轴 90° 正交 (内积)**: re((1+i)·conj(1−i)) = 0 — 折线的两根半轴
    内积为 0, 即 90° 直角 (共轭元: conj(1−i) = 1+i).
    English: the two fold segments are orthogonal: the Hermitian inner
    product (1+i)·conj(1−i) has real part 0. -/
theorem fold_axes_orthogonal_re : re (((1 + I) : ℂ) * conj (1 - I)) = 0 := by
  rw [map_sub, map_one, Complex.conj_I]
  norm_num [Complex.I_mul_I]

/-- **两半轴方向差 = 90°**: arg(1+i) − arg(1−i) = π/2 — 折线的两根半轴
    方向夹角恰为直角.
    English: the fold segments differ in direction by exactly 90°. -/
theorem fold_axes_arg_diff : (1 + I).arg - (1 - I).arg = π / 2 := by
  rw [neg_one_to_I_direction, neg_one_to_neg_I_direction]
  ring

-- ===== 元6: 折线半段长度 =====

/-- **折线半段长度 = √2**: ‖1+i‖ = √2 — 从 −1 到 i 的 45° 连线长度.
    English: the fold segment from −1 to i has length √2. -/
theorem fold_length_sqrt_two : ‖(1 + I : ℂ)‖ = √2 := by
  have hsq : (‖(1 + I : ℂ)‖ : ℝ) ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    rw [Complex.add_re, Complex.one_re, Complex.I_re, Complex.add_im, Complex.one_im, Complex.I_im]
    norm_num
  have hsqrt : (√2 : ℝ) ^ 2 = 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (‖(1 + I : ℂ)‖ : ℝ) ^ 2 = (√2 : ℝ) ^ 2 := by rw [hsq, hsqrt]
  have habs : |(‖(1 + I : ℂ)‖ : ℝ)| = |(√2 : ℝ)| := by
    rw [← sq_eq_sq_iff_abs_eq_abs (‖(1 + I : ℂ)‖ : ℝ) (√2 : ℝ)]
    exact hpow
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg 2)] at habs
  exact habs

/-- **对偶半段长度 = √2**: ‖1−i‖ = √2.
    English: the fold segment from −1 to −i has length √2. -/
theorem fold_length_neg_sqrt_two : ‖(1 - I : ℂ)‖ = √2 := by
  have hsq : (‖(1 - I : ℂ)‖ : ℝ) ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    rw [Complex.sub_re, Complex.one_re, Complex.I_re, Complex.sub_im, Complex.one_im, Complex.I_im]
    norm_num
  have hsqrt : (√2 : ℝ) ^ 2 = 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (‖(1 - I : ℂ)‖ : ℝ) ^ 2 = (√2 : ℝ) ^ 2 := by rw [hsq, hsqrt]
  have habs : |(‖(1 - I : ℂ)‖ : ℝ)| = |(√2 : ℝ)| := by
    rw [← sq_eq_sq_iff_abs_eq_abs (‖(1 - I : ℂ)‖ : ℝ) (√2 : ℝ)]
    exact hpow
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg 2)] at habs
  exact habs

-- ===== 组装7: 极坐标形式 (方向元 + 长度元 → e^{±iπ/4} 显式) =====

/-- **√2 的复数逆**: (√2:ℂ)⁻¹ = ↑(√2/2) — 组装: ofReal 桥 + sq_sqrt.
    English: the inverse of √2 in ℂ is √2/2. -/
theorem sqrt_two_inv : (√2 : ℂ)⁻¹ = ((√2 / 2 : ℝ) : ℂ) := by
  have hsqrt_ne : (√2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    norm_num
  have hsqrt : (√2 : ℂ) ^ 2 = 2 := by
    rw [sq]
    rw [← Complex.ofReal_mul]
    rw [← Complex.ofReal_ofNat]
    rw [Complex.ofReal_inj]
    rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [hsqrt_ne]
  -- 目标: 1 = ↑√2 · ↑(√2/2) — ofReal 桥收归一
  rw [← Complex.ofReal_one]
  rw [← Complex.ofReal_mul (r := √2) (s := √2 / 2)]
  rw [Complex.ofReal_inj]
  -- 目标: 1 = √2 * (√2 / 2) (ℝ)
  have hsqr : (√2 : ℝ) * √2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    1 = (√2 * √2) / 2 := by rw [hsqr]; norm_num
    _ = √2 * (√2 / 2) := by ring

/-- **e^{iπ/4} 显式**: e^{iπ/4} = (√2/2)(1+i) — 组装: 极坐标元
    (‖z‖·e^{i·arg z} = z) 代入方向元 (arg = π/4) 与长度元 (‖1+i‖ = √2).
    English: e^{iπ/4} = (√2/2)(1+i) — assembled from the polar unit
    ‖z‖·e^{i·arg z} = z with the direction and length units. -/
theorem exp_pi_div_four_form : exp ((π / 4 : ℝ) * I) = ((√2 / 2 : ℝ) : ℂ) * (1 + I) := by
  have hsqrt_ne : (√2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    norm_num
  have h : ‖(1 + I : ℂ)‖ * exp ((π / 4 : ℝ) * I) = 1 + I := by
    calc
      ‖(1 + I : ℂ)‖ * exp ((π / 4 : ℝ) * I) = ‖(1 + I : ℂ)‖ * exp (arg (1 + I) * I) := by
        congr 1
        rw [← neg_one_to_I_direction]
      _ = 1 + I := Complex.norm_mul_exp_arg_mul_I _
  have h2 : (√2 : ℂ) * exp ((π / 4 : ℝ) * I) = 1 + I := by
    rw [fold_length_sqrt_two] at h
    exact h
  calc
    exp ((π / 4 : ℝ) * I) = ((√2 : ℂ) * exp ((π / 4 : ℝ) * I)) * (√2 : ℂ)⁻¹ := by
      field_simp [hsqrt_ne]
    _ = (1 + I) * (√2 : ℂ)⁻¹ := by rw [h2]
    _ = ((√2 / 2 : ℝ) : ℂ) * (1 + I) := by
      rw [sqrt_two_inv]
      ring

/-- **e^{−iπ/4} 显式**: e^{−iπ/4} = (√2/2)(1−i) — 对偶半轴极坐标.
    English: e^{−iπ/4} = (√2/2)(1−i) — the dual segment polar form. -/
theorem exp_neg_pi_div_four_form : exp (-(π / 4 : ℝ) * I) = ((√2 / 2 : ℝ) : ℂ) * (1 - I) := by
  have hsqrt_ne : (√2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    norm_num
  have h : ‖(1 - I : ℂ)‖ * exp (-(π / 4 : ℝ) * I) = 1 - I := by
    calc
      ‖(1 - I : ℂ)‖ * exp (-(π / 4 : ℝ) * I) = ‖(1 - I : ℂ)‖ * exp (arg (1 - I) * I) := by
        congr 1
        rw [← Complex.ofReal_neg]
        rw [← neg_one_to_neg_I_direction]
      _ = 1 - I := Complex.norm_mul_exp_arg_mul_I _
  have h2 : (√2 : ℂ) * exp (-(π / 4 : ℝ) * I) = 1 - I := by
    rw [fold_length_neg_sqrt_two] at h
    exact h
  calc
    exp (-(π / 4 : ℝ) * I) = ((√2 : ℂ) * exp (-(π / 4 : ℝ) * I)) * (√2 : ℂ)⁻¹ := by
      field_simp [hsqrt_ne]
    _ = (1 - I) * (√2 : ℂ)⁻¹ := by rw [h2]
    _ = ((√2 / 2 : ℝ) : ℂ) * (1 - I) := by
      rw [sqrt_two_inv]
      ring

-- ===== 组装8: 假复平面 (90° 正交轴的唯一实坐标分解) =====

/-- **45° 组合的实部**: re(u·e^{iπ/4} + v·e^{−iπ/4}) = (√2/2)(u+v) — 折线
    轴组合的实部由两实坐标之和给出 (坐标全实数).
    English: real part of a 45°-basis combination. -/
lemma fold_re (u v : ℝ) :
    re ((u : ℂ) * exp ((π / 4 : ℝ) * I) + (v : ℂ) * exp (-(π / 4 : ℝ) * I)) =
      (√2 / 2) * (u + v) := by
  rw [exp_pi_div_four_form, exp_neg_pi_div_four_form]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.sub_re, Complex.I_re, zero_mul, add_zero]
  ring

/-- **45° 组合的虚部**: im(u·e^{iπ/4} + v·e^{−iπ/4}) = (√2/2)(u−v) — 虚部由
    两实坐标之差给出 (符号取号来自正交轴).
    English: imaginary part of a 45°-basis combination. -/
lemma fold_im (u v : ℝ) :
    im ((u : ℂ) * exp ((π / 4 : ℝ) * I) + (v : ℂ) * exp (-(π / 4 : ℝ) * I)) =
      (√2 / 2) * (u - v) := by
  rw [exp_pi_div_four_form, exp_neg_pi_div_four_form]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_im, Complex.sub_im, Complex.I_im, zero_mul, add_zero]
  ring

/-- **假复平面构造 (90° 正交轴分解)**: 任意复数 z 在两根 45° 轴上唯一实数
    分解 — z = u·e^{iπ/4} + v·e^{−iπ/4}, u = (√2/2)(re+im), v = (√2/2)(re−im).
    两根轴互相 90° 正交, 坐标 u, v 全是实数 ("从负侧实轴取复数, 从正交的
    另一根实轴取号" — 数值与符号分离).
    English: every z decomposes uniquely on the two orthogonal 45° axes with
    real coordinates u = (√2/2)(re+im), v = (√2/2)(re−im). -/
theorem fold_basis_decomp (z : ℂ) :
    z = (((√2 / 2) * (z.re + z.im) : ℝ) : ℂ) * exp ((π / 4 : ℝ) * I) +
      (((√2 / 2) * (z.re - z.im) : ℝ) : ℂ) * exp (-(π / 4 : ℝ) * I) := by
  have hc2r : ((√2 / 2 : ℝ) ^ 2) = 1 / 2 := by
    rw [div_pow]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz]
  apply Complex.ext
  · -- re 侧: z.re = c²·2·z.re (c = √2/2)
    rw [fold_re]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · -- im 侧: z.im = c²·2·z.im
    rw [fold_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

/-- **分解唯一**: 45° 轴上的实坐标分解唯一 — (u₁,v₁) 与 (u₂,v₂) 给出同一
    复数 ⟹ u₁ = u₂ ∧ v₁ = v₂ (两根轴构成合法基底).
    English: the 45°-basis decomposition is unique. -/
theorem fold_basis_unique {u₁ v₁ u₂ v₂ : ℝ}
    (h : (u₁ : ℂ) * exp ((π / 4 : ℝ) * I) + (v₁ : ℂ) * exp (-(π / 4 : ℝ) * I) =
      (u₂ : ℂ) * exp ((π / 4 : ℝ) * I) + (v₂ : ℂ) * exp (-(π / 4 : ℝ) * I)) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  have hre : (√2 / 2) * (u₁ + v₁) = (√2 / 2) * (u₂ + v₂) := by
    have h0 := congrArg Complex.re h
    rw [fold_re, fold_re] at h0
    exact h0
  have him : (√2 / 2) * (u₁ - v₁) = (√2 / 2) * (u₂ - v₂) := by
    have h0 := congrArg Complex.im h
    rw [fold_im, fold_im] at h0
    exact h0
  have hc : (√2 / 2 : ℝ) ≠ 0 := by norm_num
  have hs : u₁ + v₁ = u₂ + v₂ := mul_left_cancel₀ hc hre
  have hd : u₁ - v₁ = u₂ - v₂ := mul_left_cancel₀ hc him
  constructor <;> linarith

/-- **坐标全实数**: 任意复数在 90° 正交折线轴上都有实数坐标 —
    ∃ u v : ℝ, z = u·e^{iπ/4} + v·e^{−iπ/4} ("假复平面" = 两根 45° 实轴,
    互相 90° 正交, 坐标全是实数).
    English: every z has real coordinates on the two orthogonal 45° axes. -/
theorem fold_coords_real (z : ℂ) :
    ∃ u v : ℝ, z = (u : ℂ) * exp ((π / 4 : ℝ) * I) + (v : ℂ) * exp (-(π / 4 : ℝ) * I) := by
  refine ⟨√2 / 2 * (z.re + z.im), √2 / 2 * (z.re - z.im), ?_⟩
  exact fold_basis_decomp z

-- ===== 等价: 折线轴 ↔ 复平面虚轴 (观测前的锚定) =====

/-- **折线端点 = 虚轴单位**: ±i 都在虚轴上 (re = 0) — 折线的两个顶点
    就是虚轴的两个单位点.
    English: the fold vertices ±i lie on the imaginary axis (re = 0):
    the fold endpoints are the imaginary-axis units. -/
theorem fold_vertices_are_imag_units : re I = 0 ∧ re (-I) = 0 := by
  constructor <;> simp

/-- **虚轴 = 折线端点生成的直线**: {z | re z = 0} = {t·i} — 折线的两端点
    ±i 连线就是标准虚轴 (折线把虚轴撑出来: 数学界的虚轴 = 折线端点连线).
    English: the imaginary axis is the line spanned by the fold endpoints
    ±i — the fold generates the classical imaginary axis. -/
theorem imag_axis_eq_span_fold_vertices :
    {z : ℂ | re z = 0} = {z : ℂ | ∃ t : ℝ, z = t * I} := by
  ext z
  constructor
  · intro hz
    refine ⟨z.im, ?_⟩
    apply Complex.ext
    · simpa using hz
    · simp
  · rintro ⟨t, rfl⟩
    simp

/-- **两种生成同一单位**: 从 −1 旋转 90° 与从 1 旋转 90° 到达同一点 i —
    折线构造的虚轴单位 = 标准虚轴单位 (生成方式不同, 轴相同).
    English: the fold construction (−1 rotated by 90°) and the standard
    construction (1 rotated by 90°) reach the same unit i: same axis. -/
theorem imag_axis_unit_from_fold :
    (-1 : ℂ) * exp (-π / 2 * I) = exp ((π / 2) * I) := by
  rw [I_from_neg_one_rotation, I_eq_exp_half_pi]

/-- **折线方向差 = 虚轴方向**: e^{iπ/4} − e^{−iπ/4} = (√2/2)·(2i) — 折线
    的两根半轴之差沿虚轴方向 (90° 正交结构撑出虚轴).
    English: the difference of the two fold directions is along the
    imaginary axis: the 90°-orthogonal fold generates the imaginary
    direction. -/
theorem fold_axes_difference_is_imag_direction :
    exp ((π / 4 : ℝ) * I) - exp (-(π / 4 : ℝ) * I) = ((√2 / 2 : ℝ) : ℂ) * (2 * I) := by
  rw [exp_pi_div_four_form, exp_neg_pi_div_four_form]
  ring

/-- **方向差显式**: e^{iπ/4} − e^{−iπ/4} = √2·i.
    English: the fold direction difference equals √2·i explicitly. -/
theorem fold_axes_difference_sqrt_two :
    exp ((π / 4 : ℝ) * I) - exp (-(π / 4 : ℝ) * I) = √2 * I := by
  rw [fold_axes_difference_is_imag_direction]
  apply Complex.ext
  · simp
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
      Complex.I_re, mul_zero, zero_mul, add_zero]
    norm_num [← sq, Real.sq_sqrt]

/-- **坐标字典 (折线 → 标准)**: 折线坐标 u,v 恢复标准 re/im —
    re = (√2/2)(u+v), im = (√2/2)(u−v) — 轴等价 ⟹ 坐标可换.
    English: the fold coordinates u, v recover the standard re/im:
    re = (√2/2)(u+v), im = (√2/2)(u−v). -/
theorem fold_coords_to_standard (u v : ℝ) :
    re ((u : ℂ) * exp ((π / 4 : ℝ) * I) + (v : ℂ) * exp (-(π / 4 : ℝ) * I)) =
        (√2 / 2) * (u + v) ∧
    im ((u : ℂ) * exp ((π / 4 : ℝ) * I) + (v : ℂ) * exp (-(π / 4 : ℝ) * I)) =
        (√2 / 2) * (u - v) := by
  constructor
  · exact fold_re u v
  · exact fold_im u v

/-- **坐标字典往返**: 标准坐标 → 折线坐标 (fold_basis_decomp) → 折线坐标
    → 标准坐标 (fold_coords_to_standard) 恢复原 re/im — 双向往返恒等.
    English: roundtrip — standard to fold coordinates and back recovers
    the original re/im: the two coordinate systems are equivalent. -/
theorem fold_coord_roundtrip (z : ℂ) :
    re ((((√2 / 2) * (z.re + z.im) : ℝ) : ℂ) * exp ((π / 4 : ℝ) * I) +
        (((√2 / 2) * (z.re - z.im) : ℝ) : ℂ) * exp (-(π / 4 : ℝ) * I)) = z.re ∧
    im ((((√2 / 2) * (z.re + z.im) : ℝ) : ℂ) * exp ((π / 4 : ℝ) * I) +
        (((√2 / 2) * (z.re - z.im) : ℝ) : ℂ) * exp (-(π / 4 : ℝ) * I)) = z.im := by
  constructor
  · rw [fold_re]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · rw [fold_im]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

-- ===== 直觉层锚定: 三对应 (实数性 / 正负号 / 虚数性) =====

/-- **直觉对应 1a — 虚轴坐标 = 实数**: 虚轴上任意点 t·i 的实部 re = 0 是实数,
    坐标 t 是实数 — 虚轴没有引入新数, 只有方向 (虚轴的"坐标"全是实数).
    English: coordinates on the imaginary axis are real (re = 0, t ∈ ℝ):
    the imaginary axis introduces no new numbers, only a direction. -/
theorem imag_axis_coords_real (t : ℝ) : (t * I : ℂ).re = 0 := by
  simp

-- 直觉对应 1b — 折线坐标 = 实数: 折线上任意点的坐标 u, v 是实数
-- (fold_coords_real 已证: 任意 z 有实坐标 u = (√2/2)(re+im), v = (√2/2)(re−im))
-- — 与虚轴同: 折线也没有新数, 只有方向 (折线的"坐标"全是实数).
-- English: coordinates on the fold are real (fold_coords_real): every z
-- has real coordinates u, v — like the imaginary axis, the fold
-- introduces no new numbers.

/-- **直觉对应 2a — 虚轴正负号**: 虚轴的两个方向 i 与 −i 相反 — 虚部取正负号
    ("虚部有正负号").
    English: the imaginary axis carries both signs: i and −i are opposite. -/
theorem imag_axis_units_opposite : (-I : ℂ) ≠ I := by
  intro h
  have : (-I : ℂ).im = I.im := congrArg Complex.im h
  norm_num at this

/-- **直觉对应 2b — 折线纵坐标正负号**: ±i 在折线轴上的 v 坐标符号相反 —
    v(i) = −√2/2, v(−i) = +√2/2 ("折线也可以取纵坐标有正负号").
    English: the fold takes both signs: the v-coordinates of i and −i
    have opposite signs. -/
theorem fold_v_coords_opposite :
    (√2 / 2) * (I.re - I.im) = -(√2 / 2) ∧
    (√2 / 2) * ((-I).re - (-I).im) = √2 / 2 := by
  constructor <;> norm_num

/-- **直觉对应 3a — 虚轴代表虚数**: 虚轴上非零点都是虚数 — t ≠ 0 ⟹ im(t·i) ≠ 0
    (不在实数轴上).
    English: nonzero points on the imaginary axis are imaginary numbers
    (im ≠ 0). -/
theorem imag_axis_points_imaginary {t : ℝ} (ht : t ≠ 0) : (t * I : ℂ).im ≠ 0 := by
  simpa using ht

/-- **直觉对应 3b — 折线的投影也是虚数**: 折线点 z = u·e^{iπ/4} + v·e^{−iπ/4}
    的虚部 = (√2/2)(u−v) — 虚数性由两实坐标之差决定: 差为 0 (u = v) 在实轴
    方向, 差非 0 即虚数 ("折线的投影也是虚数" — 虚分量 = 实坐标差, 符号取号
    来自正交轴).
    English: the fold's imaginary part is (√2/2)(u−v): a fold point is
    imaginary iff its two real coordinates differ (the imaginary component
    is the difference of the real coordinates). -/
theorem fold_im_zero_iff (u v : ℝ) :
    im ((u : ℂ) * exp ((π / 4 : ℝ) * I) + (v : ℂ) * exp (-(π / 4 : ℝ) * I)) = 0 ↔ u = v := by
  rw [fold_im]
  constructor
  · intro h
    have hc : (√2 / 2 : ℝ) ≠ 0 := by norm_num
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc)
  · intro h
    rw [h]
    ring

end ZeroRelative

namespace ZeroRelative

-- ===== 拓扑等价与捋直 (假复平面 ≅ R²; 折线在折叠坐标里是直线) =====

/-- **折叠坐标映射 (ℝ² → ℂ)**: (u,v) ↦ u·e^{iπ/4} + v·e^{−iπ/4} — 假复平面
    的坐标嵌入.
    English: the fold-coordinate embedding of the fake plane. -/
noncomputable def foldCoordToC : ℝ × ℝ → ℂ :=
  fun p => p.1 * exp ((π / 4 : ℝ) * I) + p.2 * exp (-(π / 4 : ℝ) * I)

/-- **逆映射 (ℂ → ℝ²)**: z ↦ (u,v) = ((√2/2)(re+im), (√2/2)(re−im)).
    English: the inverse coordinate map. -/
noncomputable def foldCoordFromC : ℂ → ℝ × ℝ :=
  fun z => (√2 / 2 * (z.re + z.im), √2 / 2 * (z.re - z.im))

/-- **左逆**: foldCoordFromC (foldCoordToC (u,v)) = (u,v) — 折叠坐标嵌入后
    取回原坐标 (线性互逆的一侧).
    English: left inverse — embedding then extracting recovers (u,v). -/
theorem foldCoord_left_inv (p : ℝ × ℝ) : foldCoordFromC (foldCoordToC p) = p := by
  -- 先用折叠组合元算 re/im (未展开的整体模式)
  have hre : (foldCoordToC p).re = (√2 / 2) * (p.1 + p.2) := by
    unfold foldCoordToC
    rw [fold_re]
  have him : (foldCoordToC p).im = (√2 / 2) * (p.1 - p.2) := by
    unfold foldCoordToC
    rw [fold_im]
  apply Prod.ext
  · -- u 恢复: c(c(u+v) + c(u−v)) = u
    simp [foldCoordFromC, hre, him]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · -- v 恢复: c(c(u+v) − c(u−v)) = v
    simp [foldCoordFromC, hre, him]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

/-- **右逆**: foldCoordToC (foldCoordFromC z) = z — 任意复数被折叠坐标
    还原 (fold_basis_decomp 的映射形式).
    English: right inverse — every z is recovered from its fold coordinates. -/
theorem foldCoord_right_inv (z : ℂ) : foldCoordToC (foldCoordFromC z) = z := by
  -- foldCoordFromC z = ((√2/2)(re+im), (√2/2)(re−im))
  -- foldCoordToC 代入 = fold_basis_decomp 右侧
  dsimp [foldCoordToC, foldCoordFromC]
  exact (fold_basis_decomp z).symm

/-- **捋直 1 — 假复平面与复平面同胚**: 折叠坐标映射是 ℝ² 与 ℂ 的同胚 —
    假复平面 ≅ R² ≅ 复平面 (拓扑等价: 双射 + 双向连续).
    English: the fake plane is homeomorphic to the complex plane:
    ℝ² ≃ₜ ℂ via the fold coordinates. -/
noncomputable def foldCoordHomeo : ℝ × ℝ ≃ₜ ℂ where
  toFun := foldCoordToC
  invFun := foldCoordFromC
  left_inv := foldCoord_left_inv
  right_inv := foldCoord_right_inv
  continuous_toFun := by
    unfold foldCoordToC
    continuity
  continuous_invFun := by
    unfold foldCoordFromC
    continuity

-- ===== 捋直元族 (Straighten): 弧长参数化 γ 的拓扑/几何/分析三面 =====

/-- **折线点集**: 从 −1 出发沿 ±45° 的两条射线 (V 形折线, 两半轴共点 −1).
    English: the fold set — two rays from −1 along ±45°. -/
def foldSet : Set ℂ :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ (z = -1 + t * exp ((π / 4 : ℝ) * I) ∨ z = -1 + t * exp (-(π / 4 : ℝ) * I))}

/-- **捋直操作 (弧长参数化)**: γ : ℝ → 折线 — s ≥ 0 走正支 (到 i 方向),
    s < 0 走负支 (到 −i 方向) — 单位速度参数, 把 V 形折线捋成实数轴.
    English: the straightening map γ — arc-length parametrization of the
    fold: s ≥ 0 on the +45° arm, s < 0 on the −45° arm. -/
noncomputable def foldArc : ℝ → ℂ :=
  fun s => if 0 ≤ s then -1 + s * exp ((π / 4 : ℝ) * I) else -1 + (-s) * exp (-(π / 4 : ℝ) * I)

/-- **正支公式**: s ≥ 0 时 γ(s) = −1 + s·e^{iπ/4} (净元: 分支化简).
    English: on the positive arm γ(s) = −1 + s·e^{iπ/4}. -/
theorem foldArc_pos (s : ℝ) (hs : 0 ≤ s) :
    foldArc s = -1 + s * exp ((π / 4 : ℝ) * I) := by
  unfold foldArc
  rw [if_pos hs]

/-- **负支公式**: s ≤ 0 时 γ(s) = −1 + (−s)·e^{−iπ/4} (净元: 分支化简,
    s = 0 处两分支一致).
    English: on the negative arm γ(s) = −1 + (−s)·e^{−iπ/4}. -/
theorem foldArc_neg (s : ℝ) (hs : s ≤ 0) :
    foldArc s = -1 + (-s) * exp (-(π / 4 : ℝ) * I) := by
  unfold foldArc
  by_cases h : 0 ≤ s
  · -- s = 0: 两支相等
    have hs0 : s = 0 := le_antisymm hs h
    rw [if_pos h, hs0]
    simp
  · rw [if_neg h]

/-- **值域**: γ(s) ∈ 折线 ∀ s (捋直映射的值落在折线上).
    English: γ maps ℝ into the fold. -/
theorem foldArc_mem (s : ℝ) : foldArc s ∈ foldSet := by
  unfold foldSet
  by_cases h : 0 ≤ s
  · exact ⟨s, h, Or.inl (foldArc_pos s h)⟩
  · refine ⟨-s, ?_, Or.inr ?_⟩
    · exact neg_nonneg.mpr (le_of_lt (not_le.mp h))
    · simpa [Complex.ofReal_neg] using foldArc_neg s (le_of_not_ge h)

-- ===== A 元 (分析层): γ 的连续/可微/单位速度 =====

/-- **A1 捋直映射连续**: γ 连续 — 顶点 −1 处两支一致 (s = 0 两侧同点),
    分析层的捋直基础.
    English: the straightening map is continuous (both arms agree at −1). -/
theorem continuous_foldArc : Continuous foldArc := by
  unfold foldArc
  -- if 0 ≤ s then f' else g': Continuous.if_le (f = const 0, g = id)
  -- 两分支连续 + 边界 (s = 0) 一致
  refine Continuous.if_le (f := fun _ : ℝ => (0 : ℝ)) (g := fun x : ℝ => x)
    (f' := fun s : ℝ => -1 + s * exp ((π / 4 : ℝ) * I))
    (g' := fun s : ℝ => -1 + (-s) * exp (-(π / 4 : ℝ) * I))
    ?_ ?_ continuous_const continuous_id ?_
  · -- 正支连续
    exact (continuous_const.add
      ((Complex.continuous_ofReal).mul (continuous_const : Continuous fun _ : ℝ => exp ((π / 4 : ℝ) * I))))
  · -- 负支连续
    exact (continuous_const.add
      ((Complex.continuous_ofReal.neg).mul (continuous_const : Continuous fun _ : ℝ => exp (-(π / 4 : ℝ) * I))))
  · -- 边界: f x = g x (x = 0) 时两分支一致
    intro x hx
    have hx0 : x = 0 := hx.symm
    rw [hx0]
    simp

/-- **A2 正支可微**: s > 0 时 γ'(s) = e^{iπ/4} (分析元: 局部导数).
    English: on the positive arm γ' = e^{iπ/4}. -/
theorem foldArc_hasDerivAt_pos {s : ℝ} (hs : 0 < s) :
    HasDerivAt foldArc (exp ((π / 4 : ℝ) * I)) s := by
  have hder : HasDerivAt (fun x : ℝ => -1 + x * exp ((π / 4 : ℝ) * I))
      (exp ((π / 4 : ℝ) * I)) s := by
    simpa using ((hasDerivAt_id s).smul_const (exp ((π / 4 : ℝ) * I))).const_add (-1 : ℂ)
  have hEq : foldArc =ᶠ[𝓝 s] fun x : ℝ => -1 + x * exp ((π / 4 : ℝ) * I) := by
    have hIoi : ∀ᶠ x in 𝓝 s, x ∈ Set.Ioi (0 : ℝ) := isOpen_Ioi.mem_nhds hs
    refine hIoi.mono ?_
    intro x hx
    exact foldArc_pos x (le_of_lt hx)
  exact hder.congr_of_eventuallyEq hEq

/-- **A2' 负支可微**: s < 0 时 γ'(s) = −e^{−iπ/4}.
    English: on the negative arm γ' = −e^{−iπ/4}. -/
theorem foldArc_hasDerivAt_neg {s : ℝ} (hs : s < 0) :
    HasDerivAt foldArc (-exp (-(π / 4 : ℝ) * I)) s := by
  have hder : HasDerivAt (fun x : ℝ => -1 + (-x) * exp (-(π / 4 : ℝ) * I))
      (-exp (-(π / 4 : ℝ) * I)) s := by
    simpa using (((hasDerivAt_id s).neg.smul_const (exp (-(π / 4 : ℝ) * I))).const_add (-1 : ℂ))
  have hEq : foldArc =ᶠ[𝓝 s] fun x : ℝ => -1 + (-x) * exp (-(π / 4 : ℝ) * I) := by
    have hIio : ∀ᶠ x in 𝓝 s, x ∈ Set.Iio (0 : ℝ) := isOpen_Iio.mem_nhds hs
    refine hIio.mono ?_
    intro x hx
    exact foldArc_neg x (le_of_lt hx)
  exact hder.congr_of_eventuallyEq hEq

/-- **A3 单位速度 (正支)**: s > 0 时 ‖γ'(s)‖ = 1 — 弧长参数 (分析性质:
    参数 s 就是弧长).
    English: unit speed on the positive arm: ‖γ'(s)‖ = 1. -/
theorem foldArc_unit_speed_pos {s : ℝ} (hs : 0 < s) : ‖deriv foldArc s‖ = 1 := by
  have hder := foldArc_hasDerivAt_pos hs
  rw [hder.deriv]
  rw [Complex.norm_exp]
  simp

/-- **A3' 单位速度 (负支)**: s < 0 时 ‖γ'(s)‖ = 1.
    English: unit speed on the negative arm. -/
theorem foldArc_unit_speed_neg {s : ℝ} (hs : s < 0) : ‖deriv foldArc s‖ = 1 := by
  have hder := foldArc_hasDerivAt_neg hs
  rw [hder.deriv]
  rw [norm_neg]
  rw [Complex.norm_exp]
  simp

-- ===== G 元 (几何层): 弧长保持 / 折线在折叠坐标 = 直线 =====

/-- **G1 同支保弧长 (正支)**: a, b ≥ 0 ⟹ ‖γ(b)−γ(a)‖ = |b−a| — 折线正支
    的弧长 = 参数差 (弧长参数化: 沿支的距离 = 参数距离).
    English: arc length on the positive arm equals parameter difference. -/
theorem foldArc_dist_pos (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖foldArc b - foldArc a‖ = |b - a| := by
  rw [foldArc_pos b hb, foldArc_pos a ha]
  calc
    ‖(-1 + b * exp ((π / 4 : ℝ) * I)) - (-1 + a * exp ((π / 4 : ℝ) * I))‖
        = ‖(b - a) * exp ((π / 4 : ℝ) * I)‖ := by congr 1; ring
    _ = |b - a| * ‖exp ((π / 4 : ℝ) * I)‖ := by
      rw [norm_mul]
      rw [← Complex.ofReal_sub]
      rw [Complex.norm_real (b - a)]
      rw [Real.norm_eq_abs]
    _ = |b - a| := by
      rw [Complex.norm_exp]
      simp

/-- **G1' 同支保弧长 (负支)**: a, b ≤ 0 ⟹ ‖γ(b)−γ(a)‖ = |b−a|.
    English: arc length on the negative arm equals parameter difference. -/
theorem foldArc_dist_neg (a b : ℝ) (ha : a ≤ 0) (hb : b ≤ 0) :
    ‖foldArc b - foldArc a‖ = |b - a| := by
  rw [foldArc_neg b hb, foldArc_neg a ha]
  calc
    ‖(-1 + (-b) * exp (-(π / 4 : ℝ) * I)) - (-1 + (-a) * exp (-(π / 4 : ℝ) * I))‖
        = ‖((-b) - (-a)) * exp (-(π / 4 : ℝ) * I)‖ := by congr 1; ring
    _ = |b - a| * ‖exp (-(π / 4 : ℝ) * I)‖ := by
      rw [norm_mul]
      rw [← Complex.ofReal_neg, ← Complex.ofReal_neg]
      rw [← Complex.ofReal_sub]
      rw [Complex.norm_real ((-b) - (-a))]
      rw [Real.norm_eq_abs]
      rw [show (-b : ℝ) - (-a) = -(b - a) by ring]
      rw [abs_neg]
    _ = |b - a| := by
      rw [Complex.norm_exp]
      simp

/-- **G2 诚实边界 — 跨支不保弧长**: ‖γ(−1)−γ(1)‖ = √2 ≠ 2 = |−1−1| — 折线
    的弯折是真实的: 拓扑同胚 (捋直) 存在, 但跨支直线距离被弯折压缩
    (度量结构不随拓扑捋直保持; 只有同支保弧长).
    English: honest boundary — across arms the fold distance is √2, not
    2: the bend is real, only same-arm arc length is preserved. -/
theorem foldArc_cross_dist_sqrt_two : ‖foldArc (-1) - foldArc 1‖ = √2 := by
  rw [foldArc_neg (-1) (by norm_num), foldArc_pos 1 (by norm_num)]
  -- 归一系数 (精确 rw, 禁 norm_num 重排指数形): -↑(-1) = ↑1 = 1, 1·e = e
  rw [← Complex.ofReal_neg]
  rw [show (- -1 : ℝ) = 1 by norm_num]
  rw [Complex.ofReal_one]
  rw [one_mul, one_mul]
  -- 目标: ‖−1 + e⁻ − (−1 + e⁺)‖ = √2 — 负号重排 + 距离对称
  have h : -1 + exp (-(π / 4 : ℝ) * I) - (-1 + exp ((π / 4 : ℝ) * I))
      = -(exp ((π / 4 : ℝ) * I) - exp (-(π / 4 : ℝ) * I)) := by
    ring
  rw [h]
  rw [norm_neg]
  rw [fold_axes_difference_sqrt_two]
  -- ‖√2·I‖ = √2
  rw [norm_mul]
  rw [Complex.norm_real (√2)]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [Complex.norm_I]
  ring

-- ===== T 元 (拓扑层): 折线 ≅ R 的同胚 =====

/-- **逆捋直**: 折线点 → 参数 s — 折叠坐标判定分支 (u > −√2/2 走正支,
    u = −√2/2 走负支; 顶点 −1 处两分支一致给 0).
    English: the inverse straightening — a fold point to its parameter s. -/
noncomputable def foldArg (z : foldSet) : ℝ :=
  if (√2 / 2) * (z.1.re + z.1.im) > -(√2 / 2) then
    (√2 / 2) * (z.1.re + z.1.im) + √2 / 2
  else
    -((√2 / 2) * (z.1.re - z.1.im) + √2 / 2)

/-- **折线点 u 坐标下界**: z ∈ 折线 ⟹ u ≥ −√2/2 (判定引理).
    English: u-coordinate lower bound on the fold. -/
theorem fold_u_ge_neg_c {z : ℂ} (hz : z ∈ foldSet) :
    -(√2 / 2) ≤ (√2 / 2) * (z.re + z.im) := by
  rcases hz with ⟨t, ht, hz | hz⟩
  · rw [hz]
    rw [exp_pi_div_four_form]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero, zero_add]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [mul_nonneg ht (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · rw [hz]
    rw [exp_neg_pi_div_four_form]
    simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero]
    ring_nf
    nlinarith [mul_nonneg ht (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- **折线点 v 坐标下界**: z ∈ 折线 ⟹ v ≥ −√2/2 (判定引理).
    English: v-coordinate lower bound on the fold. -/
theorem fold_v_ge_neg_c {z : ℂ} (hz : z ∈ foldSet) :
    -(√2 / 2) ≤ (√2 / 2) * (z.re - z.im) := by
  rcases hz with ⟨t, ht, hz | hz⟩
  · rw [hz]
    rw [exp_pi_div_four_form]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero, zero_add]
    ring_nf
    nlinarith [mul_nonneg ht (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · rw [hz]
    rw [exp_neg_pi_div_four_form]
    simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [mul_nonneg ht (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- **负支判定**: z ∈ 折线且 v > −√2/2 ⟹ u = −√2/2 (负支上 u 恒定).
    English: on the fold, v > −√2/2 forces the negative arm (u constant). -/
theorem fold_u_neg_c_of_v_gt {z : ℂ} (hz : z ∈ foldSet)
    (hv : (√2 / 2) * (z.re - z.im) > -(√2 / 2)) :
    (√2 / 2) * (z.re + z.im) = -(√2 / 2) := by
  rcases hz with ⟨t, ht, hz | hz⟩
  · -- 正支: v = −c 恒定 — 与 hv 矛盾
    rw [hz] at hv ⊢
    rw [exp_pi_div_four_form] at hv ⊢
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero, zero_add] at hv ⊢
    ring_nf at hv ⊢
    nlinarith
  · -- 负支: u = −c
    rw [hz]
    rw [exp_neg_pi_div_four_form]
    simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero]
    ring_nf

/-- **折叠坐标函数**: u = (√2/2)(re+im), v = (√2/2)(re−im) — 45° 基底的两分量.
    English: the fold coordinate functions u, v. -/
def fold_u : ℂ → ℝ := fun z => (√2 / 2) * (z.re + z.im)

def fold_v : ℂ → ℝ := fun z => (√2 / 2) * (z.re - z.im)

/-- **分析层连续元**: u/v 坐标连续.
    English: the fold coordinates u, v are continuous. -/
theorem fold_u_cont : Continuous fold_u := by
  unfold fold_u
  continuity

theorem fold_v_cont : Continuous fold_v := by
  unfold fold_v
  continuity

/-- **分析层连续元**: 正支局部函数 f = u + √2/2, 负支局部函数 g = −(v + √2/2)
    (foldArc 两分支的解析式, 顶点连续性的两半). -/
def fold_f : ℂ → ℝ := fun w => (√2 / 2) * (w.re + w.im) + √2 / 2

def fold_g : ℂ → ℝ := fun w => -((√2 / 2) * (w.re - w.im) + √2 / 2)

theorem fold_f_cont : Continuous fold_f := by
  unfold fold_f
  continuity

theorem fold_g_cont : Continuous fold_g := by
  unfold fold_g
  continuity

/-- **分析层开集元**: {u > −√2/2} 与 {v > −√2/2} 开 (连续函数严格不等式).
    English: the upper half-planes of the fold coordinates are open. -/
theorem fold_u_upper_open : IsOpen {w : ℂ | (√2 / 2) * (w.re + w.im) > -(√2 / 2)} :=
  isOpen_lt (continuous_const : Continuous fun _ : ℂ => -(√2 / 2)) fold_u_cont

theorem fold_v_upper_open : IsOpen {w : ℂ | (√2 / 2) * (w.re - w.im) > -(√2 / 2)} :=
  isOpen_lt (continuous_const : Continuous fun _ : ℂ => -(√2 / 2)) fold_v_cont

/-- **T2 左逆**: foldArg (γ(s)) = s — 捋直后取回原参数.
    English: foldArg (γ(s)) = s — straightening then un-straightening. -/
theorem foldArg_left_inv (s : ℝ) : foldArg ⟨foldArc s, foldArc_mem s⟩ = s := by
  by_cases hs : 0 < s
  · -- s > 0: 正支, u 坐标 > −c ⟹ then 支
    have hu : (√2 / 2) * ((foldArc s).re + (foldArc s).im) > -(√2 / 2) := by
      rw [foldArc_pos s (le_of_lt hs)]
      rw [exp_pi_div_four_form]
      simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
        Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_im,
        zero_mul, add_zero, zero_add]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hs]
    unfold foldArg
    simp only [Subtype.coe_mk]
    rw [if_pos hu]
    rw [foldArc_pos s (le_of_lt hs)]
    rw [exp_pi_div_four_form]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero, zero_add]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · -- s ≤ 0: 负支或顶点, u 坐标 = −c ⟹ else 支
    have hnot : ¬ (√2 / 2) * ((foldArc s).re + (foldArc s).im) > -(√2 / 2) := by
      rw [foldArc_neg s (le_of_not_gt hs)]
      rw [exp_neg_pi_div_four_form]
      simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
        Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.one_im,
        zero_mul, add_zero]
      nlinarith
    unfold foldArg
    simp only [Subtype.coe_mk]
    rw [if_neg hnot]
    rw [foldArc_neg s (le_of_not_gt hs)]
    rw [exp_neg_pi_div_four_form]
    simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

/-- **T2' 右逆**: γ (foldArg z) = z — 每个折线点被参数化还原.
    English: γ (foldArg z) = z — every fold point is recovered. -/
theorem foldArg_right_inv (z : foldSet) : foldArc (foldArg z) = z.1 := by
  unfold foldArg
  rcases z.2 with ⟨t, ht, hz | hz⟩
  · -- 正支: z = −1 + t·e⁺ (t ≥ 0)
    rw [hz]
    by_cases htpos : 0 < t
    · -- t > 0: then 支, foldArg = 2c²t = t, foldArc t = 表达式 ✓
      have hu : (√2 / 2) * ((-1 + t * exp ((π / 4 : ℝ) * I)).re +
          (-1 + t * exp ((π / 4 : ℝ) * I)).im) > -(√2 / 2) := by
        rw [exp_pi_div_four_form]
        simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
          Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_im,
          zero_mul, add_zero, zero_add]
        ring_nf
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [htpos]
      rw [if_pos hu]
      rw [exp_pi_div_four_form]
      simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
        Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_im,
        zero_mul, add_zero, zero_add]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
      rw [foldArc_pos _ (le_of_lt htpos)]
      rw [exp_pi_div_four_form]
      ring
    · -- t = 0: 顶点, else 支给 0, foldArc 0 = −1
      have ht0 : t = 0 := le_antisymm (le_of_not_gt htpos) ht
      have hnot : ¬ (√2 / 2) * ((-1 + 0 * exp ((π / 4 : ℝ) * I)).re +
          (-1 + 0 * exp ((π / 4 : ℝ) * I)).im) > -(√2 / 2) := by
        rw [exp_pi_div_four_form]
        simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im,
          zero_mul, add_zero]
        nlinarith
      rw [ht0]
      simp only [Complex.ofReal_zero]
      rw [if_neg hnot]
      simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im,
        zero_mul, add_zero]
      have h0 : -(√2 / 2 * (-1 - -0) + √2 / 2) = 0 := by ring
      rw [h0]
      rw [foldArc_pos 0 (by norm_num)]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
  · -- 负支: z = −1 + t·e⁻ (t ≥ 0) — else 支, foldArg = −(v+c) = −t
    rw [hz]
    have hnot : ¬ (√2 / 2) * ((-1 + t * exp (-(π / 4 : ℝ) * I)).re +
        (-1 + t * exp (-(π / 4 : ℝ) * I)).im) > -(√2 / 2) := by
      rw [exp_neg_pi_div_four_form]
      simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
        Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.one_im,
        zero_mul, add_zero]
      nlinarith
    rw [if_neg hnot]
    rw [exp_neg_pi_div_four_form]
    simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.one_im,
      zero_mul, add_zero]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
    rw [foldArc_neg (-t) (by nlinarith [ht])]
    rw [exp_neg_pi_div_four_form]
    rw [Complex.ofReal_neg]
    ring

/-- **T3 折线 ≅ R (同胚)**: 弧长参数化 γ 是 ℝ 与折线的同胚 — 捋直的拓扑
    形态: 折线 (V 形弯折) 拓扑上就是实数轴.
    English: the fold is homeomorphic to ℝ: γ is a homeomorphism. -/
noncomputable def foldArcHomeo : ℝ ≃ₜ foldSet where
  toFun := fun s => ⟨foldArc s, foldArc_mem s⟩
  invFun := foldArg
  left_inv := foldArg_left_inv
  right_inv := fun z => Subtype.ext (foldArg_right_inv z)
  continuous_toFun := continuous_foldArc.subtype_mk _
  continuous_invFun := by
    -- foldArg 逐点连续: 三情况 (正支开段 / 负支开段 / 顶点),
    -- 开邻域与局部函数全部引用命名元 (fold_u_upper_open / fold_f_cont 等)
    rw [continuous_iff_continuousAt]
    intro z
    unfold foldArg
    by_cases hu : (√2 / 2) * (z.1.re + z.1.im) > -(√2 / 2)
    · -- 情况1 正支开段: 开邻域 {u > -c} 内恒走 then 支 — 局部 = f (连续)
      have hopen : IsOpen {w : foldSet | (√2 / 2) * (w.1.re + w.1.im) > -(√2 / 2)} := by
        exact isOpen_lt (continuous_const : Continuous fun _ : foldSet => -(√2 / 2))
          (fold_u_cont.comp continuous_subtype_val)
      refine ContinuousAt.congr_of_eventuallyEq (fold_f_cont.comp continuous_subtype_val).continuousAt ?_
      have hmem : z ∈ {w : foldSet | (√2 / 2) * (w.1.re + w.1.im) > -(√2 / 2)} := hu
      refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
      intro w hw
      change foldArg w = fold_f w.1
      unfold foldArg
      rw [if_pos (show (√2 / 2) * (w.1.re + w.1.im) > -(√2 / 2) from hw)]
      rfl
    · -- u z ≤ -c — 折线点 ⟹ u z = -c
      have hu_eq : (√2 / 2) * (z.1.re + z.1.im) = -(√2 / 2) :=
        le_antisymm (le_of_not_gt hu) (fold_u_ge_neg_c z.2)
      by_cases hv : (√2 / 2) * (z.1.re - z.1.im) > -(√2 / 2)
      · -- 情况2 负支开段: 开邻域 {v > -c} 内恒走 else 支 — 局部 = g (连续)
        have hopen : IsOpen {w : foldSet | (√2 / 2) * (w.1.re - w.1.im) > -(√2 / 2)} := by
          exact isOpen_lt (continuous_const : Continuous fun _ : foldSet => -(√2 / 2))
            (fold_v_cont.comp continuous_subtype_val)
        refine ContinuousAt.congr_of_eventuallyEq (fold_g_cont.comp continuous_subtype_val).continuousAt ?_
        have hmem : z ∈ {w : foldSet | (√2 / 2) * (w.1.re - w.1.im) > -(√2 / 2)} := hv
        refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
        intro w hw
        -- w 在负支: v w > -c ⟹ u w = -c ⟹ if 走 else
        have hw_u : (√2 / 2) * (w.1.re + w.1.im) ≤ -(√2 / 2) := by
          have : (√2 / 2) * (w.1.re + w.1.im) = -(√2 / 2) := fold_u_neg_c_of_v_gt w.2 hw
          rw [this]
        change foldArg w = fold_g w.1
        unfold foldArg
        rw [if_neg (not_lt.mpr hw_u)]
        rfl
      · -- 情况3 顶点 (u = v = -c): 两分支一致 → 连续
        have hv_eq : (√2 / 2) * (z.1.re - z.1.im) = -(√2 / 2) :=
          le_antisymm (le_of_not_gt hv) (fold_v_ge_neg_c z.2)
        -- foldArg z = 0
        have hz0 : foldArg z = 0 := by
          unfold foldArg
          rw [if_neg (not_lt.mpr (le_of_eq hu_eq))]
          rw [hv_eq]
          ring
        -- 连续: Filter.Tendsto foldArg (𝓝 z) (𝓝 0) — f, g 连续且 f z = g z = 0,
        -- 邻域分解: (f⁻¹U ∩ {u>-c}) ∪ (g⁻¹U ∩ {u≤-c}) ⊇ f⁻¹U ∩ g⁻¹U
        change Filter.Tendsto foldArg (𝓝 z) (𝓝 (foldArg z))
        rw [hz0]
        rw [Filter.tendsto_def]
        intro U hU
        have hfz : fold_f z.1 = 0 := by
          unfold fold_f
          rw [hu_eq]
          ring
        have hgz : fold_g z.1 = 0 := by
          unfold fold_g
          rw [hv_eq]
          ring
        have hfU : fold_f ⁻¹' U ∈ 𝓝 z.1 :=
          (fold_f_cont.continuousAt).preimage_mem_nhds (by rw [hfz]; exact hU)
        have hgU : fold_g ⁻¹' U ∈ 𝓝 z.1 :=
          (fold_g_cont.continuousAt).preimage_mem_nhds (by rw [hgz]; exact hU)
        -- 核心邻域: f⁻¹U ∩ g⁻¹U (⊆ 覆盖并集)
        have hcore : fold_f ⁻¹' U ∩ fold_g ⁻¹' U ∈ 𝓝 z.1 :=
          Filter.inter_mem hfU hgU
        -- 覆盖: core ⊆ (f⁻¹U ∩ {u>-c}) ∪ (g⁻¹U ∩ {u≤-c})
        have hcover : fold_f ⁻¹' U ∩ fold_g ⁻¹' U ⊆
            (fold_f ⁻¹' U ∩ {w : ℂ | (√2 / 2) * (w.re + w.im) > -(√2 / 2)}) ∪
            (fold_g ⁻¹' U ∩ {w : ℂ | ¬ (√2 / 2) * (w.re + w.im) > -(√2 / 2)}) := by
          intro w hw
          by_cases h : (√2 / 2) * (w.re + w.im) > -(√2 / 2)
          · exact Or.inl ⟨hw.1, h⟩
          · exact Or.inr ⟨hw.2, h⟩
        -- 相对化到 subtype
        have hpre : (fun w : foldSet => w.1) ⁻¹'
            ((fold_f ⁻¹' U ∩ {w : ℂ | (√2 / 2) * (w.re + w.im) > -(√2 / 2)}) ∪
             (fold_g ⁻¹' U ∩ {w : ℂ | ¬ (√2 / 2) * (w.re + w.im) > -(√2 / 2)})) ∈ 𝓝 z :=
          (continuous_subtype_val.continuousAt.preimage_mem_nhds (Filter.mem_of_superset hcore hcover))
        refine Filter.mem_of_superset hpre ?_
        intro w hw
        rcases hw with hwf | hwg
        · rcases hwf with ⟨hwfU, hwu⟩
          change (if (√2 / 2) * (w.1.re + w.1.im) > -(√2 / 2) then fold_f w.1 else fold_g w.1) ∈ U
          rw [if_pos (show (√2 / 2) * (w.1.re + w.1.im) > -(√2 / 2) from hwu)]
          exact hwfU
        · rcases hwg with ⟨hwgU, hwnot⟩
          change (if (√2 / 2) * (w.1.re + w.1.im) > -(√2 / 2) then fold_f w.1 else fold_g w.1) ∈ U
          rw [if_neg hwnot]
          exact hwgU


-- ===== 逻辑完备桥族 (折叠坐标 ↔ 标准坐标): Part IV 接入断点 C 的必要件 =====

/-- **桥 1 (u 分量)**: 共轭在折叠坐标 = u↔v 对换 — u(conj z) = v(z).
    English: conjugation swaps the fold coordinates (u-component). -/
theorem fold_conj_swap_u (z : ℂ) : fold_u (conj z) = fold_v z := by
  unfold fold_u fold_v
  rw [Complex.conj_re, Complex.conj_im]
  ring

/-- **桥 1' (v 分量)**: v(conj z) = u(z). -/
theorem fold_conj_swap_v (z : ℂ) : fold_v (conj z) = fold_u z := by
  unfold fold_u fold_v
  rw [Complex.conj_re, Complex.conj_im]
  ring

/-- **桥 1 (pair 版)**: conj z 的折叠坐标 = z 的折叠坐标交换对 — 实轴反射
    在折叠坐标下 = 两根 45° 半轴的角色交换.
    English: conj in fold coordinates is the swap (u,v) → (v,u). -/
theorem fold_conj_swap (z : ℂ) : foldCoordFromC (conj z) = ((foldCoordFromC z).2, (foldCoordFromC z).1) := by
  unfold foldCoordFromC
  apply Prod.ext <;> rw [Complex.conj_re, Complex.conj_im] <;> ring

/-- **桥 2**: 虚轴 re=0 ⟺ 折叠坐标对角线 u+v=0 — 数学史的虚轴在折线框架
    下是对角线.
    English: the imaginary axis is the diagonal u+v=0 in fold coordinates. -/
theorem fold_imag_axis_diag (z : ℂ) : z.re = 0 ↔ fold_u z + fold_v z = 0 := by
  constructor
  · intro h
    unfold fold_u fold_v
    rw [h]
    ring
  · intro h
    have hsum : fold_u z + fold_v z = (√2 : ℝ) * z.re := by
      unfold fold_u fold_v
      ring
    have hh : (√2 : ℝ) * z.re = 0 := by
      rw [← hsum, h]
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num : (√2 : ℝ) ≠ 0)

/-- **桥 3**: 临界线 re=1/2 ⟺ 折叠坐标水平线 u+v=√2/2 — 临界线在折线框架
    下是水平线 (u 坐标恒定).
    English: the critical line is the horizontal line u+v=√2/2. -/
theorem fold_critical_line_horiz (z : ℂ) : z.re = 1 / 2 ↔ fold_u z + fold_v z = √2 / 2 := by
  constructor
  · intro h
    unfold fold_u fold_v
    rw [h]
    ring
  · intro h
    have hsum : fold_u z + fold_v z = (√2 : ℝ) * z.re := by
      unfold fold_u fold_v
      ring
    have hh : (√2 : ℝ) * z.re = √2 / 2 := by
      rw [← hsum, h]
    calc
      z.re = (√2 : ℝ) * z.re / (√2 : ℝ) := by
        field_simp [show (√2 : ℝ) ≠ 0 by norm_num]
      _ = (√2 / 2) / (√2 : ℝ) := by rw [hh]
      _ = 1 / 2 := by
        field_simp [show (√2 : ℝ) ≠ 0 by norm_num]

/-- **桥 4**: 实值 im=0 ⟺ u=v (对换不动线) — 实轴在折叠坐标下是共轭对换
    的不动线.
    English: real values are the fixed line u=v of the swap. -/
theorem fold_real_iff_swap_fixed (z : ℂ) : z.im = 0 ↔ fold_u z = fold_v z := by
  constructor
  · intro h
    unfold fold_u fold_v
    rw [h]
    ring
  · intro h
    have hsub : fold_u z - fold_v z = (√2 : ℝ) * z.im := by
      unfold fold_u fold_v
      ring
    have hh : (√2 : ℝ) * z.im = 0 := by
      rw [← hsub]
      exact sub_eq_zero.mpr h
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num : (√2 : ℝ) ≠ 0)


-- ===== 对称呈现元 (C 对称元在折叠坐标下的形): Part IV 呈现层 =====

/-- **对称呈现元 1**: 反射 s↦1−s 在折叠坐标 = 每分量的镜像平移
    u → √2/2 − u, v → √2/2 − v (u 分量) — 临界线 u+v=√2/2 是平移不动线.
    English: the reflection s ↦ 1−s is the mirror shift of each fold
    coordinate. -/
theorem fold_reflection_mirror_u (z : ℂ) : fold_u (1 - z) = √2 / 2 - fold_u z := by
  unfold fold_u
  rw [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- **对称呈现元 1'**: v 分量: fold_v (1−z) = √2/2 − fold_v z. -/
theorem fold_reflection_mirror_v (z : ℂ) : fold_v (1 - z) = √2 / 2 - fold_v z := by
  unfold fold_v
  rw [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- **对称呈现元 2**: 共轭保持折叠临界线 — conj z 在 u+v=√2/2 上 ⟺ z 在
    其上 (桥 1 对换 + 桥 3 水平线的组合).
    English: conjugation preserves the fold critical line. -/
theorem fold_critical_conj (z : ℂ) :
    fold_u (conj z) + fold_v (conj z) = √2 / 2 ↔ fold_u z + fold_v z = √2 / 2 := by
  rw [fold_conj_swap_u, fold_conj_swap_v]
  rw [add_comm]

/-- **对称呈现元 3**: 折叠临界线上, 反射 = 共轭 (两操作在 u+v=√2/2 上合一
    — 标准事实 critical_line_iff_reflect_fixed 的折叠形).
    English: on the fold critical line, reflection equals conjugation. -/
theorem fold_reflection_eq_conj_on_line (z : ℂ)
    (hz : fold_u z + fold_v z = √2 / 2) : fold_u (1 - z) = fold_u (conj z) := by
  rw [fold_reflection_mirror_u, fold_conj_swap_u]
  -- √2/2 − fold_u z = fold_v z: 由临界线 hz
  have hv : fold_v z = √2 / 2 - fold_u z := by
    linarith
  rw [hv]


-- ===== 折叠三角对称 (FoldTriangleSymmetry): 两读数对称 — D115 (2026-08-27) =====
--
-- 用户主张 (原话要点, D115): "两个等腰直角三角形, 斜边一个 1 一个 −1,
-- 直角边一个 √2/2 一个 0.5i — 这样就能证对称".
-- 修正 (D115 对齐): "0.5i" 是直角边的**垂直分量** (每条腿 ‖·‖ = √2/2,
-- 垂直分量 1/2 → 0.5i), 不是边长本身 — 字面值勾股 (0.5i)²·2 = −1/2 ≠ 1 为假.
-- T1 (假复平面分解三角): 直角在原点, 腿 = ±45° 两臂 (1±i)/2 (‖·‖ = √2/2),
-- 斜边 = 长度 1 = |i|. T2 (负侧值三角): 斜边 = 实轴段 [0,−1] (值 −1),
-- 直角 = 折线臂中点 (−1±i)/2, 腿 ‖·‖ = √2/2, 垂直分量 ±1/2 = ±0.5i.
-- 对称 = 同一构型的两种读数 (长度读 / 值读) + 全等; 值链: 0.5i + 0.5i = i,
-- i·i = −1 (负侧值 = 腿合 i 的平方).
-- English: two right isosceles triangles with the same shape: T1 reads the
-- lengths (hyp 1, legs √2/2), T2 reads the values (hyp segment [0,−1] with the
-- value −1, apex (−1±i)/2 whose legs have vertical components ±1/2 = ±0.5i).

/-- **T1 腿 1 长度**: ‖(1+i)/2‖ = √2/2 — 45°↗ 臂长.
    English: the first leg of the decomposition triangle has length √2/2. -/
theorem fold_tri_leg1 : ‖((1 : ℂ) + I) / 2‖ = √2 / 2 := by
  calc
    ‖((1 : ℂ) + I) / 2‖ = ‖(1 + I : ℂ)‖ / ‖(2 : ℂ)‖ := by rw [norm_div]
    _ = √2 / 2 := by
      rw [fold_length_sqrt_two]
      norm_num

/-- **T1 腿 2 长度**: ‖(1−i)/2‖ = √2/2 — −45° 臂长.
    English: the second leg of the decomposition triangle has length √2/2. -/
theorem fold_tri_leg2 : ‖((1 : ℂ) - I) / 2‖ = √2 / 2 := by
  calc
    ‖((1 : ℂ) - I) / 2‖ = ‖(1 - I : ℂ)‖ / ‖(2 : ℂ)‖ := by rw [norm_div]
    _ = √2 / 2 := by
      rw [fold_length_neg_sqrt_two]
      norm_num

/-- **T1 斜边长度 = 1**: ‖(1+i)/2 − (1−i)/2‖ = 1 (= |i|).
    English: the hypotenuse of the decomposition triangle has length 1. -/
theorem fold_tri_hyp :
    ‖((1 : ℂ) + I) / 2 - ((1 : ℂ) - I) / 2‖ = 1 := by
  rw [show ((1 : ℂ) + I) / 2 - ((1 : ℂ) - I) / 2 = I by ring]
  have hsq : (‖I‖ : ℝ) ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    norm_num
  have habs : |(‖I‖ : ℝ)| = |(1 : ℝ)| := by
    rw [← sq_eq_sq_iff_abs_eq_abs (‖I‖ : ℝ) 1]
    rw [hsq]
    norm_num
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at habs
  exact habs

/-- **T1 直角**: 原点到两腿端点的内积实部为零 (方向差 90°).
    English: the two legs from the origin are orthogonal (90°). -/
theorem fold_tri_right_angle :
    (((1 : ℂ) + I) / 2).re * (((1 : ℂ) - I) / 2).re +
      (((1 : ℂ) + I) / 2).im * (((1 : ℂ) - I) / 2).im = 0 := by
  simp
  norm_num

/-- **T1 勾股**: 两腿平方和 = 斜边平方 (数值勾股).
    English: Pythagoras for the decomposition triangle (length reading). -/
theorem fold_tri_pythagorean :
    (‖((1 : ℂ) + I) / 2‖ : ℝ) ^ 2 + (‖((1 : ℂ) - I) / 2‖ : ℝ) ^ 2 =
      (‖((1 : ℂ) + I) / 2 - ((1 : ℂ) - I) / 2‖ : ℝ) ^ 2 := by
  rw [fold_tri_leg1, fold_tri_leg2, fold_tri_hyp]
  rw [div_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **T2 腿 1 (到原点)**: ‖(−1+i)/2‖ = √2/2 — 折线臂中点出射腿.
    English: the leg from the apex (−1+i)/2 to the origin has length √2/2. -/
theorem fold_tri_apex_norm : ‖((-1 : ℂ) + I) / 2‖ = √2 / 2 := by
  rw [show (-1 : ℂ) + I = -(1 - I : ℂ) by ring]
  rw [norm_div, norm_neg, fold_length_neg_sqrt_two]
  norm_num

/-- **T2 腿 2 (到 −1)**: ‖(−1+i)/2 − (−1)‖ = √2/2.
    English: the leg from the apex to −1 has length √2/2. -/
theorem fold_tri_apex_to_neg_one :
    ‖((-1 : ℂ) + I) / 2 - (-1)‖ = √2 / 2 := by
  rw [show ((-1 : ℂ) + I) / 2 - (-1) = ((1 : ℂ) + I) / 2 by ring]
  exact fold_tri_leg1

/-- **T2 斜边 (值 −1)**: ‖0 − (−1)‖ = 1 — 实轴段 [0,−1], 即值 −1 的读数.
    English: the hypotenuse is the real segment [0,−1], length 1, value −1. -/
theorem fold_tri_minus_hyp : ‖(0 : ℂ) - (-1)‖ = 1 := by
  norm_num

/-- **T2 直角**: 顶点 (−1+i)/2 处两腿正交 — 腿 1 = apex→0 = (1−i)/2,
    腿 2 = apex→−1 = (−1−i)/2, 实点积为零.
    English: the right angle at the apex (−1+i)/2 (real dot product of the two
    legs is zero). -/
theorem fold_tri_minus_right_angle :
    (((1 : ℂ) - I) / 2).re * (((-1 : ℂ) - I) / 2).re +
      (((1 : ℂ) - I) / 2).im * (((-1 : ℂ) - I) / 2).im = 0 := by
  simp
  norm_num

/-- **垂直分量 = ±1/2 (值 0.5i)**: 两臂的垂直分量各 = 1/2 — "直角边 0.5i" 的
    正确读法 (分量), 与长度读 √2/2 是同一条腿.
    English: each arm's vertical component is 1/2, read as 0.5i. -/
theorem fold_tri_arm_im :
    (((1 : ℂ) + I) / 2).im = 1 / 2 ∧ (((-1 : ℂ) + I) / 2).im = 1 / 2 := by
  constructor <;> simp

/-- **值链 (0.5i + 0.5i = i)**: 两臂之和 = i — 每条臂垂直分量 1/2 (0.5i),
    合在一起 = 虚数单位 (±45° 臂合成).
    English: the two arms (each vertical component 1/2) sum to the unit i. -/
theorem fold_tri_arms_sum :
    ((1 : ℂ) + I) / 2 + ((-1 : ℂ) + I) / 2 = I := by
  ring

/-- **值链 (i·i = −1)**: 虚数单位的平方 = 负侧值 −1 — 值链闭合:
    0.5i+0.5i = i ⟹ i·i = −1.
    English: the value chain closes: the squared unit is the negative-side −1. -/
theorem fold_tri_value_square : I * I = -1 := by
  simp

end ZeroRelative
