/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous

English: symmetric tool family (IV): symmetric counting (the flip-count chain) -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
set_option linter.style.longLine false

/-!
# 对称计数 (方法四: 对称结构的计数) — 纯已知数学, 零洞

四方法之一 (对称消去/对称延拓/三桥/对称计数)。对称计数 =
对称结构的计数:
  * 零点计数: sin x = 0 ⟺ x = kπ (整数平移计数); cos x = 0 ⟺
    x = (2k+1)π/2 (半整数平移计数) — 零点结构 = 整数格点
  * 周期内零点计数: sin 在 [0, 2π) 恰 2 个零点 {0, π} (半周期
    对称: 零点对)
  * 单位根计数: z⁴ = 1 ⟺ z ∈ {±1, ±I} (四相位计数 — 4 个 4 次
    单位根 = 相位格点 {1, -1, I, -I})
  * 圈数对称计数: 正反圈数回到同一位置 (exp(2πi·k) = exp(2πi·(-k))
    = 1, 桥 2 的计数侧: 整数平移对)

全部 mathlib 锚定, 不引入 Pat 概念 (0pat)。

## 用户指示 (2026-08-21, 从黎曼路线复制 — 出处: 37_riemann_unified/observation.md 观测 AN/观测 S)

用户方向: "相位调制的时候存在映射相位关系, 把迭代终点和起点间的对称映射
构建出来, 是不是就不需要迭代逼近了? 迭代逼近本身不就是有限可达无限吗?"
翻转计数 = 提升差/2π (用户"圆的直径"方向): 直径投影见 π 翻转, 连续提升见
2π 圈数, 两者互补。
对称计数 = 该指示的落点: 零点计数 (sin/cos 零点 = 整数/半整数格点),
单位根计数 (z⁴ = 1 四相位), 周期内零点对, 正反圈数对 (整数平移对对称)。

## 用户指示 (2026-08-22, 通用化改造 — 原话): "所有对称工具族, 必须进行
通用化改造, 乘除法能对消一些相位, 有可能是因为基点都锁定在 1 不是 0,
或者其他某些原因, 因此对称工具族必须能无视基点移动的任意消相位才好。"
通用化 = 零点计数结构无视基点移动: sin(x - e) = 0 的零点 = 基点 e +
整数格点 (零点结构平移, 计数律不变)。
English summary: Symmetry tool family #4 — Symmetry Counting. Zero counting (sin zeros = integer lattice kπ, cos zeros = half-integer lattice (2k+1)π/2), unit-root counting (z⁴ = 1 ⟺ z ∈ {±1, ±I}, four phase lattice points, distinct), in-period zero pairs (0, π), forward/reverse turn pairs. Mathlib-only, 零洞.
-/
namespace ZeroRelative

/-! ## 1. 零点计数 (整数/半整数平移) -/

/-- **sin 零点计数**: sin x = 0 ⟺ ∃ k : ℤ, x = k·π — 正弦零点 =
整数倍 π (零点结构 = 整数平移格点, mathlib sin_eq_zero_iff).   sin zero counting: sin x = 0 ⟺ ∃ k : ℤ, k·π = x (zeros = integer translation lattice). 
English: sin zero counting: sin x = 0 ⟺ ∃ k : ℤ, x = k·π — the sine zeros are integer multiples of π (zero structure = integer translation lattice, mathlib sin_eq_zero_iff). -/
theorem sin_zero_iff_periodic (x : ℝ) :
    Real.sin x = 0 ↔ ∃ k : ℤ, (k : ℝ) * Real.pi = x := by
  exact Real.sin_eq_zero_iff

/-- **cos 零点计数**: cos x = 0 ⟺ ∃ k : ℤ, x = (2k+1)·π/2 — 余弦
零点 = 半整数倍 π (奇数半格点, mathlib cos_eq_zero_iff).   cos zero counting: cos x = 0 ⟺ ∃ k : ℤ, x = (2k+1)·π/2 (half-integer lattice). 
English: cos zero counting: cos x = 0 ⟺ ∃ k : ℤ, x = (2k+1)·π/2 — the cosine zeros are half-integer multiples of π (odd half-lattice, mathlib cos_eq_zero_iff). -/
theorem cos_zero_iff_odd_half (x : ℝ) :
    Real.cos x = 0 ↔ ∃ k : ℤ, x = (2 * (k : ℤ) + 1) * Real.pi / 2 := by
  exact Real.cos_eq_zero_iff

/-! ## 2. 单位根计数 (四相位格点) -/

/-- **z² = -1 的解 = ±I**: z² = -1 ⟺ z = I ∨ z = -I — (z-I)(z+I)
= z² - I² = z² + 1 = 0, 域上无零因子 (计数: 2 个平方根).   Solutions of z² = -1 are ±I: (z-I)(z+I) = 0, domain has no zero divisors. 
English: Solutions of z² = -1 are ±I: z² = -1 ⟺ z = I ∨ z = -I — (z-I)(z+I) = z² - I² = z² + 1 = 0, a field has no zero divisors (count: 2 square roots). -/
theorem sq_eq_neg_one_iff (z : ℂ) :
    z ^ 2 = -1 ↔ z = Complex.I ∨ z = -Complex.I := by
  constructor
  · intro hz
    have h : (z - Complex.I) * (z + Complex.I) = 0 := by
      calc
        (z - Complex.I) * (z + Complex.I) = z ^ 2 - Complex.I ^ 2 := by ring
        _ = z ^ 2 + 1 := by rw [Complex.I_sq]; ring
        _ = 0 := by rw [hz]; ring
    rcases mul_eq_zero.mp h with hzI | hzI'
    · left
      exact sub_eq_zero.mp hzI
    · right
      exact eq_neg_of_add_eq_zero_left hzI'
  · intro h
    rcases h with rfl | rfl
    · exact Complex.I_sq
    · rw [neg_sq]
      exact Complex.I_sq

/-- **四相位计数**: z⁴ = 1 ⟺ z ∈ {1, -1, I, -I} — 4 个 4 次单位根
= 四相位格点 (z⁴ = (z²)², 两层平方根计数: z² = ±1, 各 2 解).   Four-phase counting: z⁴ = 1 ⟺ z ∈ {1, -1, I, -I} (z⁴ = (z²)², two layers of square-root counting). 
English: Four-phase counting: z⁴ = 1 ⟺ z ∈ {1, -1, I, -I} — the 4 fourth roots of unity are the four-phase lattice points (z⁴ = (z²)², two layers of square-root counting: z² = ±1, each with 2 solutions). -/
theorem unit_root_four (z : ℂ) :
    z ^ 4 = 1 ↔ z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I := by
  constructor
  · intro hz
    have hsq' : (z ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      norm_num
      exact hz
    have hsq : z ^ 2 = 1 ∨ z ^ 2 = -1 := (sq_eq_one_iff).mp hsq'
    rcases hsq with h1 | hm1
    · rcases (sq_eq_one_iff).mp h1 with hz1 | hz1'
      · left
        exact hz1
      · right
        left
        exact hz1'
    · rcases (sq_eq_neg_one_iff z).mp hm1 with hzi | hzi'
      · right
        right
        left
        exact hzi
      · right
        right
        right
        exact hzi'
  · intro h
    rcases h with h1 | h2 | h3 | h4
    · rw [h1]
      norm_num
    · rw [h2]
      norm_num
    · rw [h3]
      calc
        Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by norm_num [pow_mul]
        _ = (-1 : ℂ) ^ 2 := by rw [Complex.I_sq]
        _ = 1 := by norm_num
    · rw [h4]
      calc
        (-Complex.I) ^ 4 = (Complex.I ^ 4) := by ring
        _ = (Complex.I ^ 2) ^ 2 := by norm_num [pow_mul]
        _ = (-1 : ℂ) ^ 2 := by rw [Complex.I_sq]
        _ = 1 := by norm_num

/-- **四根互异**: {1, -1, I, -I} 四元素两两不同 (四相位格点
计数 = 4, 无重复).   Four roots are distinct: pairwise different (count = 4, no duplicates). 
English: Four roots are distinct: {1, -1, I, -I} are pairwise different (four-phase lattice count = 4, no duplicates). -/
theorem four_roots_distinct :
    (1 : ℂ) ≠ -1 ∧ (1 : ℂ) ≠ Complex.I ∧ (1 : ℂ) ≠ -Complex.I ∧
      (-1 : ℂ) ≠ Complex.I ∧ (-1 : ℂ) ≠ -Complex.I ∧ Complex.I ≠ -Complex.I := by
  constructor
  · intro h
    have hre : (1 : ℂ).re = (-1 : ℂ).re := congrArg Complex.re h
    norm_num at hre
  · constructor
    · intro h
      have hre : (1 : ℂ).re = Complex.I.re := congrArg Complex.re h
      norm_num at hre
    · constructor
      · intro h
        have hre : (1 : ℂ).re = (-Complex.I).re := congrArg Complex.re h
        norm_num at hre
      · constructor
        · intro h
          have hre : (-1 : ℂ).re = Complex.I.re := congrArg Complex.re h
          norm_num at hre
        · constructor
          · intro h
            have hre : (-1 : ℂ).re = (-Complex.I).re := congrArg Complex.re h
            norm_num at hre
          · intro h
            have him : Complex.I.im = (-Complex.I).im := congrArg Complex.im h
            norm_num at him

/-! ## 3. 周期内零点计数 (半周期对称) -/

/-- **sin 周期内零点 = 2 个**: 0 ≤ x < 2π ∧ sin x = 0 ⟹ x = 0 ∨
x = π — 半周期对称: 零点成对 (0 与 π 相距半周期).   Sine has exactly 2 zeros in one period: x = 0 ∨ x = π (half-period symmetry: zeros come in pairs). 
English: sin has exactly 2 zeros in one period: 0 ≤ x < 2π ∧ sin x = 0 ⟹ x = 0 ∨ x = π — half-period symmetry: zeros come in pairs (0 and π are half a period apart). -/
theorem sin_zero_in_period (x : ℝ) (h0 : 0 ≤ x) (hx : x < 2 * Real.pi) :
    Real.sin x = 0 → x = 0 ∨ x = Real.pi := by
  intro hs
  rcases Real.sin_eq_zero_iff.mp hs with ⟨k, hk⟩
  have hkge : (0 : ℝ) ≤ (k : ℝ) := by
    have h0' : 0 ≤ Real.pi * (k : ℝ) := by simpa [hk.symm, mul_comm] using h0
    exact (mul_nonneg_iff_right_nonneg_of_pos Real.pi_pos).mp h0'
  have hklt : (k : ℝ) < 2 := by
    have hx' : Real.pi * (k : ℝ) < Real.pi * 2 := by
      simpa [hk.symm, mul_comm, mul_left_comm, mul_assoc] using hx
    exact (mul_lt_mul_iff_left₀ (a := Real.pi) Real.pi_pos).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hx')
  have hk0 : (0 : ℤ) ≤ k := by
    exact_mod_cast hkge
  have hk1 : k ≤ 1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    nlinarith
  interval_cases k
  · left
    rw [← hk]
    norm_num
  · right
    rw [← hk]
    norm_num

/-! ## 4. 圈数对称计数 (正反圈数对) -/

/-- **正反圈数同一**: exp(2πi·k) = exp(2πi·(-k)) — 转 k 圈与转
-k 圈回到同一位置 (桥 2 的计数侧: 整数平移对 {k, -k} 对称).   Forward and reverse turn counts coincide: exp(2πi·k) = exp(2πi·(-k)). 
English: Forward and reverse winding numbers agree: exp(2πi·k) = exp(2πi·(-k)) — turning k laps and -k laps returns to the same position (counting side of bridge 2: the integer translation pair {k, -k} is symmetric). -/
theorem turn_pair_same (k : ℤ) :
    Complex.exp (k * (2 * Real.pi * Complex.I)) =
      Complex.exp ((-k) * (2 * Real.pi * Complex.I)) := by
  have h1 : Complex.exp (k * (2 * Real.pi * Complex.I)) = 1 := by
    rw [Complex.exp_int_mul]
    rw [Complex.exp_two_pi_mul_I]
    simp
  have h2 : Complex.exp ((-k) * (2 * Real.pi * Complex.I)) = 1 := by
    have hneg : -↑k * (2 * Real.pi * Complex.I) = -(↑k * (2 * Real.pi * Complex.I)) := by ring
    rw [hneg, Complex.exp_neg, h1]
    simp
  rw [h1, h2]


/-! ## 5. 通用化: 计数无视基点移动 (2026-08-22 用户指示) -/

/-- **★基点平移零点**: sin(x - e) = 0 ⟺ x - e = kπ — 零点结构在
基点平移 e 下不变 (sin_eq_zero_iff 对平移后的坐标, 计数律 = 整数
格点, 与基点无关).   ★Basepoint-shifted zeros: sin(x - e) = 0 ⟺
x - e = kπ — the zero structure is invariant under basepoint shift
(counting law = integer lattice, independent of the basepoint). 
English: ★Basepoint-shifted zeros: sin(x - e) = 0 ⟺ x - e = kπ — the zero structure is invariant under the basepoint shift e (sin_eq_zero_iff on the shifted coordinate; the counting law = integer lattice, independent of the basepoint). -/
theorem sin_zero_shift (e x : ℝ) :
    Real.sin (x - e) = 0 ↔ ∃ k : ℤ, (k : ℝ) * Real.pi = x - e := by
  exact Real.sin_eq_zero_iff

/-- **★零点格点 = 基点 + 整数格点**: sin(x - e) = 0 ⟺ ∃ k, x = e +
kπ — 任意基点 e 下, 零点 = 基点 + 整数平移格点 (计数结构无视基点
移动; 与 sin_zero_iff_periodic 差一个基点平移).   ★Zero grid =
basepoint + integer lattice: at any basepoint e, zeros are e + kπ —
the counting structure ignores basepoint shifts. 
English: ★Zero grid = basepoint + integer lattice: at any basepoint e, sin(x - e) = 0 ⟺ x = e + kπ — zeros are the basepoint plus the integer translation lattice (counting structure ignores basepoint shifts; differs from sin_zero_iff_periodic by a basepoint shift). -/
theorem sin_zero_grid_at_basepoint (e x : ℝ) :
    Real.sin (x - e) = 0 ↔ ∃ k : ℤ, x = e + (k : ℝ) * Real.pi := by
  constructor
  · intro h
    rcases (sin_zero_shift e x).mp h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    linarith
  · intro h
    rcases h with ⟨k, hk⟩
    exact (sin_zero_shift e x).mpr ⟨k, by linarith⟩


/-! ## 零点格点复数版 (相位基点 sin 非零) -/

/-- **sin(π/2+iy) = cosh y**: 相位基点处 sin 的零点格点形式 —
sin(π/2+iy) = cos(iy) = cosh y (临界线相位格点; 观测 S 的构件:
χ 单位模前置).   sin(π/2+iy) = cosh y: the phase-lattice form at
the phase basepoint (sin(π/2+iy) = cos(iy) = cosh y; the building
block of the χ unit-modulus observation). 
English: sin(π/2+iy) = cosh y: the zero-lattice form of sin at the phase basepoint — sin(π/2+iy) = cos(iy) = cosh y (critical-line phase lattice; building block of observation S: precondition of χ's unit modulus). -/
theorem sin_half_pi_add_mul_I_cosh (y : ℝ) :
    Complex.sin (Real.pi / 2 + y * Complex.I) = Complex.cosh y := by
  calc
    Complex.sin (Real.pi / 2 + y * Complex.I) = Complex.cos (y * Complex.I) := by
      rw [Complex.sin_add]
      rw [Complex.sin_pi_div_two, Complex.cos_pi_div_two]
      ring
    _ = Complex.cosh y := Complex.cos_mul_I y

/-- **cosh 非零**: cosh y ≠ 0 — cosh 实值恒正 (零点格点: 相位
基点处 cosh 无零点).   cosh nonzero: cosh y ≠ 0 (cosh is
positive; no zeros at the phase basepoint). 
English: cosh nonzero: cosh y ≠ 0 — cosh is always positive for real y (zero lattice: cosh has no zeros at the phase basepoint). -/
theorem cosh_ne_zero (y : ℝ) : Complex.cosh y ≠ 0 := by
  rw [← Complex.ofReal_cosh]
  exact_mod_cast (ne_of_gt (Real.cosh_pos y))

/-- **★相位基点 sin 非零**: sin(π/2+iy) ≠ 0 — 临界线上 sin 因子
无零点 (零点格点的相位基点版; χ(s)·χ(1-s)=1 的前置 sin(πs)≠0
的构件).   ★sin nonzero at the phase basepoint: sin(π/2+iy) ≠ 0
— the sin factor has no zeros on the critical line (the
phase-basepoint form of the zero lattice). 
English: ★sin nonzero at the phase basepoint: sin(π/2+iy) ≠ 0 — the sin factor has no zeros on the critical line (phase-basepoint form of the zero lattice; building block for the sin(πs) ≠ 0 precondition of χ(s)·χ(1-s) = 1). -/
theorem sin_half_pi_add_ne_zero (y : ℝ) :
    Complex.sin (Real.pi / 2 + y * Complex.I) ≠ 0 := by
  rw [sin_half_pi_add_mul_I_cosh y]
  exact cosh_ne_zero y


end ZeroRelative
