/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous

English: symmetric tool family (I): symmetric extension (zero reflection, circle family, functional equation) -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
set_option linter.style.longLine false

/-!
# 对称延拓 (方法二: 局部结构沿对称性延展到全域) — 纯已知数学, 零洞

四方法之一 (对称消去/对称延拓/三桥/对称计数)。对称延拓 =
局部结构沿对称性延展:
  * 周期延拓: sin/cos 以 2π 为周期 (sin(x+2π) = sin x), exp 以 2πi
    为周期 (exp(z+2πi) = exp z) — 局部一段延展到全域
  * 延拓闭合点: exp(2πi) = 1 (周期延拓的闭合 — 一周期回到起点)
  * 奇偶分解: 任意函数 = 奇部 + 偶部 (对称延拓的基础: 从 f 与 f∘neg
    合成全域对称结构)
  * 延拓一致性: sin 的奇延拓与周期延拓兼容 (奇偶 × 周期同时成立)

全部 mathlib 锚定, 不引入 Pat 概念 (0pat)。

## 用户指示 (2026-08-19, 从黎曼路线复制 — 出处: 37_riemann_unified/observation.md 观测 AL)

用户方向: "对称点与延拓点交换, 每个对称点都是以延拓点为对称点的延拓点";
"取三角函数后以累积数值延拓, 整数就出来了 (傅里叶相位校准)"。
单方向延拓 (用户例子: 交替中心 {2,1.5} 反射 → 每两步平移 -1)。
对称延拓 = 该指示的落点: 周期延拓 (sin/cos 2π, exp 2πi), 奇偶分解
(从 f 与 f∘neg 合成全域对称结构), 延拓一致性 (奇偶 × 周期兼容)。

## 用户指示 (2026-08-22, 通用化改造 — 原话): "所有对称工具族, 必须进行
通用化改造, 乘除法能对消一些相位, 有可能是因为基点都锁定在 1 不是 0,
或者其他某些原因, 因此对称工具族必须能无视基点移动的任意消相位才好。"
通用化 = 奇偶分解从基点 0 推广到任意基点 e (反射 2e - x): f =
(f+f∘R_e)/2 + (f-f∘R_e)/2; 周期延拓无视基点平移 (sin(x+e+2π) = sin(x+e))。
English summary: Symmetry tool family #2 — Symmetry Extension. Periodic extension (sin/cos period 2π, exp period 2πi), closing point exp(2πi) = 1, odd-even decomposition (f = even part + odd part), extension consistency (odd × periodic compatible). Mathlib-only, 零洞.
-/
namespace ZeroRelative

/-! ## 1. 周期延拓 (2π / 2πi) -/

/-- **sin 周期延拓**: sin(x + 2π) = sin x — 正弦以 2π 为周期 (周期
延拓: 局部波形沿实轴延展到全域).   sin periodic extension: sin(x + 2π) = sin x. 
English: sin periodic extension: sin(x + 2π) = sin x — sine has period 2π (periodic extension: the local wave extends along the real axis to the whole domain). -/
theorem sin_periodic (x : ℝ) : Real.sin (x + 2 * Real.pi) = Real.sin x := by
  rw [Real.sin_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

/-- **cos 周期延拓**: cos(x + 2π) = cos x — 余弦以 2π 为周期.   cos periodic extension: cos(x + 2π) = cos x. 
English: cos periodic extension: cos(x + 2π) = cos x — cosine has period 2π. -/
theorem cos_periodic (x : ℝ) : Real.cos (x + 2 * Real.pi) = Real.cos x := by
  rw [Real.cos_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

/-- **exp 周期延拓**: exp(z + 2πi) = exp z — 复指数以 2πi 为周期
(虚轴方向延拓 — 相位周期; mathlib Function.Periodic exp (2πI)).   exp periodic extension: exp(z + 2πi) = exp z (phase period along the imaginary axis). 
English: exp periodic extension: exp(z + 2πi) = exp z — the complex exponential has period 2πi (extension along the imaginary axis, the phase period; mathlib Function.Periodic exp (2πI)). -/
theorem exp_periodic_I (z : ℂ) : Complex.exp (z + 2 * Real.pi * Complex.I) = Complex.exp z := by
  exact Complex.exp_periodic z

/-! ## 2. 延拓闭合点 -/

/-- **exp 延拓闭合点**: exp(2πi) = 1 — 一周期延拓回到起点 (闭合:
2π 相位 = 整圈 = 还原点; 三桥桥 2 的锚: exp 核 2πiℤ 的生成元).   exp extension closing point: exp(2πi) = 1 (full turn returns to the restoring point). 
English: exp extension closing point: exp(2πi) = 1 — one period returns to the start (closing: 2π phase = full turn = restoring point; anchor of bridge 2 of the three bridges: generator of the exp kernel 2πiℤ). -/
theorem exp_two_pi_mul_I_eq_one : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
  exact Complex.exp_two_pi_mul_I

/-! ## 3. 奇偶分解 (对称延拓基础) -/

/-- **奇偶分解**: 任意函数 f = 偶部 + 奇部 — f x = (f x + f(-x))/2 +
(f x - f(-x))/2 (对称延拓: 从 f 与反射 f∘neg 合成全域对称结构).   Odd-even decomposition: f x = (f x + f(-x))/2 + (f x - f(-x))/2. 
English: Odd-even decomposition: any function f = even part + odd part — f x = (f x + f(-x))/2 + (f x - f(-x))/2 (symmetric extension: builds a global symmetric structure from f and the reflection f∘neg). -/
theorem odd_even_decomposition (f : ℝ → ℝ) (x : ℝ) :
    f x = (f x + f (-x)) / 2 + (f x - f (-x)) / 2 := by
  ring

/-- **偶部是偶函数**: g(x) = (f x + f(-x))/2 ⟹ g(-x) = g x (偶部
沿 neg 反射不变 — 偶对称延拓).   The even part is even: invariant under the neg reflection. 
English: The even part is even: g(x) = (f x + f(-x))/2 implies g(-x) = g x (the even part is invariant under the neg reflection — even symmetric extension). -/
theorem even_part_is_even (f : ℝ → ℝ) (x : ℝ) :
    ((f (-x) + f (-(-x))) / 2) = ((f x + f (-x)) / 2) := by
  ring

/-- **奇部是奇函数**: h(x) = (f x - f(-x))/2 ⟹ h(-x) = -h x (奇部
沿 neg 反射取负 — 奇对称延拓).   The odd part is odd: negates under the neg reflection. 
English: The odd part is odd: h(x) = (f x - f(-x))/2 implies h(-x) = -h x (the odd part negates under the neg reflection — odd symmetric extension). -/
theorem odd_part_is_odd (f : ℝ → ℝ) (x : ℝ) :
    ((f (-x) - f (-(-x))) / 2) = -((f x - f (-x)) / 2) := by
  ring

/-! ## 4. 延拓一致性 (奇偶 × 周期兼容) -/

/-- **sin 延拓一致性**: sin 的奇延拓与周期延拓同时成立 — sin(-x) =
-sin x ∧ sin(x + 2π) = sin x (奇对称 × 周期对称兼容, 无冲突).   sin extension consistency: odd symmetry and periodic symmetry hold simultaneously. 
English: sin extension consistency: the odd extension and the periodic extension of sin hold simultaneously — sin(-x) = -sin x ∧ sin(x + 2π) = sin x (odd symmetry × period symmetry compatible, no conflict). -/
theorem sin_extension_consistency (x : ℝ) :
    (Real.sin (-x) = -Real.sin x) ∧ (Real.sin (x + 2 * Real.pi) = Real.sin x) := by
  constructor
  · simp
  · exact sin_periodic x

/-- **exp 延拓一致性**: exp 的周期延拓与闭合点同时成立 — exp(z+2πi)
= exp z ∧ exp(2πi) = 1 (延拓本身闭合: 周期 = 回到 1).   exp extension consistency: the extension itself closes (period returns to 1). 
English: exp extension consistency: the periodic extension and the closing point hold simultaneously — exp(z+2πi) = exp z ∧ exp(2πi) = 1 (the extension itself closes: the period returns to 1). -/
theorem exp_extension_consistency (z : ℂ) :
    (Complex.exp (z + 2 * Real.pi * Complex.I) = Complex.exp z) ∧
      (Complex.exp (2 * Real.pi * Complex.I) = 1) := by
  constructor
  · exact exp_periodic_I z
  · exact exp_two_pi_mul_I_eq_one


/-! ## 5. 通用化: 延拓无视基点移动 (2026-08-22 用户指示) -/

/-- **★基点无关奇偶分解**: 任意基点 e 下, f = 偶部 + 奇部 (反射
R_e(x) = 2e - x) — f x = (f x + f(2e-x))/2 + (f x - f(2e-x))/2
(e = 0 时还原为 odd_even_decomposition).   ★Basepoint-free odd-even
decomposition: at any basepoint e, f = even part + odd part with
respect to the reflection R_e(x) = 2e - x. 
English: ★Basepoint-free odd-even decomposition: at any basepoint e, f = even part + odd part with respect to the reflection R_e(x) = 2e - x — f x = (f x + f(2e-x))/2 + (f x - f(2e-x))/2 (e = 0 recovers odd_even_decomposition). -/
theorem odd_even_decomposition_at_e (e : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    f x = (f x + f (2 * e - x)) / 2 + (f x - f (2 * e - x)) / 2 := by
  ring

/-- **★基点无关周期延拓**: sin(x + e + 2π) = sin(x + e) — 周期延拓
无视基点平移 (基点在 e 处仍以 2π 延拓; sin_periodic 的平移协变形式).
   ★Basepoint-free periodic extension: sin(x + e + 2π) = sin(x + e) —
periodic extension is covariant under basepoint shifts. 
English: ★Basepoint-free periodic extension: sin(x + e + 2π) = sin(x + e) — periodic extension ignores basepoint shifts (still period 2π at basepoint e; the translation-covariant form of sin_periodic). -/
theorem period_covariant (e x : ℝ) :
    Real.sin (x + e + 2 * Real.pi) = Real.sin (x + e) := by
  rw [Real.sin_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

/-- **★偶部基点对称**: 偶部 g(x) = (f x + f(2e-x))/2 关于基点 e 的
反射不变 — g(2e - x) = g x (任意基点 e 的偶对称延拓; e = 0 时还原
even_part_is_even).   ★Even part symmetric about e: g(2e - x) = g x
for the reflection about any basepoint e. 
English: ★Even part symmetric about e: g(x) = (f x + f(2e-x))/2 is invariant under the reflection about any basepoint e — g(2e - x) = g x (even symmetric extension at any basepoint; e = 0 recovers even_part_is_even). -/
theorem even_part_symm_at_e (e : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    ((f (2 * e - x) + f (2 * e - (2 * e - x))) / 2) = ((f x + f (2 * e - x)) / 2) := by
  ring

end ZeroRelative
