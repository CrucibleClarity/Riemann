/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous

English: symmetric tool family (III): symmetric cancellation -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
set_option linter.style.longLine false

/-!
# 对称消去 (方法一: 对称冗余的结构性对消) — 纯已知数学, 零洞

四方法之一 (对称消去/对称延拓/三桥/对称计数)。对称消去 =
对称冗余被结构性对消 (一阶对消 / 二阶保留):
  * 对消对: x + (-x) = 0 (一阶对消 — 静态层, 42 习题残差公式基础)
  * 奇偶对称: sin 奇 / cos 偶 (三角对称结构)
  * 对称区间积分: 奇函数 ∫_{-a}^{a} = 0 (奇对称结构性对消)
  * 周期积分: ∫₀^{2π} sin = ∫₀^{2π} cos = 0 (相位叠加消去)
  * 二阶保留: ∫_{-a}^{a} x² = 2a³/3 ≠ 0, ∫₀^{2π} sin² = π ≠ 0
    (一阶对消 ⟨x⟩ = 0 而二阶 ⟨x²⟩ > 0 — 残差-投影二象性的代数核)

全部 mathlib 锚定, 不引入 Pat 概念 (0pat)。

## 用户指示 (2026-08-21, 从黎曼路线复制 — 出处: 37_riemann_unified/observation.md 观测 AR)

用户方向: "找到一组对称性, 双向证明, 两个对称方向的相位对消, 不要单向的
力迫" + "利用共轭, 通过乘除法而不是加减法对消相位"。
对称消去 = 该指示的代数核: 对消对 x + (-x) = 0 (乘除法对消的加法对),
奇函数对称区间积分 = 0 (双向对消), 一阶对消二阶保留 (⟨x⟩=0 ∧ ⟨x²⟩>0)。

## 用户指示 (2026-08-22, 通用化改造 — 原话): "所有对称工具族, 必须进行
通用化改造, 乘除法能对消一些相位, 有可能是因为基点都锁定在 1 不是 0,
或者其他某些原因, 因此对称工具族必须能无视基点移动的任意消相位才好。"
通用化 = 对消结构从基点 0/1 锁定推广到任意基点 e: 反射对消 x + (2e - x)
= 2e (残差只依赖基点), 反射对合, 基点协变公式 (基点移动 = 平移 + 对消 +
平移回)。e = 0 时还原为原对消对。
English summary: Symmetry tool family #1 — Symmetry Cancellation. Cancellation pairs (x + (-x) = 0), odd/even symmetry (sin odd, cos even), symmetric-interval integration (∫_{-a}^{a} odd f = 0), full-period integration (∫₀^{2π} sin = ∫₀^{2π} cos = 0), second-order retention (∫_{-a}^{a} x² = 2a³/3, ∫₀^{2π} sin² = π — first-order cancellation ⟨x⟩=0 with second-order survival ⟨x²⟩>0, residual-projection duality). Mathlib-only, 零洞.
-/
namespace ZeroRelative

/-! ## 1. 对消对 (一阶对消) -/

/-- **对消对**: x + (-x) = 0 — 对称对的结构性对消 (静态层一阶对消,
42 习题残差公式: 一阶对消 x + (-x) = 0 的代数核).   Cancellation pair: x + (-x) = 0 — structural cancellation of a symmetric pair (first-order cancellation). 
English: Cancellation pair: x + (-x) = 0 — structural cancellation of a symmetric pair (static-layer first-order cancellation; the algebraic core of the 42-exercise residual formula). -/
theorem cancel_pair (x : ℝ) : x + (-x) = 0 := by
  ring

/-- **对消对 (一般代数)**: 任意加法交换群中 x + (-x) = 0.   Cancellation pair (general): x + (-x) = 0 in any additive commutative group. 
English: Cancellation pair (general): x + (-x) = 0 in any additive commutative group. -/
theorem cancel_pair_general {G : Type*} [AddCommGroup G] (x : G) : x + (-x) = 0 := by
  simp

/-- **投影对消**: x 与 -x 的算术平均 = 0 (对称对投影到中点 = 0).   Projection cancellation: the mean of x and -x is 0 (symmetric pair projects to the midpoint 0). 
English: Projection cancellation: the arithmetic mean of x and -x is 0 (a symmetric pair projects to the midpoint 0). -/
theorem projection_cancel (x : ℝ) : (x + (-x)) / 2 = 0 := by
  ring

/-! ## 2. 三角奇偶 (对称结构) -/

/-- **sin 奇**: sin(-x) = -sin x (三角对称消去的前提).   sin is odd: sin(-x) = -sin x (premise of trigonometric symmetry cancellation). 
English: sin is odd: sin(-x) = -sin x (premise of trigonometric symmetry cancellation). -/
theorem sin_neg_odd (x : ℝ) : Real.sin (-x) = -Real.sin x := by
  simp

/-- **cos 偶**: cos(-x) = cos x (三角对称保留的前提).   cos is even: cos(-x) = cos x (premise of trigonometric symmetry preservation). 
English: cos is even: cos(-x) = cos x (premise of trigonometric symmetry preservation). -/
theorem cos_neg_even (x : ℝ) : Real.cos (-x) = Real.cos x := by
  simp

/-! ## 3. 对称区间积分消去 (奇函数结构性对消) -/

/-- **奇函数对称区间积分 = 0**: ∀x, f(-x) = -f x ⟹ ∫_{-a}^{a} f = 0
— 奇对称性在对称区间被结构性对消 (换元 x ↦ -x 后 X = -X).   Odd function integrates to 0 over a symmetric interval: f(-x) = -f x implies ∫_{-a}^{a} f = 0 (substitution x ↦ -x gives X = -X). 
English: Odd function integrates to 0 over a symmetric interval: f(-x) = -f x ⟹ ∫_{-a}^{a} f = 0 — odd symmetry is structurally cancelled there (substitution x ↦ -x gives X = -X). -/
theorem odd_integral_symm_zero {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (a : ℝ) :
    ∫ x in -a..a, f x = 0 := by
  have hX : (∫ x in -a..a, f x) = -(∫ x in -a..a, f x) := by
    calc
      (∫ x in -a..a, f x) = ∫ x in -a..a, -f (-x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp
        rw [hf x]
        ring
      _ = -(∫ x in -a..a, f (-x)) := by
        rw [intervalIntegral.integral_neg]
      _ = -(∫ x in -a..a, f x) := by
        have hcomp : (∫ x in -a..a, f (-x)) = ∫ x in -a..a, f x := by
          simp [intervalIntegral.integral_comp_neg]
        rw [hcomp]
  linarith

/-! ## 4. 周期积分消去 (相位叠加) -/

/-- **∫₀^{2π} sin = 0**: 正弦整周期积分 = 0 (相位叠加消去: 半周期
正负对消).   ∫₀^{2π} sin = 0: sine integrates to 0 over a full period (phase-superposition cancellation). 
English: ∫₀^{2π} sin = 0: sine integrates to 0 over a full period (phase-superposition cancellation: the two halves cancel). -/
theorem integral_sin_full_period_zero :
    ∫ x in 0..2 * Real.pi, Real.sin x = 0 := by
  rw [integral_sin]
  norm_num [Real.cos_zero, Real.cos_two_pi]

/-- **∫₀^{2π} cos = 0**: 余弦整周期积分 = 0 (相位叠加消去).   ∫₀^{2π} cos = 0: cosine integrates to 0 over a full period. 
English: ∫₀^{2π} cos = 0: cosine integrates to 0 over a full period (phase-superposition cancellation). -/
theorem integral_cos_full_period_zero :
    ∫ x in 0..2 * Real.pi, Real.cos x = 0 := by
  rw [integral_cos]
  norm_num [Real.sin_zero, Real.sin_two_pi]

/-! ## 5. 二阶保留 (一阶对消 ⟨x⟩=0 而二阶 ⟨x²⟩>0) -/

/-- **二阶保留 (对称区间)**: ∫_{-a}^{a} x² = 2a³/3 ≠ 0 — 奇对称性
消去一阶 (x 奇), 二阶 (x² 偶) 保留 — 残差-投影二象性的代数核:
⟨x⟩ = 0 ∧ ⟨x²⟩ > 0 (a ≠ 0 时).   Second order survives (symmetric interval): ∫_{-a}^{a} x² = 2a³/3 ≠ 0 — odd symmetry cancels first order, second order survives: ⟨x⟩ = 0 ∧ ⟨x²⟩ > 0. 
English: Second order survives (symmetric interval): ∫_{-a}^{a} x² = 2a³/3 ≠ 0 — odd symmetry cancels the first order (x odd), the second order (x² even) survives — the algebraic core of residual-projection duality: ⟨x⟩ = 0 ∧ ⟨x²⟩ > 0 for a ≠ 0. -/
theorem second_order_survives_symm (a : ℝ) :
    ∫ x in -a..a, x ^ 2 = 2 * a ^ 3 / 3 := by
  rw [integral_pow]
  ring_nf

/-- **二阶保留 (整周期)**: ∫₀^{2π} sin² = π ≠ 0 — sin 一阶积分消去
(∫ sin = 0) 而二阶 (sin²) 保留 — 相干积累的基础 (42 习题: 层级同向
特征 j² 依赖的积分核).   Second order survives (full period): ∫₀^{2π} sin² = π ≠ 0 — basis of coherent accumulation. 
English: Second order survives (full period): ∫₀^{2π} sin² = π ≠ 0 — the first order cancels (∫ sin = 0) while the second order (sin²) survives — the basis of coherent accumulation (the 42-exercise integral kernel of the same-level same-direction feature j²). -/
theorem integral_sin_sq_full_period :
    ∫ x in 0..2 * Real.pi, Real.sin x ^ 2 = Real.pi := by
  rw [integral_sin_sq]
  norm_num [Real.sin_zero, Real.sin_two_pi, Real.cos_two_pi]

/-- **一阶消去二阶保留 (合取)**: ∫₀^{2π} sin = 0 ∧ ∫₀^{2π} sin² = π
— 同一对称结构的两层投影: 一阶对消 (⟨x⟩=0), 二阶保留 (⟨x²⟩>0).   First-order cancellation with second-order retention: ∫₀^{2π} sin = 0 ∧ ∫₀^{2π} sin² = π. 
English: First-order cancellation with second-order retention (conjunction): ∫₀^{2π} sin = 0 ∧ ∫₀^{2π} sin² = π — two projection layers of the same symmetry structure: the first order cancels (⟨x⟩=0), the second order survives (⟨x²⟩>0). -/
theorem first_order_cancel_second_order_keep :
    (∫ x in 0..2 * Real.pi, Real.sin x = 0) ∧
      (∫ x in 0..2 * Real.pi, Real.sin x ^ 2 = Real.pi) := by
  constructor
  · exact integral_sin_full_period_zero
  · exact integral_sin_sq_full_period


/-! ## 6. 通用化: 无视基点移动的任意消相位 (2026-08-22 用户指示) -/

/-- **★基点无关反射对消**: 任意基点 e 下, x 与反射对 (2e - x) 完全
对消: x + (2e - x) = 2e — 残差只依赖基点 e, 与 x 无关 (无视基点移动
的任意消相位; e = 0 时还原为 cancel_pair).   ★Basepoint-free
reflection cancellation: at any basepoint e, x and its reflection
(2e - x) cancel completely: x + (2e - x) = 2e — the residual depends
only on e, not on x (e = 0 recovers cancel_pair). 
English: ★Basepoint-free reflection cancellation: at any basepoint e, x and its reflection (2e - x) cancel exactly: x + (2e - x) = 2e — the residual depends only on e, not on x (arbitrary phase cancellation regardless of basepoint shift; e = 0 recovers cancel_pair). -/
theorem reflection_cancel_at_basepoint (e x : ℝ) : x + (2 * e - x) = 2 * e := by
  ring

/-- **★基点无关反射对合**: R_e(R_e(x)) = x, R_e(x) = 2e - x — 任意
基点 e 的反射是对合 (两次反射回到自身; 对消结构可逆).   ★Basepoint-
free reflection involution: R_e(R_e(x)) = x — reflection about any
basepoint e is an involution (cancellation structure is reversible). 
English: ★Basepoint-free reflection involution: R_e(R_e(x)) = x with R_e(x) = 2e - x — reflection about any basepoint e is an involution (two reflections return to the start; the cancellation structure is reversible). -/
theorem reflection_involutive (e x : ℝ) : 2 * e - (2 * e - x) = x := by
  ring

/-- **★基点协变公式**: R_e(x) = e + R_0(x - e) — 基点移动 = 坐标平移
+ 基点 0 对消 + 平移回 (对消结构无视基点移动: 任意基点下同一对消
律, 只是坐标平移; 用户: 基点都锁定在 1 不是 0 的怀疑的消解 — 对消
律本身不锁基点, 锁的是坐标).   ★Basepoint covariance: R_e(x) = e +
R_0(x - e) — basepoint shift = translate + cancel at 0 + translate back
(cancellation law itself is basepoint-free; only the coordinates are
anchored). 
English: ★Basepoint covariance: R_e(x) = e + R_0(x - e) — basepoint shift = translate + cancel at 0 + translate back; the same law holds at any basepoint, only coordinates shift (resolves the suspicion: the law is basepoint-free, coordinates anchored). -/
theorem reflection_covariance (e x : ℝ) : 2 * e - x = e + (-(x - e)) := by
  ring

/-- **★通用消相位 (加法)**: 任意基点 e 与任意 x, 存在对消伙伴
y = 2e - x, 使 x + y = 2e (残差 = 2·基点, 预计算, 与 x 无关) — 任意
消相位的存在性: 基点无关.   ★Universal cancellation (additive): at
any basepoint e and any x, there exists a partner y = 2e - x with
x + y = 2e (residual = 2·basepoint, precomputable, independent of x). 
English: ★Universal cancellation (additive): at any basepoint e and any x there is a partner y = 2e - x with x + y = 2e (residual = 2·basepoint, precomputable, independent of x) — the existence of arbitrary phase cancellation is basepoint-independent. -/
theorem universal_cancel_at_basepoint (e x : ℝ) : ∃ y : ℝ, x + y = 2 * e := by
  refine ⟨2 * e - x, ?_⟩
  ring


end ZeroRelative
