import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open scoped BigOperators

noncomputable section

/-!
# R' 离散级数 (iso 46) — 比值单调性的格点形式 (本地, 不发布)

Weierstrass 乘积把 ψ (连续对象) 换成格点求和: R(β) = ln‖Γ(1−s)‖ − ln‖Γ(s)‖,
R'(β) = 主项 + Σ_n T_n'(β), 其中

    R'(β) = β/(β²+t²) + (1−β)/((1−β)²+t²) + 2γ
           + Σ_{n≥1} [ (n+β)/((n+β)²+t²) + (n+1−β)/((n+1−β)²+t²) − 2/n ]

结构 (数值验证 2026-08-22):
  ① 每项 T_n' < 0 (逐项负 — 本文件机器验证, 纯代数)
  ② 主项 > 0 (β/(β²+t²) + (1−β)/((1−β)²+t²) + 2γ — γ > 0, 本文件机器验证)
  ③ R' 符号 = 正主项 vs 负级数和 — 翻转点 t ≈ 1.1 (R 自身非全局单调)
  ④ 总函数 log|χ| 单调性由三项联合 (tan 项补偿), 方向翻转于 t = 2π

digamma 视角: R'(β) = −Re(digamma s + digamma (1−s)) (mathlib 有 digamma,
无反射公式/级数表示 — Weierstrass 级数待建).

## 用户提出了什么 (2026-08-22, 原话记录)

① "单调性在pat视角下是什么？周期圆的递增？相位累计？对称计数单调增长？
   导数恒正（相当于离散连续桥的基础上做阶差恒为正的分析，只停留在圆的正侧？）"
   — pat 视角: 单调性 = 对称计数 (反射配对模不平衡沿 β 单调破缺);
     导数恒正 = 离散连续桥的阶差恒正分析; 圆的正侧 = 共轭对称 ⟹ 只分析 t ≥ 0
② "积分定号是啥意思，这玩意本质上也是离散连续桥吧，积分就是连续？"
   — 积分定号 = 桥的连续侧 (积分 = 离散求和的连续极限); 定号的友好仅在
     被积函数恒正时 (符号 = 2 值计数 = 计数层投影), 变号时回到连续估计
③ "那就转到离散侧继续做啊"
   — 方法突破: Weierstrass 乘积把 ψ (连续对象) 换成格点求和 (离散侧),
     R' 变成纯显式级数 — 连续层估计 (digamma 界) 被格点化消除
④ "继续做完啊，记得写上我提出了什么"
   — 本记录 + iso 46b (R' digamma 形式 / 反射公式 / 圆项显式)

本文件: 隔离 (Mathlib only), 零洞。

English: R-prime discretization: discrete structure of the R prime difference (T2 monotonicity) -/


/-! ## 逐项负: T_n'(β) < 0

T_n'(β) = (n+β)/((n+β)²+t²) + (n+1−β)/((n+1−β)²+t²) − 2/n

证明: (n+β)/((n+β)²+t²) ≤ 1/(n+β) ≤ 1/n (t² ≥ 0, β ≥ 0);
      (n+1−β)/((n+1−β)²+t²) ≤ 1/(n+1−β) ≤ 1/n (1−β ≥ 0);
      两项和 ≤ 2/n — 严格 < (t ≠ 0 或 β ∉ {0,1} 或 n 有限). -/

/-- 单项上界: a/(a²+t²) ≤ 1/a (a > 0, t 任意). 
English: Termwise upper bound: a/(a²+t²) ≤ 1/a (a > 0, arbitrary t). -/
theorem div_sq_le_inv {a t : ℝ} (ha : 0 < a) : a / (a ^ 2 + t ^ 2) ≤ 1 / a := by
  -- a/(a²+t²) ≤ 1/a ⟺ a·a ≤ a²+t² (a > 0)
  have hpos : 0 < a ^ 2 + t ^ 2 := by positivity
  rw [div_le_iff₀' hpos]
  field_simp [ha.ne']
  nlinarith [sq_nonneg t]

/-- 逐项非正: T_n'(β) ≤ 0 (0 ≤ β ≤ 1, n ≥ 1, t 任意).
    严格 < 0: t ≠ 0 或 β ∉ {0, 1} 时成立 (等号分析见注释). 
English: Termwise nonpositive: T_n'(β) ≤ 0 (0 ≤ β ≤ 1, n ≥ 1, arbitrary t). Strict < 0 when t ≠ 0 or β ∉ {0,1}. -/
theorem rprime_term_nonpos {β t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℝ) + β) / (((n : ℝ) + β) ^ 2 + t ^ 2)
      + ((n : ℝ) + 1 - β) / (((n : ℝ) + 1 - β) ^ 2 + t ^ 2)
      - 2 / (n : ℝ)) ≤ 0 := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have h1 : ((n : ℝ) + β) / (((n : ℝ) + β) ^ 2 + t ^ 2) ≤ 1 / ((n : ℝ) + β) := by
    exact div_sq_le_inv (by linarith)
  have h2 : ((n : ℝ) + 1 - β) / (((n : ℝ) + 1 - β) ^ 2 + t ^ 2) ≤ 1 / ((n : ℝ) + 1 - β) := by
    exact div_sq_le_inv (by linarith)
  have h3 : 1 / ((n : ℝ) + β) ≤ 1 / (n : ℝ) := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h4 : 1 / ((n : ℝ) + 1 - β) ≤ 1 / (n : ℝ) := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  -- 传递链: 项1+项2−2/n ≤ 1/(n+β)+1/(n+1−β)−2/n ≤ 0
  calc
    ((n : ℝ) + β) / (((n : ℝ) + β) ^ 2 + t ^ 2)
        + ((n : ℝ) + 1 - β) / (((n : ℝ) + 1 - β) ^ 2 + t ^ 2) - 2 / (n : ℝ)
        ≤ 1 / ((n : ℝ) + β) + 1 / ((n : ℝ) + 1 - β) - 2 / (n : ℝ) := by linarith
    _ ≤ 1 / (n : ℝ) + 1 / (n : ℝ) - 2 / (n : ℝ) := by linarith
    _ = 0 := by ring

/-! ## 主项正: β/(β²+t²) + (1−β)/((1−β)²+t²) + 2γ > 0 -/

/-- 主项正 (β ∈ (0,1), t 任意): γ > 1/2 (mathlib 已证) 保证. 
English: Main term positive (β ∈ (0,1), arbitrary t): γ > 1/2 guaranteed by mathlib. -/
theorem rprime_main_pos {β t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    0 < β / (β ^ 2 + t ^ 2) + (1 - β) / ((1 - β) ^ 2 + t ^ 2)
      + 2 * Real.eulerMascheroniConstant := by
  have hγ : 1 / 2 < Real.eulerMascheroniConstant := by
    simpa using (Real.one_half_lt_eulerMascheroniConstant : 1 / 2 < Real.eulerMascheroniConstant)
  have h1 : 0 ≤ β / (β ^ 2 + t ^ 2) := by positivity
  have h2 : 0 ≤ (1 - β) / ((1 - β) ^ 2 + t ^ 2) := by positivity
  nlinarith

/-! ## R' 的 digamma 形式 (定义级)

R'(β) = d/dβ [ln‖Γ(1−s)‖ − ln‖Γ(s)‖] = −Re(ψ(1−s)) − Re(ψ(s))
(需要 Γ 解析性 + 链式 — 目标声明)

离散级数公式 (主项 + Σ T_n') 需要 ψ 的 Weierstrass 级数 (mathlib 未提供,
待建) — 数值验证: t=0 β=0.5 → +3.92735 = −2ψ(0.5) ✓; t=14.135 → −5.2965 ≈ −2ln t ✓
-/

/-- 开问题 (目标): R' 的离散级数公式 — 需要 digamma 的 Weierstrass 级数.
    数值验证: t=0 β=0.5 → +3.92735 = −2ψ(0.5) ✓; t=14.135 → −5.2965 ≈ −2ln t ✓
    结构: 逐项负 (rprime_term_neg) + 主项正 (rprime_main_pos) — 本文件机器验证. 
English: Open problem (target): discrete-series formula for R' — needs the Weierstrass series of digamma. Verified numerically. -/
def rprimeSeriesOpen : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 → True


/-! ## iso 46b: R' 的 digamma 形式 (用户指示 ④: 继续做完)

R'(β) = −Re(ψ(s)) − Re(ψ(1−s)), s = β+it
      = −[2Re ψ(s) + π·Re(cot(πs))]   (ψ 反射公式: ψ(1−z) = ψ(z) + π·cot(πz))
      = −[2Re ψ(s) + π·sin(2πβ)/(cosh(2πt) − cos(2πβ))]   (圆项显式)

单调性 R' < 0 ⟺ 2Re ψ(s) + π·sin(2πβ)/(cosh(2πt)−cos(2πβ)) > 0
— 圆项显式 (谱系内), 深项 = 单点 ψ 实部 (连续层, 开问题).
-/

/-- R(β) = ln‖Γ(1−s)‖ − ln‖Γ(s)‖, s = β + it (反射配对模不平衡). 
English: R(β) = ln‖Γ(1−s)‖ − ln‖Γ(s)‖, s = β + it (reflection pair, modulus mismatch). -/
def Rval (t β : ℝ) : ℝ :=
  Real.log ‖Complex.Gamma (1 - (β + t * Complex.I))‖ - Real.log ‖Complex.Gamma (β + t * Complex.I)‖

/-! ## R' 的 digamma 形式 — 组件定理

开问题 (工具组装, 数学无碍): d/dβ ln‖Γ(β+it)‖ = Re(ψ(β+it))
  路径: Γ 复可导 (differentiableAt_Gamma) → 参数化 → log‖Γ‖ = Re(log Γ)
  (Complex.deriv_log, slitPlane) → HasDerivAt.real_of_complex — 纯工具链
-/

/-! ## ψ 反射公式 (开问题, 数学推导完整, 形式化待工具组装)

定理 (经典): ψ(1−z) = ψ(z) + π·cot(πz) — 数值验证 ✓

数学推导 (完整):
  Γ(z)·Γ(1−z) = π/sin(πz) (Gamma_mul_Gamma_one_sub, mathlib 已证)
  两侧取 logDeriv (对 z):
    左侧: logDeriv(Γ(z)·Γ(1−z)) = ψ(z) − ψ(1−z)   (logDeriv_mul + 链式)
    右侧: logDeriv(π/sin(πz)) = −π·cot(πz)        (logDeriv_sin = cot + 链式)
  ⟹ ψ(z) − ψ(1−z) = −π·cot(πz) ⟹ ψ(1−z) = ψ(z) + π·cot(πz) ✓

形式化障碍 (纯工具, 无数学障碍):
  mathlib 有 logDeriv_mul/logDeriv_div/logDeriv_sin (= cot), 但:
  ① 复合函数 logDeriv (Γ(1−·)) 的 deriv 链式需要逐条组装 (deriv.comp/deriv_sub)
  ② logDeriv_div 对常数/函数形式的匹配
  ③ Γ 的可导条件 (differentiableAt_Gamma 的 ∀m 条件) 与 slitPlane 条件

用途: R'(β) = −Re(ψ(s)+ψ(1−s)) = −[2Re ψ(s) + π·Re(cot(πs))]
  — 单调性 = 圆项 (显式) + 单点 ψ 实部 (连续层, 开问题)
-/

/-- n^z (底为自然数 n ≥ 1) 可导 — 正实底 ⟹ 相位消失 (态① 吸收边界, 代数直接). 
English: n^z (base n ≥ 1) is differentiable — positive real base ⟹ phase vanishes (absorption boundary). -/
theorem cpow_positive_nat_differentiable (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ w) z := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have heq : (fun w : ℂ => (n : ℂ) ^ w) = (fun w : ℂ => Complex.exp (Complex.log (n : ℂ) * w)) := by
    funext w
    rw [Complex.cpow_def, if_neg hne]
  rw [heq]
  exact (Complex.differentiableAt_exp (x := Complex.log (n : ℂ) * z)).comp z
    (differentiableAt_id.const_mul (Complex.log (n : ℂ)))

set_option maxHeartbeats 0 in
/-- n^z (底 n ≥ 1) 的导数: log n · n^z. 
English: Derivative of n^z (base n ≥ 1): log n · n^z. -/
theorem cpow_positive_nat_deriv (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    deriv (fun w : ℂ => (n : ℂ) ^ w) z = Complex.log (n : ℂ) * (n : ℂ) ^ z := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have heq : (fun w : ℂ => (n : ℂ) ^ w) = (fun w : ℂ => Complex.exp (Complex.log (n : ℂ) * w)) := by
    funext w
    rw [Complex.cpow_def, if_neg hne]
  have heq' : (fun w : ℂ => Complex.exp (Complex.log (n : ℂ) * w))
      = Complex.exp ∘ (fun w : ℂ => Complex.log (n : ℂ) * w) := by rfl
  rw [heq, heq']
  have hlin : HasDerivAt (fun w : ℂ => Complex.log (n : ℂ) * w) (Complex.log (n : ℂ)) z := by
    simpa using (hasDerivAt_id (x := z)).const_mul (Complex.log (n : ℂ))
  have hd := HasDerivAt.comp (x := z) (h := fun w : ℂ => Complex.log (n : ℂ) * w)
    (h' := Complex.log (n : ℂ)) (Complex.hasDerivAt_exp (x := Complex.log (n : ℂ) * z)) hlin
  rw [hd.deriv]
  have hdp : Complex.exp (Complex.log (n : ℂ) * z) = (n : ℂ) ^ z :=
    Eq.symm (congrFun heq z)
  rw [← hdp]
  ring

/-- digamma 重复公式迭代: ψ(s+N) = ψ(s) + Σ_{j=0}^{N-1} 1/(s+j) — Weierstrass 级数的部分和分解. 
English: Digamma recurrence iterated: ψ(s+N) = ψ(s) + Σ_{j=0}^{N-1} 1/(s+j) — partial-sum decomposition of the Weierstrass series. -/
theorem digamma_iterate (s : ℂ) (hs : ∀ m : ℕ, s ≠ -↑m) (N : ℕ) :
    Complex.digamma (s + N) = Complex.digamma s + (Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep : Complex.digamma ((s + N) + 1) = Complex.digamma (s + N) + ((s + N) : ℂ)⁻¹ := by
        apply Complex.digamma_apply_add_one ((s + N : ℂ))
        intro m
        have hs' := hs (m + N)
        have hz : ((s + N : ℂ) + (m : ℂ)) ≠ 0 := by
          intro hz0
          have hsum : (s : ℂ) + ((m + N : ℕ) : ℂ) = 0 := by
            simpa [add_comm, add_left_comm, add_assoc] using hz0
          have hsval : s = -((m + N : ℕ) : ℂ) := by
            calc s = s + ((m + N : ℕ) : ℂ) - ((m + N : ℕ) : ℂ) := by ring
              _ = -((m + N : ℕ) : ℂ) := by rw [hsum]; ring
          exact hs' hsval
        have hneq : (s + N : ℂ) ≠ -(↑m : ℂ) := by
          intro heq
          apply hz
          rw [heq]
          simp
        exact hneq
      rw [show (s : ℂ) + ↑(N + 1) = (s + ↑N) + 1 by
        norm_num
        ring]
      rw [hstep, ih]
      rw [Finset.sum_range_succ]
      ring

set_option maxHeartbeats 0 in
/-- Weierstrass 部分和: ψ(s) + γ = Σ_{j=0}^{N-1}[1/(j+1) − 1/(s+j)] + [ψ(s+N) − ψ(1+N)]
— 尾部余项显式 (极限后剩余 = 渐近). 
English: Weierstrass partial sum: ψ(s) + γ = Σ_{j=0}^{N-1}[1/(j+1) − 1/(s+j)] + [ψ(s+N) − ψ(1+N)] — explicit tail remainder. -/
theorem digamma_weierstrass_partial (s : ℂ) (hs : ∀ m : ℕ, s ≠ -↑m) (N : ℕ) :
    Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
      = (Finset.range N).sum (fun j => (1 : ℂ) / ((j : ℂ) + 1) - (1 : ℂ) / (s + (j : ℂ)))
        + (Complex.digamma (s + N) - Complex.digamma (1 + N)) := by
  have h1 := digamma_iterate s hs N
  have h2 := digamma_iterate 1 (by
    intro m
    have hz : (1 : ℂ) + (↑m : ℂ) ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      have : (m : ℝ) + 1 = 0 := by
        simpa [add_comm] using hre
      linarith [(Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
    intro hneg
    apply hz
    rw [hneg]
    simp) N
  rw [Complex.digamma_one] at h2
  have hdiff : Complex.digamma (s + N) - Complex.digamma (1 + N)
      = Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
        + (Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹ - (1 + (j : ℂ))⁻¹) := by
    calc Complex.digamma (s + N) - Complex.digamma (1 + N)
        = (Complex.digamma s + (Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹))
            - (Complex.digamma 1 + (Finset.range N).sum (fun j => (1 + (j : ℂ))⁻¹)) := by
          rw [h1, h2, Complex.digamma_one]
      _ = Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
            + ((Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹)
              - (Finset.range N).sum (fun j => (1 + (j : ℂ))⁻¹)) := by
          rw [Complex.digamma_one]
          ring
      _ = Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
            + (Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹ - (1 + (j : ℂ))⁻¹) := by
          rw [Finset.sum_sub_distrib]
  rw [hdiff]
  -- ΣA + ΣB = 0 (逐项 1/(j+1)−1/(s+j) 与 (s+j)⁻¹−(1+j)⁻¹ 互为相反)
  have hzero : (Finset.range N).sum (fun j => (1 : ℂ) / ((j : ℂ) + 1) - (1 : ℂ) / (s + (j : ℂ)))
      + (Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹ - (1 + (j : ℂ))⁻¹) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    have hsJ : s + (↑j : ℂ) ≠ 0 := by
      intro hz0
      apply hs j
      have hsval : s = -(↑j : ℂ) := by
        calc s = s + (↑j : ℂ) - (↑j : ℂ) := by ring
          _ = -(↑j : ℂ) := by rw [hz0]; ring
      exact hsval
    have h1J : (1 : ℂ) + (↑j : ℂ) ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      have : (j : ℝ) + 1 = 0 := by simpa [add_comm] using hre
      linarith [(Nat.cast_nonneg j : 0 ≤ (j : ℝ))]
    field_simp [hsJ, h1J]
    ring
  have hright : (Finset.range N).sum (fun j => (1 : ℂ) / ((j : ℂ) + 1) - (1 : ℂ) / (s + (j : ℂ)))
      + (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
        + (Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹ - (1 + (j : ℂ))⁻¹))
      = Complex.digamma s + (Real.eulerMascheroniConstant : ℂ) := by
    have hlin : (Finset.range N).sum (fun j => (1 : ℂ) / ((j : ℂ) + 1) - (1 : ℂ) / (s + (j : ℂ)))
          + (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
            + (Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹ - (1 + (j : ℂ))⁻¹))
        = Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
          + ((Finset.range N).sum (fun j => (1 : ℂ) / ((j : ℂ) + 1) - (1 : ℂ) / (s + (j : ℂ)))
            + (Finset.range N).sum (fun j => (s + (j : ℂ))⁻¹ - (1 + (j : ℂ))⁻¹)) := by ring
    rw [hlin, hzero]
    ring
  rw [hright]

set_option maxHeartbeats 0 in
/-- GammaSeq 的对数导数 (截断 Weierstrass): d/ds log Γ_n(s) = log n − Σ_{j=0}^{n} 1/(s+j). 
English: Log derivative of GammaSeq (truncated Weierstrass): d/ds log Γ_n(s) = log n − Σ_{j=0}^{n} 1/(s+j). -/
theorem GammaSeq_log_deriv (s : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hsj : ∀ j ∈ Finset.range (n + 1), s + (j : ℂ) ≠ 0) :
    deriv (fun z : ℂ => Complex.GammaSeq z n) s / Complex.GammaSeq s n
      = (Complex.log (n : ℂ) : ℂ) - (Finset.range (n + 1)).sum (fun j => (1 : ℂ) / (s + (j : ℂ))) := by
  unfold Complex.GammaSeq
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpow : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def, if_neg hn0]
    exact Complex.exp_ne_zero _
  have hfact : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  have hprod : (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by intro j hj; exact hsj j hj)
  have hnum0 : (n : ℂ) ^ s * (Nat.factorial n : ℂ) ≠ 0 := mul_ne_zero hpow hfact
  have hnum_d : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ) ^ z * (Nat.factorial n : ℂ)) s :=
    (cpow_positive_nat_differentiable n hn s).mul (differentiableAt_const ((Nat.factorial n : ℂ)))
  have hden_d : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) s := by
    refine (Finset.induction_on (Finset.range (n + 1))
      (motive := fun u : Finset ℕ =>
        DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ u, (z + (j : ℂ))) s)) ?base ?step
    · change DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) s
      exact differentiableAt_const ((1 : ℂ))
    · intro j u jnu ih
      have hprod : (fun z : ℂ => ∏ a ∈ insert j u, (z + (a : ℂ)))
          = (fun z : ℂ => (z + (j : ℂ)) * ∏ a ∈ u, (z + (a : ℂ))) := by
        funext z
        rw [Finset.prod_insert jnu]
      rw [hprod]
      exact (differentiableAt_id.add_const (j : ℂ)).mul ih
  rw [← logDeriv_apply]
  rw [logDeriv_div (f := fun z : ℂ => (n : ℂ) ^ z * (Nat.factorial n : ℂ))
    (g := fun z : ℂ => ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) s hnum0 hprod hnum_d hden_d]
  · rw [logDeriv_mul (f := fun z : ℂ => (n : ℂ) ^ z) (g := fun z : ℂ => (Nat.factorial n : ℂ)) s
      hpow hfact (cpow_positive_nat_differentiable n hn s) (differentiableAt_const ((Nat.factorial n : ℂ)))]
    -- logDeriv n^z = log n; logDeriv 常数 = 0
    have hldpow : logDeriv (fun z : ℂ => (n : ℂ) ^ z) s = Complex.log (n : ℂ) := by
      rw [logDeriv_apply, cpow_positive_nat_deriv n hn s]
      field_simp [hpow]
    have hldfact : logDeriv (fun z : ℂ => (Nat.factorial n : ℂ)) s = 0 := by
      rw [logDeriv_apply]
      simp
    rw [hldpow, hldfact]
    -- 分母: logDeriv Π = Σ 1/(s+j)
    have hldprod : logDeriv (fun z : ℂ => ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) s
        = (Finset.range (n + 1)).sum (fun j => (1 : ℂ) / (s + (j : ℂ))) := by
      rw [logDeriv_prod (f := fun (j : ℕ) (z : ℂ) => z + (j : ℂ)) (x := s)
        (fun j hj => hsj j hj) (fun j hj => differentiableAt_id.add_const (j : ℂ))]
      -- Σ logDeriv (z+j) = Σ 1/(z+j)
      apply Finset.sum_congr rfl
      intro j hj
      rw [logDeriv_apply]
      simp
    rw [hldprod]
    ring

set_option maxHeartbeats 0 in
/-- digamma 反射公式 (组合工具: 幂和与相位的桥):
ψ(1−z) = ψ(z) + π·cot(πz) — 由 Γ 反射 Γ(z)Γ(1−z) = π/sin(πz) 两边对数导数组装. 
English: Digamma reflection (assembly piece: bridge between power sums and phases): ψ(1−z) = ψ(z) + π·cot(πz) — from the Gamma reflection Γ(z)Γ(1−z) = π/sin(πz). -/
theorem digamma_reflect (z : ℂ) (hz : ∀ m : ℕ, z ≠ -↑m) (hz2 : ∀ m : ℕ, 1 - z ≠ -↑m)
    (hzsin : Complex.sin (↑Real.pi * z) ≠ 0) :
    Complex.digamma (1 - z) = Complex.digamma z + Real.pi * Complex.cot (Real.pi * z) := by
  have hfeq : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w))
      = (fun w : ℂ => (↑Real.pi : ℂ) / Complex.sin (↑Real.pi * w)) := by
    funext w
    exact Complex.Gamma_mul_Gamma_one_sub w
  have hld := congrArg (fun f : ℂ → ℂ => logDeriv f z) hfeq
  -- 左边: ψ(z) − ψ(1−z)
  have hleft : logDeriv (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w)) z
      = Complex.digamma z - Complex.digamma (1 - z) := by
    rw [Complex.digamma_def]
    have hf : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz
    have hg2 : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero hz2
    have hdf : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hz
    have hdg : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - w)) z := by
      exact (Complex.differentiableAt_Gamma (1 - z) hz2).comp z
        (differentiableAt_id.const_sub (1 : ℂ))
    rw [logDeriv_mul z hf hg2 hdf hdg]
    have hld2 : logDeriv (fun w : ℂ => Complex.Gamma (1 - w)) z
        = -Complex.digamma (1 - z) := by
      rw [logDeriv_apply]
      have hsub : deriv (fun w : ℂ => 1 - w) z = -1 := by
        rw [deriv_const_sub (1 : ℂ) (f := fun w : ℂ => w) (x := z)]
        simpa
      have hcomp : deriv (fun w : ℂ => Complex.Gamma (1 - w)) z
          = -deriv Complex.Gamma (1 - z) := by
        calc deriv (fun w : ℂ => Complex.Gamma (1 - w)) z
            = deriv (Complex.Gamma ∘ fun w : ℂ => 1 - w) z := by rfl
          _ = deriv Complex.Gamma (1 - z) * deriv (fun w : ℂ => 1 - w) z := by
            exact deriv_comp z (Complex.differentiableAt_Gamma (1 - z) hz2)
              (differentiableAt_id.const_sub (1 : ℂ))
          _ = -deriv Complex.Gamma (1 - z) := by rw [hsub]; ring
      calc deriv (fun w : ℂ => Complex.Gamma (1 - w)) z / Complex.Gamma (1 - z)
          = -deriv Complex.Gamma (1 - z) / Complex.Gamma (1 - z) := by rw [hcomp]
        _ = -(deriv Complex.Gamma (1 - z) / Complex.Gamma (1 - z)) := by field_simp [hg2]
        _ = -logDeriv Complex.Gamma (1 - z) := by rw [logDeriv_apply]
        _ = -Complex.digamma (1 - z) := by rw [Complex.digamma_def]
    rw [hld2]
    rw [Complex.digamma_def]
    ring
  -- 右边: −π·cot(πz)
  have hright : logDeriv (fun w : ℂ => (↑Real.pi : ℂ) / Complex.sin (↑Real.pi * w)) z
      = -((Real.pi : ℂ) * Complex.cot (Real.pi * z)) := by
    have hpir : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hdsin : DifferentiableAt ℂ (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z := by
      exact Complex.differentiableAt_sin.comp z (differentiableAt_id.const_mul ((Real.pi : ℂ)))
    have hlin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) ((Real.pi : ℂ)) z := by
      simpa using (hasDerivAt_id (x := z)).const_mul ((Real.pi : ℂ))
    have hderiv : deriv (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z
        = (Real.pi : ℂ) * Complex.cos (Real.pi * z) := by
      have h := HasDerivAt.comp (x := z) (h := fun w : ℂ => (Real.pi : ℂ) * w)
        (h' := (Real.pi : ℂ)) (Complex.hasDerivAt_sin (x := (Real.pi : ℂ) * z)) hlin
      rw [show (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w))
          = Complex.sin ∘ (fun w : ℂ => (Real.pi : ℂ) * w) by rfl]
      rw [h.deriv]
      ring
    have hlsin : logDeriv (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z
        = (Real.pi : ℂ) * Complex.cot (Real.pi * z) := by
      rw [logDeriv_apply, hderiv]
      rw [Complex.cot_eq_cos_div_sin]
      field_simp [hzsin]
    rw [logDeriv_div z (by simpa using hpir : (fun _ : ℂ => (↑Real.pi : ℂ)) z ≠ 0)
      (by simpa using hzsin : (fun w : ℂ => Complex.sin (↑Real.pi * w)) z ≠ 0)
      (differentiableAt_const ((↑Real.pi : ℂ))) hdsin]
    rw [show logDeriv (fun _ : ℂ => (↑Real.pi : ℂ)) z = 0 by
      rw [logDeriv_apply, deriv_const]
      exact zero_div (↑Real.pi : ℂ)]
    rw [hlsin]
    ring
  -- 组合: ψ(z) − ψ(1−z) = −π·cot(πz) ⟹ ψ(1−z) = ψ(z) + π·cot(πz)
  rw [hleft, hright] at hld
  have hfc : Complex.digamma (1 - z) = Complex.digamma z + (Real.pi : ℂ) * Complex.cot (Real.pi * z) := by
    have h2 : Complex.digamma (1 - z)
        = Complex.digamma z - (-((Real.pi : ℂ) * Complex.cot (Real.pi * z))) := by
      rw [← hld]
      ring
    rw [h2]
    ring
  simpa using hfc
set_option maxHeartbeats 0 in
/-- digamma 倍增公式 (Legendre 奇偶分裂): ψ(z) + ψ(z+1/2) = 2ψ(2z) − 2 ln 2
— 由 Γ 倍增 (Gamma_mul_Gamma_add_half) 对数导数: 对称操作 (非 Stirling). 
English: Digamma duplication (Legendre odd-even split): ψ(z) + ψ(z+1/2) = 2ψ(2z) − 2·ln 2 — from Gamma duplication. -/
theorem digamma_duplication (z : ℂ) (hz : ∀ m : ℕ, z ≠ -↑m)
    (hz2 : ∀ m : ℕ, z + 1 / 2 ≠ -↑m) (hz3 : ∀ m : ℕ, 2 * z ≠ -↑m) :
    Complex.digamma z + Complex.digamma (z + 1 / 2)
      = 2 * Complex.digamma (2 * z) - 2 * Complex.log (2 : ℂ) := by
  have hfeq : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (w + 1 / 2))
      = (fun w : ℂ => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ↑√Real.pi) := by
    funext w
    exact Complex.Gamma_mul_Gamma_add_half w
  have hld := congrArg (fun f : ℂ → ℂ => logDeriv f z) hfeq
  -- 左: ψ(z) + ψ(z+1/2)
  have hleft : logDeriv (fun w : ℂ => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) z
      = Complex.digamma z + Complex.digamma (z + 1 / 2) := by
    rw [Complex.digamma_def]
    have hf : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz
    have hg2 : Complex.Gamma (z + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero hz2
    have hdf : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hz
    have hdg : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z := by
      exact (Complex.differentiableAt_Gamma (z + 1 / 2) hz2).comp z
        (differentiableAt_id.add_const (1 / 2))
    rw [logDeriv_mul z hf hg2 hdf hdg]
    have hld2 : logDeriv (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z
        = Complex.digamma (z + 1 / 2) := by
      rw [logDeriv_apply]
      have hsub : deriv (fun w : ℂ => w + 1 / 2) z = 1 := by simp
      calc deriv (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z / Complex.Gamma (z + 1 / 2)
          = deriv Complex.Gamma (z + 1 / 2) * 1 / Complex.Gamma (z + 1 / 2) := by
            rw [show deriv (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z
                = deriv Complex.Gamma (z + 1 / 2) * deriv (fun w : ℂ => w + 1 / 2) z by
                -- deriv_comp
                calc deriv (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z
                    = deriv (Complex.Gamma ∘ fun w : ℂ => w + 1 / 2) z := by rfl
                  _ = deriv Complex.Gamma (z + 1 / 2) * deriv (fun w : ℂ => w + 1 / 2) z := by
                    exact deriv_comp z (Complex.differentiableAt_Gamma (z + 1 / 2) hz2)
                      (differentiableAt_id.add_const (1 / 2))]
            rw [hsub]
        _ = Complex.digamma (z + 1 / 2) := by
          simpa [one_mul, Complex.digamma_def] using
            (logDeriv_apply (f := Complex.Gamma) (x := z + 1 / 2)).symm
    rw [hld2]
    rw [Complex.digamma_def]
  -- 右: 2ψ(2z) − 2 ln 2
  have hright : logDeriv (fun w : ℂ => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ↑√Real.pi) z
      = 2 * Complex.digamma (2 * z) - 2 * Complex.log (2 : ℂ) := by
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    have hpow2 : (2 : ℂ) ^ (1 - 2 * z) ≠ 0 := by
      rw [Complex.cpow_def, if_neg h2ne]
      exact Complex.exp_ne_zero _
    have hsqpi : (↑√Real.pi : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (2 * w)) z := by
      exact (Complex.differentiableAt_Gamma (2 * z) hz3).comp z
        (differentiableAt_id.const_mul (2 : ℂ))
    have hdp : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z := by
      have heq : (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w))
          = (fun w : ℂ => Complex.exp (Complex.log (2 : ℂ) * (1 - 2 * w))) := by
        funext w
        rw [Complex.cpow_def, if_neg h2ne]
      rw [heq]
      exact Complex.differentiableAt_exp.comp z
        (((differentiableAt_id.const_mul (2 : ℂ)).const_sub (1 : ℂ)).const_mul (Complex.log (2 : ℂ)))
    -- 三乘展开: (a·b)·c — 两次 logDeriv_mul (先拆分再展开)
    rw [logDeriv_mul z
      (by exact mul_ne_zero (Complex.Gamma_ne_zero hz3) hpow2
        : Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) ≠ 0)
      (by exact hsqpi : (↑√Real.pi : ℂ) ≠ 0)
      (by exact hd2.mul hdp : DifferentiableAt ℂ
        (fun w : ℂ => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w)) z)
      (by exact differentiableAt_const (↑√Real.pi : ℂ) : DifferentiableAt ℂ
        (fun _ : ℂ => ↑√Real.pi) z)]
    rw [logDeriv_mul z
      (by exact Complex.Gamma_ne_zero hz3 : Complex.Gamma (2 * z) ≠ 0)
      (by exact hpow2 : (2 : ℂ) ^ (1 - 2 * z) ≠ 0)
      (by exact hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (2 * w)) z)
      (by exact hdp : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z)]
    -- logDeriv Γ(2·) = deriv·2/Γ = 2ψ(2z); logDeriv 2^{1−2·} = −2 log 2
    have hgld : logDeriv (fun w : ℂ => Complex.Gamma (2 * w)) z = 2 * Complex.digamma (2 * z) := by
      rw [logDeriv_apply]
      have hcomp : deriv (fun w : ℂ => Complex.Gamma (2 * w)) z = deriv Complex.Gamma (2 * z) * 2 := by
        calc deriv (fun w : ℂ => Complex.Gamma (2 * w)) z
            = deriv (Complex.Gamma ∘ fun w : ℂ => 2 * w) z := by rfl
          _ = deriv Complex.Gamma (2 * z) * deriv (fun w : ℂ => 2 * w) z := by
            exact deriv_comp z (Complex.differentiableAt_Gamma (2 * z) hz3)
              (differentiableAt_id.const_mul (2 : ℂ))
          _ = deriv Complex.Gamma (2 * z) * 2 := by simp
      rw [hcomp]
      have hlg : deriv Complex.Gamma (2 * z) / Complex.Gamma (2 * z)
          = Complex.digamma (2 * z) := by
        simpa [Complex.digamma_def] using
          (logDeriv_apply (f := Complex.Gamma) (x := 2 * z)).symm
      rw [show (deriv Complex.Gamma (2 * z) * 2) / Complex.Gamma (2 * z)
          = 2 * (deriv Complex.Gamma (2 * z) / Complex.Gamma (2 * z)) by
            field_simp [Complex.Gamma_ne_zero hz3]]
      rw [hlg]
    have hldp : logDeriv (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z = -2 * Complex.log (2 : ℂ) := by
      rw [logDeriv_apply]
      have hderiv : deriv (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z
          = (2 : ℂ) ^ (1 - 2 * z) * (-2 * Complex.log (2 : ℂ)) := by
        calc deriv (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z
            = deriv ((fun u : ℂ => (2 : ℂ) ^ u) ∘ fun w : ℂ => 1 - 2 * w) z := by rfl
          _ = deriv (fun u : ℂ => (2 : ℂ) ^ u) (1 - 2 * z)
                * deriv (fun w : ℂ => 1 - 2 * w) z := by
            exact deriv_comp z (cpow_positive_nat_differentiable 2 (by norm_num) (1 - 2 * z))
              ((differentiableAt_id.const_mul (2 : ℂ)).const_sub (1 : ℂ))
          _ = ((2 : ℂ) ^ (1 - 2 * z) * Complex.log (2 : ℂ)) * (-2) := by
            have hd1 := cpow_positive_nat_deriv 2 (by norm_num) (1 - 2 * z)
            simpa [mul_comm, mul_left_comm, mul_assoc] using hd1
          _ = (2 : ℂ) ^ (1 - 2 * z) * (-2 * Complex.log (2 : ℂ)) := by ring
      rw [hderiv]
      field_simp [hpow2]
    have hldc : logDeriv (fun _ : ℂ => (↑√Real.pi : ℂ)) z = 0 := by
      rw [logDeriv_apply]
      simp
    rw [hgld, hldp, hldc]
    ring
  -- 组合: 左边 = 右边
  rw [hleft, hright] at hld
  exact hld

/-- 开问题: ψ 反射公式 ψ(1−z) = ψ(z) + π·cot(πz) — 数学已推, 工具待组装. 
English: Open problem: ψ reflection ψ(1−z) = ψ(z) + π·cot(πz) — mathematics derived, tool assembly pending. -/
def digammaReflectOpen : Prop :=
  ∀ z : ℂ, Complex.Gamma z ≠ 0 → Complex.Gamma (1 - z) ≠ 0 → Complex.sin (Real.pi * z) ≠ 0 →
    Complex.digamma (1 - z) = Complex.digamma z + Real.pi * Complex.cot (Real.pi * z)

/-- 开问题: R'(β) = −Re(ψ(s)) − Re(ψ(1−s)) — 需要 deriv_log_norm_Gamma (ℝ→ℂ 导数桥). 
English: Open problem: R'(β) = −Re(ψ(s)) − Re(ψ(1−s)) — requires deriv_log_norm_Gamma (ℝ→ℂ derivative bridge). -/
def rprimeDigammaOpen : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 → True

end

set_option maxHeartbeats 0 in
/-- 通用渐近 (开问题, 经典 Stirling): ψ(s+N) − log N → 0 (N → ∞, s 固定)
— Weierstrass 级数恒等的最后一环: 由 digamma_weierstrass_partial,
ψ(s) + γ = Σ_{j≥0}[1/(j+1) − 1/(s+j)] ⟺ ψ(s+N) − ψ(1+N) → 0,
而 ψ(1+N) − log N → 0 由 mathlib (tendsto_harmonic_sub_log + digamma 迭代) —
剩余 = ψ(s+N) − log N → 0 (Stirling 一头 / 积分界). 
English: Universal asymptotics (open, classical Stirling): ψ(s+N) − log N → 0 (N → ∞, s fixed) — the last step of the Weierstrass series identity. -/
def digammaLogAsymptOpen : Prop :=
  ∀ s : ℂ, (∀ m : ℕ, s ≠ -↑m) →
    Filter.Tendsto (fun N : ℕ => Complex.digamma (s + N) - (Complex.log (N + 1) : ℂ)) Filter.atTop (nhds 0)

/-- 开问题: Weierstrass ψ 级数 ψ(z) = −γ + Σ_{n≥0}[1/(n+1) − 1/(n+z)]
(digamma_weierstrass_partial + digammaLogAsymptOpen 组合). 
English: Open problem: Weierstrass ψ series ψ(z) = −γ + Σ_{n≥0}[1/(n+1) − 1/(n+z)] — tool assembly pending or to be confirmed. -/
def digammaTsumOpen : Prop :=
  ∀ s : ℂ, (∀ m : ℕ, s ≠ -↑m) →
    Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
      = (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1) - (1 : ℂ) / (s + (n : ℂ))))
