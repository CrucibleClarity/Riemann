import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# 相位对齐位置刻画 (iso 44)

奇偶拆分的公共零点 = ζ 零点 (iso 42); 相位对齐量 u² = χ (u = ζ/|ζ|) 的
非平凡解位置 = 本文件对象.

定义: χ(s) := ζ(s)/ζ(1−s) (函数方程因子, 分母非零处);
      相位对齐: ζ(s) = χ(s)·conj(ζ(s)).

结构 (机器验证):
  1. 相位对齐 ⟺ ζ(1−s) = conj(ζ(s))        (等值反射条件, 代数化简)
  2. 相位对齐 ⟹ ‖χ(s)‖ = 1                  (必要条件: 单位模)
  3. 临界线 ⟺ s = 1 − conj s                 (复合反射不动点, 几何)
  4. 临界线 ⟹ 相位对齐                        (对齐的充分位置, 已知方向)
  5. ζ 零点 ⟹ 相位对齐 (平凡解, 任意位置)     (零点 = 相位奇点, 方程平凡真)

开问题 (数值支持, 未证): 非平凡相位对齐解 ⊆ 临界线 —
即 ζ(1−s) = ζ(conj s) 无非临界线解 (ζ 等值线结构, 深层).

## 用户指示记录 (2026-08-22): 单调性的 pat 视角

用户讨论原话 (节选):
  "单调性在pat视角下是什么？周期圆的递增？相位累计？对称计数单调增长？
   导数恒正（相当于离散连续桥的基础上做阶差恒为正的分析，只停留在圆的正侧？）"
  "积分定号是啥意思，这玩意本质上也是离散连续桥吧，积分就是连续？"

指示内容 (pat/谱系视角):
  ① 单调性 = 对称计数: R(β) = ln‖Γ(1−s)/Γ(s)‖ 是反射配对 Γ(s)Γ(1−s)
     两侧模的不平衡 — β = 1/2 处 R = 0 (完全对称), 离开对称轴单调破缺
  ② 导数恒正 = 离散连续桥的阶差分析: 阶差 R(β+Δ) − R(β) < 0 (离散)
     ↔ R'(β) < 0 (连续桥) — 桥的连续侧
  ③ 积分定号本质 = 桥的连续侧 (积分 = 离散求和的连续极限) — 无桥外之物;
     定号的友好仅在"被积函数恒正"时 (符号 = 2 值计数 = 计数层投影),
     变号/振荡时回到连续估计
  ④ 只停留圆的正侧: R 是 t 的偶函数 (共轭对称) — 只需 t ≥ 0 半平面

digamma 反射公式的结构 (用户视角的产物):
  ψ(1−z) − ψ(z) = π·cot(πz) — 差是纯圆函数 (谱系内)
  R'(β) = −[Re ψ(s) + Re ψ(1−s)] = −[2Re ψ(s) + π·Re(cot(πs))]
  圆项显式: Re(cot(πβ+iπt)) = sin(2πβ)/(cosh(2πt) − cos(2πβ)) (分母 > 0, t ≠ 0)
  — 单调性 = 圆项 (显式) + 单点 ψ 实部 (连续层估计)

数值观察 (2026-08-22, 定性, **未证** — 仅扫描记录, 非定理):
  ① log|χ| 的 β 单调性全 t 域成立; 方向翻转于 t = 2π:
     t < 2π 递增, t > 2π 递减, t = 2π 退化 (整线等模渐近) — 斜率 = −ln(t/2π)
  ② 三项符号: 项1 (2β−1)ln2π 增, tan 项 增 (小 t)/0 (大 t), R 减 — 联合定号
  ③ 等模点每 t 恰一个 β = 1/2 (含小 t 区域, t = 0.2..3.0 扫描)
  ④ 教训: digamma 渐近级数在 Im 小时不可靠 (实轴极点方向), 直接 R 差分可靠

本文件: 隔离 (Mathlib only), 零洞。

English: phase-alignment position (iso 44): alignment iff ζ(1-s)=conj ζ(s); critical line as the fixed locus of the composite reflection -/

noncomputable section

namespace PhaseAlign

open scoped ComplexConjugate

/-- 函数方程因子: χ(s) = ζ(s)/ζ(1−s) (ζ(1−s) ≠ 0 处). 
English: Functional equation factor: χ(s) = ζ(s)/ζ(1−s) (where ζ(1−s) ≠ 0). -/
def chi (s : ℂ) : ℂ := riemannZeta s / riemannZeta (1 - s)

/-- 相位对齐: ζ(s) = χ(s)·conj(ζ(s)) (u² = χ 的代数形式, ζ(s) ≠ 0 处等价). 
English: Phase alignment: ζ(s) = χ(s)·conj(ζ(s)) (algebraic form u² = χ; equivalent where ζ(s) ≠ 0). -/
def phaseAlign (s : ℂ) : Prop := riemannZeta s = chi s * conj (riemannZeta s)

/-- 相位对齐 ⟺ 等值反射条件 ζ(1−s) = conj(ζ(s)) (ζ(s), ζ(1−s) 非零处). 
English: Phase alignment ⟺ equal-value reflection condition ζ(1−s) = conj(ζ(s)) (where ζ(s), ζ(1−s) ≠ 0). -/
theorem phaseAlign_iff_zeta_reflect {s : ℂ} (hz : riemannZeta s ≠ 0)
    (hz1 : riemannZeta (1 - s) ≠ 0) :
    phaseAlign s ↔ riemannZeta (1 - s) = conj (riemannZeta s) := by
  constructor
  · intro h
    have h' := congrArg (fun z : ℂ => z * riemannZeta (1 - s)) h
    -- ζ(s)·ζ(1−s) = (ζ(s)/ζ(1−s))·conj(ζ(s))·ζ(1−s)
    rw [chi] at h'
    field_simp [hz1] at h'
    -- field_simp 已约简: ζ(1−s) = conj(ζ(s))
    exact h'
  · intro h
    -- χ(s)·conj(ζ(s)) = (ζ(s)/ζ(1−s))·ζ(1−s) = ζ(s)
    rw [phaseAlign, chi]
    rw [← h]
    exact (div_mul_cancel₀ _ hz1).symm

/-- 必要条件: 相位对齐 ⟹ |χ(s)| = 1 (单位模, 在 ζ(s), ζ(1−s) 非零处). 
English: Necessary condition: phase alignment ⟹ |χ(s)| = 1 (unit modulus, where ζ(s), ζ(1−s) ≠ 0). -/
theorem phaseAlign_imp_unit_modulus {s : ℂ} (h : phaseAlign s) (hz : riemannZeta s ≠ 0)
    (hz1 : riemannZeta (1 - s) ≠ 0) : ‖chi s‖ = 1 := by
  have hr : riemannZeta (1 - s) = conj (riemannZeta s) :=
    (phaseAlign_iff_zeta_reflect hz hz1).mp h
  have hm : ‖riemannZeta (1 - s)‖ = ‖riemannZeta s‖ := by
    rw [hr]
    exact norm_star (riemannZeta s)
  rw [chi, norm_div, hm]
  exact div_self (norm_ne_zero_iff.mpr hz)

/-- 临界线 = 复合反射不动点: s = 1 − conj s ⟺ re s = 1/2. 
English: Critical line = fixed point of the composite reflection: s = 1 − conj s ⟺ re s = 1/2. -/
theorem critical_line_iff_reflect_fixed (s : ℂ) : (s = 1 - conj s) ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    -- re (1 − conj s) = 1 − re s
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    linarith
  · intro h
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
      rw [h]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      norm_num

/-- 临界线 ⟹ 相位对齐 (对齐的充分位置; 用 riemannZeta_conj 共轭对称). 
English: Critical line ⟹ phase alignment (sufficient position for alignment; uses riemannZeta_conj conjugate symmetry). -/
theorem phaseAlign_of_critical_line {s : ℂ} (hs : s.re = 1 / 2) (hz : riemannZeta s ≠ 0)
    (hz1 : riemannZeta (1 - s) ≠ 0) : phaseAlign s := by
  have h1s : 1 - s = conj s := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
      rw [hs]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      norm_num
  have hr : riemannZeta (1 - s) = conj (riemannZeta s) := by
    rw [h1s, riemannZeta_conj]
  exact (phaseAlign_iff_zeta_reflect hz hz1).mpr hr

/-- ζ 零点是相位对齐的平凡解 (任意位置): 零点 = 相位奇点, 方程平凡真.
    这钉死: 相位对齐方程不排除离线零点 (诚实边界). 
English: ζ zeros are trivial phase-alignment solutions (any position): zero = phase singularity, equation trivially true. This pins down: the phase alignment equation does not rule out off-line zeros (honest boundary). -/
theorem zeta_zero_phaseAlign {s : ℂ} (hz : riemannZeta s = 0) : phaseAlign s := by
  rw [phaseAlign, chi, hz, zero_div, zero_mul]

/-- 模对齐: |χ(s)| = 1 ⟺ 反射配对等模 |ζ(s)| = |ζ(1−s)| (ζ(1−s) ≠ 0 处).
    只涉 χ, 不涉 ζ 的相位. 
English: Modulus alignment: |χ(s)| = 1 ⟺ reflection pair equimodular |ζ(s)| = |ζ(1−s)| (where ζ(1−s) ≠ 0). Involves only χ, not the phase of ζ. -/
theorem chi_unit_modulus_iff_equimod {s : ℂ} (hz1 : riemannZeta (1 - s) ≠ 0) :
    ‖chi s‖ = 1 ↔ ‖riemannZeta s‖ = ‖riemannZeta (1 - s)‖ := by
  rw [chi, norm_div]
  exact div_eq_one_iff_eq (norm_ne_zero_iff.mpr hz1)

/-- ★ 相位对齐分解: 对齐 = 等模 (|χ|=1) ∧ 相位抵消 (ζ(s)·ζ(1−s) ∈ ℝ_{>0}).
    "拆开做分析"的精确形式: 模条件只涉 χ; 相位条件 = 反射配对乘积实正. 
English: Phase alignment decomposition: alignment = equimodular (|χ|=1) ∧ phase cancellation (ζ(s)·ζ(1−s) ∈ ℝ_{>0}). Exact form of 'separate and analyze': the modulus condition involves only χ; the phase condition = reflection pair product real positive. -/
theorem phaseAlign_iff_equimod_and_cancel {s : ℂ} (hz : riemannZeta s ≠ 0)
    (hz1 : riemannZeta (1 - s) ≠ 0) :
    phaseAlign s ↔ ‖riemannZeta s‖ = ‖riemannZeta (1 - s)‖ ∧
      ∃ r : ℝ, 0 < r ∧ riemannZeta s * riemannZeta (1 - s) = (r : ℂ) := by
  constructor
  · intro h
    have hr : riemannZeta (1 - s) = conj (riemannZeta s) :=
      (phaseAlign_iff_zeta_reflect hz hz1).mp h
    constructor
    · rw [hr]
      exact (norm_star (riemannZeta s)).symm
    · rw [hr]
      refine ⟨‖riemannZeta s‖ ^ 2, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz), ?_⟩
      -- ζ(s)·conj(ζ(s)) = ‖ζ(s)‖²  (normSq 桥)
      rw [mul_comm]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  · rintro ⟨hm, r, hrpos, hprod⟩
    -- 从乘积: ζ(1−s) = r/ζ(s)
    have hw : riemannZeta (1 - s) = (r : ℂ) / riemannZeta s := by
      field_simp [hz] at hprod ⊢
      exact hprod
    -- r = ‖ζ(s)‖²: |r| = |z|·|w| = |z|² (等模)
    have hrab : ‖(r : ℂ)‖ = ‖riemannZeta s‖ ^ 2 := by
      rw [← hprod, norm_mul]
      rw [hm]
      ring_nf
    have hr_eq : (r : ℂ) = ‖riemannZeta s‖ ^ 2 := by
      rw [← Complex.ofReal_pow]
      exact congrArg Complex.ofReal (by
        rw [← hrab]
        exact ((RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_pos hrpos)).symm)
    -- ‖z‖² = z·conj(z) (normSq 桥)
    have hnorm : (‖riemannZeta s‖ : ℂ) ^ 2 = riemannZeta s * conj (riemannZeta s) := by
      rw [← Complex.ofReal_pow]
      rw [← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_eq_conj_mul_self]
      rw [mul_comm]
    -- 走反射等价: 等模 + 实正 ⟹ ζ(1−s) = conj(ζ(s))
    apply (phaseAlign_iff_zeta_reflect hz hz1).mpr
    rw [hw, hr_eq, hnorm]
    field_simp [hz]

/-- 已证方向组装: 临界线 (临界带内) ⟹ 相位对齐. 
English: Assembling the proved direction: critical line (within the strip) ⟹ phase alignment. -/
theorem phaseAlign_of_critical_line_in_strip {s : ℂ} (_hs : 0 < s.re ∧ s.re < 1)
    (hs' : s.re = 1 / 2) (hz : riemannZeta s ≠ 0) (hz1 : riemannZeta (1 - s) ≠ 0) :
    phaseAlign s :=
  phaseAlign_of_critical_line hs' hz hz1

/-! ## 开问题 (数值支持, 未证) — "相位对齐位置 = 临界线" 的 ⟹ 方向

目标等价定理形态 (数值全支持, 机器验证只差 ⟹ 方向):

    phaseAlign s ↔ s.re = 1 / 2     (临界带内, 非平凡)

数值证据 (2026-08-22, 定性观察非证明):
  1. 对齐残差 f = ζ − χ·conj(ζ) 的极小点 128/128 全在临界线 (T ≤ 30 粗扫)
  2. 分解结构: 对齐 ⟺ 等模 ∧ 相位抵消 (本文件机器验证);
     等模 |χ| = 1 的数值解 = 临界线 ∪ 退化线 t = 2π (log|χ| ≈ (0.5−β)·ln(t/2π),
     Stirling 渐近, 大 t 精度 1e-5);
     退化线 t = 2π 上相位抵消失败 (Im(ζζ(1−s)) ≠ 0 于 β ≠ 1/2, 关于 β = 1/2 反对称)

两级缺口:
  A. 等模解集 (纯 χ, 不涉 ζ): log|χ(β+it)| = 0 ⟹ β = 1/2 ∨ t = 2π — 未证
  B. 退化线相位 (涉 ζ 相位, 深层): t = 2π 线上 arg χ(s) ≠ −2·arg ζ(s) — 未证
-/

/-- 开问题 (⟹ 方向): 临界带内非平凡相位对齐位置 ⊆ 临界线.
    等价于: ζ(1−s) = ζ(conj s) 在临界带内无非平凡解. 
English: Open problem (⟹ direction): nontrivial phase alignment positions in the strip ⊆ critical line. Equivalent: ζ(1−s) = ζ(conj s) has no nontrivial solution in the strip. -/
def phaseAlignPositionsOpen : Prop :=
  ∀ s : ℂ, (0 < s.re ∧ s.re < 1) → riemannZeta s ≠ 0 → riemannZeta (1 - s) ≠ 0 →
    phaseAlign s → s.re = 1 / 2

/-- 开问题 A (纯 χ): 等模解集 = 临界线 ∪ 退化线 t = 2π. 
English: Open problem A (pure χ): equimodular solution set = critical line ∪ degenerate line t = 2π. -/
def equimodPositionsOpen : Prop :=
  ∀ s : ℂ, (0 < s.re ∧ s.re < 1) → ‖riemannZeta s‖ = ‖riemannZeta (1 - s)‖ →
    s.re = 1 / 2 ∨ s.im = 2 * Real.pi

/-- 组合链 (机器验证): 开问题 ⟸ 开问题 A ∧ 开问题 B (退化线相位排除).
    即: 若等模位置 ⊆ {临界线 ∪ t=2π} 且 t=2π 上非平凡相位对齐不存在,
    则 phaseAlignPositionsOpen 成立. 
English: Composition chain (machine-verified): open problem ⟸ open problem A ∧ open problem B (degenerate-line phase exclusion), i.e., equimodular positions ⊆ {critical line ∪ t=2π} and no nontrivial phase alignment on t=2π ⟹ phaseAlignPositionsOpen. -/
theorem open_problem_chain (hA : equimodPositionsOpen)
    (hB : ∀ s : ℂ, (0 < s.re ∧ s.re < 1) → s.im = 2 * Real.pi →
      riemannZeta s ≠ 0 → riemannZeta (1 - s) ≠ 0 → ¬ phaseAlign s) :
    phaseAlignPositionsOpen := by
  intro s hs hz hz1 hpa
  -- 对齐 ⟹ 等模 (分解): |ζ(s)| = |ζ(1−s)|
  have hm : ‖riemannZeta s‖ = ‖riemannZeta (1 - s)‖ :=
    (phaseAlign_iff_equimod_and_cancel hz hz1).mp hpa |>.1
  -- 等模 ⟹ β = 1/2 或 t = 2π (开问题 A)
  rcases hA s hs hm with h_line | h_degen
  · exact h_line
  -- 退化线 t = 2π: 开问题 B 排除 (相位对齐不成立)
  · exact False.elim (hB s hs h_degen hz hz1 hpa)

/-- ★ 退化线 = e 基点的实相位线: t = 2π 上 e^{−s} = e^{−β} ∈ ℝ₊ (纯实, 无相位).
    B 缺口 (退化线相位) 深转浅的支点: e 拆分因子在退化线上全实,
    相位由 O₂ 单独承载. 
English: Degenerate line = real phase line of basepoint e: on t = 2π, e^{−s} = e^{−β} ∈ ℝ₊ (pure real, no phase). Pivot for gap B: e split factors all real, phase carried by O₂ alone. -/
theorem exp_neg_real_on_2pi_line {s : ℂ} (hs : s.im = 2 * Real.pi) :
    Complex.exp (-s) = (Real.exp (-s.re) : ℂ) := by
  -- exp 周期: −s = −s.re + (−1)·2πi  (exp 周期 2πi), 再经 ofReal_exp 转实数
  have hper : Complex.exp (-s) = Complex.exp (-(s.re : ℂ)) := by
    apply (Complex.exp_eq_exp_iff_exists_int (x := -s) (y := (-(s.re : ℂ)))).mpr
    refine ⟨-1, ?_⟩
    apply Complex.ext
    · norm_num [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    · norm_num [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hs]
  rw [hper]
  rw [show (-(s.re : ℂ)) = ((-s.re : ℝ) : ℂ) by norm_num]
  exact (Complex.ofReal_exp (-s.re)).symm

/-- 退化线上 e 因子为正实数: 0 < e^{−β}. 
English: The e factor on the degenerate line is a positive real: 0 < e^{−β}. -/
theorem exp_neg_pos_on_2pi_line {s : ℂ} (hs : s.im = 2 * Real.pi) :
    ∃ r : ℝ, 0 < r ∧ Complex.exp (-s) = (r : ℂ) := by
  refine ⟨Real.exp (-s.re), Real.exp_pos _, ?_⟩
  exact exp_neg_real_on_2pi_line hs

/-- 显式 χ (函数方程因子, 不涉 ζ): χE(s) = 2ˢ·π^{s−1}·sin(πs/2)·Γ(1−s). 
English: Explicit χ (functional equation factor, no ζ): χE(s) = 2ˢ·π^{s−1}·sin(πs/2)·Γ(1−s). -/
def chiExplicit (s : ℂ) : ℂ :=
  (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.sin (Real.pi * s / 2) * Complex.Gamma (1 - s)

/-- 正实底 cpow 的模: ‖(x:ℂ)^s‖ = x^{re s} (x > 0). 
English: Modulus of cpow with positive real base: ‖(x:ℂ)^s‖ = x^{re s} (x > 0). -/
theorem norm_cpow_ofReal_pos (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ‖(x : ℂ) ^ s‖ = x ^ s.re := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos hx s

/-- sin(πs) = 2·sin(πs/2)·cos(πs/2) (倍角). 
English: sin(πs) = 2·sin(πs/2)·cos(πs/2) (double angle). -/
theorem sin_pi_double (s : ℂ) :
    Complex.sin (Real.pi * s)
      = 2 * Complex.sin (Real.pi * s / 2) * Complex.cos (Real.pi * s / 2) := by
  rw [← Complex.sin_two_mul]
  congr 1
  ring

/-- Γ 反射的模: ‖Γ(s)‖·‖Γ(1−s)‖ = π/(2·‖sin(πs/2)‖·‖cos(πs/2)‖). 
English: Modulus of Γ reflection: ‖Γ(s)‖·‖Γ(1−s)‖ = π/(2·‖sin(πs/2)‖·‖cos(πs/2)‖). -/
theorem norm_Gamma_reflect (s : ℂ) (hsin : Complex.sin (Real.pi * s / 2) ≠ 0)
    (hcos : Complex.cos (Real.pi * s / 2) ≠ 0) :
    ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖
      = (Real.pi : ℝ)
        / (2 * ‖Complex.sin (Real.pi * s / 2)‖ * ‖Complex.cos (Real.pi * s / 2)‖) := by
  have hc := congrArg (fun z : ℂ => ‖z‖) (Complex.Gamma_mul_Gamma_one_sub s)
  rw [norm_mul] at hc
  rw [sin_pi_double s] at hc
  rw [norm_div, norm_mul, norm_mul] at hc
  have hsn : ‖Complex.sin (Real.pi * s / 2)‖ ≠ 0 := norm_ne_zero_iff.mpr hsin
  have hcn : ‖Complex.cos (Real.pi * s / 2)‖ ≠ 0 := norm_ne_zero_iff.mpr hcos
  rw [show ‖(Real.pi : ℂ)‖ = Real.pi by exact (RCLike.norm_ofReal Real.pi).trans (abs_of_pos Real.pi_pos)] at hc
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at hc
  exact hc

/-- ★ 三项分解 (对称恢复): ‖χE(s)‖² = (2π)^{2β−1}·(‖sin‖/‖cos‖)·(‖Γ(1−s)‖/‖Γ(s)‖). 
English: Three-term decomposition (symmetric recovery): ‖χE(s)‖² = (2π)^{2β−1}·(‖sin‖/‖cos‖)·(‖Γ(1−s)‖/‖Γ(s)‖). -/
theorem chiExplicit_norm_sq_symm (s : ℂ) (hΓ : Complex.Gamma s ≠ 0)
    (hΓ1 : Complex.Gamma (1 - s) ≠ 0)
    (hsin : Complex.sin (Real.pi * s / 2) ≠ 0) (hcos : Complex.cos (Real.pi * s / 2) ≠ 0) :
    ‖chiExplicit s‖ ^ 2 = (2 * Real.pi) ^ (2 * s.re - 1)
      * (‖Complex.sin (Real.pi * s / 2)‖ / ‖Complex.cos (Real.pi * s / 2)‖)
      * (‖Complex.Gamma (1 - s)‖ / ‖Complex.Gamma s‖) := by
  -- 欧拉圆结构: 全因子为模 (‖·‖), 组合进 (2π)^{2β−1}
  rw [chiExplicit]
  repeat rw [norm_mul]
  rw [show ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ s.re by
    exact norm_cpow_ofReal_pos (2 : ℝ) (by norm_num : (0 : ℝ) < 2) s]
  rw [show ‖(Real.pi : ℂ) ^ (s - 1)‖ = (Real.pi : ℝ) ^ (s - 1).re by
    exact norm_cpow_ofReal_pos (Real.pi : ℝ) Real.pi_pos (s - 1)]
  rw [Complex.sub_re, Complex.one_re]
  rw [mul_pow, mul_pow, mul_pow]
  -- 幂的幂合并: (2^β)^2 = 2^{2β}, (π^{β−1})^2 = π^{2β−2}
  have h2sq : (2 : ℝ) ^ (2 * s.re) = ((2 : ℝ) ^ s.re) ^ 2 := by
    calc
      (2 : ℝ) ^ (2 * s.re) = (2 : ℝ) ^ (s.re * 2) := by congr 1; ring
      _ = ((2 : ℝ) ^ s.re) ^ (2 : ℝ) :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) s.re (2 : ℝ)
      _ = ((2 : ℝ) ^ s.re) ^ 2 := by exact (Real.rpow_natCast ((2 : ℝ) ^ s.re) 2)
  have hπsq : (Real.pi : ℝ) ^ (2 * s.re - 2) = ((Real.pi : ℝ) ^ (s.re - 1)) ^ 2 := by
    calc
      (Real.pi : ℝ) ^ (2 * s.re - 2) = (Real.pi : ℝ) ^ ((s.re - 1) * 2) := by congr 1; ring
      _ = ((Real.pi : ℝ) ^ (s.re - 1)) ^ (2 : ℝ) :=
        Real.rpow_mul Real.pi_pos.le (s.re - 1) (2 : ℝ)
      _ = ((Real.pi : ℝ) ^ (s.re - 1)) ^ 2 := by
        exact (Real.rpow_natCast ((Real.pi : ℝ) ^ (s.re - 1)) 2)
  rw [← h2sq, ← hπsq]
  -- 拆 (2π)^{2β−1} = 2^{2β−1}·π^{2β−1}
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le]
  -- 交叉乘消分母 (模非零)
  have hsn : ‖Complex.sin (Real.pi * s / 2)‖ ≠ 0 := norm_ne_zero_iff.mpr hsin
  have hcn : ‖Complex.cos (Real.pi * s / 2)‖ ≠ 0 := norm_ne_zero_iff.mpr hcos
  have hΓn : ‖Complex.Gamma s‖ ≠ 0 := norm_ne_zero_iff.mpr hΓ
  have hΓ1n : ‖Complex.Gamma (1 - s)‖ ≠ 0 := norm_ne_zero_iff.mpr hΓ1
  field_simp [hsn, hcn, hΓn, hΓ1n]
  -- 指数合并: 2^{2β} = 2^{2β−1}·2; π^{2β−2} = π^{2β−1}·π^{−1}
  have h2e : (2 : ℝ) ^ (2 * s.re) = (2 : ℝ) ^ (2 * s.re - 1) * 2 := by
    calc
      (2 : ℝ) ^ (2 * s.re) = (2 : ℝ) ^ (2 * s.re - 1 + 1) := by congr 1; ring
      _ = (2 : ℝ) ^ (2 * s.re - 1) * (2 : ℝ) ^ 1 :=
        Real.rpow_add (by norm_num : (0 : ℝ) < 2) (2 * s.re - 1) 1
      _ = (2 : ℝ) ^ (2 * s.re - 1) * 2 := by rw [Real.rpow_one]
  have hπe : (Real.pi : ℝ) ^ (2 * (s.re - 1)) =
      (Real.pi : ℝ) ^ (2 * s.re - 1) * (Real.pi : ℝ) ^ (-1 : ℝ) := by
    calc
      (Real.pi : ℝ) ^ (2 * (s.re - 1)) = (Real.pi : ℝ) ^ (2 * s.re - 1 + (-1 : ℝ)) := by congr 1; ring
      _ = (Real.pi : ℝ) ^ (2 * s.re - 1) * (Real.pi : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_add Real.pi_pos (2 * s.re - 1) (-1 : ℝ)
  rw [h2e, hπe]
  have h2 : (2 : ℝ) ^ (2 * s.re - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * s.re - 1))
  have hπ : (Real.pi : ℝ) ^ (2 * s.re - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos (2 * s.re - 1))
  field_simp [h2, hπ]
  -- 目标: 2·π^{−1}·‖sin‖·‖Γ(1−s)‖·‖cos‖·‖Γ(s)‖ = 1 — Γ 反射代入
  have href := norm_Gamma_reflect s hsin hcos
  calc
    2 * Real.pi ^ (-1 : ℝ) * ‖Complex.sin (Real.pi * s / 2)‖ * ‖Complex.Gamma (1 - s)‖
        * ‖Complex.cos (Real.pi * s / 2)‖ * ‖Complex.Gamma s‖
        = 2 * Real.pi ^ (-1 : ℝ) * ‖Complex.sin (Real.pi * s / 2)‖ * ‖Complex.cos (Real.pi * s / 2)‖
          * (‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖) := by ring
    _ = 2 * Real.pi ^ (-1 : ℝ) * ‖Complex.sin (Real.pi * s / 2)‖ * ‖Complex.cos (Real.pi * s / 2)‖
          * ((Real.pi : ℝ) / (2 * ‖Complex.sin (Real.pi * s / 2)‖ * ‖Complex.cos (Real.pi * s / 2)‖)) := by
            rw [href]
    _ = 1 := by
          rw [Real.rpow_neg_one (Real.pi : ℝ)]
          field_simp [hsn, hcn]

theorem log_chiExplicit_symm (s : ℂ) (hΓ : Complex.Gamma s ≠ 0) (hΓ1 : Complex.Gamma (1 - s) ≠ 0)
    (hsin : Complex.sin (Real.pi * s / 2) ≠ 0) (hcos : Complex.cos (Real.pi * s / 2) ≠ 0) :
    2 * Real.log ‖chiExplicit s‖ = (2 * s.re - 1) * Real.log (2 * Real.pi)
      + Real.log ‖Complex.sin (Real.pi * s / 2)‖ - Real.log ‖Complex.cos (Real.pi * s / 2)‖
      + Real.log ‖Complex.Gamma (1 - s)‖ - Real.log ‖Complex.Gamma s‖ := by
  have hpos : 0 < ‖chiExplicit s‖ := by
    have hsq := chiExplicit_norm_sq_symm s hΓ hΓ1 hsin hcos
    have hp : 0 < ‖chiExplicit s‖ ^ 2 := by
      rw [hsq]
      positivity
    exact lt_of_le_of_ne (norm_nonneg _) (sq_pos_iff.mp hp).symm
  have hlp : 2 * Real.log ‖chiExplicit s‖ = Real.log (‖chiExplicit s‖ ^ 2) := by
    exact (Real.log_pow ‖chiExplicit s‖ 2).symm
  rw [hlp]
  rw [chiExplicit_norm_sq_symm s hΓ hΓ1 hsin hcos]
  rw [Real.log_mul]
  rw [Real.log_mul]
  rw [Real.log_div]
  rw [Real.log_div]
  rw [Real.log_rpow (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]
  ring
  · exact norm_ne_zero_iff.mpr hΓ1
  · exact norm_ne_zero_iff.mpr hΓ
  · exact norm_ne_zero_iff.mpr hsin
  · exact norm_ne_zero_iff.mpr hcos
  · exact ne_of_gt (Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) _)
  · exact div_ne_zero (norm_ne_zero_iff.mpr hsin) (norm_ne_zero_iff.mpr hcos)
  · exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos
      (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) _))
      (div_ne_zero (norm_ne_zero_iff.mpr hsin) (norm_ne_zero_iff.mpr hcos))
  · exact div_ne_zero (norm_ne_zero_iff.mpr hΓ1) (norm_ne_zero_iff.mpr hΓ)

end PhaseAlign
