import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# 离线 ρ 的 T 坐标一阶重述 (断点 C 组装骨架, 2026-08-26)

用户路径 (2026-08-26): "精确移动到复平面假实轴的 1/2 (i^{1/(2i)} = e^{π/4}
位置), 然后进行奇偶拆分后观测, 就能完成离线矛盾证明。"

本文件 = 该路径的**机证骨架**: 把离线 ρ (ζ(ρ)=0, 带内, Re ρ ≠ 1/2) 投影到
T 坐标 (基点精确移动, PreciseMigration 族) 的一阶判定 + 奇偶结构:

- **降阶 (位置 → 模)**: T(z) = 1/(z−i) − 1, 三档判定 (PreciseMigration
  已机证): |T(z)|² = 1 ⟺ Re z = 1/2 (临界线 ⟺ 单位圆), < 1 ⟺ Re > 1/2
  (左半带 ⟺ 圆内), > 1 ⟺ Re < 1/2 (右半带 ⟺ 圆外);
  T_normSq_diff: ‖z−1−i‖² − ‖z−i‖² = 1 − 2·Re z — "Re z vs 1/2" 的判定
  降为一阶量 "1 − 2·Re z vs 0"。
- **奇偶观测**: 离线 ρ 是奇偶公共零点 (O₂ = E₂ = 0, 等价链已机证),
  差结构 (2ᵖ−1) ≠ 0 (相位差显式, OddEvenPhaseDiff 已机证)。
- **骨架结论 (本文件机证)**: 离线 ρ ⟹ |T(ρ)|² ≠ 1 ∧ (1−2·Re ρ) ≠ 0 ∧
  O₂(ρ)=0 ∧ E₂(ρ)=0 ∧ 2ᵖ ≠ 1 — 全部分量相容, 无一被违背;
  断点 C 的矛盾量 (哪个一阶量在 ρ 处违背全局事实) 仍未给出 — 本骨架
  标出精确位置: "奇偶拆分后观测" 的观测量需要是圆内/圆外零点违背的
  全局事实 (当前无零区/轨道配对/翻转计数均与圆内零点相容)。

English: T-coordinate first-order restatement of an off-line zero ρ — the
machine-verified skeleton of the user's contradiction path: basepoint
exact migration (T = 1/(z−i)−1, three-tier criterion) reduces the
position predicate (Re z vs 1/2) to a first-order quantity (1−2·Re z vs 0);
the odd-even split gives common zeros plus the explicit difference
structure. All components are consistent; the contradiction quantity
(which first-order fact an off-line zero violates) remains the open step.
-/

noncomputable section

open Complex
open scoped Topology

namespace ZeroRelative

/-! ## 1. 基点精确移动 (T 算子, PreciseMigration 核) -/

/-- 精确移动算子: 压缩 (recip, 中心 = 基点 i) + 平移 (−1, 结构值)。
    Exact migration operator: compression (recip, center = basepoint i)
    + translation (−1, structural value). -/
def T (z : ℂ) : ℂ := 1 / (z - Complex.I) - 1

/-- 距离平方差 = 一阶位置谓词: ‖z−1−i‖² − ‖z−i‖² = 1 − 2·Re z —
    "Re z vs 1/2" 的判定 ⟺ 一阶量 "1 − 2·Re z vs 0" (降阶核).
    Squared-distance difference = first-order position predicate. -/
lemma T_normSq_diff (z : ℂ) :
    Complex.normSq (z - 1 - Complex.I) - Complex.normSq (z - Complex.I) = 1 - 2 * z.re := by
  rw [Complex.normSq_apply, Complex.normSq_apply]
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_im, Complex.sub_im]
  simp
  ring

/-- 三档判定 (等): |T(z)|² = 1 ⟺ Re z = 1/2 — 临界线 ⟺ 单位圆 (一阶判定). -/
theorem T_normSq_eq_one_iff (z : ℂ) (hz : z ≠ Complex.I) :
    Complex.normSq (T z) = 1 ↔ z.re = 1 / 2 := by
  have hz' : z - Complex.I ≠ 0 := sub_ne_zero.mpr hz
  have hd : Complex.normSq (z - Complex.I) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hz')
  calc
    Complex.normSq (T z) = 1
        ↔ Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) = 1 := by
          rw [show Complex.normSq (T z) =
                Complex.normSq (z - 1 - Complex.I) / Complex.normSq (z - Complex.I) by
            rw [T]
            rw [← div_sub_same hz']
            rw [Complex.normSq_div]
            have hEq : 1 - (z - Complex.I) = -(z - 1 - Complex.I) := by ring
            rw [hEq, Complex.normSq_neg]]
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

/-- **离线 ⟹ 模判定**: Re ρ ≠ 1/2 ⟹ |T(ρ)|² ≠ 1 (带内离线零点在单位圆内/外,
    临界线 = 单位圆 — 位置谓词 → 模谓词, 一阶). -/
theorem offline_T_normSq_ne_one {ρ : ℂ} (hρ0 : 0 < ρ.re) (href : ρ.re ≠ 1 / 2) :
    Complex.normSq (T ρ) ≠ 1 := by
  have hne : ρ ≠ Complex.I := by
    intro h
    have : ρ.re = 0 := by rw [h]; simp
    linarith
  intro h
  exact href ((T_normSq_eq_one_iff ρ hne).mp h)

/-- **离线 ⟹ 一阶位置差非零**: Re ρ ≠ 1/2 ⟹ ‖ρ−1−i‖² − ‖ρ−i‖² ≠ 0
    (降阶核: 位置判定 = 一阶量 1 − 2·Re ρ 与 0 的比较). -/
theorem offline_position_diff_ne_zero {ρ : ℂ} (href : ρ.re ≠ 1 / 2) :
    Complex.normSq (ρ - 1 - Complex.I) - Complex.normSq (ρ - Complex.I) ≠ 0 := by
  intro h
  have hd : 1 - 2 * ρ.re = 0 := by
    rw [← T_normSq_diff ρ]
    exact h
  have hre : ρ.re = 1 / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
    rw [mul_comm]
    exact (sub_eq_zero.mp hd).symm
  exact href hre

/-! ## 2. 奇偶拆分观测 (奇偶公共零点 + 差结构) -/

/-- 奇部 (基点 2): O₂(s) = (1 − 2⁻ˢ)·ζ(s). -/
def oddPart (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s

/-- 偶部 (基点 2): E₂(s) = 2⁻ˢ·ζ(s). -/
def evenPart (s : ℂ) : ℂ := (2 : ℂ) ^ (-s : ℂ) * riemannZeta s

/-- 带内 (0 < Re s) ⟹ 2⁻ˢ ≠ 1 (奇偶拆分在带内无额外零点). -/
theorem two_pow_neg_ne_one_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    (2 : ℂ) ^ (-s : ℂ) ≠ 1 := by
  intro h
  have hdef : (2 : ℂ) ^ (-s : ℂ) = Complex.exp (Complex.log (2 : ℂ) * (-s : ℂ)) := by
    exact Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (-s : ℂ)
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hexp : Complex.exp (Complex.log (2 : ℂ) * (-s : ℂ)) = 1 := by
    rwa [hdef] at h
  rw [hlog] at hexp
  rcases (Complex.exp_eq_exp_iff_exists_int
      (x := (Real.log 2 : ℂ) * (-s : ℂ)) (y := 0)).mp (by simpa using hexp) with ⟨k, hk⟩
  have hre : ((Real.log 2 : ℂ) * (-s : ℂ)).re =
      (0 + (k : ℂ) * (2 * Real.pi * Complex.I)).re := by
    rw [hk]
  have hleft : ((Real.log 2 : ℂ) * (-s : ℂ)).re = Real.log 2 * -s.re := by
    rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.neg_re]
    ring
  have hright : (0 + (k : ℂ) * (2 * Real.pi * Complex.I)).re = 0 := by
    simp
  have hre0 : Real.log 2 * -s.re = 0 := by
    rw [hleft, hright] at hre
    exact hre
  have hs0 : s.re = 0 := by
    have hl2 : Real.log 2 ≠ 0 := (Real.log_ne_zero).mpr (by norm_num)
    have hz : -s.re = 0 := (mul_eq_zero.mp hre0).resolve_left hl2
    linarith
  exact (ne_of_gt hs) hs0

/-- **离线零点 ⟹ 奇偶公共零点 + 差结构良好**: ζ(ρ)=0 (带内) ⟹
    O₂(ρ) = 0 ∧ E₂(ρ) = 0 ∧ 2ᵖ ≠ 1 — 奇偶拆分观测的完整结构
    (单提升在零点奇异, 差结构 (2ˢ−1) 处处良定义). -/
theorem offline_zero_odd_even {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) :
    oddPart ρ = 0 ∧ evenPart ρ = 0 ∧ (2 : ℂ) ^ ρ ≠ 1 := by
  have hne : (2 : ℂ) ^ (-ρ : ℂ) ≠ 1 := two_pow_neg_ne_one_of_re_pos hρ0
  constructor
  · unfold oddPart
    simp [hζ]
  · constructor
    · unfold evenPart
      simp [hζ]
    · intro h1
      have hneg : (2 : ℂ) ^ (-ρ : ℂ) = ((2 : ℂ) ^ ρ)⁻¹ := Complex.cpow_neg (2 : ℂ) ρ
      rw [h1] at hneg
      exact hne (by simpa using hneg)

/-! ## 3. 主骨架: 离线 ρ 的 T 坐标一阶重述 -/

/-- **★离线 ρ 的 T 坐标一阶重述** (断点 C 组装骨架): ζ(ρ)=0, 带内,
    Re ρ ≠ 1/2 ⟹
    ① |T(ρ)|² ≠ 1 (模判定: 圆内/圆外, 三档判定) ∧
    ② ‖ρ−1−i‖² − ‖ρ−i‖² ≠ 0 (一阶位置差, 降阶核) ∧
    ③ O₂(ρ) = 0 ∧ E₂(ρ) = 0 (奇偶公共零点) ∧ 2ᵖ ≠ 1 (差结构良好).
    **全部分量相容**: 无零区/轨道配对/翻转计数均与圆内零点相容 —
    矛盾量 (哪个一阶量在 ρ 处违背全局事实) 是断点 C 的开放步.
    ★T-coordinate first-order restatement of an off-line zero: modulus
    criterion + first-order position difference + odd-even common zeros
    + well-defined difference structure. All components are consistent;
    the contradiction quantity is the open step. -/
theorem offline_T_coord_skeleton (ρ : ℂ) (hζ : riemannZeta ρ = 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (href : ρ.re ≠ 1 / 2) :
    Complex.normSq (T ρ) ≠ 1 ∧
    Complex.normSq (ρ - 1 - Complex.I) - Complex.normSq (ρ - Complex.I) ≠ 0 ∧
    oddPart ρ = 0 ∧ evenPart ρ = 0 ∧ (2 : ℂ) ^ ρ ≠ 1 := by
  constructor
  · exact offline_T_normSq_ne_one hρ0 href
  · constructor
    · exact offline_position_diff_ne_zero href
    · rcases offline_zero_odd_even hζ hρ0 with ⟨hO, hE, h2⟩
      exact ⟨hO, hE, h2⟩


/-! ## 4. 矛盾量检查: "奇侧 1/2 外只有孤立零" ⟺ rh_oddeven -/

/-- rh_oddeven (奇偶公共零点只在 1/2) 的命题形式: 带内奇偶公共零点 ⟹ Re = 1/2. -/
def rh_oddeven : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → oddPart s = 0 → evenPart s = 0 → s.re = 1 / 2

/-- 奇侧 1/2 外零点都孤立 (独有): 带内 O₂ 零点在 1/2 外 ⟹ 非 ζ 零点
    (即: 1/2 外的奇侧零点只有独有零点 — 用户的"前提"). -/
def oddOnlyIsolatedOffHalf : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → oddPart s = 0 → s.re ≠ 1 / 2 → riemannZeta s ≠ 0

/-- **"奇侧 1/2 外只有孤立零" ⟺ rh_oddeven** (等价性机证):
    用户的矛盾前提 ⟺ 目标命题 (RH 的奇偶形式) — 前提即目标, 非已证事实.
    "Odd-side zeros off 1/2 are only isolated" ⟺ rh_oddeven: the
    contradiction premise is equivalent to the goal itself. -/
theorem rh_oddeven_iff_odd_only_isolated :
    rh_oddeven ↔ oddOnlyIsolatedOffHalf := by
  constructor
  · intro hrh
    intro s hs0 hs1 hO href hζ
    -- 反设 hζ : ζ(s) = 0 — 由偶部 2⁻ˢ·ζ = 0 得公共零点, rh_oddeven 给出 Re = 1/2 矛盾
    have hE : evenPart s = 0 := by
      unfold evenPart
      simp [hζ]
    exact href (hrh s hs0 hs1 hO hE)
  · intro hiso
    intro s hs0 hs1 hO hE
    by_contra href
    -- 公共零点 s (re ≠ 1/2) ⟹ ζ(s) = 0 (偶部非零因子)
    have hz : riemannZeta s = 0 := by
      unfold evenPart at hE
      have h2 : (2 : ℂ) ^ (-s : ℂ) ≠ 0 :=
        (Complex.cpow_ne_zero_iff).mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
      exact (mul_eq_zero.mp hE).resolve_left h2
    -- 奇侧 1/2 外零点 ⟹ 非 ζ 零点 (hiso) — 与 hz : ζ(s) = 0 矛盾
    exact (hiso s hs0 hs1 hO href) hz


/-! ## 5. 投影不可兼得: 保零点集 ⟺ 非零因子倍 (自指仍在) -/

/-- **保零点集的投影 = 非零因子倍**: 任何与 ζ 共享零点集的良定义函数
    Φ = g·ζ (g ≠ 0) — 零点判定 (自指) 原样保留, 没有丢失.
    Zero-set-preserving projections are exactly nonzero-factor multiples:
    the self-referential zero determination survives. -/
theorem zero_set_shared_nonzero_factor {s : ℂ} (g : ℂ) (hg : g ≠ 0) :
    (g * riemannZeta s = 0) ↔ riemannZeta s = 0 := by
  rw [mul_eq_zero]
  constructor
  · intro h
    exact h.resolve_left hg
  · intro hz
    exact Or.inr hz

/-- **丢自指的投影丢零点**: 相位差分子 (2ˢ−1) 带内 (0 < Re s) 无零点
    (2ˢ = 1 ⟹ 2⁻ˢ = 1 ⟹ Re s = 0) — 与 ζ 的零点集无关: 自指丢失,
    矛盾源同步丢失 (投影 = 显式函数, 不含 ρ 位置信息). -/
theorem phase_diff_numerator_no_zero_in_strip {s : ℂ} (hs : 0 < s.re) :
    (2 : ℂ) ^ s ≠ 1 := by
  intro h1
  have hne : (2 : ℂ) ^ (-s : ℂ) ≠ 1 := two_pow_neg_ne_one_of_re_pos hs
  have hneg : (2 : ℂ) ^ (-s : ℂ) = ((2 : ℂ) ^ s)⁻¹ := Complex.cpow_neg (2 : ℂ) s
  rw [h1] at hneg
  exact hne (by simpa using hneg)

/-! ## 6. 新轴构造: 临界线投影成点 + 奇侧因子周期震荡 (用户构造机证) -/

/-- **新正交坐标投影**: 新轴 (u, v) = (Re s − 1/2, Im s) 下, 临界线
    (Re s = 1/2) 投影成单点 u = 0 — 整条临界线在垂直方向 (u 轴) 塌缩为点. -/
theorem critical_line_projects_to_point (s : ℂ) (hre : s.re = 1 / 2) :
    s.re - 1 / 2 = 0 := by
  rw [hre]
  ring

/-- **奇侧因子周期震荡**: 2⁻ˢ 沿临界线方向 (虚部) 是周期函数,
    周期 = 2π/ln 2 — 2^{−(s + 2πi/ln2)} = 2^{−s}
    (奇侧 O₂ = (1−2⁻ˢ)·ζ 的因子部分在新轴视角下周期震荡). -/
theorem two_pow_neg_periodic (s : ℂ) :
    (2 : ℂ) ^ (-s + (-(2 * Real.pi / Real.log 2) * Complex.I)) = (2 : ℂ) ^ (-s) := by
  let z : ℂ := -(2 * Real.pi / Real.log 2) * Complex.I
  have hz : (2 : ℂ) ^ z = 1 := by
    have hdef : (2 : ℂ) ^ z = Complex.exp (Complex.log (2 : ℂ) * z) := by
      exact Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0) z
    rw [hdef]
    have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
      exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [hlog]
    have harg : (Real.log 2 : ℂ) * z = -(2 * Real.pi * Complex.I) := by
      dsimp [z]
      have hl2 : Real.log 2 ≠ 0 := (Real.log_ne_zero).mpr (by norm_num)
      have hl2c : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hl2
      field_simp [hl2c]
    rw [harg]
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I]
    norm_num
  calc
    (2 : ℂ) ^ (-s + z) = (2 : ℂ) ^ (-s) * (2 : ℂ) ^ z := by
      rw [Complex.cpow_add (x := (2 : ℂ)) (y := (-s : ℂ)) (z := z) (by norm_num : (2 : ℂ) ≠ 0)]
    _ = (2 : ℂ) ^ (-s) * 1 := by rw [hz]
    _ = (2 : ℂ) ^ (-s) := by rw [mul_one]

end ZeroRelative
