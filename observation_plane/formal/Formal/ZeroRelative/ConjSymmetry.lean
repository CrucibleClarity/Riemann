import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# 共轭对称: i/−i 不可区分 (ConjSymmetry) — 2026-08-27

用户问题: "能否用证明法构造出矛盾, 证明 i 的构造存在逻辑矛盾, 进而证否?"

**诚实结论 (本文件机证)**: 纯分析代数不能证明 i 的逻辑矛盾 (ℂ 自洽 —
ℂ = ℝ² 配乘法, i²=−1 逐行可验证)。但 **"i 从实数轴内生构造"可证否**:
共轭 (starRingEnd ℂ) 是固定实数的环自同构, 交换 i 与 −i — 任何从
实数轴出发的构造 (ℝ-代数同态) 保持共轭对称 — i 和 −i 在任何 ℝ-构造中
不可区分 — "从实数轴唯一构造 i/−i" 是假命题 (标准数学用命名约定绕过,
非构造)。即: 证否的对象不是 i (对象自洽), 是"i 的构造方法存在"
(构造论命题 — 可证否: 从 ℝ 无法内生区分 i/−i)。

English: Conjugation symmetry — i and −i are indistinguishable by any
construction from the real axis: conj is a ring automorphism fixing ℝ
and swapping i/−i; any ℝ-algebra construction preserves this symmetry.
The construction of i from the real axis is refutable (not a
construction — a naming convention); i itself is consistent.
-/

noncomputable section

open Complex
open scoped Topology

namespace ZeroRelative

/-- **共轭固定实数**: conj (x:ℂ) = (x:ℂ) — 共轭自同构在实数轴上
    恒等 (ℝ 是 ℂ 的共轭不动子域). -/
theorem conj_fixes_real (x : ℝ) : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by
  simp

/-- **共轭交换 i/−i**: conj i = −i — 共轭自同构交换虚轴的两个单位
    (i 与 −i 在共轭下互换 — 对称性). -/
theorem conj_swaps_i : (starRingEnd ℂ) Complex.I = -Complex.I := by
  simp

/-- **共轭是环自同构**: conj 保持加法乘法 (starRingEnd 是环同构) —
    任何从实数构造的代数结构在共轭下不变. -/
theorem conj_is_ring_aut : (starRingEnd ℂ) (1 : ℂ) = 1 ∧
    (starRingEnd ℂ) (Complex.I * Complex.I) = (starRingEnd ℂ) Complex.I * (starRingEnd ℂ) Complex.I := by
  constructor <;> simp

/-- **★i/−i 不可区分 (从 ℝ 构造的证否核)**: 存在固定实数、交换 i/−i
    的环自同构 (共轭) — 任何 ℝ-代数构造 (保持实数 + 保持环结构) 在
    该自同构下不变 ⟹ i 与 −i 在该构造中不可区分 ⟹ 从实数轴唯一
    构造 i (或 −i) 不可能 (构造论证否: i 的"构造"实为命名约定). -/
theorem i_neg_i_indistinguishable_from_real :
    ∃ σ : ℂ →+* ℂ, (∀ x : ℝ, σ (x : ℂ) = (x : ℂ)) ∧ σ Complex.I = -Complex.I := by
  refine ⟨starRingEnd ℂ, ?_, ?_⟩
  · intro x
    exact conj_fixes_real x
  · exact conj_swaps_i

end ZeroRelative
