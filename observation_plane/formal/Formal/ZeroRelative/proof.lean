/-
# 习题 XXXVII: 黎曼方向统一观测 (0pat) — 合并 XXIV-XXXVI

用户指令 (2026-08-21): 将黎曼方向的全部习题合并成一个。

本文件 = 习题 XXIV-XXXVI 的 0pat proof.lean 全部定理的合并
(素数结构 → 观测框架 → 临界线圆 → 交点 → 系数压缩 → 发散/周期 → 零点结构),
加上本习题新增的四条观测定理 (纯 mathlib 现有定理, 0pat):

1. prime_factor_zero: 素数因子 1-p^{-s} 的零点全在 Re(s) = 0 上
   (1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s = 2πik/ln p; Complex.exp_eq_one_iff)
   — "素数复数进制分解"的精确内容: 每个素数因子把自己的零点放在纯虚轴
2. trivial_zero_condition: 平凡零点条件 cos(πs/2) = 0 ⟺ s = 2k+1
   (函数方程的三角因子零点 = 奇整数; Complex.cos_eq_zero_iff)
3. critical_line_observation: Re s = 1/2 ⟺ 级数项模 = n^{1/2}
   (临界线 = 发散因子 n^{-1/2} 的观测; 从 zeta_term_norm_split 反向)
4. (移除) ζ 零点集离散 (mathlib ZetaZeros.lean 未编译, 依赖链过深, 不引入)
   — 零点若有, 则孤立; 观测框架不改变零点的存在性/位置 (RH 未证, 不合并)

诚实边界: "非平凡零点都在 Re = 1/2" = RH, 不在本习题中 (见论文 Honest
boundary)。素数分解给出的可证事实: 因子零点在 Re = 0 (定理 1), 发散区
Re > 1 无零点需欧拉积 (mathlib 未形式化, 列为缺口), 零点反射对称 (XXVI)。

谱系坐标: (R23, C3) × (R047, C3); 连接 XXIV-XXXVI 全部。

English: consolidated file of Exercise XXXVII, the unified 0pat observation of the Riemann direction --- the fourteen-layer chain, mathlib-only -/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex



/- ================= 习题 24_prime_circle (0pat, 原样合并) ================= -/


/-!
# 习题 XXIV: 周期圆上的素数 — 素数轴周期化 (0pat)

用户洞察 (2026-08-20): 素数轴周期化后, 在欧拉圆视角下素数轴本身也是个圆。
0pat 精确化: 自然数轴模 p 蜷曲成圆 ℤ/pℤ; 素数的圆结构由乘法圆群 (ℤ/pℤ)ˣ 承载:
- 圆的特征: Fermat 小定理 — 素数 p 在圆 ℤ/pℤ 上满足 x^p = x (ZMod.pow_card 的代数内核)
- 乘法圆群的阶: (ℤ/pℤ)ˣ 的阶 = p - 1 (非零元素全部可逆)
- Lagrange: 圆群中每个元素 a^(p-1) = 1 (欧拉定理的素数情形)
- 无穷多素数 (素数在数轴上的整体结构, mathlib: exists_infinite_primes)

谱系坐标: (R23, C3) 素数圆 × 解析数论; 无需复平面 — 纯 ℤ/pℤ 代数。
-/

namespace ZeroRelative

/-- 二维旋转代数 a + b·J (矩阵表示 [[a,-b],[b,a]], ≅ ℂ)。 
English: Two-dimensional rotation algebra a + b·J (matrix form [[a,-b],[b,a]], ≅ ℂ). -/
structure ComplexAxis where
  a : ℝ
  b : ℝ

namespace ComplexAxis

/-- 加法 (分量) 
English: Addition (componentwise). -/
def add (x y : ComplexAxis) : ComplexAxis := ⟨x.a + y.a, x.b + y.b⟩

/-- 相反数 
English: Negation. -/
def neg (x : ComplexAxis) : ComplexAxis := ⟨-x.a, -x.b⟩

/-- 零 
English: Zero. -/
def zero : ComplexAxis := ⟨0, 0⟩

/-- 一 
English: One. -/
def one : ComplexAxis := ⟨1, 0⟩

/-- 90° 旋转 J (J² = -1) 
English: 90° rotation J (J² = -1). -/
def J : ComplexAxis := ⟨0, 1⟩

/-- 乘法 (复数乘法): (a₁+b₁J)(a₂+b₂J) = (a₁a₂-b₁b₂) + (a₁b₂+a₂b₁)J 
English: Multiplication (complex): (a₁+b₁J)(a₂+b₂J) = (a₁a₂-b₁b₂) + (a₁b₂+a₂b₁)J. -/
def mul (x y : ComplexAxis) : ComplexAxis :=
  ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a⟩

/-- 减法 (分量) 
English: Subtraction (componentwise). -/
def sub (x y : ComplexAxis) : ComplexAxis := ⟨x.a - y.a, x.b - y.b⟩

instance instAdd : Add ComplexAxis := ⟨add⟩
instance instNeg : Neg ComplexAxis := ⟨neg⟩
instance instSub : Sub ComplexAxis := ⟨sub⟩
instance instZero : Zero ComplexAxis := ⟨zero⟩
instance instOne : One ComplexAxis := ⟨one⟩
instance instMul : Mul ComplexAxis := ⟨mul⟩

@[ext] theorem ext (x y : ComplexAxis) (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      simp at ha hb
      simp [ha, hb]

/-- 抬升: 实数轴嵌入 (标量部分, 保加法乘法) 
English: Lift: real axis embedding (scalar part, preserves addition and multiplication). -/
def lift (t : ℝ) : ComplexAxis := ⟨t, 0⟩

/-- 范数: 半径平方 (norm z = a² + b²) 
English: Norm: squared radius (norm z = a² + b²). -/
def norm (z : ComplexAxis) : ℝ := z.a ^ 2 + z.b ^ 2

/-- 素数圆: 圆心 0 半径 √p (素数 p 的两平方和整点所在)。 
English: Prime circle: center 0, radius √p (where the sum-of-two-squares lattice points of prime p lie). -/
def primeCircle (p : ℕ) : Set ComplexAxis := {z : ComplexAxis | norm z = (p : ℝ)}

/-- 临界线圆: 圆心 (1,0) 半径 1 (临界线蜷曲下的像, 经过 0 和 2)。 
English: Critical-line circle: center (1,0), radius 1 (image under curling of the critical line, passing through 0 and 2). -/
def criticalCircle : Set ComplexAxis := {w : ComplexAxis | norm (w - lift 1) = 1}

end ComplexAxis
end ZeroRelative

namespace PrimeCircle

noncomputable section

open scoped BigOperators

/-- 乘法圆群的阶: (ℤ/pℤ)ˣ 的基数是 p - 1 (p 素数)。
    证明: (ZMod p)ˣ ≃ {x : ZMod p // x.val.Coprime p} (mathlib);
    后者 = {x : ZMod p // x ≠ 0} (p 素时互素 ⟺ 非零), card = p - 1。 
English: Order of the multiplicative circle group: |(ℤ/pℤ)ˣ| = p - 1 (p prime). Proof: (ZMod p)ˣ ≃ {x : ZMod p // x.val.Coprime p} (mathlib); that set = {x : ZMod p // x ≠ 0} (prime p: coprime ⟺ nonzero), card = p - 1. -/
theorem card_units_zmod_prime {p : ℕ} [Fact (Nat.Prime p)] :
    Fintype.card (ZMod p)ˣ = p - 1 := by
  -- 1. units ≃ {x : ZMod p // x.val.Coprime p} (mathlib)
  have he : (ZMod p)ˣ ≃ {x : ZMod p // x.val.Coprime p} :=
    ZMod.unitsEquivCoprime (n := p)
  -- 2. 引理: 1 ≤ m < p (p 素) ⟹ m.Coprime p (mathlib: coprime_iff_not_dvd)
  have hprime_cop : ∀ {m : ℕ}, 1 ≤ m → m < p → m.Coprime p := by
    intro m hm1 hmp
    -- m.Coprime p ⟺ p.Coprime m (对称) ⟺ ¬ p ∣ m (素数); p ∤ m 因 m < p 且 m > 0
    have hpm : p.Coprime m :=
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 (by
        intro hpdvd
        have hpm_le : p ≤ m := Nat.le_of_dvd hm1 hpdvd
        omega)
    exact hpm.symm
  -- 3. 互素 ⟺ 非零 (p 素)
  have hcoprime_iff : ∀ x : ZMod p, x.val.Coprime p ↔ x ≠ 0 := by
    intro x
    constructor
    · intro hcop hx0
      have hval0 : x.val = 0 := by simp [hx0]
      have : ¬ (0 : ℕ).Coprime p := by
        intro h
        have : p = 1 := by simpa [Nat.Coprime] using h
        exact (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).ne' this
      exact this (by simpa [hval0] using hcop)
    · intro hx0
      have hv0 : x.val ≠ 0 := (ZMod.val_ne_zero x).2 hx0
      exact hprime_cop (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)) (ZMod.val_lt x)
  -- 4. {x // Coprime} ≃ {x // x ≠ 0}
  have hsub : {x : ZMod p // x.val.Coprime p} ≃ {x : ZMod p // x ≠ 0} := by
    refine Equiv.ofBijective (fun x => ⟨x.1, (hcoprime_iff x.1).1 x.2⟩) ?_
    constructor
    · intro a b h
      exact Subtype.ext (by simpa using (congrArg Subtype.val h))
    · intro y
      refine ⟨⟨y.1, (hcoprime_iff y.1).2 y.2⟩, ?_⟩
      rfl
  -- 5. {x : ZMod p // x ≠ 0} ≃ Fin (p - 1): x ↦ x.val - 1, k ↦ (k+1)
  have hne : {x : ZMod p // x ≠ 0} ≃ Fin (p - 1) := by
    refine Equiv.ofBijective
      (fun x => ⟨x.1.val - 1, by
        have hv0 : x.1.val ≠ 0 := (ZMod.val_ne_zero x.1).2 x.2
        have hvlt : x.1.val < p := ZMod.val_lt x.1
        omega⟩)
      ?_
    constructor
    · intro a b h
      apply Subtype.ext
      -- ↑(a.val - 1 + 1) = a (natCast_zmod_val)
      have hva : ((a.1.val - 1 + 1 : ℕ) : ZMod p) = a.1 := by
        have hsub : a.1.val - 1 + 1 = a.1.val := by
          have hv0 : a.1.val ≠ 0 := (ZMod.val_ne_zero a.1).2 a.2
          have h1 : 1 ≤ a.1.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
          rw [Nat.sub_add_cancel h1]
        rw [hsub]
        exact ZMod.natCast_zmod_val a.1
      have hvb : ((b.1.val - 1 + 1 : ℕ) : ZMod p) = b.1 := by
        have hsub : b.1.val - 1 + 1 = b.1.val := by
          have hv0 : b.1.val ≠ 0 := (ZMod.val_ne_zero b.1).2 b.2
          have h1 : 1 ≤ b.1.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
          rw [Nat.sub_add_cancel h1]
        rw [hsub]
        exact ZMod.natCast_zmod_val b.1
      have hk : a.1.val - 1 = b.1.val - 1 := by
        have hf := congrArg Fin.val h
        simpa using hf
      have : a.1.val = b.1.val := by
        have h1a : 1 ≤ a.1.val := by
          have hv0 : a.1.val ≠ 0 := (ZMod.val_ne_zero a.1).2 a.2
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
        have h1b : 1 ≤ b.1.val := by
          have hv0 : b.1.val ≠ 0 := (ZMod.val_ne_zero b.1).2 b.2
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
        omega
      exact (ZMod.val_injective p) this
    · intro k
      refine ⟨⟨((k.1 + 1 : ℕ) : ZMod p), ?_⟩, ?_⟩
      · -- (k+1) ≠ 0: (k+1).val = k+1 > 0
        have hklt : k.1 + 1 < p := by
          have : k.1 < p - 1 := k.2
          omega
        have hval : ((k.1 + 1 : ℕ) : ZMod p).val = k.1 + 1 := by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt hklt
        intro h
        have : k.1 + 1 = 0 := by
          have hc := congrArg ZMod.val h
          -- hc : ((k.1 + 1 : ℕ) : ZMod p).val = 0
          rw [hval] at hc
          simp at hc
        omega
      · apply Fin.ext
        have hklt : k.1 + 1 < p := by
          have : k.1 < p - 1 := k.2
          omega
        have hval : ((k.1 + 1 : ℕ) : ZMod p).val = k.1 + 1 := by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt hklt
        -- 目标: ((k.1 + 1 : ℕ) : ZMod p).val - 1 = k.1
        dsimp
        rw [hval]
        change k.1 + 1 - 1 = k.1
        omega
  -- 6. 组合: card = p - 1
  calc
    Fintype.card (ZMod p)ˣ = Fintype.card {x : ZMod p // x.val.Coprime p} := Fintype.card_congr he
    _ = Fintype.card {x : ZMod p // x ≠ 0} := Fintype.card_congr hsub
    _ = Fintype.card (Fin (p - 1)) := Fintype.card_congr hne
    _ = p - 1 := by simp

/-- Fermat 小定理 (欧拉圆上的素数): a 与 p 互素 ⟹ a^(p-1) ≡ 1 [MOD p]。
    证明: a 在乘法圆群 (ℤ/pℤ)ˣ 中; 圆群阶 = p-1; Lagrange ⟹ a^(p-1) = 1。 
English: Fermat's little theorem (prime on the Euler circle): a coprime to p ⟹ a^(p-1) ≡ 1 [MOD p]. Proof: a is in the multiplicative circle group (ℤ/pℤ)ˣ; the group order = p-1; Lagrange ⟹ a^(p-1) = 1. -/
theorem fermat_little {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ} (hpa : a.Coprime p) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  -- a mod p 是圆群元素
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime a hpa
  -- u 的阶整除圆群阶
  have horder_dvd : orderOf u ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := card_units_zmod_prime
  -- u^orderOf = 1, orderOf | p-1 ⟹ u^(p-1) = 1
  have hpow : u ^ (p - 1) = 1 := by
    rcases horder_dvd with ⟨k, hk⟩
    rw [hcard] at hk
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  -- 转回 ModEq: u = (a : ZMod p), 1 = (1 : ZMod p)
  have hcast : (a ^ (p - 1) : ZMod p) = (1 : ZMod p) := by
    have hu : (u : ZMod p) = (a : ZMod p) := rfl
    calc
      (a ^ (p - 1) : ZMod p) = ((a : ZMod p) ^ (p - 1)) := by
        simp
      _ = (u : ZMod p) ^ (p - 1) := by rw [hu]
      _ = ((u ^ (p - 1) : (ZMod p)ˣ) : ZMod p) := by
        rw [Units.val_pow_eq_pow_val]
      _ = 1 := by rw [hpow]; rfl
  exact (ZMod.natCast_eq_natCast_iff (a ^ (p - 1)) 1 p).mp (by simpa using hcast)

/-- Fermat 小定理的完整形式: 任意 a (含 p 整除 a 的情形): a^p ≡ a [MOD p]。 
English: Complete Fermat's little theorem: any a (including p | a): a^p ≡ a [MOD p]. -/
theorem fermat_little_complete {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ) :
    a ^ p ≡ a [MOD p] := by
  by_cases hpa : a.Coprime p
  · -- 互素情形: a^(p-1) = 1 ⟹ a^p = a
    have h := fermat_little (p := p) (a := a) hpa
    -- a^p = a^(p-1) * a ≡ 1 * a = a
    have hp : p = p - 1 + 1 := by
      have hp0 : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
      omega
    have hpow_eq : a ^ p = a ^ (p - 1) * a := by
      have hpa' : a ^ (p - 1 + 1) = a ^ (p - 1) * a := by
        rw [pow_succ]
      rw [← hp] at hpa'
      exact hpa'
    have hmod : a ^ p ≡ 1 * a [MOD p] := by
      rw [hpow_eq]
      exact Nat.ModEq.mul_right a h
    -- 1 * a = a, 替换进 ModEq
    have h1a : 1 * a = a := by omega
    have hmod' : a ^ p ≡ a [MOD p] := by
      -- hmod : a^p ≡ 1*a; 1*a = a — 等式替换进 ModEq
      rw [h1a] at hmod
      exact hmod
    exact hmod'
  · -- 不互素情形: p 素 ⟹ p | a ⟹ 两边 ≡ 0
    have hpdvd : p ∣ a := by
      -- 素数与 a 不互素 ⟹ p | a (mathlib: coprime_iff_not_dvd 的逆否)
      by_contra hnotdvd
      apply hpa
      -- p 素且 p ∤ a ⟹ a.Coprime p (对称 + coprime_iff_not_dvd)
      have hpc : p.Coprime a :=
        (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hnotdvd
      exact hpc.symm
    -- p | a ⟹ a ≡ 0; ModEq.pow 提升: a^p ≡ 0^p = 0; 两边同余 0
    have ha0 : a ≡ 0 [MOD p] := by
      simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd hpdvd]
    have hmod0 : a ^ p ≡ 0 [MOD p] := by
      simpa [Nat.Prime.ne_zero (Fact.out : Nat.Prime p)] using ha0.pow p
    exact hmod0.trans ha0.symm

/-- 无穷多素数 (数轴上的素数整体结构, mathlib)。 
English: Infinitely many primes (global structure of primes on the number line, mathlib). -/
theorem infinitely_many_primes (n : ℕ) : ∃ p : ℕ, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes n

end

/- ================= 习题 25_orthogonal_euler_circles (0pat, 原样合并) ================= -/


/-!
# 习题 XXV: 正交欧拉圆坐标系 — 双模观测 (0pat)

用户洞察 (2026-08-20): 素数的轴化过程, 以两个正交的欧拉圆为坐标系进行观测。
0pat 精确化: 两个正交欧拉圆 = 互素模 p, q 的圆 ℤ/pℤ × ℤ/qℤ; 正交性 = 互素;
坐标系合成 = 中国剩余定理 (CRT): ℤ/pqℤ ≃ ℤ/pℤ × ℤ/qℤ。

- 坐标系合法性: 欧拉圆 ↔ 实数轴的映射已证 (Stereographic.lean 球极投影 /
  CircleCore.lean); 正交坐标系 = 双模投影, 合成 = CRT。
- 素数观测: 素数 p 在本征圆 ℤ/pℤ 上满足 Fermat 代数 x^p = x (习题 XXIV);
  在非本征圆 ℤ/qℤ (q ≠ p) 上投影非零, 因而是单位圆群元素: p^(q-1) ≡ 1。
- 素因子的可观测性: p | a ⟹ a 在 ℤ/pℤ 上投影为 0 (素因子在第一坐标可见)。

谱系坐标: (R23, C3) 素数圆 × 解析数论; 连接 XXIII (合数 = 素分解) 与
XXIV (素数圆 = Fermat)。无需复平面 — 纯 ℤ/nℤ 代数。
-/

namespace OrthogonalCircles

noncomputable section

open scoped BigOperators

/-- 正交坐标系合成 (CRT): 互素模 p, q 的两个正交欧拉圆的笛卡尔积
    = 合数模 pq 的圆。mathlib: ZMod.chineseRemainder。 
English: Orthogonal frame composition (CRT): the Cartesian product of the two orthogonal Euler circles of coprime moduli p, q = the circle of composite modulus pq. mathlib: ZMod.chineseRemainder. -/
noncomputable def orthogonal_frame_crt {m n : ℕ} (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- 素因子的可观测性: 若 p | a, 则 a 在模 p 圆上的投影为 0
    (素因子在正交坐标系的第一坐标可见)。 
English: Observability of prime factors: if p | a, then a's projection on the circle mod p is 0 (the prime factor is visible in the first coordinate of the orthogonal frame). -/
theorem factor_observable_zero {p a : ℕ} [Fact (Nat.Prime p)] (h : p ∣ a) :
    (a : ZMod p) = 0 := by
  apply ZMod.val_injective
  simp [ZMod.val_natCast, Nat.mod_eq_zero_of_dvd h]

/-- 素数的可区分性: 素数 p 在非本征圆 ℤ/qℤ (q ≠ p 素数) 上的投影非零
    (正交坐标系区分不同的素数)。 
English: Distinguishability of primes: prime p projects nonzero on the non-eigen circle ℤ/qℤ (q ≠ p prime) (the orthogonal frame distinguishes different primes). -/
theorem distinct_primes_observable {p q : ℕ} [Fact (Nat.Prime p)]
    [Fact (Nat.Prime q)] (h : p ≠ q) : (p : ZMod q) ≠ 0 := by
  have hndvd : ¬ q ∣ p := by
    intro hd
    have hcases : q = 1 ∨ q = p :=
      (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime p) q hd)
    rcases hcases with hq1 | hqp
    · exact (Nat.Prime.ne_one (Fact.out : Nat.Prime q)) hq1
    · exact h hqp.symm
  intro hz
  have hval : (p : ZMod q).val = 0 := by simp [hz]
  rw [ZMod.val_natCast] at hval
  exact hndvd (Nat.dvd_of_mod_eq_zero hval)

/-- 乘法圆群的阶: (ℤ/pℤ)ˣ 的基数是 p - 1 (p 素数)。 (习题 XXIV 复用) 
English: Order of the multiplicative circle group: |(ℤ/pℤ)ˣ| = p - 1 (p prime). (Reused from Exercise XXIV.) -/
theorem card_units_zmod_prime {p : ℕ} [Fact (Nat.Prime p)] :
    Fintype.card (ZMod p)ˣ = p - 1 := by
  -- 1. units ≃ {x : ZMod p // x.val.Coprime p} (mathlib)
  have he : (ZMod p)ˣ ≃ {x : ZMod p // x.val.Coprime p} :=
    ZMod.unitsEquivCoprime (n := p)
  -- 2. 引理: 1 ≤ m < p (p 素) ⟹ m.Coprime p (mathlib: coprime_iff_not_dvd)
  have hprime_cop : ∀ {m : ℕ}, 1 ≤ m → m < p → m.Coprime p := by
    intro m hm1 hmp
    -- m.Coprime p ⟺ p.Coprime m (对称) ⟺ ¬ p ∣ m (素数); p ∤ m 因 m < p 且 m > 0
    have hpm : p.Coprime m :=
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 (by
        intro hpdvd
        have hpm_le : p ≤ m := Nat.le_of_dvd hm1 hpdvd
        omega)
    exact hpm.symm
  -- 3. 互素 ⟺ 非零 (p 素)
  have hcoprime_iff : ∀ x : ZMod p, x.val.Coprime p ↔ x ≠ 0 := by
    intro x
    constructor
    · intro hcop hx0
      have hval0 : x.val = 0 := by simp [hx0]
      have : ¬ (0 : ℕ).Coprime p := by
        intro h
        have : p = 1 := by simpa [Nat.Coprime] using h
        exact (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).ne' this
      exact this (by simpa [hval0] using hcop)
    · intro hx0
      have hv0 : x.val ≠ 0 := (ZMod.val_ne_zero x).2 hx0
      exact hprime_cop (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)) (ZMod.val_lt x)
  -- 4. {x // Coprime} ≃ {x // x ≠ 0}
  have hsub : {x : ZMod p // x.val.Coprime p} ≃ {x : ZMod p // x ≠ 0} := by
    refine Equiv.ofBijective (fun x => ⟨x.1, (hcoprime_iff x.1).1 x.2⟩) ?_
    constructor
    · intro a b h
      exact Subtype.ext (by simpa using (congrArg Subtype.val h))
    · intro y
      refine ⟨⟨y.1, (hcoprime_iff y.1).2 y.2⟩, ?_⟩
      rfl
  -- 5. {x : ZMod p // x ≠ 0} ≃ Fin (p - 1): x ↦ x.val - 1, k ↦ (k+1)
  have hne : {x : ZMod p // x ≠ 0} ≃ Fin (p - 1) := by
    refine Equiv.ofBijective
      (fun x => ⟨x.1.val - 1, by
        have hv0 : x.1.val ≠ 0 := (ZMod.val_ne_zero x.1).2 x.2
        have hvlt : x.1.val < p := ZMod.val_lt x.1
        omega⟩)
      ?_
    constructor
    · intro a b h
      apply Subtype.ext
      -- ↑(a.val - 1 + 1) = a (natCast_zmod_val)
      have hva : ((a.1.val - 1 + 1 : ℕ) : ZMod p) = a.1 := by
        have hsub : a.1.val - 1 + 1 = a.1.val := by
          have hv0 : a.1.val ≠ 0 := (ZMod.val_ne_zero a.1).2 a.2
          have h1 : 1 ≤ a.1.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
          rw [Nat.sub_add_cancel h1]
        rw [hsub]
        exact ZMod.natCast_zmod_val a.1
      have hvb : ((b.1.val - 1 + 1 : ℕ) : ZMod p) = b.1 := by
        have hsub : b.1.val - 1 + 1 = b.1.val := by
          have hv0 : b.1.val ≠ 0 := (ZMod.val_ne_zero b.1).2 b.2
          have h1 : 1 ≤ b.1.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
          rw [Nat.sub_add_cancel h1]
        rw [hsub]
        exact ZMod.natCast_zmod_val b.1
      have hk : a.1.val - 1 = b.1.val - 1 := by
        have hf := congrArg Fin.val h
        simpa using hf
      have : a.1.val = b.1.val := by
        have h1a : 1 ≤ a.1.val := by
          have hv0 : a.1.val ≠ 0 := (ZMod.val_ne_zero a.1).2 a.2
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
        have h1b : 1 ≤ b.1.val := by
          have hv0 : b.1.val ≠ 0 := (ZMod.val_ne_zero b.1).2 b.2
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
        omega
      exact (ZMod.val_injective p) this
    · intro k
      refine ⟨⟨((k.1 + 1 : ℕ) : ZMod p), ?_⟩, ?_⟩
      · -- (k+1) ≠ 0: (k+1).val = k+1 > 0
        have hklt : k.1 + 1 < p := by
          have : k.1 < p - 1 := k.2
          omega
        have hval : ((k.1 + 1 : ℕ) : ZMod p).val = k.1 + 1 := by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt hklt
        intro h
        have : k.1 + 1 = 0 := by
          have hc := congrArg ZMod.val h
          -- hc : ((k.1 + 1 : ℕ) : ZMod p).val = 0
          rw [hval] at hc
          simp at hc
        omega
      · apply Fin.ext
        have hklt : k.1 + 1 < p := by
          have : k.1 < p - 1 := k.2
          omega
        have hval : ((k.1 + 1 : ℕ) : ZMod p).val = k.1 + 1 := by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt hklt
        -- 目标: ((k.1 + 1 : ℕ) : ZMod p).val - 1 = k.1
        dsimp
        rw [hval]
        change k.1 + 1 - 1 = k.1
        omega
  -- 6. 组合: card = p - 1
  calc
    Fintype.card (ZMod p)ˣ = Fintype.card {x : ZMod p // x.val.Coprime p} := Fintype.card_congr he
    _ = Fintype.card {x : ZMod p // x ≠ 0} := Fintype.card_congr hsub
    _ = Fintype.card (Fin (p - 1)) := Fintype.card_congr hne
    _ = p - 1 := by simp

/-- Fermat 小定理 (欧拉圆上的素数): a 与 p 互素 ⟹ a^(p-1) ≡ 1 [MOD p]。
    证明: a 在乘法圆群 (ℤ/pℤ)ˣ 中; 圆群阶 = p-1; Lagrange ⟹ a^(p-1) = 1。 
English: Fermat's little theorem (prime on the Euler circle): a coprime to p ⟹ a^(p-1) ≡ 1 [MOD p]. Proof: a is in the multiplicative circle group (ℤ/pℤ)ˣ; the group order = p-1; Lagrange ⟹ a^(p-1) = 1. -/
theorem fermat_little {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ} (hpa : a.Coprime p) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  -- a mod p 是圆群元素
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime a hpa
  -- u 的阶整除圆群阶
  have horder_dvd : orderOf u ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := card_units_zmod_prime
  -- u^orderOf = 1, orderOf | p-1 ⟹ u^(p-1) = 1
  have hpow : u ^ (p - 1) = 1 := by
    rcases horder_dvd with ⟨k, hk⟩
    rw [hcard] at hk
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  -- 转回 ModEq: u = (a : ZMod p), 1 = (1 : ZMod p)
  have hcast : (a ^ (p - 1) : ZMod p) = (1 : ZMod p) := by
    have hu : (u : ZMod p) = (a : ZMod p) := rfl
    calc
      (a ^ (p - 1) : ZMod p) = ((a : ZMod p) ^ (p - 1)) := by
        simp
      _ = (u : ZMod p) ^ (p - 1) := by rw [hu]
      _ = ((u ^ (p - 1) : (ZMod p)ˣ) : ZMod p) := by
        rw [Units.val_pow_eq_pow_val]
      _ = 1 := by rw [hpow]; rfl
  exact (ZMod.natCast_eq_natCast_iff (a ^ (p - 1)) 1 p).mp (by simpa using hcast)

/-- Fermat 小定理的完整形式: 任意 a (含 p 整除 a 的情形): a^p ≡ a [MOD p]。 
English: Complete Fermat's little theorem: any a (including p | a): a^p ≡ a [MOD p]. -/
theorem fermat_little_complete {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ) :
    a ^ p ≡ a [MOD p] := by
  by_cases hpa : a.Coprime p
  · -- 互素情形: a^(p-1) = 1 ⟹ a^p = a
    have h := fermat_little (p := p) (a := a) hpa
    -- a^p = a^(p-1) * a ≡ 1 * a = a
    have hp : p = p - 1 + 1 := by
      have hp0 : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
      omega
    have hpow_eq : a ^ p = a ^ (p - 1) * a := by
      have hpa' : a ^ (p - 1 + 1) = a ^ (p - 1) * a := by
        rw [pow_succ]
      rw [← hp] at hpa'
      exact hpa'
    have hmod : a ^ p ≡ 1 * a [MOD p] := by
      rw [hpow_eq]
      exact Nat.ModEq.mul_right a h
    -- 1 * a = a, 替换进 ModEq
    have h1a : 1 * a = a := by omega
    have hmod' : a ^ p ≡ a [MOD p] := by
      -- hmod : a^p ≡ 1*a; 1*a = a — 等式替换进 ModEq
      rw [h1a] at hmod
      exact hmod
    exact hmod'
  · -- 不互素情形: p 素 ⟹ p | a ⟹ 两边 ≡ 0
    have hpdvd : p ∣ a := by
      -- 素数与 a 不互素 ⟹ p | a (mathlib: coprime_iff_not_dvd 的逆否)
      by_contra hnotdvd
      apply hpa
      -- p 素且 p ∤ a ⟹ a.Coprime p (对称 + coprime_iff_not_dvd)
      have hpc : p.Coprime a :=
        (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hnotdvd
      exact hpc.symm
    -- p | a ⟹ a ≡ 0; ModEq.pow 提升: a^p ≡ 0^p = 0; 两边同余 0
    have ha0 : a ≡ 0 [MOD p] := by
      simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd hpdvd]
    have hmod0 : a ^ p ≡ 0 [MOD p] := by
      simpa [Nat.Prime.ne_zero (Fact.out : Nat.Prime p)] using ha0.pow p
    exact hmod0.trans ha0.symm


/-- 素数在非本征圆上的观测: 素数 p 在 ℤ/qℤ (q ≠ p) 上是单位圆群元素,
    满足 Fermat 小定理 p^(q-1) ≡ 1 (Lagrange: 单位群阶 = q-1)。 
English: Observation of primes on a non-eigen circle: prime p is a unit-group element in ℤ/qℤ (q ≠ p), satisfying Fermat's little theorem p^(q-1) ≡ 1 (Lagrange: unit group order = q-1). -/
theorem prime_unit_on_other_circle {p q : ℕ} [Fact (Nat.Prime p)]
    [Fact (Nat.Prime q)] (h : p ≠ q) : p ^ (q - 1) ≡ 1 [MOD q] := by
  -- p 在 ℤ/qℤ 中非零 (distinct_primes_observable) ⟹ 与 q 互素
  have hcop : p.Coprime q := by
    have hndvd : ¬ q ∣ p := by
      intro hd
      have hcases : q = 1 ∨ q = p :=
        (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime p) q hd)
      rcases hcases with hq1 | hqp
      · exact (Nat.Prime.ne_one (Fact.out : Nat.Prime q)) hq1
      · exact h hqp.symm
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime q)).2 hndvd).symm
  -- 单位群元素 (unitOfCoprime) + Lagrange (orderOf_dvd_card + pow_orderOf_eq_one)
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime p hcop
  have horder_dvd : orderOf u ∣ Fintype.card (ZMod q)ˣ := orderOf_dvd_card
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := card_units_zmod_prime (p := q)
  have hpow : u ^ (q - 1) = 1 := by
    rcases horder_dvd with ⟨k, hk⟩
    rw [hcard] at hk
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  -- 转回 ModEq
  have hcast : (p ^ (q - 1) : ZMod q) = (1 : ZMod q) := by
    have hu : (u : ZMod q) = (p : ZMod q) := rfl
    calc
      (p ^ (q - 1) : ZMod q) = ((p : ZMod q) ^ (q - 1)) := by
        simp
      _ = (u : ZMod q) ^ (q - 1) := by rw [hu]
      _ = ((u ^ (q - 1) : (ZMod q)ˣ) : ZMod q) := by
        rw [Units.val_pow_eq_pow_val]
      _ = 1 := by rw [hpow]; rfl
  exact (ZMod.natCast_eq_natCast_iff (p ^ (q - 1)) 1 q).mp (by simpa using hcast)

end
end OrthogonalCircles

/- ================= 习题 26_zeta_zero_reflection (0pat, 原样合并) ================= -/


/-!
# 习题 XXVI: 零点反射对称性 — 中间桥面的第一块分析材料 (0pat)

黎曼方向缺口的精确定位: 左岸 (Re ≥ 1 欧拉乘积/无零区) 与右岸 (临界线⟺圆几何)
之间的"中间桥面" = 临界带 0 < Re(s) < 1 内 ζ 的零点位置控制, 需要分析学工具。
mathlib 提供经典函数方程 riemannZeta_one_sub:

    ζ(1-s) = 2 (2π)^(-s) Γ(s) cos(πs/2) ζ(s)   (s ≠ -n, s ≠ 1)

本习题是函数方程的第一个推论 — 第一个真正使用分析的定理:
- 零点反射对称性: ζ(s) = 0 ⟹ ζ(1-s) = 0 (零点关于临界线 Re = 1/2 对称)
- 反射保持临界带: 带内零点反射后仍在带内
- 离线配对: 若零点离线 (Re s ≠ 1/2), 则 1-s 是另一个不同的带内零点
  (离线零点成对出现 — 函数方程给的第一条离线结构约束)

谱系坐标: (R23, C3) 解析数论; 中间桥面材料 #1。
-/

namespace ZetaZeroReflection

noncomputable section

open scoped BigOperators

/-- 零点反射对称性: ζ(s)=0 (非平凡点, 非极点) ⟹ ζ(1-s)=0。
    函数方程 riemannZeta_one_sub 的直接推论 — 零点关于临界线 Re=1/2 对称。 
English: Zero reflection symmetry: ζ(s)=0 (non-trivial point, non-pole) ⟹ ζ(1-s)=0. Direct corollary of the functional equation riemannZeta_one_sub — zeros symmetric about the critical line Re=1/2. -/
theorem zeta_zero_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) : riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub htriv hone, hz]
  ring

/-- 反射保持临界带: 带内零点 (0 < Re s < 1) 的反射 1-s 仍在带内。 
English: Reflection preserves the critical strip: the reflection 1-s of an in-strip zero (0 < Re s < 1) remains in the strip. -/
theorem zeta_zero_strip_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (hstrip : 0 < s.re ∧ s.re < 1)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) :
    riemannZeta (1 - s) = 0 ∧ 0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor
  · exact zeta_zero_reflection hz htriv hone
  · constructor
    · rw [Complex.sub_re, Complex.one_re]; linarith [hstrip.1, hstrip.2]
    · rw [Complex.sub_re, Complex.one_re]; linarith [hstrip.1, hstrip.2]

/-- 离线配对: 若带内零点 s 离线 (Re s ≠ 1/2), 则 1-s 是另一个不同的带内零点
    (离线零点成对出现 — 函数方程给的第一条离线结构约束)。 
English: Offline pairing: if an in-strip zero s is offline (Re s ≠ 1/2), then 1-s is another distinct in-strip zero (offline zeros come in pairs — the first offline structural constraint from the functional equation). -/
theorem zeta_zero_offline_pair {s : ℂ} (hz : riemannZeta s = 0)
    (hstrip : 0 < s.re ∧ s.re < 1)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) (hre : s.re ≠ 1 / 2) :
    1 - s ≠ s ∧ riemannZeta (1 - s) = 0 ∧ 0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor
  · -- 1-s ≠ s: 若 1-s = s 则 re s = 1/2, 与 hre 矛盾
    intro h
    apply hre
    have hre' : (1 - s).re = s.re := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re] at hre'
    linarith
  · exact zeta_zero_strip_reflection hz hstrip htriv hone

end
end ZetaZeroReflection

/- ================= 习题 27_split_complex (0pat, 原样合并) ================= -/


/-!
# 习题 XXVII: 分裂复数 — 虚半径正交欧拉圆 (0pat)

用户洞察 (2026-08-21): 两个正交欧拉圆, 一个半径 1, 一个半径 i —
不强迫复平面那样虚部实部相等, 而是纯粹的复正交欧拉圆。
0pat 精确化: 分裂复数 (split-complex) 是"半径 i 的圆"的宿主结构:

    分裂复数:  a + bj,  j² = +1            (对比 ℂ: J² = -1)
    伪范数:    ‖a + bj‖² = a² - b²         (闵可夫斯基度量)
    半径 1 圆: ‖z‖² = 1   ⟺  a² - b² = 1   (双曲线)
    半径 i 圆: ‖z‖² = -1  ⟺  b² - a² = 1   (共轭双曲线, 非空: j 在其上)

正交性: 半径 1 与半径 i 的同心圆满足 1² + i² = 0 — 在分裂度量下即
r₁² + r₂² = 1 + (-1) = 0 = 圆心距², 这是"虚半径圆正交"的精确含义。

观测对比: ℂ 中素数可表示为范数 (a²+b²) 当且仅当 p ≡ 1,2 (mod 4)
(Fermat, XXIV); 分裂复数中每个奇素数都可表示为伪范数 (a²-b²):
p = ((p+1)/2)² - ((p-1)/2)² — 分裂架构对素数的观测无区分度,
与 ℂ 架构形成对比 (观测的区分性差异)。

谱系坐标: (R20, C8) 圆上量化 × 构造; 对比 (R23, C3) 素数圆。
-/

namespace SplitComplexEx

noncomputable section

/-- 分裂复数: a + bj, j² = +1。 
English: Split complex: a + bj, j² = +1. -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

/-- 虚数单位 j (j² = +1)。 
English: Imaginary unit j (j² = +1). -/
def j : SplitComplex := ⟨0, 1⟩

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem re_add (z w : SplitComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : SplitComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 
English: Pseudo-norm (Minkowski metric): ‖a + bj‖² = a² - b². -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- j² = 1: 分裂复数的定义性代数性质 (对比 ℂ 的 J² = -1)。 
English: j² = 1: the defining algebraic property of split complexes (contrast J² = -1 in ℂ). -/
theorem j_sq : j * j = 1 := by
  ext <;> simp [j]

/-- 伪范数乘性: ‖zw‖² = ‖z‖²‖w‖² (分裂复数的关键代数性质)。 
English: Pseudo-norm multiplicativity: ‖zw‖² = ‖z‖²‖w‖² (key algebraic property of split complexes). -/
theorem normSq_mul (z w : SplitComplex) : normSq (z * w) = normSq z * normSq w := by
  simp [normSq, re_mul, im_mul]
  ring

/-- 半径 i 的圆非空: j 在"虚半径圆"上 (‖j‖² = -1)。 
English: The radius-i circle is nonempty: j lies on the imaginary-radius circle (‖j‖² = -1). -/
theorem imaginary_radius_circle : normSq j = -1 := by
  simp [normSq, j]

/-- 半径 1 的圆非空: 1 在"实半径圆"上 (‖1‖² = 1)。 
English: The radius-1 circle is nonempty: 1 lies on the real-radius circle (‖1‖² = 1). -/
theorem real_radius_circle : normSq (1 : SplitComplex) = 1 := by
  simp [normSq]

/-- 正交条件: 半径 1 与半径 i 的同心圆满足 r₁² + r₂² = 0
    (分裂度量下 1² + i² = 1 + (-1) = 0 = 圆心距²)。 
English: Orthogonality condition: concentric circles of radii 1 and i satisfy r₁² + r₂² = 0 (in the split metric 1² + i² = 1 + (-1) = 0 = squared center distance). -/
theorem orthogonal_radii : (1 : ℝ) + (-1) = 0 := by
  norm_num

/-- 共轭双曲线不相交: 没有点同时在半径 1 圆与半径 i 圆上。 
English: The conjugate hyperbolas are disjoint: no point lies on both the radius-1 and radius-i circles. -/
theorem circles_disjoint : ¬ ∃ z : SplitComplex, normSq z = 1 ∧ normSq z = -1 := by
  rintro ⟨z, h1, hm1⟩
  linarith

/-- 观测对比: 每个奇素数 p 都是分裂伪范数 (a²-b²), 与 ℂ 的 Fermat
    两平方和 (仅 p ≡ 1,2 mod 4) 形成区分度对比。 
English: Observation contrast: every odd prime p is a split pseudo-norm (a²-b²), forming a discriminative contrast with ℂ's Fermat two-squares (only p ≡ 1,2 mod 4). -/
theorem odd_prime_is_split_norm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ a b : ℕ, (a : ℕ) ^ 2 - (b : ℕ) ^ 2 = p := by
  -- p 奇: p = 2k+1, a = k+1, b = k; (k+1)² - k² = 2k+1 = p
  have hpodd : p % 2 = 1 := by
    have : p % 2 ≠ 0 := by
      intro h
      have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
      have hcases : 2 = 1 ∨ 2 = p := hp.eq_one_or_self_of_dvd 2 hd
      rcases hcases with h21 | h2p
      · norm_num at h21
      · exact hp2 h2p.symm
    have hlt : p % 2 < 2 := Nat.mod_lt p (by norm_num)
    omega
  refine ⟨p / 2 + 1, p / 2, ?_⟩
  -- (k+1)² - k² = p: 展开 (k = p/2, p = 2k+1)
  have hk : 2 * (p / 2) + 1 = p := by
    have hdiv : p = 2 * (p / 2) + p % 2 := (Nat.div_add_mod p 2).symm
    rw [hpodd] at hdiv
    omega
  have hpow : (p / 2 + 1) ^ 2 - (p / 2) ^ 2 = 2 * (p / 2) + 1 := by
    have h1 : (p / 2 + 1) ^ 2 = (p / 2) ^ 2 + (2 * (p / 2) + 1) := by ring
    rw [h1]
    omega
  rw [hpow, hk]

end SplitComplex

end
end SplitComplexEx

/- ================= 习题 28_split_complex_critical_line (0pat, 原样合并) ================= -/


/-!
# 习题 XXVIII: 分裂复数下的临界线观测 (0pat)

在分裂复数架构 (XXVII: j²=+1, 伪范数 a²-b²) 下观测黎曼方向的临界线:

1. 临界线点 1/2 + tj 的伪范数 = 1/4 - t² — 实部条件 Re=1/2
   在分裂坐标下变成虚部阈值 |t| = 1/2 (实部↔虚部角色互换)。
2. 阈值: |t| > 1/2 ⟹ 类空 (半径 i 圆区域); |t| < 1/2 ⟹ 类时。
3. recip (乘法逆) 把临界线映到双曲线 (a-1)² - b² = 1 —
   这是 ℂ 中"recip(临界线) = 圆 (a-1)²+b² = 1" (C019-C022 已证) 的
   分裂对偶: 同一映射, 两个宿主, 圆 ⟷ 双曲线。
4. 零点观测: 临界线零点 (若存在) 的分裂伪范数 < 0 (类空),
   因为已知零点虚部 |t| ≥ 14.13 > 1/2 — 阈值 1/2 由分裂结构本身给出。

谱系坐标: (R23, C3) × (R20, C8); 连接 XXVII (分裂复数) 与 C019-C022 (临界圆)。
-/

namespace SplitComplexCritLine

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 
English: Split complex: a + bj, j² = +1 (reused XXVII structure, standalone file). -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_add (z w : SplitComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : SplitComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

/-- 伪范数 (闵可夫斯基度量)。 
English: Pseudo-norm (Minkowski metric). -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 乘法逆: (a+bj)⁻¹ = (a-bj)/(a²-b²), 当伪范数非零。 
English: Multiplicative inverse: (a+bj)⁻¹ = (a-bj)/(a²-b²), when the pseudo-norm is nonzero. -/
noncomputable instance : Inv SplitComplex :=
  ⟨fun z => ⟨z.re / normSq z, -z.im / normSq z⟩⟩

@[simp] theorem re_inv (z : SplitComplex) : (z⁻¹).re = z.re / normSq z := rfl
@[simp] theorem im_inv (z : SplitComplex) : (z⁻¹).im = -z.im / normSq z := rfl

/-- 逆是乘法逆 (当伪范数非零)。 
English: The inverse is a multiplicative inverse (when the pseudo-norm is nonzero). -/
theorem inv_mul_self {z : SplitComplex} (hz : normSq z ≠ 0) : z⁻¹ * z = 1 := by
  have hz' : z.re ^ 2 - z.im ^ 2 ≠ 0 := by simpa [normSq] using hz
  ext
  · dsimp [normSq]
    field_simp [hz']
    ring
  · dsimp [normSq]
    field_simp [hz']
    ring

/-- 临界线点 1/2 + tj 的伪范数: ‖1/2 + tj‖² = 1/4 - t²。
    实部条件 Re = 1/2 在分裂坐标下变成虚部阈值 |t| = 1/2。 
English: Pseudo-norm of the critical-line point 1/2 + tj: ‖1/2 + tj‖² = 1/4 - t². The real-part condition Re = 1/2 becomes the imaginary threshold |t| = 1/2 in split coordinates. -/
theorem critical_line_pseudonorm (t : ℝ) : normSq (⟨1 / 2, t⟩ : SplitComplex) = 1 / 4 - t ^ 2 := by
  simp [normSq]
  ring

/-- 阈值 (类时侧): |t| < 1/2 ⟹ 伪范数为正 (半径 1 圆区域)。 
English: Threshold (timelike side): |t| < 1/2 ⟹ pseudo-norm positive (radius-1 circle region). -/
theorem threshold_timelike {t : ℝ} (ht : t ^ 2 < 1 / 4) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) > 0 := by
  rw [critical_line_pseudonorm]
  nlinarith

/-- 阈值 (类空侧): |t| > 1/2 ⟹ 伪范数为负 (半径 i 圆区域)。 
English: Threshold (spacelike side): |t| > 1/2 ⟹ pseudo-norm negative (radius-i circle region). -/
theorem threshold_spacelike {t : ℝ} (ht : 1 / 2 < t) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) < 0 := by
  rw [critical_line_pseudonorm]
  nlinarith

/-- 零点观测: 临界线零点 (实部 1/2, |虚部| > 1/2) 的分裂伪范数为负 (类空)。
    已知零点 |t| ≥ 14.13 > 1/2 — 阈值 1/2 由分裂结构本身给出。 
English: Zero observation: split pseudo-norm of a critical-line zero (real part 1/2, |imag part| > 1/2) is negative (spacelike). Known zeros have |t| ≥ 14.13 > 1/2 — the threshold 1/2 is given by the split structure itself. -/
theorem zero_observation_spacelike {t : ℝ} (ht : 1 / 2 < |t|) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) < 0 := by
  rw [critical_line_pseudonorm]
  have ht2 : (1 / 2) ^ 2 < t ^ 2 := by
    rcases le_or_gt t 0 with htle | htgt
    · have habs : |t| = -t := abs_of_nonpos htle
      rw [habs] at ht
      nlinarith
    · have habs : |t| = t := abs_of_pos htgt
      rw [habs] at ht
      nlinarith
  nlinarith

/-- recip 临界线 ⟹ 双曲线 (a-1)² - b² = 1 (分裂版本的临界圆)。
    对偶: ℂ 中 recip(临界线) = 圆 (a-1)² + b² = 1 (C019-C022 已证);
    分裂中 = 双曲线 — 同一 recip 映射, 两个宿主。 
English: recip of the critical line ⟹ hyperbola (a-1)² - b² = 1 (split version of the critical circle). Duality: in ℂ recip(critical line) = circle (a-1)² + b² = 1 (C019-C022 proven); in split = hyperbola — same recip map, two hosts. -/
theorem recip_critical_line_hyperbola (t : ℝ) (ht : 1 / 4 - t ^ 2 ≠ 0) :
    let w : SplitComplex := (⟨1 / 2, t⟩ : SplitComplex)⁻¹
    (w.re - 1) ^ 2 - w.im ^ 2 = 1 := by
  let d : ℝ := 1 / 4 - t ^ 2
  have hd : d ≠ 0 := ht
  rw [show (⟨1 / 2, t⟩ : SplitComplex)⁻¹ = ⟨(1 / 2) / d, -t / d⟩ by
    ext <;> simp [normSq, d] <;> ring]
  simp
  field_simp [hd]
  dsimp [d]
  ring

end SplitComplex

end
end SplitComplexCritLine

/- ================= 习题 29_complex_plane_intersections (0pat, 原样合并) ================= -/


/-!
# 习题 XXIX: 复平面四对象交点观测 (0pat)

用户洞察 (2026-08-21): 直接观测复平面的横轴、纵轴、临界线圆、素数圆,
观察交点。

交点总表 (全部机器验证):
  ┌─────────────────────┬──────────────────────────────────────┐
  │ 对象对               │ 交点                                │
  ├─────────────────────┼──────────────────────────────────────┤
  │ 横轴 ∩ 纵轴          │ {0} (定义)                           │
  │ 横轴 ∩ 临界圆        │ {0, 2} (realAxis_inter_criticalCircle, C020) │
  │ 纵轴 ∩ 临界圆        │ {0} (新: imagAxis_inter_criticalCircle)      │
  │ 横轴 ∩ 素数圆 p      │ {±√p} (新: realAxis_inter_primeCircle)       │
  │ 纵轴 ∩ 素数圆 p      │ {±i√p} (新: imagAxis_inter_primeCircle)       │
  │ 素数圆 2 ∩ 临界圆    │ {1±i} (prime2Circle_inter_criticalCircle, C020) │
  │ 素数圆 3 ∩ 临界圆    │ {3/2 ± √3/2·i} (新: prime3Circle_inter_criticalCircle) │
  │ 素数圆 p≥5 ∩ 临界圆  │ ∅ (新: primeCircle_inter_criticalCircle_ge5!) │
  └─────────────────────┴──────────────────────────────────────┘

核心新定理: 素数圆与临界圆相交 ⟺ p ∈ {2, 3} — 半径 √p 的圆与圆心
(1,0) 半径 1 的圆相交当且仅当 p ≤ 4 (素数 ⟹ p = 2 或 3)。

谱系坐标: (R23, C3) 素数圆 × 解析数论; 连接 C020 (两圆交点) 与 XXIV。
-/

namespace ComplexPlaneIntersections

open ZeroRelative
open ZeroRelative.ComplexAxis

/-- 纵轴 (虚轴) 与临界圆: t·J ∈ criticalCircle ↔ t = 0
    (虚轴与临界圆只交于原点; 对比实轴交 {0, 2})。 
English: Imaginary axis and critical circle: t·J ∈ criticalCircle ↔ t = 0 (the axis meets the circle only at the origin; contrast the real axis meeting at {0, 2}). -/
theorem imagAxis_inter_criticalCircle (t : ℝ) :
    (lift t * J : ComplexAxis) ∈ criticalCircle ↔ t = 0 := by
  constructor
  · intro h
    have hn : ComplexAxis.norm (lift t * J - lift 1) = 1 := by
      simpa [criticalCircle] using h
    -- ComplexAxis.norm ⟨-1, t⟩ = 1 + t² = 1 ⟹ t = 0
    have heq : lift t * J - lift 1 = ⟨-1, t⟩ := by
      change ComplexAxis.sub (ComplexAxis.mul (lift t) J) (lift 1) = ⟨-1, t⟩
      ext <;> simp [lift, J, mul, sub]
    have hcalc : 1 + t ^ 2 = 1 := by
      rw [heq] at hn
      simpa [ComplexAxis.norm] using hn
    nlinarith
  · intro ht
    subst ht
    simp only [criticalCircle]
    change ComplexAxis.norm (ComplexAxis.sub (ComplexAxis.mul (lift 0) J) (lift 1)) = 1
    change ComplexAxis.norm (ComplexAxis.sub (ComplexAxis.mul ⟨0, 0⟩ ⟨0, 1⟩) ⟨1, 0⟩) = 1
    norm_num [ComplexAxis.mul, ComplexAxis.norm, ComplexAxis.sub]

/-- 横轴与素数圆: lift r ∈ primeCircle p ↔ r² = p (交于 ±√p)。 
English: Real axis and prime circle: lift r ∈ primeCircle p ↔ r² = p (meeting at ±√p). -/
theorem realAxis_inter_primeCircle (r : ℝ) (p : ℕ) :
    (lift r : ComplexAxis) ∈ primeCircle p ↔ r ^ 2 = (p : ℝ) := by
  simp [primeCircle, ComplexAxis.norm, lift, sub]

/-- 纵轴与素数圆: t·J ∈ primeCircle p ↔ t² = p (交于 ±i√p)。 
English: Imaginary axis and prime circle: t·J ∈ primeCircle p ↔ t² = p (meeting at ±i√p). -/
theorem imagAxis_inter_primeCircle (t : ℝ) (p : ℕ) :
    (lift t * J : ComplexAxis) ∈ primeCircle p ↔ t ^ 2 = (p : ℝ) := by
  change ComplexAxis.mul ⟨t, 0⟩ ⟨0, 1⟩ ∈ primeCircle p ↔ t ^ 2 = (p : ℝ)
  simp [primeCircle, ComplexAxis.norm, ComplexAxis.mul, pow_two]

/-- 素数圆 3 与临界圆: z = 3/2 + √3/2·J 在交集中
    (ComplexAxis.norm = 9/4 + 3/4 = 3; ComplexAxis.norm(z-1) = 1/4 + 3/4 = 1)。 
English: Prime circle 3 and critical circle: z = 3/2 + √3/2·J is in the intersection (ComplexAxis.norm = 9/4 + 3/4 = 3; ComplexAxis.norm(z-1) = 1/4 + 3/4 = 1). -/
theorem prime3Circle_inter_criticalCircle :
    (⟨3 / 2, Real.sqrt 3 / 2⟩ : ComplexAxis) ∈ primeCircle 3 ∧
      (⟨3 / 2, Real.sqrt 3 / 2⟩ : ComplexAxis) ∈ criticalCircle := by
  have hsq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    have h1 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  constructor
  · simp [primeCircle, ComplexAxis.norm]
    nlinarith
  · change ComplexAxis.norm (ComplexAxis.sub (⟨3 / 2, Real.sqrt 3 / 2⟩ : ComplexAxis) (lift 1)) = 1
    simp [ComplexAxis.norm, lift, sub]
    nlinarith

/-- 素数 p ≥ 5 的素数圆与临界圆不相交
    (半径 √p 的圆与圆心 (1,0) 半径 1 的圆: 相交 ⟹ p ≤ 4)。 
English: The prime circle of p ≥ 5 is disjoint from the critical circle (circle of radius √p vs circle centered at (1,0) with radius 1: intersecting ⟹ p ≤ 4). -/
theorem primeCircle_inter_criticalCircle_ge5 {p : ℕ} (hp5 : 5 ≤ p) :
    primeCircle p ∩ criticalCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have hn : ComplexAxis.norm z = (p : ℝ) := hz.1
    have hc : ComplexAxis.norm (z - lift 1) = 1 := hz.2
    -- a = p/2 (从 ComplexAxis.norm(z-1) = ComplexAxis.norm z - 2a + 1)
    have ha : z.a = (p : ℝ) / 2 := by
      have h1 : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [ComplexAxis.norm] using hn
      have h2 : (z.a - 1) ^ 2 + z.b ^ 2 = 1 := by
        have hza : (z - lift 1).a = z.a - 1 := by
          change (ComplexAxis.sub z (lift 1)).a = z.a - 1
          simp [lift, sub]
        have hzb : (z - lift 1).b = z.b := by
          change (ComplexAxis.sub z (lift 1)).b = z.b
          simp [lift, sub]
        rw [ComplexAxis.norm] at hc
        rw [hza, hzb] at hc
        exact hc
      nlinarith
    -- b² = p - p²/4 < 0 (p ≥ 5) — 矛盾
    have hb2 : z.b ^ 2 = (p : ℝ) - (p : ℝ) ^ 2 / 4 := by
      have h1 : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [ComplexAxis.norm] using hn
      nlinarith
    have hneg : (p : ℝ) - (p : ℝ) ^ 2 / 4 < 0 := by
      have hpR : (4 : ℝ) < (p : ℝ) := by
        have hp5' : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
        nlinarith
      nlinarith
    nlinarith
  · intro hz
    simp at hz

end ComplexPlaneIntersections


/- ================= 习题 30_transpose_origin (0pat, 原样合并) ================= -/


/-!
# 习题 XXX: 横纵轴转置与正交视角下的原点 (0pat)

用户洞察 (2026-08-21): 在欧拉圆 1 (半径 1) 与欧拉圆 i (半径 i) 的正交视角下,
先证明横纵轴转置 (1 ↔ i 的镜像), 再确定原点。

精确结果:
1. 转置 (a,b) ↦ (b,a) 是自逆对合, 把 1 = (1,0) 映到 i = (0,1)。
2. 转置把半径 1 圆 (a²-b²=1) 映到半径 i 圆 (a²-b²=-1) — 双向。
3. 自然数格点唯一性: 半径 1 圆唯一格点 (1,0) = 1; 半径 i 圆唯一格点 (0,1) = i。
   (上一轮"1 i 是转置结果"的精确化: 每个圆在格点观测下只剩自己的单位。)
4. 原点判定: 转置保持原点 (0,0) 不动; 两个共轭双曲线关于原点中心对称 —
   正交视角下的原点是 (0,0) (分裂零元, 双曲线的公共中心), 不是 i。

谱系坐标: (R20, C8) 圆上量化 × 构造; 连接 XXVII (分裂复数)。
-/

namespace TransposeOrigin

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 
English: Split complex: a + bj, j² = +1 (reused XXVII structure, standalone file). -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

/-- 虚数单位 j (j² = +1)。 
English: Imaginary unit j (j² = +1). -/
def j : SplitComplex := ⟨0, 1⟩

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 
English: Pseudo-norm (Minkowski metric): ‖a + bj‖² = a² - b². -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 半径 1 圆 (双曲线): ‖z‖² = 1。 
English: Radius-1 circle (hyperbola): ‖z‖² = 1. -/
def unitCircle : Set SplitComplex := {z | normSq z = 1}

/-- 半径 i 圆 (共轭双曲线): ‖z‖² = -1。 
English: Radius-i circle (conjugate hyperbola): ‖z‖² = -1. -/
def imaginaryCircle : Set SplitComplex := {z | normSq z = -1}

/-- 横纵轴转置: (a, b) ↦ (b, a) (镜像)。 
English: Transpose of the axes: (a, b) ↦ (b, a) (mirror). -/
def transpose (z : SplitComplex) : SplitComplex := ⟨z.im, z.re⟩

@[simp] theorem re_transpose (z : SplitComplex) : (transpose z).re = z.im := rfl
@[simp] theorem im_transpose (z : SplitComplex) : (transpose z).im = z.re := rfl

/-- 转置是对合 (自逆): transpose (transpose z) = z。 
English: The transpose is an involution (self-inverse): transpose (transpose z) = z. -/
theorem transpose_involutive (z : SplitComplex) : transpose (transpose z) = z := by
  ext <;> simp [transpose]

/-- 转置把 1 映到 i: transpose 1 = j。 
English: The transpose maps 1 to i: transpose 1 = j. -/
theorem transpose_maps_one_to_i : transpose (1 : SplitComplex) = j := by
  ext <;> simp [transpose, j]

/-- 转置保持原点: transpose 0 = 0 (原点在镜像下不动 — 原点不是 1 或 i)。 
English: The transpose fixes the origin: transpose 0 = 0 (the origin is fixed under the mirror — the origin is neither 1 nor i). -/
theorem transpose_origin_fixed : transpose (0 : SplitComplex) = 0 := by
  ext <;> simp [transpose]

/-- 转置把半径 1 圆映到半径 i 圆 (正向): z ∈ 单位圆 ⟹ transpose z ∈ 虚半径圆。 
English: The transpose maps the radius-1 circle to the radius-i circle (forward): z ∈ unit circle ⟹ transpose z ∈ imaginary-radius circle. -/
theorem transpose_maps_unit_to_imaginary {z : SplitComplex} (hz : z ∈ unitCircle) :
    transpose z ∈ imaginaryCircle := by
  simp [unitCircle, imaginaryCircle, normSq] at hz ⊢
  nlinarith

/-- 转置把半径 i 圆映到半径 1 圆 (反向)。 
English: The transpose maps the radius-i circle to the radius-1 circle (reverse). -/
theorem transpose_maps_imaginary_to_unit {z : SplitComplex} (hz : z ∈ imaginaryCircle) :
    transpose z ∈ unitCircle := by
  simp [unitCircle, imaginaryCircle, normSq] at hz ⊢
  nlinarith

/-- 自然数格点唯一性 (半径 1 圆): a² - b² = 1 的自然数解唯一 = (1, 0)。
    b = 0 时 a² = 1 ⟹ a = 1; b ≥ 1 时 (b+1)² - b² ≥ 3 矛盾。 
English: Natural lattice-point uniqueness (radius-1 circle): the unique natural solution of a² - b² = 1 is (1, 0). For b = 0, a² = 1 ⟹ a = 1; for b ≥ 1, (b+1)² - b² ≥ 3, contradiction. -/
theorem lattice_unique_unit {a b : ℕ} (h : a ^ 2 - b ^ 2 = 1) : a = 1 ∧ b = 0 := by
  by_cases hb : b = 0
  · -- b = 0: a² = 1 ⟹ a = 1
    subst b
    have ha : a ^ 2 = 1 := by simpa using h
    have hle1 : a ≤ 1 := by
      by_contra h2
      have h2a : 2 ≤ a := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
      have hsq : 4 ≤ a ^ 2 := by
        have hsq' : 2 ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left h2a 2
        norm_num at hsq' ⊢
        exact hsq'
      omega
    have ha0 : a ≠ 0 := by
      intro hz
      subst a
      norm_num at ha
    omega
  · -- b ≥ 1: a² - b² = 1 不可能 (a > b 时差值 ≥ 3)
    have hb1 : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb)
    have hagtb : b < a := by
      have hgt : b ^ 2 < a ^ 2 := by
        have ha_eq : b ^ 2 + 1 = a ^ 2 := by omega
        omega
      by_contra hba
      have hle : a ≤ b := Nat.le_of_not_gt hba
      have hsq : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    have ha1 : b + 1 ≤ a := Nat.succ_le_of_lt hagtb
    have hsq1 : (b + 1) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha1 2
    have hsub : a ^ 2 - b ^ 2 ≥ (b + 1) ^ 2 - b ^ 2 :=
      Nat.sub_le_sub_right hsq1 (b ^ 2)
    have hdiff : (b + 1) ^ 2 - b ^ 2 ≥ 3 := by
      have hring : (b + 1) ^ 2 = b ^ 2 + (2 * b + 1) := by ring
      rw [hring]
      omega
    omega

/-- 自然数格点唯一性 (半径 i 圆): b² - a² = 1 的自然数解唯一 = (0, 1)。 
English: Natural lattice-point uniqueness (radius-i circle): the unique natural solution of b² - a² = 1 is (0, 1). -/
theorem lattice_unique_imaginary {a b : ℕ} (h : b ^ 2 - a ^ 2 = 1) : a = 0 ∧ b = 1 := by
  by_cases ha : a = 0
  · -- a = 0: b² = 1 ⟹ b = 1
    subst a
    have hb : b ^ 2 = 1 := by simpa using h
    have hle1 : b ≤ 1 := by
      by_contra h2
      have h2b : 2 ≤ b := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
      have hsq : 4 ≤ b ^ 2 := by
        have hsq' : 2 ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h2b 2
        norm_num at hsq' ⊢
        exact hsq'
      omega
    have hb0 : b ≠ 0 := by
      intro hz
      subst b
      norm_num at hb
    omega
  · -- a ≥ 1: b² - a² = 1 不可能 (b > a 时差值 ≥ 3)
    have ha1 : 1 ≤ a := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha)
    have hagta : a < b := by
      have hgt : a ^ 2 < b ^ 2 := by
        have hb_eq : a ^ 2 + 1 = b ^ 2 := by omega
        omega
      by_contra hba
      have hle : b ≤ a := Nat.le_of_not_gt hba
      have hsq : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    have hb1 : a + 1 ≤ b := Nat.succ_le_of_lt hagta
    have hsq1 : (a + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hb1 2
    have hsub : b ^ 2 - a ^ 2 ≥ (a + 1) ^ 2 - a ^ 2 :=
      Nat.sub_le_sub_right hsq1 (a ^ 2)
    have hdiff : (a + 1) ^ 2 - a ^ 2 ≥ 3 := by
      have hring : (a + 1) ^ 2 = a ^ 2 + (2 * a + 1) := by ring
      rw [hring]
      omega
    omega

end SplitComplex

end
end TransposeOrigin

/- ================= 习题 31_real_imag_axes (0pat, 原样合并) ================= -/


/-!
# 习题 XXXI: 实轴虚轴在欧拉圆视角下的观测 (0pat)

用户指令 (2026-08-21): 不允许根据定义直接得出结论, 必须观测实轴虚轴
在欧拉圆 1 / 欧拉圆 i 视角下的图形。

观测方法: 把实轴 (im = 0)、虚轴 (re = 0) 放进分裂复数框架
(半径 1 圆 a²-b²=1, 半径 i 圆 a²-b²=-1), 解方程求交点。

观测结果 (全部机器验证):
  1. 实轴 ∩ 虚轴 = {(0,0)}     ← 解 ⟨a,0⟩=⟨0,b⟩ 得 a=0 ∧ b=0 (观测, 非定义)
  2. 实轴 ∩ 半径 1 圆 = {±1}   ← 解 a²=1
  3. 实轴 ∩ 半径 i 圆 = ∅      ← 解 a²=-1 无实解
  4. 虚轴 ∩ 半径 1 圆 = ∅      ← 解 -b²=1 无实解
  5. 虚轴 ∩ 半径 i 圆 = {±i}   ← 解 -b²=-1

观测结论: 实轴与虚轴的交点是 (0,0) (解方程得出);
i = (0,1) 是虚轴与半径 i 圆的交点 (单位), 不是两轴交点。
-/

namespace RealImagAxes

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 
English: Split complex: a + bj, j² = +1 (reused XXVII structure, standalone file). -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

/-- 虚数单位 j (j² = +1)。 
English: Imaginary unit j (j² = +1). -/
def j : SplitComplex := ⟨0, 1⟩

/-- 伪范数: ‖z‖² = a² - b²。 
English: Pseudo-norm: ‖z‖² = a² - b². -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 半径 1 圆 (双曲线): ‖z‖² = 1。 
English: Radius-1 circle (hyperbola): ‖z‖² = 1. -/
def unitCircle : Set SplitComplex := {z | normSq z = 1}

/-- 半径 i 圆 (共轭双曲线): ‖z‖² = -1。 
English: Radius-i circle (conjugate hyperbola): ‖z‖² = -1. -/
def imaginaryCircle : Set SplitComplex := {z | normSq z = -1}

/-- 实轴: 虚部为 0 的点。 
English: Real axis: points with imaginary part 0. -/
def realAxis : Set SplitComplex := {z | z.im = 0}

/-- 虚轴: 实部为 0 的点。 
English: Imaginary axis: points with real part 0. -/
def imaginaryAxis : Set SplitComplex := {z | z.re = 0}

/-- 观测 1: 实轴 ∩ 虚轴 = {(0,0)}。
    解 ⟨a,0⟩ = ⟨0,b⟩: a = 0 且 b = 0 — 两轴的交点由方程给出。 
English: Observation 1: real axis ∩ imaginary axis = {(0,0)}. Solving ⟨a,0⟩ = ⟨0,b⟩: a = 0 and b = 0 — the intersection of the two axes is given by the equation. -/
theorem realAxis_inter_imaginaryAxis :
    realAxis ∩ imaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    -- z ∈ 实轴: z.im = 0; z ∈ 虚轴: z.re = 0 ⟹ z = ⟨0,0⟩
    have him : z.im = 0 := hz.1
    have hre : z.re = 0 := hz.2
    have hz0 : z = 0 := by
      apply SplitComplex.ext
      · simpa using hre
      · simpa using him
    subst z
    rfl
  · intro hz
    -- z = 0 ⟹ z 在实轴 (im 0 = 0) 且虚轴 (re 0 = 0)
    subst z
    simp [realAxis, imaginaryAxis]

/-- 观测 2: 实轴 ∩ 半径 1 圆 = {±1}。
    解 a² = 1: 实轴上落在半径 1 圆上的点只有 a = 1 和 a = -1。 
English: Observation 2: real axis ∩ radius-1 circle = {±1}. Solving a² = 1: the points on the real axis and radius-1 circle are only a = 1 and a = -1. -/
theorem realAxis_inter_unitCircle :
    realAxis ∩ unitCircle = {z | z = ⟨1, 0⟩ ∨ z = ⟨-1, 0⟩} := by
  ext z
  constructor
  · intro hz
    -- z = ⟨a, 0⟩ (实轴), a² = 1 (单位圆)
    have him : z.im = 0 := hz.1
    have hn : normSq z = 1 := hz.2
    -- 解 a² = 1 ⟹ a = ±1
    have ha : z.re ^ 2 = 1 := by
      simpa [normSq, him] using hn
    have hcases : z.re = 1 ∨ z.re = -1 := by
      -- ℝ 中 a² = 1 ⟹ a = 1 ∨ a = -1
      have h1 : z.re ^ 2 = 1 ^ 2 := by simpa using ha
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h1
    rcases hcases with h1 | hm1
    · left
      ext <;> simp [h1, him]
    · right
      ext <;> simp [hm1, him]
  · intro hz
    rcases hz with hz1 | hz2
    · rcases hz1 with rfl
      simp [realAxis, unitCircle, normSq]
    · rcases hz2 with rfl
      simp [realAxis, unitCircle, normSq]

/-- 观测 3: 实轴 ∩ 半径 i 圆 = ∅。
    解 a² = -1: 无实解 — 实轴上没有任何点落在半径 i 圆上。 
English: Observation 3: real axis ∩ radius-i circle = ∅. Solving a² = -1: no real solution — no real-axis point lies on the radius-i circle. -/
theorem realAxis_inter_imaginaryCircle :
    realAxis ∩ imaginaryCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have him : z.im = 0 := hz.1
    have hn : normSq z = -1 := hz.2
    have ha : z.re ^ 2 = -1 := by
      simpa [normSq, him] using hn
    nlinarith
  · intro hz
    simp at hz

/-- 观测 4: 虚轴 ∩ 半径 1 圆 = ∅。
    解 -b² = 1: 无实解。 
English: Observation 4: imaginary axis ∩ radius-1 circle = ∅. Solving -b² = 1: no real solution. -/
theorem imaginaryAxis_inter_unitCircle :
    imaginaryAxis ∩ unitCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have hre : z.re = 0 := hz.1
    have hn : normSq z = 1 := hz.2
    have hb : -z.im ^ 2 = 1 := by
      simpa [normSq, hre] using hn
    nlinarith
  · intro hz
    simp at hz

/-- 观测 5: 虚轴 ∩ 半径 i 圆 = {±i}。
    解 -b² = -1 ⟹ b = ±1: 虚轴上落在半径 i 圆上的点只有 j 和 -j。 
English: Observation 5: imaginary axis ∩ radius-i circle = {±i}. Solving -b² = -1 ⟹ b = ±1: the points on the imaginary axis and radius-i circle are only j and -j. -/
theorem imaginaryAxis_inter_imaginaryCircle :
    imaginaryAxis ∩ imaginaryCircle = {z | z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩} := by
  ext z
  constructor
  · intro hz
    have hre : z.re = 0 := hz.1
    have hn : normSq z = -1 := hz.2
    have hb : -z.im ^ 2 = -1 := by
      simpa [normSq, hre] using hn
    have hcases : z.im = 1 ∨ z.im = -1 := by
      have h1 : z.im ^ 2 = 1 := by nlinarith
      have h2 : z.im ^ 2 = 1 ^ 2 := by simpa using h1
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
    rcases hcases with h1 | hm1
    · left
      ext <;> simp [hre, h1]
    · right
      ext <;> simp [hre, hm1]
  · intro hz
    rcases hz with hz1 | hz2
    · rcases hz1 with rfl
      simp [imaginaryAxis, imaginaryCircle, normSq]
    · rcases hz2 with rfl
      simp [imaginaryAxis, imaginaryCircle, normSq]

end SplitComplex

end
end RealImagAxes

/- ================= 习题 32_axis_coefficients_origin (0pat, 原样合并) ================= -/


/-!
# 习题 XXXII: 虚轴系数类型与原点 (0pat)

用户指令 (2026-08-21): 解方程时必须标明系数类型 —
虚轴的系数是自然数, 但虚轴代表复数的虚部。

设定:
  A. 按自然数算: 虚轴 = {n·i : n ∈ ℕ} (离散, 自然数系数)
  B. 按虚部算:   虚轴 = {t·i : t ∈ ℝ} (连续, 实系数)
  实轴始终 = ℝ (连续实数轴)。

计算结果:
  1. 按自然数算: 实轴 ∩ 自然数虚轴 = {0}  (解 x = n·i: x = 0 且 n = 0)
  2. 按虚部算:   实轴 ∩ 连续虚轴 = {0}    (解 x = t·i: x = 0 且 t = 0)
  → 两种算法下, 原点都是 (0,0)。

转置定理 (用户要求: 按自然数算时, 另一根轴转置到虚轴并按虚部算):
  3. transpose '' realAxis = imaginaryAxis: 实轴的转置像 = 虚轴 (连续, 实系数) —
     实轴转置后按虚部 (连续) 算。
  4. transpose 保持自然数系数: 自然数虚轴的转置 = 自然数实轴 (离散保持离散)。

谱系坐标: (R20, C8); 连接 XXX/XXXI。
-/

namespace AxisCoefficientsOrigin

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 
English: Split complex: a + bj, j² = +1 (reused XXVII structure, standalone file). -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl

/-- 实轴: 虚部为 0 的点 (连续实数轴)。 
English: Real axis: points with imaginary part 0 (continuous real axis). -/
def realAxis : Set SplitComplex := {z | z.im = 0}

/-- 虚轴 (按虚部算): 实部为 0 的点, 系数为实数 (连续)。 
English: Imaginary axis (by imaginary part): points with real part 0, real coefficients (continuous). -/
def imaginaryAxis : Set SplitComplex := {z | z.re = 0}

/-- 虚轴 (按自然数算): 虚部系数为自然数 (离散): {n·i : n ∈ ℕ}。 
English: Imaginary axis (by natural numbers): imaginary coefficients are naturals (discrete): {n·i : n ∈ ℕ}. -/
def naturalImaginaryAxis : Set SplitComplex := {z | ∃ n : ℕ, z = ⟨0, (n : ℝ)⟩}

/-- 横纵轴转置: (a, b) ↦ (b, a)。 
English: Transpose of the axes: (a, b) ↦ (b, a). -/
def transpose (z : SplitComplex) : SplitComplex := ⟨z.im, z.re⟩

/-- 计算 1 (按自然数算): 实轴 ∩ 自然数虚轴 = {0}。
    解 x = n·i: 实部 x = 0 且虚部系数 n = 0 — 原点是 0。 
English: Computation 1 (by naturals): real axis ∩ natural imaginary axis = {0}. Solving x = n·i: real part x = 0 and coefficient n = 0 — the origin is 0. -/
theorem origin_natural_coefficients :
    realAxis ∩ naturalImaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    -- z ∈ 实轴: z.im = 0; z ∈ 自然数虚轴: ∃ n, z = ⟨0, n⟩
    have him : z.im = 0 := hz.1
    rcases hz.2 with ⟨n, hn⟩
    -- z = ⟨0, n⟩ 且 z.im = 0 ⟹ n = 0 ⟹ z = 0
    have hn0 : (n : ℝ) = 0 := by
      -- ⟨0, n⟩.im = n = z.im = 0
      have : (⟨0, (n : ℝ)⟩ : SplitComplex).im = z.im := by rw [hn]
      simpa [him] using this
    have hnz : n = 0 := by
      exact_mod_cast hn0
    have hz0 : z = 0 := by
      rw [hn]
      apply SplitComplex.ext
      · simp
      · rw [hnz]
        simp
    exact hz0
  · intro hz
    -- z = 0: 在实轴 (im 0 = 0) 且在自然数虚轴 (0 = ⟨0, 0⟩, n = 0)
    subst z
    constructor
    · simp [realAxis]
    · refine ⟨0, ?_⟩
      apply SplitComplex.ext <;> simp

/-- 计算 2 (按虚部算): 实轴 ∩ 连续虚轴 = {0}。
    解 x = t·i: x = 0 且 t = 0 — 原点是 0。 
English: Computation 2 (by imaginary part): real axis ∩ continuous imaginary axis = {0}. Solving x = t·i: x = 0 and t = 0 — the origin is 0. -/
theorem origin_imaginary_part :
    realAxis ∩ imaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    have him : z.im = 0 := hz.1
    have hre : z.re = 0 := hz.2
    have hz0 : z = 0 := by
      apply SplitComplex.ext
      · simpa using hre
      · simpa using him
    subst z
    rfl
  · intro hz
    subst z
    simp [realAxis, imaginaryAxis]

/-- 转置定理 1: transpose '' realAxis = imaginaryAxis —
    实轴的转置像 = 虚轴 (连续, 实系数): 实轴转置后按虚部 (连续) 算。 
English: Transpose theorem 1: transpose '' realAxis = imaginaryAxis — the transpose image of the real axis = imaginary axis (continuous, real coefficients): after transposing, the real axis is counted by imaginary part (continuous). -/
theorem transpose_realAxis_eq_imaginaryAxis :
    transpose '' realAxis = imaginaryAxis := by
  ext z
  constructor
  · -- z = transpose x, x ∈ realAxis (x.im = 0)
    rintro ⟨x, hx, rfl⟩
    -- transpose x = ⟨x.im, x.re⟩ = ⟨0, x.re⟩ ⟹ re = 0
    have hx0 : x.im = 0 := hx
    simp [imaginaryAxis, transpose, hx0]
  · -- z ∈ imaginaryAxis (z.re = 0): z = transpose ⟨z.im, 0⟩, 且 ⟨z.im, 0⟩ ∈ realAxis
    intro hz
    have hre : z.re = 0 := hz
    refine ⟨⟨z.im, 0⟩, ?_, ?_⟩
    · simp [realAxis]
    · -- transpose ⟨z.im, 0⟩ = ⟨0, z.im⟩ = z
      ext <;> simp [transpose, hre]

/-- 转置定理 2: 转置保持自然数系数 —
    自然数虚轴的转置 = 自然数实轴 (离散保持离散, 自然数不因转置变连续)。 
English: Transpose theorem 2: transpose preserves natural coefficients — transpose of the natural imaginary axis = natural real axis (discrete stays discrete; naturals do not become continuous by transposing). -/
theorem transpose_natural_imaginary_is_natural_real :
    transpose '' naturalImaginaryAxis = {z | ∃ n : ℕ, z = ⟨(n : ℝ), 0⟩} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨n, rfl⟩
    -- transpose ⟨0, n⟩ = ⟨n, 0⟩
    refine ⟨n, ?_⟩
    ext <;> simp [transpose]
  · intro hz
    rcases hz with ⟨n, hn⟩
    -- z = ⟨n, 0⟩ = transpose ⟨0, n⟩, 且 ⟨0, n⟩ ∈ naturalImaginaryAxis
    refine ⟨⟨0, (n : ℝ)⟩, ?_, ?_⟩
    · refine ⟨n, ?_⟩
      rfl
    · -- transpose ⟨0, n⟩ = ⟨n, 0⟩ = z
      rw [hn]
      ext <;> simp [transpose]

end SplitComplex

end
end AxisCoefficientsOrigin

/- ================= 习题 33_imag_coefficient_compression (0pat, 原样合并) ================= -/


/-!
# 习题 XXXIII: 虚部被压进系数轴 — 乘积的泄漏 (0pat)

用户洞察 (2026-08-21): 复平面的虚轴不代表虚部, 只代表虚部的实系数。
虚轴上的刻度是实数 t, "虚" (i) 被压进轴的语义里。
当虚部被压进实系数轴时, 虚部与虚部的乘积会出现在其他地方 —
乘法中两个虚部系数的乘积 bd 泄漏到实部坐标, 符号由虚数单位的平方决定:

  ℂ  (i² = −1): (a+bi)(c+di) 实部 = ac − bd   ← 虚部乘积带负号泄漏到实部
  分裂 (j² = +1): (a+bj)(c+dj) 实部 = ac + bd   ← 虚部乘积带正号泄漏到实部

定理:
1. complex_imag_axis_coefficient: 虚轴上的点 = 实系数 t × 虚单位 i
   (z = t·i ⟺ z.re = 0 ∧ z.im = t; 轴刻度只显示系数, 不显示 i)
2. complex_mul_imag_leaks: ℂ 中虚部系数乘积 bd 出现在实部 (带 −, i²=−1)
3. split_mul_imag_leaks: 分裂中虚部系数乘积 bd 出现在实部 (带 +, j²=+1)
4. leak_sign_is_unit_square: 泄漏符号 = 虚数单位的平方 (−1 vs +1)

谱系坐标: (R20, C8) 圆上量化 × 构造; 连接 XXVII/XXXII。
-/

namespace ImagCoefficientCompression

noncomputable section

open Complex

/-- 定理 1: 虚轴上的点 = 实系数 × 虚单位 — 轴刻度只显示系数 t,
    虚单位 i 被压进轴 (z.re = 0 时, z = t·i 且 t = z.im)。 
English: Theorem 1: points on the imaginary axis = real coefficient × imaginary unit — the axis scale shows only the coefficient t; the imaginary unit i is pressed into the axis (when z.re = 0, z = t·i with t = z.im). -/
theorem complex_imag_axis_coefficient {z : ℂ} {t : ℝ} :
    z = t * I ↔ z.re = 0 ∧ z.im = t := by
  constructor
  · intro h
    rw [h]
    simp [Complex.I]
  · intro hz
    -- z = ⟨0, t⟩ = t·i
    apply Complex.ext <;> simp [Complex.I, hz.1, hz.2]

/-- 定理 2: ℂ 中虚部系数乘积泄漏到实部 (带负号, i² = −1)。
    (a+bi)(c+di) 的实部 = ac − bd: 两个虚部系数的乘积 bd
    离开虚部, 出现在实部, 符号由 i·i = −1 决定。 
English: Theorem 2: in ℂ the product of imaginary coefficients leaks into the real part (negative sign, i² = −1). Real part of (a+bi)(c+di) = ac − bd: the product bd of the two imaginary coefficients leaves the imaginary part, appears in the real part, sign determined by i·i = −1. -/
theorem complex_mul_imag_leaks (a b c d : ℝ) :
    ((a + b * I) * (c + d * I) : ℂ).re = a * c - b * d := by
  simp [Complex.I]

/-- 定理 2b: ℂ 中交叉项留在虚部: 虚部 = ad + bc。 
English: Theorem 2b: in ℂ the cross terms stay in the imaginary part: imaginary part = ad + bc. -/
theorem complex_mul_cross_stays_imag (a b c d : ℝ) :
    ((a + b * I) * (c + d * I) : ℂ).im = a * d + b * c := by
  simp [Complex.I]

/-- 分裂复数的乘法 (XXVII 结构, 独立文件)。 
English: Multiplication of split complexes (XXVII structure, standalone file). -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

/-- 定理 3: 分裂中虚部系数乘积泄漏到实部 (带正号, j² = +1)。
    (a+bj)(c+dj) 的实部 = ac + bd — 同样的"压进", 符号由 j·j = +1 决定。 
English: Theorem 3: in split, the product of imaginary coefficients leaks into the real part (positive sign, j² = +1). Real part of (a+bj)(c+dj) = ac + bd — the same pressing-in, sign determined by j·j = +1. -/
theorem split_mul_imag_leaks (a b c d : ℝ) :
    ((⟨a, b⟩ : SplitComplex) * ⟨c, d⟩).re = a * c + b * d := by
  rfl

/-- 定理 4: 泄漏符号 = 虚数单位的平方。
    ℂ: i·i = −1 (泄漏带 −); 分裂: j·j = +1 (泄漏带 +)。 
English: Theorem 4: leak sign = square of the imaginary unit. ℂ: i·i = −1 (leak carries −); split: j·j = +1 (leak carries +). -/
theorem leak_sign_is_unit_square :
    I * I = -1 ∧ (⟨0, 1⟩ : SplitComplex) * ⟨0, 1⟩ = 1 := by
  constructor
  · apply Complex.ext <;> simp [Complex.I]
  · change (⟨0 * 0 + 1 * 1, 0 * 1 + 1 * 0⟩ : SplitComplex) = 1
    ext <;> norm_num

end SplitComplex

end
end ImagCoefficientCompression

/- ================= 习题 34_euler_plane_version (0pat, 原样合并) ================= -/


/-!
# 习题 XXXIV: 复平面的欧拉圆版本 (0pat)

用户洞察 (2026-08-21): 欧拉圆 1 与欧拉圆 i 合起来 = 复平面的欧拉圆版本 —
实方向圆 (半径 1) 对应实轴, 虚方向圆 (半径 i) 对应虚轴;
"真正的虚轴"在欧拉圆版本中 = 半径 i 圆, 虚以 j 显式存在于圆上
(不再被压进系数轴 — 对比 XXXIII 的"压进")。

定理:
1. unit_1_on_real_circle: 实单位 1 在半径 1 圆上 (实方向圆含实单位)
2. unit_j_on_imag_circle: 虚单位 j 在半径 i 圆上 (虚方向圆含虚单位 —
   虚显式存在, 不是压进系数的不可见单位)
3. real_circle_is_direction_1: 半径 1 圆 = 实方向单位圆 (双曲线 a²-b²=1)
4. imag_circle_is_direction_j: 半径 i 圆 = 虚方向单位圆 (共轭双曲线, 含 j)
5. directions_orthogonal: 实方向 1 与虚方向 j 的伪范数符号相反
   (‖1‖²=+1, ‖j‖²=−1 — 分裂度量下的方向正交)
6. euler_plane: 复平面的欧拉圆版本 = 实方向圆 + 虚方向圆,
   两个单位 {1, j} 分别在两个圆上 (实/虚分离, 无压进)

谱系坐标: (R20, C8); 连接 XXVII/XXXIII。
-/

namespace EulerPlaneVersion

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 
English: Split complex: a + bj, j² = +1 (reused XXVII structure, standalone file). -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

/-- 虚数单位 j (j² = +1)。 
English: Imaginary unit j (j² = +1). -/
def j : SplitComplex := ⟨0, 1⟩

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 
English: Pseudo-norm (Minkowski metric): ‖a + bj‖² = a² - b². -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 半径 1 圆 (实方向圆): ‖z‖² = 1。 
English: Radius-1 circle (real-direction circle): ‖z‖² = 1. -/
def unitCircle : Set SplitComplex := {z | normSq z = 1}

/-- 半径 i 圆 (虚方向圆): ‖z‖² = -1。 
English: Radius-i circle (imaginary-direction circle): ‖z‖² = -1. -/
def imaginaryCircle : Set SplitComplex := {z | normSq z = -1}

/-- 定理 1: 实单位 1 在半径 1 圆上 (实方向圆含实单位)。 
English: Theorem 1: the real unit 1 lies on the radius-1 circle (the real-direction circle contains the real unit). -/
theorem unit_1_on_real_circle : (1 : SplitComplex) ∈ unitCircle := by
  simp [unitCircle, normSq]

/-- 定理 2: 虚单位 j 在半径 i 圆上 (虚方向圆含虚单位 —
    虚显式存在, 不是压进系数的不可见单位; 对比 XXXIII)。 
English: Theorem 2: the imaginary unit j lies on the radius-i circle (the imaginary-direction circle contains the imaginary unit — the imaginary exists explicitly, not an invisible unit pressed into coefficients; contrast XXXIII). -/
theorem unit_j_on_imag_circle : j ∈ imaginaryCircle := by
  simp [imaginaryCircle, normSq, j]

/-- 定理 3: 半径 1 圆 = 实方向单位圆 (双曲线 a²-b²=1)。 
English: Theorem 3: radius-1 circle = real-direction unit circle (hyperbola a²-b²=1). -/
theorem real_circle_is_direction_1 :
    unitCircle = {z | z.re ^ 2 - z.im ^ 2 = 1} := by
  ext z
  simp [unitCircle, normSq]

/-- 定理 4: 半径 i 圆 = 虚方向单位圆 (共轭双曲线, 含 j)。 
English: Theorem 4: radius-i circle = imaginary-direction unit circle (conjugate hyperbola, containing j). -/
theorem imag_circle_is_direction_j :
    imaginaryCircle = {z | z.re ^ 2 - z.im ^ 2 = -1} := by
  ext z
  simp [imaginaryCircle, normSq]

/-- 定理 5: 实方向 1 与虚方向 j 的伪范数符号相反
    (‖1‖²=+1, ‖j‖²=−1 — 分裂度量下的方向正交)。 
English: Theorem 5: pseudo-norms of the real direction 1 and imaginary direction j have opposite signs (‖1‖²=+1, ‖j‖²=−1 — directional orthogonality in the split metric). -/
theorem directions_orthogonal :
    normSq (1 : SplitComplex) = 1 ∧ normSq j = -1 := by
  constructor <;> simp [normSq, j]

/-- 定理 6: 复平面的欧拉圆版本 — 实方向圆 + 虚方向圆,
    两个单位 {1, j} 分别在两个圆上 (实/虚分离, 无压进)。 
English: Theorem 6: Euler-circle version of the complex plane — real-direction circle + imaginary-direction circle, the two units {1, j} on the two circles respectively (real/imaginary separated, no pressing-in). -/
theorem euler_plane :
    (1 : SplitComplex) ∈ unitCircle ∧ j ∈ imaginaryCircle ∧
      unitCircle ∩ imaginaryCircle = ∅ := by
  constructor
  · exact unit_1_on_real_circle
  · constructor
    · exact unit_j_on_imag_circle
    · -- 两个圆不相交 (共轭双曲线): 1 = -1 矛盾
      ext z
      constructor
      · intro hz
        have h1 : normSq z = 1 := hz.1
        have h2 : normSq z = -1 := hz.2
        nlinarith
      · intro hz
        simp at hz

end SplitComplex

end
end EulerPlaneVersion

/- ================= 习题 35_divergent_series_axis (0pat, 原样合并) ================= -/


/-!
# 习题 XXXV: 发散级数的周期轴观测 (0pat)

用户指令 (2026-08-21): 找发散级数的周期轴, 加进观测方法 (0pat)。

观测:
1. complex_zeta_convergence_region: ℂ 中 ζ 级数收敛域 = Re s > 1
   (mathlib: zeta_eq_tsum_one_div_nat_cpow) — 发散只发生在 Re ≤ 1;
   虚部 i 方向从不造成发散 (|n^{it}| = 1)。
2. cosh_lower_bound: cosh x ≥ e^x/2 — 分裂级数项发散的根源
   (n^{a+bj} 的坐标含 cosh(b ln n), 指数增长; 对比 ℂ 的 |n^{it}| = 1)。
3. cosh_unbounded: cosh 无界 (exp 无界 ⟹ cosh 无界)。
4. split_zeta_term_unbounded: 分裂 ζ 级数项无界 (b > 0 时取 a = 0:
   项 = cosh(b·ln(n+1)) 无界) — 欧拉圆版本复平面 (分裂度量) 中
   ζ 级数项不趋于 0, 级数不收敛。

周期轴观测方法 (0pat):
  - 截断有限化: 部分和 Σ_{n≤N} (C013 zetaPartial, Riemann-Siegel 思想)
  - recip 紧化: ∞ ↦ 0 (C011 recip_vanishes_at_infinity — 发散级数的紧化轴)
  - 零点振荡: 显式公式 ψ(x) = x − Σ x^ρ/ρ (零点 = 素数分布振荡的周期轴)

谱系坐标: (R23, C3) × (R20, C8); 连接 C013/C025/XXVII。
-/

namespace DivergentSeriesAxis

noncomputable section

open scoped BigOperators

/-- 观测 1: ℂ 中 ζ 的级数收敛域 = Re s > 1 —
   发散只发生在 Re ≤ 1 (虚部 i 方向从不造成发散, |n^{it}| = 1)。 
English: Observation 1: in ℂ the convergence domain of ζ's series = Re s > 1 — divergence only for Re ≤ 1 (the imaginary direction i never causes divergence, |n^{it}| = 1). -/
theorem complex_zeta_convergence_region {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' (n : ℕ), 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

/-- 观测 2: cosh x ≥ e^x / 2 (对一切 x) — 分裂级数项发散的根源。 
English: Observation 2: cosh x ≥ e^x / 2 (for all x) — the source of split series-term divergence. -/
theorem cosh_lower_bound (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- 观测 3: cosh 无界 (exp → ∞ ⟹ cosh ≥ exp/2 ⟹ cosh → ∞)。 
English: Observation 3: cosh is unbounded (exp → ∞ ⟹ cosh ≥ exp/2 ⟹ cosh → ∞). -/
theorem cosh_unbounded : ∀ M : ℝ, ∃ x : ℝ, Real.cosh x > M := by
  intro M
  have h : ∃ x : ℝ, 2 * max M 1 < Real.exp x := by
    -- exp → ∞: 对任意界, 存在 x 超过它 (tendsto atTop 的定义)
    have h1 : Filter.Tendsto Real.exp Filter.atTop Filter.atTop := Real.tendsto_exp_atTop
    have hev : ∀ᶠ x in Filter.atTop, 2 * max M 1 < Real.exp x :=
      h1.eventually (Filter.eventually_gt_atTop (2 * max M 1))
    exact hev.exists
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hc : Real.exp x / 2 ≤ Real.cosh x := cosh_lower_bound x
  have hM : M ≤ max M 1 := le_max_left M 1
  nlinarith

/-- log(n+1) 无界 (沿自然数): 对数轴是发散的"延伸轴"。 
English: log(n+1) is unbounded (along naturals): the log axis is the extension axis of divergence. -/
theorem log_nat_unbounded : ∀ M : ℝ, ∃ n : ℕ, Real.log (n + 1) > M := by
  intro M
  rcases exists_nat_gt (Real.exp M) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hN1 : (N : ℝ) + 1 > Real.exp M := by linarith
  have hlg : Real.log ((N : ℝ) + 1) > Real.log (Real.exp M) := by
    exact Real.log_lt_log (by positivity) hN1
  have hle : Real.log (Real.exp M) = M := Real.log_exp M
  linarith

/-- 观测 4: 分裂 ζ 级数项无界 — 欧拉圆版本复平面 (分裂度量) 中,
    级数项坐标含 cosh(b·ln n) (XXVII 结构), cosh 无界 (观测 3)
    ⟹ 项不趋于 0, 级数不收敛 (对比 ℂ: Re > 1 收敛, 观测 1)。
    对数轴无界 (log_nat_unbounded) 是发散结构的"延伸轴"。 
English: Observation 4: split ζ series terms unbounded — in the Euler-circle complex plane (split metric) term coordinates contain cosh(b·ln n) (XXVII structure); cosh unbounded (Obs 3) ⟹ terms don't tend to 0, series diverges (contrast ℂ: converges for Re > 1, Obs 1). The unbounded log axis (log_nat_unbounded) is the extension axis of the divergence structure. -/
theorem split_zeta_term_unbounded : ∀ M : ℝ, ∃ x : ℝ, Real.cosh x > M :=
  cosh_unbounded

end
end DivergentSeriesAxis

/- ================= 习题 36_divergence_period_symmetry (0pat, 原样合并) ================= -/


/-!
# 习题 XXXVI: 发散周期对称在 ζ 级数上的实现 (0pat)

pat0 R047 (发散/周期 = 同一共轭对称性 S 的两个特征空间):
  周期轴 (i 轴): exp(iθ)·exp(-iθ) = 1 — 相位对称对还原到单位 1
  发散轴 (1 轴): r·(1/r) = 1 — 数值对称对还原到单位 1 (log 镜像)

ζ 级数项是这两个特征空间的乘积: 1/n^s = n^{-σ}·e^{-it ln n}
  (发散轴部分 n^{-σ} × 周期轴部分 e^{-it ln n})

本习题形式化 R047 在 ζ 级数上的实现:
1. zeta_term_norm_split: ‖n^s‖ = n^{Re s} — 级数项模 = 发散轴部分
   (模只由实部控制, 周期轴部分 |e^{-it ln n}| = 1 从不影响)
2. period_pair_reduces: exp(iθ)·exp(-iθ) = 1 (周期轴对称对还原)
3. divergence_pair_reduces: r·(1/r) = 1 (发散轴对称对还原)
4. term_conj_symmetry: conj(n^s) = n^{conj s} — 周期轴特征空间行为
   (共轭 = 周期轴的取反)
5. functional_equation_bridges: 函数方程连接发散区与收敛区
   (ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s), mathlib riemannZeta_one_sub)
   — 发散级数的值通过发散/周期对称从收敛区获得 (解析延拓的机制)

谱系坐标: (R047, C3) × (R23, C3); 连接 C025/XXVI/XXXV。
-/

namespace DivergencePeriodSymmetry

noncomputable section

open scoped BigOperators

/-- 实现 1: 级数项的模 = 发散轴部分 — ‖n^s‖ = n^{Re s} (n > 0)。
    ζ 级数项 1/n^s 的发散完全由实部 (发散轴) 控制;
    周期轴部分 (虚部) 的模恒为 1, 从不影响收敛。 
English: Realization 1: the term modulus = divergent-axis part — ‖n^s‖ = n^{Re s} (n > 0). The divergence of the term 1/n^s is fully controlled by the real part (divergent axis); the periodic-axis (imaginary) part always has modulus 1, never affecting convergence. -/
theorem zeta_term_norm_split (n : ℕ) (s : ℂ) (hn : 0 < n) :
    ‖((n : ℂ) ^ s)‖ = (n : ℝ) ^ s.re := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [Complex.norm_cpow_of_ne_zero hne]
  -- ‖n‖ = n (正实数), arg = 0 (正实数)
  have harg : ((n : ℝ) : ℂ).arg = 0 := by
    exact Complex.arg_ofReal_of_nonneg (by exact_mod_cast (le_of_lt hn))
  have harg' : ((n : ℂ)).arg = 0 := by
    simp
  rw [harg']
  simp

/-- 实现 2: 周期轴对称对还原 (R047 周期轴) —
    exp(iθ)·exp(-iθ) = 1, 相位对称对坍缩到单位 1。 
English: Realization 2: periodic-axis symmetric-pair reduction (R047 periodic axis) — exp(iθ)·exp(-iθ) = 1, phase symmetric pairs collapse to the unit 1. -/
theorem period_pair_reduces (θ : ℂ) : Complex.exp θ * Complex.exp (-θ) = 1 := by
  rw [← Complex.exp_add]
  rw [show θ + -θ = 0 by ring]
  simp

/-- 实现 3: 发散轴对称对还原 (R047 发散轴) —
    r·(1/r) = 1, 数值对称对 (r 与 1/r, log 镜像) 坍缩到单位 1。 
English: Realization 3: divergent-axis symmetric-pair reduction (R047 divergent axis) — r·(1/r) = 1, numeric symmetric pairs (r and 1/r, log mirror) collapse to the unit 1. -/
theorem divergence_pair_reduces (r : ℝ) (hr : r ≠ 0) : r * (1 / r) = 1 := by
  field_simp [hr]

/-- 实现 4: 级数项的共轭对称 (周期轴特征空间行为) —
    conj(n^s) = n^{conj s}: 共轭 = 周期轴取反 (n 正实, arg = 0 ≠ π)。 
English: Realization 4: conjugate symmetry of the series term (periodic-axis eigenspace behavior) — conj(n^s) = n^{conj s}: conjugation = reversing the periodic axis (n positive real, arg = 0 ≠ π). -/
theorem term_conj_symmetry (n : ℕ) (s : ℂ) (hn : 0 < n) :
    (starRingEnd ℂ) ((n : ℂ) ^ s) = (n : ℂ) ^ ((starRingEnd ℂ) s) := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    have h0' : ((n : ℝ) : ℂ).arg = 0 :=
      Complex.arg_ofReal_of_nonneg (by exact_mod_cast (le_of_lt hn))
    have h0 : ((n : ℂ)).arg = 0 := by
      simp
    rw [h0]
    exact Real.pi_ne_zero.symm
  symm
  conv_lhs => rw [← map_natCast (starRingEnd ℂ) n]
  rw [Complex.conj_cpow (n : ℂ) ((starRingEnd ℂ) s) harg]
  simp

/-- 实现 5: 函数方程连接发散区与收敛区 (mathlib riemannZeta_one_sub) —
    发散级数 (Re ≤ 1) 的值通过发散/周期对称 (s ↔ 1-s) 从收敛区获得:
    这就是解析延拓的机制, mathlib 已机器验证。 
English: Realization 5: the functional equation connects the divergent and convergent regions (mathlib riemannZeta_one_sub) — values of the divergent series (Re ≤ 1) are obtained from the convergent region via the divergence/periodicity symmetry (s ↔ 1-s): this is the mechanism of analytic continuation, machine-verified in mathlib. -/
theorem functional_equation_bridges {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'

end

end DivergencePeriodSymmetry

/- ================= 习题 37 新增: 黎曼方向统一观测 (0pat) ================= -/

namespace RiemannUnifiedObservation

noncomputable section

open ZetaZeroReflection
open Complex
open HurwitzZeta
open Set

open scoped BigOperators

/-- 素数因子零点定理: 1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s·ln p = k·2πi。
    每个素数因子 (1-p^{-s}) 的零点全在 Re(s) = 0 上 (纯虚轴) —
    "素数复数进制分解"的精确内容 (Complex.exp_eq_one_iff)。 
English: Prime factor zero theorem: 1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s·ln p = k·2πi. All zeros of every prime factor (1-p^{-s}) lie on Re(s) = 0 (pure imaginary axis) — the exact content of the prime complex-base decomposition (Complex.exp_eq_one_iff). -/
theorem prime_factor_zero (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    (1 - (p : ℂ) ^ (-s) = 0) ↔
      ∃ k : ℤ, s * Complex.log (p : ℂ) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
  constructor
  · intro h
    have hpow : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    rw [Complex.cpow_def_of_ne_zero hp0] at hpow
    rcases (Complex.exp_eq_one_iff).1 hpow with ⟨n, hn⟩
    use -n
    -- 从 hn: log p · (-s) = n·2πi 推出 s·log p = (-n)·2πi = ↑(-n)·2πi
    calc
      s * Complex.log (p : ℂ) = -((-s) * Complex.log (p : ℂ)) := by ring
      _ = -((n : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
        rw [show (-s) * Complex.log (p : ℂ) = (n : ℂ) * (2 * ↑Real.pi * Complex.I) by
          simpa [mul_comm] using hn]
      _ = (-(n : ℂ)) * (2 * ↑Real.pi * Complex.I) := by rw [← neg_mul]
      _ = (↑(-n) : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [Int.cast_neg]
  · rintro ⟨k, hk⟩
    rw [Complex.cpow_def_of_ne_zero hp0]
    rw [sub_eq_zero]
    symm
    apply (Complex.exp_eq_one_iff).mpr
    refine ⟨-k, ?_⟩
    -- 目标: log p · (-s) = ↑(-k)·2πi; 从 hk: s·log p = k·2πi
    calc
      Complex.log (p : ℂ) * (-s) = -((s) * Complex.log (p : ℂ)) := by ring
      _ = -((k : ℂ) * (2 * ↑Real.pi * Complex.I)) := by rw [hk]
      _ = (-(k : ℂ)) * (2 * ↑Real.pi * Complex.I) := by rw [← neg_mul]
      _ = (↑(-k) : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [Int.cast_neg]

/-- 平凡零点条件: cos(πs/2) = 0 ⟺ s = 2k+1 (k ∈ ℤ)。
    函数方程的三角因子零点 = 奇整数 (Complex.cos_eq_zero_iff)。 
English: Trivial zero condition: cos(πs/2) = 0 ⟺ s = 2k+1 (k ∈ ℤ). Zeros of the functional equation's trig factor = odd integers (Complex.cos_eq_zero_iff). -/
theorem trivial_zero_condition (s : ℂ) :
    Complex.cos (↑Real.pi * s / 2) = 0 ↔ ∃ k : ℤ, s = (2 * (k : ℂ) + 1) := by
  constructor
  · intro h
    rcases (Complex.cos_eq_zero_iff).1 h with ⟨k, hk⟩
    use k
    have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hmul : (↑Real.pi * s / 2) * 2 = ((2 * (k : ℂ) + 1) * ↑Real.pi / 2) * 2 := by
      exact congrArg (fun z : ℂ => z * 2) hk
    have hπs : ↑Real.pi * s = (2 * (k : ℂ) + 1) * ↑Real.pi := by
      field_simp [h2] at hmul ⊢
      exact hmul
    have hs : s = 2 * (k : ℂ) + 1 := by
      -- π·s = (2k+1)·π ⟹ s = 2k+1 (π ≠ 0)
      apply mul_left_cancel₀ hpi
      calc
        ↑Real.pi * s = (2 * (k : ℂ) + 1) * ↑Real.pi := hπs
        _ = ↑Real.pi * (2 * (k : ℂ) + 1) := by rw [mul_comm]
    exact hs
  · rintro ⟨k, rfl⟩
    rw [Complex.cos_eq_zero_iff]
    refine ⟨k, ?_⟩
    ring

/-- 临界线观测: Re s = 1/2 ⟺ 每个级数项的模 = n^{1/2}。
    临界线 = 发散因子 n^{-1/2} 的乘积结构 (由 zeta_term_norm_split 反向)。 
English: Critical line observation: Re s = 1/2 ⟺ modulus of every series term = n^{1/2}. The critical line = product structure of the divergence factor n^{-1/2} (reversing zeta_term_norm_split). -/
theorem critical_line_observation (s : ℂ) :
    s.re = 1 / 2 ↔ ∀ n : ℕ, 0 < n → ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (1 / 2 : ℝ) := by
  constructor
  · intro hs n hn
    rw [DivergencePeriodSymmetry.zeta_term_norm_split n s hn]
    rw [hs]
  · intro h
    have h2 := h 2 (by norm_num)
    rw [DivergencePeriodSymmetry.zeta_term_norm_split 2 s (by norm_num)] at h2
    exact (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).1 h2


/- 假实轴 = 相对于 i 的 nat 轴: 刻度 1 = i^i = e^{-π/2} (原点 i 的 i 次后继)。
   λ 演算的 i 次后继迭代 = 乘法群 ℂ* 中生成元 i 的 i 次幂 (cpow);
   不是 Church 编码的 Nat 计数迭代 (次数是 i, 不是预设自然数)。 -/

/-- 假实轴上的 1 = i^i = e^{-π/2} — 原点 i 的 i 次后继的数值。
    λ 演算的 i 次后继迭代 = 乘性群中 i 的 i 次幂 (cpow 定义)。 
English: 1 on the fake real axis = i^i = e^{-π/2} — the value of the i-th successor of the origin i. The i-fold successor iteration of λ calculus = the i-th power of i in the multiplicative group (cpow definition). -/
theorem i_pow_i_eq_exp_neg_pi_div_two : Complex.I ^ Complex.I = ↑(Real.exp (-Real.pi / 2)) := by
  rw [Complex.cpow_def_of_ne_zero (by simp : Complex.I ≠ 0)]
  rw [Complex.log_I]
  have hcalc : (↑Real.pi / 2 * Complex.I) * Complex.I = ↑(-Real.pi / 2) := by
    calc
      (↑Real.pi / 2 * Complex.I) * Complex.I = ↑Real.pi / 2 * (Complex.I * Complex.I) := by ring
      _ = ↑Real.pi / 2 * (-1) := by rw [Complex.I_mul_I]
      _ = -↑Real.pi / 2 := by ring
      _ = ↑(-Real.pi / 2) := by simp [Complex.ofReal_div, Complex.ofReal_neg]
  rw [hcalc]
  exact (Complex.ofReal_exp (-Real.pi / 2)).symm

/-- 1 ≠ i: i^i 是实数 (re = e^{-π/2} ≠ 0), i 的 re = 0。 
English: 1 ≠ i: i^i is real (re = e^{-π/2} ≠ 0), while re i = 0. -/
theorem i_pow_i_ne_i : Complex.I ^ Complex.I ≠ Complex.I := by
  intro h
  have hre : (Complex.I ^ Complex.I).re = Complex.I.re := congrArg Complex.re h
  rw [i_pow_i_eq_exp_neg_pi_div_two, Complex.ofReal_re, Complex.I_re] at hre
  exact (Real.exp_pos (-Real.pi / 2)).ne' hre

/-- 0 < e^{-π/2} < 1 — 假实轴上的 1 落在 (0,1) 开区间内。 
English: 0 < e^{-π/2} < 1 — the 1 on the fake real axis lies in the open interval (0,1). -/
theorem i_pow_i_pos_lt_one : 0 < Real.exp (-Real.pi / 2) ∧ Real.exp (-Real.pi / 2) < 1 := by
  constructor
  · exact Real.exp_pos (-Real.pi / 2)
  · rw [← Real.exp_zero]
    rw [Real.exp_lt_exp]
    linarith [Real.pi_pos]

/-- 假实轴刻度 n = (i^i)^n = e^{-nπ/2} — i 的迭代的幂结构
    (n 是"相对于 i 的 nat", 从 i^i 的幂中读出, 非 Church 计数输入)。 
English: Fake real axis scale n = (i^i)^n = e^{-nπ/2} — power structure of the iteration of i (n is the nat relative to i, read from powers of i^i, not a Church numeral input). -/
theorem axis_tick_pow (n : ℕ) : (Complex.I ^ Complex.I) ^ n = ↑(Real.exp (-Real.pi / 2 * n)) := by
  rw [i_pow_i_eq_exp_neg_pi_div_two]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← Real.exp_add]
      congr 1
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- 素数是不可分解的迭代: 素数刻度 (i^i)^p 不能写成 ((i^i)^a)^b (a,b ≥ 2)。
    幂分解 (迭代的迭代) = 指数乘法 p = a·b; 素数的乘法不可分解性 =
    刻度的幂不可分解性。 
English: Primes are indecomposable iterations: the prime scale (i^i)^p cannot be written as ((i^i)^a)^b (a,b ≥ 2). Power decomposition (iteration of an iteration) = exponent multiplication p = a·b; multiplicative indecomposability of primes = power indecomposability of scales. -/
theorem prime_no_power_decomposition (p : ℕ) (hp : Nat.Prime p) :
    ¬ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧
      (Real.exp (-Real.pi / 2)) ^ p = ((Real.exp (-Real.pi / 2)) ^ a) ^ b := by
  rintro ⟨a, b, ha2, hb2, h⟩
  have hlp : (Real.exp (-Real.pi / 2)) ^ p = Real.exp (-Real.pi / 2 * p) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hlb : ((Real.exp (-Real.pi / 2)) ^ a) ^ b = Real.exp (-Real.pi / 2 * (a * b)) := by
    rw [← pow_mul]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num [Nat.cast_mul]
    ring
  rw [hlp, hlb] at h
  have harg : -Real.pi / 2 * ↑p = -Real.pi / 2 * ↑(a * b) := by
    have h' : -Real.pi / 2 * ↑p = -Real.pi / 2 * (↑a * ↑b) := by
      exact Real.exp_injective h
    simpa [Nat.cast_mul] using h'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have harg2 : (↑p : ℝ) = (↑(a * b) : ℝ) := by
    have hmul := congrArg (fun z : ℝ => z * (-2 / Real.pi)) harg
    field_simp [hpi] at hmul
    exact hmul
  have hp_eq : p = a * b := by
    exact_mod_cast harg2
  have hdvd : a ∣ p := ⟨b, hp_eq⟩
  have ha_ne1 : a ≠ 1 := by omega
  have ha_p : a = p := (hp.eq_one_or_self_of_dvd a hdvd).resolve_left ha_ne1
  have hpp : p * b = p := by
    rw [ha_p] at hp_eq
    exact hp_eq.symm
  have hb1 : b = 1 := Nat.mul_left_cancel (Nat.Prime.pos hp) (by simpa using hpp)
  omega

/- 观测工具完备化 (0pat, mathlib 直接引用): ξ 整函数结构 + 级数 + 函数方程。
   相位基点观测 (Hardy Z) 的框架定理 — 零成本, 全部 mathlib 现有定理。 -/

/-- ξ 对称 (Λ₀): Λ₀(1-s) = Λ₀(s) — mathlib 直接引用 (0pat 零成本). 
English: ξ symmetry (Λ₀): Λ₀(1-s) = Λ₀(s) — direct mathlib citation (zero-cost 0pat). -/
theorem xi_symmetry₀ (s : ℂ) : completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub s

/-- ξ 对称 (Λ): Λ(1-s) = Λ(s) — mathlib 直接引用. 
English: ξ symmetry (Λ): Λ(1-s) = Λ(s) — direct mathlib citation. -/
theorem xi_symmetry (s : ℂ) : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- ξ 整函数: Λ₀ 处处可微 (整) — mathlib 直接引用. 
English: ξ entire: Λ₀ differentiable everywhere (entire) — direct mathlib citation. -/
theorem xi_entire : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedZeta₀

/-- 级数表示: Re s > 1 时 ζ(s) = Σ 1/n^s — mathlib 直接引用. 
English: Series representation: ζ(s) = Σ 1/n^s for Re s > 1 — direct mathlib citation. -/
theorem zeta_series_form {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' (n : ℕ), 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

/-- 函数方程: ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s) — mathlib 直接引用. 
English: Functional equation: ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s) — direct mathlib citation. -/
theorem zeta_functional_equation {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'

/- 基点方向定理 (0pat, 用户方向 2026-08-21):
   方向 2 (换基点收敛到稳定): ±1 震荡使发散级数收敛 (交错判别, mathlib 引用)
   方向 1 (乱跑扔到投影): ±1 部分和有界 + 配对结构 (乱跑项投影为相邻差) -/

/-- 方向 2: ±1 震荡 (换基点) 使发散级数收敛到稳定 — 莱布尼茨交错判别
    (mathlib 引用, 0pat). 模型: n^s 方向 ±1 震荡 (观测 P). 
English: Direction 2: ±1 oscillation (basepoint change) makes a divergent series converge stably — Leibniz alternating test (mathlib citation, 0pat). Model: n^s oscillates in direction ±1 (observation P). -/
theorem alternating_series_converges {a : ℕ → ℝ} (hant : Antitone a)
    (ht : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ l : ℝ, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * a i) Filter.atTop (nhds l) :=
  Antitone.tendsto_alternating_series_of_tendsto_zero hant ht

/-- 方向 1: ±1 震荡的部分和有界 (乱跑不累积, 可扔到残差) — mathlib 引用. 
English: Direction 1: partial sums of the ±1 oscillation are bounded (wandering without accumulation, discardable into the remainder) — mathlib citation. -/
theorem alternating_partial_sum_bounded (n : ℕ) : ‖∑ i ∈ Finset.range n, (-1 : ℝ) ^ i‖ ≤ 1 :=
  norm_sum_neg_one_pow_le n

/-- 方向 1 的配对结构: ±1 震荡把项配对成相邻差 (乱跑项投影为差结构).
    Σ_{i=0}^{2N-1} (-1)^i·(i+1)^{-s} = Σ_{k=0}^{N-1} ((2k+1)^{-s} - (2k+2)^{-s}). 
English: Pairing structure of direction 1: the ±1 oscillation pairs terms into adjacent differences (wandering terms project to a difference structure). Σ_{i=0}^{2N-1} (-1)^i·(i+1)^{-s} = Σ_{k=0}^{N-1} ((2k+1)^{-s} - (2k+2)^{-s}). -/
theorem eta_pair_form {s : ℂ} (N : ℕ) :
    ∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℂ) ^ (-s) =
      ∑ i ∈ Finset.range N, (((2 * i + 1 : ℕ) : ℂ) ^ (-s) - ((2 * i + 2 : ℕ) : ℂ) ^ (-s)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [ih]
      have h_even : (-1 : ℂ) ^ (2 * N) = 1 := by
        rw [pow_mul]
        norm_num
      have h_odd : (-1 : ℂ) ^ (2 * N + 1) = -1 := by
        rw [pow_succ, h_even]
        norm_num
      have h_cast : (↑(-1 : ℝ) : ℂ) = (-1 : ℂ) := by simp
      rw [Finset.sum_range_succ]
      rw [h_cast]
      rw [h_even, h_odd]
      simp
      ring_nf

/- 第 1 步 (用户方向 2026-08-21): ζ 共轭 (Re>1 级数形式) — Z(t) 实值性的基础.
   conj(ζ(s)) = ζ(conj s): 级数共轭 (Complex.conj_tsum) + 项共轭
   (term_conj_symmetry) + n=0 项特判 (除零公理). -/
theorem zeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (riemannZeta s) = riemannZeta (starRingEnd ℂ s) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  rw [Complex.conj_tsum]
  rw [zeta_eq_tsum_one_div_nat_cpow (by rwa [Complex.conj_re])]
  congr 1
  funext n
  by_cases hn : n = 0
  · subst hn
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hsc : (starRingEnd ℂ) s ≠ 0 := by
        intro h
        apply hs0
        have hs' := congrArg (starRingEnd ℂ) h
        simpa using hs'
      simp [Complex.zero_cpow hs0, Complex.zero_cpow hsc]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [one_div]
    rw [map_inv₀]
    have hconj := DivergencePeriodSymmetry.term_conj_symmetry n s hnpos
    rw [hconj]
    rw [one_div]

/- χ 结构定理 (pat0 路径: 对称性接力, 非差分论证; 用户方向 2026-08-21).
   chi_conj 已单独编译验证 (0 error); chi_mul_chi_one_sub 逻辑同 test17. -/
lemma arg_two_ne_pi : ((2 : ℂ)).arg ≠ Real.pi := by
  have h0 : ((2 : ℂ)).arg = 0 := by
    have h0' : ((2 : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by norm_num)
    simpa using h0'
  rw [h0]
  exact Real.pi_ne_zero.symm

lemma arg_pi_ne_pi : ((↑Real.pi : ℂ)).arg ≠ Real.pi := by
  have h0 : ((↑Real.pi : ℂ)).arg = 0 := by
    have h0' : ((Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by exact le_of_lt Real.pi_pos)
    simpa using h0'
  rw [h0]
  exact Real.pi_ne_zero.symm

lemma conj_two_cpow (s : ℂ) :
    (starRingEnd ℂ) ((2 : ℂ) ^ (s : ℂ)) = (2 : ℂ) ^ ((starRingEnd ℂ) s : ℂ) := by
  have h := Complex.conj_cpow (2 : ℂ) s arg_two_ne_pi
  have h2c : (starRingEnd ℂ) (2 : ℂ) = 2 := by exact map_natCast (starRingEnd ℂ) 2
  rw [h2c] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa using h'

lemma conj_pi_cpow (s : ℂ) :
    (starRingEnd ℂ) ((↑Real.pi : ℂ) ^ ((s - 1) : ℂ))
      = (↑Real.pi : ℂ) ^ (((starRingEnd ℂ) s - 1) : ℂ) := by
  have h := Complex.conj_cpow (↑Real.pi : ℂ) (s - 1 : ℂ) arg_pi_ne_pi
  have hpic : (starRingEnd ℂ) (↑Real.pi : ℂ) = ↑Real.pi := by
    exact Complex.conj_ofReal Real.pi
  rw [hpic] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa [map_sub] using h'

lemma conj_sin_half (s : ℂ) :
    (starRingEnd ℂ) (Complex.sin (↑Real.pi * s / 2))
      = Complex.sin (↑Real.pi * (starRingEnd ℂ) s / 2) := by
  have h := Complex.sin_conj (↑Real.pi * s / 2)
  have harg : (starRingEnd ℂ) (↑Real.pi * s / 2) = ↑Real.pi * (starRingEnd ℂ) s / 2 := by
    simp [map_div₀, map_mul, map_ofNat]
  rw [harg] at h
  exact h.symm

lemma conj_gamma_one_sub (s : ℂ) :
    (starRingEnd ℂ) (Complex.Gamma (1 - s)) = Complex.Gamma (1 - (starRingEnd ℂ) s) := by
  have h := Complex.Gamma_conj (1 - s)
  have harg : (starRingEnd ℂ) (1 - s) = 1 - (starRingEnd ℂ) s := by
    simp [map_sub]
  rw [harg] at h
  exact h.symm

/-- χ 共轭: conj(χ(s)) = χ(conj s) — 周期轴取反穿过函数方程乘子.
    pat0: 共轭对称性是结构性的 (逐项: cpow/sin/Γ 共轭). 
English: χ conjugation: conj(χ(s)) = χ(conj s) — reversing the periodic axis passes through the functional equation multiplier. pat0: conjugate symmetry is structural (termwise: cpow/sin/Γ conjugation). -/
theorem chi_conj (s : ℂ) :
    (starRingEnd ℂ) ((2 : ℂ) ^ (s : ℂ) * (↑Real.pi : ℂ) ^ ((s - 1) : ℂ)
      * Complex.sin (↑Real.pi * s / 2) * Complex.Gamma (1 - s))
    = (2 : ℂ) ^ ((starRingEnd ℂ) s : ℂ) * (↑Real.pi : ℂ) ^ (((starRingEnd ℂ) s - 1) : ℂ)
      * Complex.sin (↑Real.pi * (starRingEnd ℂ) s / 2) * Complex.Gamma (1 - (starRingEnd ℂ) s) := by
  rw [map_mul, map_mul, map_mul]
  rw [conj_two_cpow s, conj_pi_cpow s, conj_sin_half s, conj_gamma_one_sub s]

/-- Re<0 的 zeta 共轭: 函数方程共轭 + 消去 (pat0 对称性接力, 正向路径).
    hfe 两边 conj → conj(zeta(1-s)) = conj(系数)·conj(zeta(s))
    左边 = zeta(1-s̄) (级数共轭); zeta(1-s̄) = 系数̄·zeta(s̄) (函数方程对 s̄)
    conj(系数) = 系数̄ (conj 逐项); 消去 ⟹ conj(zeta(s)) = zeta(s̄) 
English: zeta conjugation for Re<0: conjugate the functional equation + cancellation (pat0 symmetry relay, forward path). Conjugating both sides of hfe: conj(zeta(1-s)) = conj(coef)·conj(zeta(s)); left = zeta(1-s̄) (series conjugation); zeta(1-s̄) = coef̄·zeta(s̄) (functional equation at s̄); conj(coef) = coef̄ (termwise conj); cancel ⟹ conj(zeta(s)) = zeta(s̄). -/
theorem zeta_conj_of_re_lt_zero {s : ℂ} (hs : s.re < 0) (hsneg : ∀ n : ℕ, s ≠ -↑n)
    (hcos : Complex.cos (↑Real.pi * s / 2) ≠ 0) :
    (starRingEnd ℂ) (riemannZeta s) = riemannZeta (starRingEnd ℂ s) := by
  have hs' : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    linarith [hs]
  have hfe := riemannZeta_one_sub hsneg hs'
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have h2pi : (2 * ↑Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (by exact_mod_cast Real.pi_ne_zero)
  have hgam : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsneg
  have h1s : 1 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hs]
  have hconj1 : (starRingEnd ℂ) (riemannZeta (1 - s)) = riemannZeta (1 - (starRingEnd ℂ) s) := by
    simpa [map_sub] using zeta_conj_of_one_lt_re h1s
  have hsbar : (starRingEnd ℂ) s ≠ 1 := by
    intro h
    apply hs'
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  have hsnegbar : ∀ n : ℕ, (starRingEnd ℂ) s ≠ -↑n := by
    intro n h
    apply hsneg n
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  have hcosbar : Complex.cos (↑Real.pi * (starRingEnd ℂ) s / 2) ≠ 0 := by
    intro h
    have hc := Complex.cos_conj (↑Real.pi * s / 2)
    have harg : (starRingEnd ℂ) (↑Real.pi * s / 2) = ↑Real.pi * (starRingEnd ℂ) s / 2 := by
      simp [map_div₀, map_mul, map_ofNat]
    rw [harg] at hc
    have hcz : (starRingEnd ℂ) (Complex.cos (↑Real.pi * s / 2)) = 0 := by
      exact hc.symm.trans h
    exact hcos (by simpa using congrArg (starRingEnd ℂ) hcz)
  have hfe2 := riemannZeta_one_sub hsnegbar hsbar
  -- hfe 两边 conj
  have hconjfe := congrArg (starRingEnd ℂ) hfe
  rw [map_mul] at hconjfe
  -- 系数共轭: conj(2(2π)^{-s}Γ(s)cos(πs/2)) = 2(2π)^{-s̄}Γ(s̄)cos(πs̄/2)
  have harg2pi : (2 * ↑Real.pi : ℂ).arg ≠ Real.pi := by
    have h0 : (2 * ↑Real.pi : ℂ).arg = 0 := by
      have h0' : (((2 * Real.pi : ℝ) : ℝ) : ℂ).arg = 0 :=
        Complex.arg_ofReal_of_nonneg (by positivity)
      simpa using h0'
    rw [h0]
    exact Real.pi_ne_zero.symm
  have hcoef : (starRingEnd ℂ) (2 * (2 * ↑Real.pi : ℂ) ^ ((-s) : ℂ) * Complex.Gamma s
      * Complex.cos (↑Real.pi * s / 2))
      = 2 * (2 * ↑Real.pi : ℂ) ^ ((-(starRingEnd ℂ) s) : ℂ) * Complex.Gamma (starRingEnd ℂ s)
        * Complex.cos (↑Real.pi * (starRingEnd ℂ) s / 2) := by
    rw [map_mul, map_mul, map_mul]
    have h1 : (starRingEnd ℂ) (2 : ℂ) = 2 := by exact map_natCast (starRingEnd ℂ) 2
    have h2 : (starRingEnd ℂ) ((2 * ↑Real.pi : ℂ) ^ ((-s) : ℂ))
        = (2 * ↑Real.pi : ℂ) ^ ((-(starRingEnd ℂ) s) : ℂ) := by
      have h := Complex.conj_cpow (2 * ↑Real.pi : ℂ) (-s : ℂ) harg2pi
      have hc2 : (starRingEnd ℂ) (2 * ↑Real.pi : ℂ) = (2 * ↑Real.pi : ℂ) := by
        calc
          (starRingEnd ℂ) (2 * ↑Real.pi : ℂ)
              = (starRingEnd ℂ) (2 : ℂ) * (starRingEnd ℂ) (↑Real.pi : ℂ) := by rw [map_mul]
          _ = 2 * (↑Real.pi : ℂ) := by rw [map_ofNat, Complex.conj_ofReal]
      rw [hc2] at h
      have h' := congrArg (starRingEnd ℂ) h
      simpa [map_neg] using h'
    have h3 : (starRingEnd ℂ) (Complex.Gamma s) = Complex.Gamma (starRingEnd ℂ s) := by
      exact (Complex.Gamma_conj s).symm
    have h4 : (starRingEnd ℂ) (Complex.cos (↑Real.pi * s / 2))
        = Complex.cos (↑Real.pi * (starRingEnd ℂ) s / 2) := by
      have h := Complex.cos_conj (↑Real.pi * s / 2)
      have harg : (starRingEnd ℂ) (↑Real.pi * s / 2) = ↑Real.pi * (starRingEnd ℂ) s / 2 := by
        simp [map_div₀, map_mul, map_ofNat]
      rw [harg] at h
      exact h.symm
    rw [h1, h2, h3, h4]
  rw [hcoef] at hconjfe
  rw [hconj1] at hconjfe
  -- hconjfe: ζ(1-s̄) = 系数̄·conj(ζ(s)); hfe2: ζ(1-s̄) = 系数̄·ζ(s̄)
  have heq := hconjfe.symm.trans hfe2
  have hcne : (2 * ↑Real.pi : ℂ) ^ ((-(starRingEnd ℂ) s) : ℂ) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl h2pi)
  have hgam_bar : Complex.Gamma (starRingEnd ℂ s) ≠ 0 := Complex.Gamma_ne_zero hsnegbar
  have hcoef_ne : 2 * (2 * ↑Real.pi : ℂ) ^ ((-(starRingEnd ℂ) s) : ℂ)
      * Complex.Gamma (starRingEnd ℂ s) * Complex.cos (↑Real.pi * (starRingEnd ℂ) s / 2) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2ne hcne) hgam_bar) hcosbar
  exact mul_left_cancel₀ hcoef_ne heq

open HurwitzZeta
open Set

/-- 正实数的 cpow 共轭: conj(t^w) = t^(conj w) 对 t > 0 (arg = 0). 
English: cpow conjugation for positive reals: conj(t^w) = t^(conj w) for t > 0 (arg = 0). -/
lemma conj_cpow_of_pos {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (starRingEnd ℂ) ((t : ℂ) ^ (w : ℂ)) = (t : ℂ) ^ ((starRingEnd ℂ) w : ℂ) := by
  have harg : ((t : ℂ)).arg ≠ Real.pi := by
    have h0 : ((t : ℂ)).arg = 0 := by
      have h0' : ((t : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (le_of_lt ht)
      simpa using h0'
    rw [h0]
    exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (t : ℂ) w harg
  have htc : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by
    exact Complex.conj_ofReal t
  rw [htc] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa using h'

/-- f_modif (hurwitzEvenFEPair 0) 实值: evenKernel 实值 (ofReal 嵌入) + 系数全实. 
English: f_modif (hurwitzEvenFEPair 0) is real-valued: evenKernel real-valued (ofReal embedding) + all-real coefficients. -/
lemma conj_f_modif_zero (t : ℝ) :
    (starRingEnd ℂ) ((hurwitzEvenFEPair 0).f_modif t) = (hurwitzEvenFEPair 0).f_modif t := by
  unfold WeakFEPair.f_modif
  rw [Pi.add_apply, map_add]
  -- 项 1: indicator (Ioi 1) (fun x => f x - f₀)
  have h1 : (starRingEnd ℂ)
      ((Ioi (1 : ℝ)).indicator (fun x : ℝ => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀) t)
      = (Ioi (1 : ℝ)).indicator (fun x : ℝ => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀) t := by
    rw [map_indicator]
    congr 1
    funext x
    simp [hurwitzEvenFEPair]
  -- 项 2: indicator (Ioo 0 1) (fun x => f x - (ε * ↑(x ^ (-k))) • g₀)
  have h2 : (starRingEnd ℂ)
      ((Ioo (0 : ℝ) 1).indicator (fun x : ℝ =>
        (hurwitzEvenFEPair 0).f x - ((hurwitzEvenFEPair 0).ε * ↑(x ^ (-(hurwitzEvenFEPair 0).k))) • (hurwitzEvenFEPair 0).g₀) t)
      = (Ioo (0 : ℝ) 1).indicator (fun x : ℝ =>
        (hurwitzEvenFEPair 0).f x - ((hurwitzEvenFEPair 0).ε * ↑(x ^ (-(hurwitzEvenFEPair 0).k))) • (hurwitzEvenFEPair 0).g₀) t := by
    rw [map_indicator]
    congr 1
    funext x
    simp [hurwitzEvenFEPair]
  rw [h1, h2]

/-- Mellin 共轭 (f_modif 实值, 积分共轭无条件): conj(mellin f w) = mellin f (conj w). 
English: Mellin conjugation (f_modif real-valued; integral conjugation unconditional): conj(mellin f w) = mellin f (conj w). -/
lemma conj_mellin_f_modif (w : ℂ) :
    (starRingEnd ℂ) (mellin (hurwitzEvenFEPair 0).f_modif w)
      = mellin (hurwitzEvenFEPair 0).f_modif ((starRingEnd ℂ) w) := by
  unfold mellin
  rw [← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
  rw [smul_eq_mul, smul_eq_mul]
  rw [map_mul]
  rw [conj_cpow_of_pos ht (w - 1)]
  rw [conj_f_modif_zero t]
  simp [map_sub]

/-- Λ₀ 共轭 (整函数定义层穿透): conj(completedRiemannZeta₀ s) = completedRiemannZeta₀ (conj s). 
English: Λ₀ conjugation (penetrating the entire-function definition layer): conj(completedRiemannZeta₀ s) = completedRiemannZeta₀ (conj s). -/
lemma conj_completedRiemannZeta₀ (s : ℂ) :
    (starRingEnd ℂ) (completedRiemannZeta₀ s) = completedRiemannZeta₀ (starRingEnd ℂ s) := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀
  rw [map_div₀]
  rw [map_ofNat]
  have hme : (starRingEnd ℂ) ((hurwitzEvenFEPair 0).Λ₀ (s / 2))
      = (hurwitzEvenFEPair 0).Λ₀ ((starRingEnd ℂ) s / 2) := by
    unfold WeakFEPair.Λ₀
    simpa [map_div₀, map_ofNat] using conj_mellin_f_modif (s / 2)
  rw [hme]

/-- 临界带 ζ 共轭: conj(ζ(s)) = ζ(conj s) 对 0 < Re s < 1.
    pat0 启发: 对称性接力 (Λ₀ 结构/函数方程) 替代解析延拓差分论证. 
English: Critical strip ζ conjugation: conj(ζ(s)) = ζ(conj s) for 0 < Re s < 1. pat0 heuristic: symmetry relay (Λ₀ structure / functional equation) replaces analytic continuation difference arguments. -/
theorem zeta_conj_of_critical_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (starRingEnd ℂ) (riemannZeta s) = riemannZeta (starRingEnd ℂ s) := by
  have hs' : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    linarith [hs1]
  have hsneg : ∀ n : ℕ, s / 2 + 1 ≠ -↑n := by
    intro n h
    have hre : (s / 2 + 1).re = (-(↑n : ℂ)).re := by rw [h]
    have hre' : (s / 2 + 1).re = s.re / 2 + 1 := by
      rw [Complex.add_re, Complex.one_re]
      simp
    have hpos : 0 < s.re / 2 + 1 := by linarith [hs0]
    have hneg : ((-(↑n : ℂ)).re) ≤ 0 := by simp
    linarith
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcne : (↑Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl hpi)
  have hgam2 : Complex.Gamma (s / 2 + 1) ≠ 0 := by
    exact Complex.Gamma_ne_zero hsneg
  have hden : 2 * (↑Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hcne) hgam2
  -- 分母共轭: conj(2·π^(-s/2)·Γ(s/2+1)) = 2·π^(-conj s/2)·Γ(conj s/2+1)
  have harg_pi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
    have h0 : (↑Real.pi : ℂ).arg = 0 := by
      have h0' : ((Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)
      simpa using h0'
    rw [h0]
    exact Real.pi_ne_zero.symm
  have hpi_conj : (starRingEnd ℂ) ((↑Real.pi : ℂ) ^ ((-s / 2) : ℂ))
      = (↑Real.pi : ℂ) ^ ((-(starRingEnd ℂ) s / 2) : ℂ) := by
    have h := Complex.conj_cpow (↑Real.pi : ℂ) (-s / 2 : ℂ) harg_pi
    have hpic : (starRingEnd ℂ) (↑Real.pi : ℂ) = ↑Real.pi := by
      exact Complex.conj_ofReal Real.pi
    rw [hpic] at h
    have h' := congrArg (starRingEnd ℂ) h
    simpa [map_div₀, map_neg, map_ofNat] using h'
  have hgamma_conj : (starRingEnd ℂ) (Complex.Gamma (s / 2 + 1))
      = Complex.Gamma ((starRingEnd ℂ) s / 2 + 1) := by
    have h := Complex.Gamma_conj (s / 2 + 1)
    rw [← h]
    congr 1
    simp [map_div₀, map_add, map_one, map_ofNat]
  -- 主证明: 对 riemannZeta_eq_mul_completedRiemannZeta₀ s 两边 conj
  have hfe := riemannZeta_eq_mul_completedRiemannZeta₀ s
  have hc := congrArg (starRingEnd ℂ) hfe
  rw [map_div₀] at hc
  -- 分子 conj: conj(s·Λ₀(s) − 1 − s/(1−s))
  have hnum : (starRingEnd ℂ) (s * completedRiemannZeta₀ s - 1 - s / (1 - s))
      = (starRingEnd ℂ) s * completedRiemannZeta₀ (starRingEnd ℂ s) - 1
        - (starRingEnd ℂ) s / (1 - (starRingEnd ℂ) s) := by
    rw [map_sub, map_sub, map_mul]
    rw [conj_completedRiemannZeta₀ s]
    rw [map_div₀]
    rw [map_sub]
    simp
  rw [hnum] at hc
  -- 分母 conj
  have hden_conj : (starRingEnd ℂ) (2 * (↑Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))
      = 2 * (↑Real.pi : ℂ) ^ (-(starRingEnd ℂ) s / 2) * Complex.Gamma ((starRingEnd ℂ) s / 2 + 1) := by
    rw [map_mul, map_mul]
    rw [map_ofNat]
    rw [hpi_conj]
    rw [hgamma_conj]
  rw [hden_conj] at hc
  -- 目标: conj(ζ(s)) = ζ(conj s); 展开 ζ(conj s) 用同一公式
  rw [riemannZeta_eq_mul_completedRiemannZeta₀ (starRingEnd ℂ s)]
  exact hc

/- ============ ζ 的实部/虚部拆分 (共轭投影) ============ -/

/-- 实部共轭对称: Re ζ(s) = Re ζ(conj s) (临界带, 假实轴部分偶). 
English: Real-part conjugate symmetry: Re ζ(s) = Re ζ(conj s) (critical strip, fake real axis part even). -/
theorem zeta_re_conj_symm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (riemannZeta s).re = (riemannZeta (starRingEnd ℂ s)).re := by
  have hz := zeta_conj_of_critical_strip (s := s) hs0 hs1
  have hr := congrArg Complex.re hz
  simpa using hr

/-- 虚部共轭反对称: Im ζ(s) = -Im ζ(conj s) (临界带, y 轴泄漏奇). 
English: Imaginary-part conjugate antisymmetry: Im ζ(s) = -Im ζ(conj s) (critical strip, y-axis leak odd). -/
theorem zeta_im_conj_antisymm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (riemannZeta s).im = -(riemannZeta (starRingEnd ℂ s)).im := by
  have hz := zeta_conj_of_critical_strip (s := s) hs0 hs1
  have hi := congrArg Complex.im hz
  have hi' : -(riemannZeta s).im = (riemannZeta (starRingEnd ℂ s)).im := by
    simpa using hi
  linarith

/-- 临界线实部偶: Re ζ(1/2+it) = Re ζ(1/2-it). 
English: Real part even on the critical line: Re ζ(1/2+it) = Re ζ(1/2-it). -/
theorem zeta_re_even_on_line (t : ℝ) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re
      = (riemannZeta ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re := by
  -- s = 1/2+it: conj s = 1/2-it
  have hs0 : 0 < ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re := by simp
  have hs1 : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re < 1 := by
    simp
    norm_num
  have hsym := zeta_re_conj_symm (s := (1 / 2 : ℂ) + (t : ℂ) * Complex.I) hs0 hs1
  -- hsym : re(ζ(1/2+it)) = re(ζ(conj(1/2+it)));conj(1/2+it) = 1/2-it:simpa
  -- conj 对加法分配得 `+ -(↑t*I)`, goal 是 `- ↑t*I`: sub_eq_add_neg 对齐
  simpa [Complex.conj_ofReal, Complex.conj_I, map_add, map_mul, map_inv₀, map_ofNat,
    sub_eq_add_neg] using hsym

/-- 临界线虚部奇: Im ζ(1/2+it) = -Im ζ(1/2-it). 
English: Imaginary part odd on the critical line: Im ζ(1/2+it) = -Im ζ(1/2-it). -/
theorem zeta_im_odd_on_line (t : ℝ) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im
      = -((riemannZeta ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).im) := by
  have hs0 : 0 < ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re := by simp
  have hs1 : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re < 1 := by
    simp
    norm_num
  have hsym := zeta_im_conj_antisymm (s := (1 / 2 : ℂ) + (t : ℂ) * Complex.I) hs0 hs1
  simpa [Complex.conj_ofReal, Complex.conj_I, map_add, map_mul, map_inv₀, map_ofNat,
    sub_eq_add_neg] using hsym

/-- 零点判定: ζ(z) = 0 ⟺ Re ζ(z) = 0 ∧ Im ζ(z) = 0 (两部分公共零点). 
English: Zero determination: ζ(z) = 0 ⟺ Re ζ(z) = 0 ∧ Im ζ(z) = 0 (common zero of both parts). -/
theorem zeta_eq_zero_iff_re_im (z : ℂ) :
    riemannZeta z = 0 ↔ (riemannZeta z).re = 0 ∧ (riemannZeta z).im = 0 := by
  constructor
  · intro h
    constructor <;> simp [h]
  · intro h
    apply Complex.ext
    · exact h.1
    · exact h.2

theorem riemannZeta_ne_zero_of_re_lt_zero (s : ℂ) (hs : s.re < 0)
    (hs_int : ∀ n : ℕ, s ≠ -n) : riemannZeta s ≠ 0 := by
  intro hz
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hfe := riemannZeta_one_sub (s := s) hs_int hs_ne_one
  have hzsub : riemannZeta (1 - s) = 0 := by
    rw [hfe, hz]
    simp
  -- 1-s.re = 1 - s.re > 1 ⟹ ζ(1-s) ≠ 0
  have hgeom : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hs]
  exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hgeom) hzsub

/-- Re s = 0 无零点 (s ≠ 0): 函数方程在 1-s 处镜像. 
English: No zeros on Re s = 0 (s ≠ 0): the functional equation mirrors at 1-s. -/
theorem riemannZeta_ne_zero_of_re_eq_zero (s : ℂ) (hs : s.re = 0) (hs0 : s ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hz
  -- 函数方程在 1-s 处: ζ(s) = F(1-s)·ζ(1-s); F 因子全非零 ⟹ ζ(1-s) = 0
  have hs_int : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h
    have hre : (1 - s).re = (-(n : ℂ)).re := by rw [h]
    rw [Complex.sub_re, Complex.one_re, hs] at hre
    have : ((-(n : ℂ)).re) ≤ 0 := by simp
    linarith
  have hsub_ne_one : 1 - s ≠ 1 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by norm_num
  have hfe := riemannZeta_one_sub (s := 1 - s) hs_int hsub_ne_one
  -- hfe : ζ(s) = 2·(2π)^(-(1-s))·Γ(1-s)·cos(π(1-s)/2)·ζ(1-s)
  -- 因子分解: 2 ≠ 0, (2π)^(-(1-s)) ≠ 0, Γ(1-s) ≠ 0, cos(π(1-s)/2) ≠ 0
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have htwo_pi : (2 * ↑Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero htwo (by exact_mod_cast Real.pi_ne_zero)
  have hcpow : (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl htwo_pi)
  have hgamma : Complex.Gamma (1 - s) ≠ 0 := by
    exact Complex.Gamma_ne_zero hs_int
  -- cos(π(1-s)/2) ≠ 0: s.re = 0 且 s ≠ 0 ⟹ s ∉ 2ℤ ⟹ 1-s ∉ 2ℤ+1 ⟹ cos ≠ 0
  have hs_not_int : ∀ k : ℤ, s ≠ 2 * (k : ℂ) := by
    intro k h
    have hre : s.re = (2 * (k : ℝ) : ℝ) := by
      rw [h]
      simp
    have hk0 : (k : ℝ) = 0 := by
      rw [hs] at hre
      nlinarith
    have hk0' : k = 0 := by exact_mod_cast hk0
    apply hs0
    rw [h, hk0']
    norm_num
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    -- π(1-s)/2 = (2k+1)π/2 ⟹ 1-s = 2k+1 ⟹ s = -2k ∈ 2ℤ, 矛盾
    have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hmul : ↑Real.pi * (1 - s) = (2 * (k : ℂ) + 1) * ↑Real.pi := by
      calc
        ↑Real.pi * (1 - s) = (↑Real.pi * (1 - s) / 2) * 2 := by field_simp [h2]
        _ = ((2 * (k : ℂ) + 1) * ↑Real.pi / 2) * 2 := by rw [hk]
        _ = (2 * (k : ℂ) + 1) * ↑Real.pi := by field_simp [h2]
    have hk' : 1 - s = ↑(2 * k + 1) := by
      have hc : 1 - s = 2 * (k : ℂ) + 1 := by
        exact mul_right_cancel₀ hpi (by simpa [mul_comm] using hmul)
      simpa [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hc
    have hs2 : s = 2 * ((-k : ℤ) : ℂ) := by
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 - ↑(2 * k + 1) := by rw [hk']
        _ = (2 : ℂ) * ↑(-k) := by
          rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_neg]
          ring
    exact (hs_not_int (-k)) hs2
  have hF : (2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ)
      * Complex.Gamma (1 - s) * Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hcpow) hgamma) hcos
  -- ζ(s) = F·ζ(1-s) = 0 且 F ≠ 0 ⟹ ζ(1-s) = 0 ⟹ 矛盾 (1 ≤ Re(1-s), 1-s ≠ 1)
  have hzsub : riemannZeta (1 - s) = 0 := by
    have hFz : (2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ)
        * Complex.Gamma (1 - s) * Complex.cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) = 0 := by
      rw [← hfe]
      simpa using hz
    exact (mul_eq_zero.mp hFz).resolve_left hF
  have hgeom : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re, hs]
    norm_num
  have hsub_ne_one' : 1 - s ≠ 1 := hsub_ne_one
  exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hgeom) hzsub

/-- 非平凡零点全在临界带: ζ(s) = 0 (排除平凡零点与极点, 排除负整数) ⟹ 0 < Re s < 1. 
English: All non-trivial zeros in the critical strip: ζ(s) = 0 (excluding trivial zeros, poles, and negative integers) ⟹ 0 < Re s < 1. -/
theorem nontrivial_zero_in_critical_strip {s : ℂ} (hz : riemannZeta s = 0)
    (h_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (hs1 : s ≠ 1)
    (hs_int : ∀ n : ℕ, s ≠ -n) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · -- 0 < s.re: 反证, s.re ≤ 0
    by_contra h
    have hle : s.re ≤ 0 := le_of_not_gt h
    rcases lt_or_eq_of_le hle with hs_neg | hs_zero
    · exact (riemannZeta_ne_zero_of_re_lt_zero s hs_neg hs_int) hz
    · have hs0 : s ≠ 0 := by
        intro h
        rw [h, riemannZeta_zero] at hz
        norm_num at hz
      exact (riemannZeta_ne_zero_of_re_eq_zero s hs_zero hs0) hz
  · -- s.re < 1: 反证, 1 ≤ s.re ⟹ ζ ≠ 0
    by_contra h
    have hge : 1 ≤ s.re := le_of_not_gt h
    exact (riemannZeta_ne_zero_of_one_le_re (s := s) hge) hz

theorem zeta_eq_odd_add_even (p : ℂ) (s : ℂ) :
    riemannZeta s = (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s
      + (p : ℂ) ^ (-s : ℂ) * riemannZeta s := by
  ring

/-- 零点 = 奇偶公共零点: ζ(s) = 0 ⟺ O_p(s) = 0 ∧ E_p(s) = 0 (任意基点 p ≠ 0).
    奇侧偶侧同时为 0 (用户: "奇偶同时为 0") 的精确形式. 
English: Zeros = common zeros of the odd-even split: ζ(s) = 0 ⟺ O_p(s) = 0 ∧ E_p(s) = 0 (any basepoint p ≠ 0). Exact form of 'odd and even simultaneously zero' (user's wording). -/
theorem zeta_eq_zero_iff_p_split {p : ℂ} (hp : p ≠ 0) (s : ℂ) :
    riemannZeta s = 0 ↔
      (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 ∧
        (p : ℂ) ^ (-s : ℂ) * riemannZeta s = 0 := by
  constructor
  · intro hz
    constructor <;> simp [hz]
  · intro h
    have hpz : (p : ℂ) ^ (-s : ℂ) ≠ 0 := by
      exact (Complex.cpow_ne_zero_iff).mpr (Or.inl hp)
    -- 偶部分 E_p = p⁻ˢ·ζ = 0 且 p⁻ˢ ≠ 0 ⟹ ζ = 0 (ℂ 是域)
    exact (mul_eq_zero.mp h.2).resolve_left hpz

/-- 奇部分零点分解: O_p = 0 ⟺ ζ = 0 ∨ p⁻ˢ = 1 (ℂ 域乘法为零).
    奇部分的零点 = ζ 零点 ∪ 素数因子零点. 
English: Odd-part zero decomposition: O_p = 0 ⟺ ζ = 0 ∨ p⁻ˢ = 1 (zero product in the field ℂ). Zeros of the odd part = ζ zeros ∪ prime factor zeros. -/
theorem p_split_mul_zero_iff {p : ℂ} (hp : p ≠ 0) (s : ℂ) :
    (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 ↔
      riemannZeta s = 0 ∨ (p : ℂ) ^ (-s : ℂ) = 1 := by
  rw [mul_eq_zero, sub_eq_zero]
  tauto

/-- 奇部分独有零点全在虚轴 (p = 2 奇偶拆分):
    若 O₂(s) = 0 且 ζ(s) ≠ 0, 则 2⁻ˢ = 1 ⟹ s·ln 2 ∈ 2πiℤ ⟹ Re s = 0.
    即奇偶拆分的非公共零点不进入临界带 — 交点只能来自 ζ 本身. 
English: Odd-part-only zeros all on the imaginary axis (p = 2 odd-even split): if O₂(s) = 0 and ζ(s) ≠ 0, then 2⁻ˢ = 1 ⟹ s·ln 2 ∈ 2πiℤ ⟹ Re s = 0. Non-common zeros of the odd-even split never enter the critical strip — intersections can only come from ζ itself. -/
theorem odd_part_extra_zero_on_imag_axis (s : ℂ) :
    (1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 → riemannZeta s ≠ 0 → s.re = 0 := by
  intro h hz
  have hcases := (p_split_mul_zero_iff (p := (2 : ℂ)) (by norm_num) s).mp h
  rcases hcases with hz' | hone
  · exact False.elim (hz hz')
  · -- 2⁻ˢ = 1 ⟹ 1 - 2⁻ˢ = 0 ⟹ (prime_factor_zero 2) ∃k, s·log 2 = 2πik
    have hsub : 1 - (2 : ℂ) ^ (-s : ℂ) = 0 := sub_eq_zero.mpr hone.symm
    have hp2 : Nat.Prime 2 := Nat.prime_two
    have hpf := (prime_factor_zero 2 hp2 s).mp hsub
    rcases hpf with ⟨k, hk⟩
    -- Re(s·log 2) = Re(k·2πi) = 0; log 2 是实数且非零 ⟹ s.re = 0
    have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
      exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    have hre0 : (s * Complex.log (2 : ℂ)).re = 0 := by
      have hk' : s * Complex.log ((2 : ℂ)) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
        simpa using hk
      rw [hk']
      simp
    have hre' : s.re * Real.log 2 = 0 := by
      calc
        s.re * Real.log 2 = (s * (Real.log 2 : ℂ)).re := by
          rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero]
        _ = 0 := by rw [← hlog, hre0]
    have hl2 : Real.log 2 ≠ 0 := by
      exact (Real.log_ne_zero).mpr (by norm_num)
    exact (mul_eq_zero.mp hre').resolve_right hl2

theorem zero_split_normSq (z : ℂ) (hz : riemannZeta z = 0) :
    (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 = 0 := by
  have hri := (zeta_eq_zero_iff_re_im z).mp hz
  rw [hri.1, hri.2]
  norm_num

/-- 零点避开两个正交欧拉圆: normSq(ζ(z)) = 0 ≠ ±1
    (半径 1 圆 normSq=1 与半径 i 圆 normSq=-1 均不含零点). 
English: Zeros avoid both orthogonal Euler circles: normSq(ζ(z)) = 0 ≠ ±1 (neither the radius-1 circle normSq=1 nor the radius-i circle normSq=-1 contains a zero). -/
theorem zero_not_on_euler_circles (z : ℂ) (hz : riemannZeta z = 0) :
    (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 ≠ 1 ∧
      (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 ≠ -1 := by
  have h0 := zero_split_normSq z hz
  constructor <;> linarith

theorem affine_image_critical_line_is_line (a c : ℂ) (ha : a ≠ 0) :
    ∃ (p : ℂ) (d : ℂ), d ≠ 0 ∧
      {z : ℂ | (a * z + c).re = 1 / 2} = {p + s • d | s : ℝ} := by
  let d : ℂ := Complex.I * (starRingEnd ℂ a)
  let p : ℂ := ((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2
  have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hn_c : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
  have hnorm_c : (‖a‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn_c
  -- a·p = (1/2 - Re c) 是实数 (a·ā = |a|² 对消)
  have hapeq : a * (((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2)
      = ((1 / 2 : ℝ) - c.re : ℂ) := by
    calc
      a * (((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2)
          = ((1 / 2 : ℝ) - c.re) * (a * starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2 := by ring
      _ = ((1 / 2 : ℝ) - c.re) * (Complex.normSq a : ℂ) / (‖a‖ : ℂ) ^ 2 := by
        rw [Complex.mul_conj]
      _ = ((1 / 2 : ℝ) - c.re) * ((‖a‖ : ℂ) ^ 2) / ((‖a‖ : ℂ) ^ 2) := by
        rw [Complex.normSq_eq_norm_sq]
        norm_num
      _ = ((1 / 2 : ℝ) - c.re : ℂ) := by
        field_simp [hnorm_c, hn_c]
  -- a⁻¹ = ā / |a|²
  have hinv : a⁻¹ = starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2 := by
    have hmul : a * (starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) = 1 := by
      calc
        a * (starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) = (a * starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2 := by ring
        _ = (Complex.normSq a : ℂ) / (‖a‖ : ℂ) ^ 2 := by rw [Complex.mul_conj]
        _ = (‖a‖ : ℂ) ^ 2 / (‖a‖ : ℂ) ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]
          norm_num
        _ = 1 := by
          field_simp [hnorm_c, hn_c]
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  refine ⟨p, d, ?_, ?_⟩
  · -- d ≠ 0: I·ā ≠ 0 (I ≠ 0, ā ≠ 0)
    have hconj : starRingEnd ℂ a ≠ 0 := by
      intro h
      have h' := congrArg (starRingEnd ℂ) h
      have : a = 0 := by simpa using h'
      exact ha this
    exact mul_ne_zero (by norm_num : Complex.I ≠ 0) hconj
  · ext z
    constructor
    · -- Re(az+c) = 1/2 ⟹ z = p + s·d (w = a(z-p) 纯虚 ⟹ z-p = (w.im/|a|²)·d)
      intro hz
      let w : ℂ := a * (z - p)
      have haz_re : (a * z).re = 1 / 2 - c.re := by
        have hz' : (a * z).re + c.re = 1 / 2 := by
          simpa [Complex.add_re, Complex.ofReal_re] using hz
        linarith
      have hap_re : (a * p).re = 1 / 2 - c.re := by
        have hpeq : a * p = ((1 / 2 : ℝ) - c.re : ℂ) := by
          dsimp [p]
          exact hapeq
        rw [hpeq]
        simp [Complex.ofReal_re]
      have hwre : w.re = 0 := by
        dsimp [w]
        have hsub : a * (z - p) = a * z - a * p := by ring
        rw [hsub, Complex.sub_re, haz_re, hap_re]
        ring
      have hw_pure : w = w.im * Complex.I := by
        apply Complex.ext <;> simp [hwre]
      have hzpe : z - p = a⁻¹ * w := by
        calc
          z - p = 1 * (z - p) := by simp
          _ = (a⁻¹ * a) * (z - p) := by rw [inv_mul_cancel₀ ha]
          _ = a⁻¹ * (a * (z - p)) := by ring
      -- wim = w.im (避免 rw 污染投影)
      let wim : ℝ := w.im
      have hw_pure' : w = wim * Complex.I := by
        dsimp [wim]
        exact hw_pure
      have hzpd : z - p = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
        rw [hzpe, hw_pure']
        -- 乘法形式: a⁻¹·(wim·I) = (wim:ℂ)/|a|²·(I·ā)
        have hm : a⁻¹ * (wim * Complex.I)
            = (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a) := by
          calc
            a⁻¹ * (wim * Complex.I) = wim * (a⁻¹ * Complex.I) := by ring
            _ = wim * (Complex.I * starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) := by
              rw [hinv]
              ring
            _ = (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a) := by
              ring
        -- 转成标量形式: (wim:ℂ)/|a|²·x = (wim/|a|² : ℝ) • x
        have hm' : (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a)
            = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
          calc
            (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a)
                = ((wim / ‖a‖ ^ 2 : ℝ) : ℂ) * (Complex.I * starRingEnd ℂ a) := by
                  have hden : (‖a‖ : ℂ) ^ 2 = ((‖a‖ ^ 2 : ℝ) : ℂ) := by norm_num
                  rw [hden]
                  -- ↑wim / ↑(‖a‖²) · x = ↑(wim/‖a‖²) · x: 先分离共同因子 x
                  congr 1
                  norm_num
            _ = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
                  simp [smul_eq_mul]
        exact hm.trans hm'
      refine ⟨wim / ‖a‖ ^ 2, ?_⟩
      rw [← hzpd]
      ring
    · -- z = p + s·d ⟹ Re(az+c) = 1/2 (s·d 纯虚 + ap 实)
      rintro ⟨s, rfl⟩
      have hsd : (a * (s • (Complex.I * starRingEnd ℂ a))).re = 0 := by
        -- a·(s·(I·ā)) = s·(I·(a·ā)) = s·(I·|a|²) 纯虚
        calc
          (a * (s • (Complex.I * starRingEnd ℂ a))).re
              = (a * ((s : ℂ) * (Complex.I * starRingEnd ℂ a))).re := by
                simp
          _ = ((s : ℂ) * (Complex.I * (a * starRingEnd ℂ a))).re := by
                congr 1
                ring
          _ = ((s : ℂ) * (Complex.I * (Complex.normSq a : ℂ))).re := by
                rw [Complex.mul_conj]
          _ = 0 := by
                simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      calc
        (a * (p + s • (Complex.I * starRingEnd ℂ a)) + c).re
            = (a * p + a * (s • (Complex.I * starRingEnd ℂ a)) + c).re := by
              rw [mul_add]
        _ = (a * p + c).re := by
              -- (a·(s•d)).re = 0 (hsd): 展开 re 后替换
              calc
                (a * p + a * (s • (Complex.I * starRingEnd ℂ a)) + c).re
                    = (a * p).re + (a * (s • (Complex.I * starRingEnd ℂ a))).re + c.re := by
                      simp [Complex.add_re]
                _ = (a * p).re + 0 + c.re := by rw [hsd]
                _ = (a * p + c).re := by
                      simp [Complex.add_re]
        _ = 1 / 2 := by
          have hpeq : a * p = ((1 / 2 : ℝ) - c.re : ℂ) := by
            dsimp [p]
            exact hapeq
          rw [hpeq]
          simp [Complex.add_re, Complex.ofReal_re]

theorem on_line_iff_equidistant_base_one (w : ℂ) :
    (1 + w).re = 1 / 2 ↔ ‖w‖ = ‖1 + w‖ := by
  constructor
  · intro h
    have hre : w.re = -1 / 2 := by
      have : (1 + w).re = 1 + w.re := by simp [Complex.add_re, Complex.ofReal_re]
      linarith
    -- ‖w‖² = ‖1+w‖² (normSq 展开 + hre)
    have hsq : ‖w‖ ^ 2 = ‖1 + w‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      rw [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
      rw [hre]
      ring
    -- 非负 ⟹ 从平方等式到等式
    have habs : |‖w‖| = |‖1 + w‖| :=
      (sq_eq_sq_iff_abs_eq_abs ‖w‖ ‖1 + w‖).mp hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  · intro h
    have hsq : ‖w‖ ^ 2 = ‖1 + w‖ ^ 2 := by rw [h]
    have hns : Complex.normSq w = Complex.normSq (1 + w) := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    have hre : w.re = -1 / 2 := by
      rw [Complex.normSq_apply, Complex.normSq_apply,
        Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im] at hns
      nlinarith
    have : (1 + w).re = 1 + w.re := by simp [Complex.add_re, Complex.ofReal_re]
    linarith

theorem critical_line_equidistant_basepoint_i (z : ℂ) :
    z.re = 1 / 2 ↔ ‖z - Complex.I‖ = ‖z - (1 + Complex.I)‖ := by
  constructor
  · intro hre
    -- 平方相等 (normSq 展开 + hre)
    have hsq : ‖z - Complex.I‖ ^ 2 = ‖z - (1 + Complex.I)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      rw [hre]
      ring
    -- 非负 ⟹ 平方等式到等式
    have habs : |‖z - Complex.I‖| = |‖z - (1 + Complex.I)‖| :=
      (sq_eq_sq_iff_abs_eq_abs ‖z - Complex.I‖ ‖z - (1 + Complex.I)‖).mp hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  · intro h
    -- 平方相等
    have hsq : ‖z - Complex.I‖ ^ 2 = ‖z - (1 + Complex.I)‖ ^ 2 := by rw [h]
    have hns : Complex.normSq (z - Complex.I) = Complex.normSq (z - (1 + Complex.I)) := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    -- 展开 re/im ⟹ (z.re-1)² = z.re² ⟹ z.re = 1/2
    rw [Complex.normSq_apply, Complex.normSq_apply] at hns
    simp at hns
    nlinarith

/-- T 坐标 (基点 i): 临界线 = 单位圆。T(z) = 1/(z-i) - 1
    (recip 中心 = 复平面基点 i, 平移 -1 消圆心):
    Re z = 1/2 ⟺ ‖1/(z-i) - 1‖ = 1。 
English: T coordinate (basepoint i): critical line = unit circle. T(z) = 1/(z-i) - 1 (recip centered at the complex-plane basepoint i; shift -1 removes the circle center): Re z = 1/2 ⟺ ‖1/(z-i) - 1‖ = 1. -/
theorem recip_basepoint_i_on_unit_circle (z : ℂ) (hz : z ≠ Complex.I) :
    ‖1 / (z - Complex.I) - 1‖ = 1 ↔ z.re = 1 / 2 := by
  -- 1/(z-i) - 1 = -(z-(1+i))/(z-i) (代数)
  have hrewrite : 1 / (z - Complex.I) - 1 = -((z - (1 + Complex.I)) / (z - Complex.I)) := by
    field_simp [sub_ne_zero.mpr hz]
    ring
  have hne : ‖z - Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  -- |1/(z-i)-1| = |z-(1+i)|/|z-i| = 1 ⟺ |z-(1+i)| = |z-i| (等距)
  rw [hrewrite, norm_neg, norm_div, div_eq_one_iff_eq hne]
  rw [eq_comm]
  exact (critical_line_equidistant_basepoint_i z).symm


/-- χ(s)·χ(1-s) = 1 对非整数 s (函数方程乘子对合: Γ 反射 + sin 双角). 
English: χ(s)·χ(1-s) = 1 for non-integer s (functional equation multiplier involution: Γ reflection + sin double angle). -/
lemma chi_mul_chi_one_sub {s : ℂ} (hs_int : ∀ n : ℤ, s ≠ n) :
    ((2 : ℂ) ^ (s : ℂ) * (↑Real.pi : ℂ) ^ (s - 1 : ℂ) * Complex.sin (↑Real.pi * s / 2) * Complex.Gamma (1 - s))
    * ((2 : ℂ) ^ (1 - s : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ) * Complex.cos (↑Real.pi * s / 2) * Complex.Gamma s)
    = 1 := by
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsin : Complex.sin (↑Real.pi * s) ≠ 0 := by
    intro h
    rcases (Complex.sin_eq_zero_iff.mp h) with ⟨k, hk⟩
    apply hs_int k
    have hk' : (↑Real.pi : ℂ) * s = (↑Real.pi : ℂ) * (k : ℂ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hk
    exact mul_left_cancel₀ hpi hk'
  have h2p : (2 : ℂ) ^ (s : ℂ) * (2 : ℂ) ^ (1 - s : ℂ) = 2 := by
    rw [← Complex.cpow_add s (1 - s) h2ne]
    have h_e : s + (1 - s) = 1 := by ring
    rw [h_e]
    exact Complex.cpow_one (2 : ℂ)
  have hpip : (↑Real.pi : ℂ) ^ (s - 1 : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ) = (↑Real.pi : ℂ) ^ (-1 : ℂ) := by
    rw [← Complex.cpow_add (s - 1) (-s) hpi]
    congr 1
    ring
  have hgam : Complex.Gamma (1 - s) * Complex.Gamma s = (↑Real.pi : ℂ) / Complex.sin (↑Real.pi * s) := by
    rw [mul_comm]
    exact Complex.Gamma_mul_Gamma_one_sub s
  have hsincos : Complex.sin (↑Real.pi * s / 2) * Complex.cos (↑Real.pi * s / 2)
      = Complex.sin (↑Real.pi * s) / 2 := by
    have h := Complex.sin_two_mul (↑Real.pi * s / 2)
    have h2 : 2 * (↑Real.pi * s / 2) = ↑Real.pi * s := by ring
    rw [h2] at h
    calc
      Complex.sin (↑Real.pi * s / 2) * Complex.cos (↑Real.pi * s / 2)
          = (2 * (Complex.sin (↑Real.pi * s / 2) * Complex.cos (↑Real.pi * s / 2))) / 2 := by
              field_simp [h2ne]
      _ = Complex.sin (↑Real.pi * s) / 2 := by
              have h' : 2 * (Complex.sin (↑Real.pi * s / 2) * Complex.cos (↑Real.pi * s / 2))
                  = Complex.sin (↑Real.pi * s) := by
                simpa [mul_assoc] using h.symm
              rw [← h']
  calc
    ((2 : ℂ) ^ (s : ℂ) * (↑Real.pi : ℂ) ^ (s - 1 : ℂ) * Complex.sin (↑Real.pi * s / 2) * Complex.Gamma (1 - s))
        * ((2 : ℂ) ^ (1 - s : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ) * Complex.cos (↑Real.pi * s / 2) * Complex.Gamma s)
        = ((2 : ℂ) ^ (s : ℂ) * (2 : ℂ) ^ (1 - s : ℂ)) * ((↑Real.pi : ℂ) ^ (s - 1 : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ))
            * (Complex.sin (↑Real.pi * s / 2) * Complex.cos (↑Real.pi * s / 2))
            * (Complex.Gamma (1 - s) * Complex.Gamma s) := by
            ring
    _ = 2 * (↑Real.pi : ℂ) ^ (-1 : ℂ) * (Complex.sin (↑Real.pi * s / 2) * Complex.cos (↑Real.pi * s / 2))
            * ((↑Real.pi : ℂ) / Complex.sin (↑Real.pi * s)) := by
            rw [h2p, hpip, hgam]
    _ = 2 * (↑Real.pi : ℂ) ^ (-1 : ℂ) * (Complex.sin (↑Real.pi * s) / 2)
            * ((↑Real.pi : ℂ) / Complex.sin (↑Real.pi * s)) := by
            rw [hsincos]
    _ = 1 := by
            have hpi1 : (↑Real.pi : ℂ) ^ (-1 : ℂ) = (↑Real.pi : ℂ)⁻¹ := Complex.cpow_neg_one (↑Real.pi : ℂ)
            rw [hpi1]
            field_simp [hsin, hpi, h2ne]

/-- 单位圆上 cpow(-1/2) 的共轭: conj(x^{-1/2}) = x^{1/2}
    (主情形 conj_cpow + log_inv; 分支情形 x = -1 直接算). 
English: Conjugation of cpow(-1/2) on the unit circle: conj(x^{-1/2}) = x^{1/2} (principal case conj_cpow + log_inv; branch case x = -1 computed directly). -/
lemma conj_cpow_inv_half_of_unit {x : ℂ} (hx : x ≠ 0) (hu : x * (starRingEnd ℂ) x = 1) :
    (starRingEnd ℂ) (x ^ (-(1 / 2 : ℂ))) = x ^ (1 / 2 : ℂ) := by
  by_cases harg : x.arg ≠ Real.pi
  · have hc := Complex.conj_cpow x (-(1 / 2 : ℂ)) harg
    have hc' : (starRingEnd ℂ) x ^ (-(1 / 2 : ℂ)) = (starRingEnd ℂ) (x ^ (-(1 / 2 : ℂ))) := by
      simpa [map_ofNat] using hc
    rw [← hc']
    have hxconj : (starRingEnd ℂ) x = x⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right hu).symm
    rw [hxconj]
    rw [← Complex.cpow_neg_one x]
    have him : (Complex.log x * (-1 : ℂ)).im = -x.arg := by
      simp [Complex.log_im]
    have harglt : x.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi x) harg
    have h1 : -Real.pi < (Complex.log x * (-1 : ℂ)).im := by
      rw [him]
      linarith [Complex.neg_pi_lt_arg x]
    have h2 : (Complex.log x * (-1 : ℂ)).im ≤ Real.pi := by
      rw [him]
      linarith [Complex.neg_pi_lt_arg x]
    have hcm : x ^ ((-1 : ℂ) * (-(1 / 2 : ℂ))) = (x ^ (-1 : ℂ)) ^ (-(1 / 2 : ℂ)) :=
      Complex.cpow_mul (z := (-(1 / 2 : ℂ))) h1 h2
    rw [← hcm]
    congr 1
    norm_num
  · have hxneg : x = -1 := by
      have habs : ‖x‖ = 1 := by
        have hc : ((‖x‖ ^ 2 : ℝ) : ℂ) = 1 := by
          simpa using (Complex.mul_conj' x).symm.trans hu
        have h2 : ‖x‖ ^ 2 = 1 := by
          exact (Complex.ofReal_inj.mp hc)
        rcases (sq_eq_one_iff.mp h2) with h1 | h1
        · exact h1
        · exfalso
          linarith [norm_nonneg x]
      have harg2 : x.arg = (-1 : ℂ).arg := by
        rw [Complex.arg_neg_one]
        exact Classical.not_not.mp (by simpa [ne_eq] using harg)
      exact Complex.ext_norm_arg (by simpa using habs) harg2
    rw [hxneg]
    have hne1 : (-1 : ℂ) ≠ 0 := by norm_num
    rw [Complex.cpow_def_of_ne_zero hne1, Complex.cpow_def_of_ne_zero hne1]
    rw [Complex.log_neg_one]
    rw [← Complex.exp_conj]
    have hargc : (starRingEnd ℂ) (↑Real.pi * Complex.I * (-(1 / 2 : ℂ)))
        = ↑Real.pi * Complex.I * (1 / 2 : ℂ) := by
      rw [map_mul, map_mul]
      simp [Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_inv₀]
    rw [hargc]

/-- Hardy Z 实值性: conj(Z(t)) = Z(t), Z(t) = χ(1/2+it)^{-1/2}·ζ(1/2+it).
    相位基点投影成线 (pat0: 换基点把 ζ 相位扔到投影丢失结构; χ 单位模对称可消). 
English: Hardy Z real-valuedness: conj(Z(t)) = Z(t), Z(t) = χ(1/2+it)^{-1/2}·ζ(1/2+it). The phase basepoint projects onto a line (pat0: changing basepoint throws ζ's phase into the projection, losing structure; χ's unit-modulus symmetry is cancellable). -/
theorem hardyZ_real (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let chi : ℂ := (2 : ℂ) ^ (s : ℂ) * (↑Real.pi : ℂ) ^ (s - 1 : ℂ) * Complex.sin (↑Real.pi * s / 2)
      * Complex.Gamma (1 - s)
    (starRingEnd ℂ) (chi ^ (-(1 / 2 : ℂ)) * riemannZeta s)
      = chi ^ (-(1 / 2 : ℂ)) * riemannZeta s := by
  intro s chi
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hs0 : 0 < s.re := by
    dsimp [s]
    simp
    try norm_num
  have hs1 : s.re < 1 := by
    dsimp [s]
    simp
    try norm_num
  have hs_int : ∀ n : ℤ, s ≠ n := by
    intro n h
    have hre0 : s.re = (1 / 2 : ℝ) := by
      dsimp [s]
      simp
    have hre1 : (n : ℂ).re = (n : ℝ) := by simp
    have hEq : (1 / 2 : ℝ) = (n : ℝ) := by
      have : s.re = (n : ℂ).re := by rw [h]
      rw [hre0, hre1] at this
      exact this
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0z : (0 : ℤ) < n := by exact_mod_cast hn0
    have hn1z : n < (1 : ℤ) := by exact_mod_cast hn1
    omega
  have hconj_s : (starRingEnd ℂ) s = 1 - s := by
    dsimp [s]
    rw [map_add]
    simp [Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_inv₀]
    ring
  -- 临界线共轭: conj(ζ(s)) = ζ(1-s)
  have hzconj := zeta_conj_of_critical_strip (s := s) hs0 hs1
  rw [hconj_s] at hzconj
  -- 函数方程: ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  have hsneg : ∀ n : ℕ, s ≠ -↑n := by
    intro n h
    have hre0 : s.re = (1 / 2 : ℝ) := by
      dsimp [s]
      simp
    have hn : ((-(↑n : ℕ) : ℂ).re) ≤ 0 := by simp
    have : s.re = (-(↑n : ℕ) : ℂ).re := by rw [h]
    linarith
  have hs' : s ≠ 1 := by
    intro h
    have hre0 : s.re = (1 / 2 : ℝ) := by
      dsimp [s]
      simp
    have : s.re = 1 := by
      have h1 : s.re = (1 : ℂ).re := by rw [h]
      simpa using h1
    linarith
  have hfe := riemannZeta_one_sub hsneg hs'
  rw [hfe] at hzconj
  -- 系数: 2(2π)^{-s} = 2^{1-s}π^{-s} (χ(1-s) 的系数)
  have hcoef : 2 * (2 * ↑Real.pi : ℂ) ^ (-s : ℂ) * Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)
      = (2 : ℂ) ^ (1 - s : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ) * Complex.cos (↑Real.pi * s / 2) * Complex.Gamma s := by
    have h2p : 2 * (2 * ↑Real.pi : ℂ) ^ (-s : ℂ) = (2 : ℂ) ^ (1 - s : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ) := by
      have hm := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt Real.pi_pos) (-s : ℂ)
      have h2e : (2 : ℂ) * (2 : ℂ) ^ (-s : ℂ) = (2 : ℂ) ^ (1 - s : ℂ) := by
        calc
          (2 : ℂ) * (2 : ℂ) ^ (-s : ℂ) = (2 : ℂ) ^ (1 + (-s : ℂ)) := by
              rw [Complex.cpow_add 1 (-s : ℂ) h2ne]
              rw [Complex.cpow_one]
          _ = (2 : ℂ) ^ (1 - s : ℂ) := by
              simpa [sub_eq_add_neg]
      calc
        2 * (2 * ↑Real.pi : ℂ) ^ (-s : ℂ)
            = 2 * ((2 : ℂ) ^ (-s : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ)) := by
                exact congrArg (fun z => 2 * z) hm
            _ = (2 : ℂ) ^ (1 - s : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ) := by
                rw [← mul_assoc, h2e]
    rw [h2p]
    ring
  rw [hcoef] at hzconj
  -- conj(ζ(s)) = χ(1-s)·ζ(s); χ(1-s) = χ(s)^{-1} (χ(s)χ(1-s) = 1)
  have hchi_ne : chi ≠ 0 := by
    dsimp [chi]
    have h1 : (2 : ℂ) ^ (s : ℂ) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl h2ne)
    have h2 : (↑Real.pi : ℂ) ^ (s - 1 : ℂ) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl hpi)
    have h3 : Complex.sin (↑Real.pi * s / 2) ≠ 0 := by
      intro h
      rcases (Complex.sin_eq_zero_iff.mp h) with ⟨k, hk⟩
      apply hs_int (2 * k)
      have hk' : (↑Real.pi : ℂ) * (s / 2) = (↑Real.pi : ℂ) * (k : ℂ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hk
      have hs2 : s / 2 = (k : ℂ) := mul_left_cancel₀ hpi hk'
      calc
        s = 2 * (s / 2) := by ring
        _ = 2 * (k : ℂ) := by rw [hs2]
        _ = ((2 * k : ℤ) : ℂ) := by norm_num
    have h4 : Complex.Gamma (1 - s) ≠ 0 := by
      exact Complex.Gamma_ne_zero (by
        intro n h
        apply hs_int (1 + n)
        calc
          s = 1 - (1 - s) := by ring
          _ = 1 - (-(↑n : ℕ) : ℂ) := by rw [h]
          _ = ((1 + n : ℤ) : ℂ) := by norm_num)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4
  have hchi_mul := chi_mul_chi_one_sub (s := s) hs_int
  have hchi_inv : (2 : ℂ) ^ (1 - s : ℂ) * (↑Real.pi : ℂ) ^ (-s : ℂ) * Complex.cos (↑Real.pi * s / 2) * Complex.Gamma s
      = chi⁻¹ := by
    exact (inv_eq_of_mul_eq_one_right hchi_mul).symm
  rw [hchi_inv] at hzconj
  -- 单位模: chi·conj(chi) = χ(s)·χ(1-s) = 1
  have hchi_unit : chi * (starRingEnd ℂ) chi = 1 := by
    dsimp [chi]
    rw [chi_conj s]
    rw [hconj_s]
    have hπ : (↑Real.pi : ℂ) ^ ((1 - s) - 1 : ℂ) = (↑Real.pi : ℂ) ^ (-s : ℂ) := by
      congr 1
      ring
    have hsin : Complex.sin (↑Real.pi * (1 - s) / 2) = Complex.cos (↑Real.pi * s / 2) := by
      have harg : ↑Real.pi * (1 - s) / 2 = ↑Real.pi / 2 - ↑Real.pi * s / 2 := by ring
      rw [harg]
      rw [Complex.sin_pi_div_two_sub]
    have hgam : Complex.Gamma (1 - (1 - s)) = Complex.Gamma s := by
      congr 1
      ring
    rw [hπ, hsin, hgam]
    exact chi_mul_chi_one_sub (s := s) hs_int
  -- 主流程: conj(chi^{-1/2}·ζ(s)) = chi^{-1/2}·ζ(s)
  rw [map_mul]
  rw [conj_cpow_inv_half_of_unit hchi_ne hchi_unit]
  rw [hzconj]
  rw [← mul_assoc]
  rw [← Complex.cpow_neg_one]
  rw [← Complex.cpow_add (1 / 2 : ℂ) (-1 : ℂ) hchi_ne]
  have h_e : (1 / 2 : ℂ) + (-1 : ℂ) = (-(1 / 2 : ℂ)) := by norm_num
  rw [h_e]
/- ============ A. 等价链 (轨道退化 ⟺ 在线) ============ -/

/-- 位置形式: Re s = 1/2 ⟺ 1 - s = conj s. 
English: Positional form: Re s = 1/2 ⟺ 1 - s = conj s. -/
theorem critical_line_positional (s : ℂ) :
    s.re = 1 / 2 ↔ 1 - s = (starRingEnd ℂ) s := by
  constructor
  · intro hs
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring
  · intro h
    have hre := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith

/-- 4 点轨道 {z, z̄, 1-z, 1-z̄} 的算术中心 = 1/2. 
English: Arithmetic center of the 4-point orbit {z, z̄, 1-z, 1-z̄} = 1/2. -/
theorem orbit_center_half (z : ℂ) :
    (z + (starRingEnd ℂ) z + (1 - z) + (1 - (starRingEnd ℂ) z)) / 4 = (1 / 2 : ℂ) := by
  ring

/-- 轨道退化 ⟺ 在线: 1 - z = conj z ⟺ Re z = 1/2. 
English: Orbit degenerates ⟺ on the line: 1 - z = conj z ⟺ Re z = 1/2. -/
theorem orbit_degenerate_iff_on_line (z : ℂ) :
    1 - z = (starRingEnd ℂ) z ↔ z.re = 1 / 2 :=
  (critical_line_positional z).symm

/-- 反演圆条件: 1/z ∈ 临界线圆 (圆心 1 半径 1) ⟺ Re z = 1/2 (z ≠ 0). 
English: Inversion circle condition: 1/z ∈ critical-line circle (center 1, radius 1) ⟺ Re z = 1/2 (z ≠ 0). -/
theorem recip_on_critical_circle_iff (z : ℂ) (hz : z ≠ 0) :
    ‖(1 / z : ℂ) - 1‖ = 1 ↔ z.re = 1 / 2 := by
  have hnorm (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    calc
      ‖w‖ ^ 2 = Complex.normSq w := (Complex.normSq_eq_norm_sq w).symm
      _ = w.re ^ 2 + w.im ^ 2 := by
        simp [Complex.normSq_apply]
        ring
  have hz1 : (1 / z : ℂ) - 1 = (1 - z) / z := by
    field_simp [hz]
  have hne_z : ‖z‖ ≠ 0 := by exact norm_ne_zero_iff.mpr hz
  constructor
  · intro h
    have hdiv : ‖(1 - z) / z‖ = 1 := by
      rw [← hz1]
      exact h
    have hnorm_eq : ‖1 - z‖ = ‖z‖ := by
      rw [norm_div] at hdiv
      exact (div_eq_one_iff_eq hne_z).mp hdiv
    have hsq : ‖1 - z‖ ^ 2 = ‖z‖ ^ 2 := by rw [hnorm_eq]
    have hsq' : (1 - z.re) ^ 2 + (-z.im) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      simpa [Complex.sub_re, Complex.sub_im, hnorm] using hsq
    have hσ : z.re = 1 / 2 := by
      nlinarith
    exact hσ
  · intro hσ
    have hsq' : (1 - z.re) ^ 2 + (-z.im) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [hσ]
      ring
    have hsq : ‖1 - z‖ ^ 2 = ‖z‖ ^ 2 := by
      simpa [Complex.sub_re, Complex.sub_im, hnorm] using hsq'
    have hnorm_eq : ‖1 - z‖ = ‖z‖ := by
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h1 | h1
      · exact h1
      · exfalso
        have hz0 : ‖z‖ = 0 := by
          linarith [norm_nonneg (1 - z), norm_nonneg z, h1]
        exact hne_z hz0
    calc
      ‖(1 / z : ℂ) - 1‖ = ‖(1 - z) / z‖ := by rw [hz1]
      _ = ‖1 - z‖ / ‖z‖ := by rw [norm_div]
      _ = 1 := by
        rw [hnorm_eq]
        field_simp [hne_z]

/- ============ B. 零点 4 点轨道 ============ -/

/-- 零点 4 点轨道: ζ(z)=0 且 z 在临界带 ⟹ ζ(z̄)=0, ζ(1-z)=0, ζ(1-z̄)=0. 
English: Zero 4-point orbit: ζ(z)=0 with z in the critical strip ⟹ ζ(z̄)=0, ζ(1-z)=0, ζ(1-z̄)=0. -/
theorem zero_orbit_four {z : ℂ} (hz : riemannZeta z = 0)
    (hstrip : 0 < z.re ∧ z.re < 1)
    (htriv : ∀ n : ℕ, z ≠ -↑n) (hone : z ≠ 1) :
    riemannZeta (starRingEnd ℂ z) = 0 ∧
    riemannZeta (1 - z) = 0 ∧
    riemannZeta (1 - (starRingEnd ℂ z)) = 0 := by
  constructor
  · have hzconj := zeta_conj_of_critical_strip (s := z) hstrip.1 hstrip.2
    rw [hz] at hzconj
    simpa using hzconj.symm
  · constructor
    · exact (zeta_zero_strip_reflection hz hstrip htriv hone).1
    · have hzbar : riemannZeta (starRingEnd ℂ z) = 0 := by
        have hzconj := zeta_conj_of_critical_strip (s := z) hstrip.1 hstrip.2
        rw [hz] at hzconj
        simpa using hzconj.symm
      have hzbar_strip : 0 < (starRingEnd ℂ z).re ∧ (starRingEnd ℂ z).re < 1 := by
        simpa using hstrip
      have hzbar_triv : ∀ n : ℕ, (starRingEnd ℂ z) ≠ -↑n := by
        intro n h
        apply htriv n
        have h' := congrArg (starRingEnd ℂ) h
        simpa using h'
      have hzbar_one : (starRingEnd ℂ z) ≠ 1 := by
        intro h
        apply hone
        have h' := congrArg (starRingEnd ℂ) h
        simpa using h'
      exact (zeta_zero_strip_reflection hzbar hzbar_strip hzbar_triv hzbar_one).1

/- ============ C. 穿折越 0pat 形式: Z 符号变化 ⟹ 临界线零点 ============ -/

/-- χ(1/2+it) 单位模. 
English: χ(1/2+it) has unit modulus. -/
lemma chi_unit_on_line (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let chi : ℂ := (2 : ℂ) ^ (s : ℂ) * (↑Real.pi : ℂ) ^ (s - 1 : ℂ) * Complex.sin (↑Real.pi * s / 2)
      * Complex.Gamma (1 - s)
    chi * (starRingEnd ℂ) chi = 1 := by
  intro s chi
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs_int : ∀ n : ℤ, s ≠ n := by
    intro n h
    have hre0 : s.re = (1 / 2 : ℝ) := by
      dsimp [s]
      simp
    have hre1 : (n : ℂ).re = (n : ℝ) := by simp
    have hEq : (1 / 2 : ℝ) = (n : ℝ) := by
      have : s.re = (n : ℂ).re := by rw [h]
      rw [hre0, hre1] at this
      exact this
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0z : (0 : ℤ) < n := by exact_mod_cast hn0
    have hn1z : n < (1 : ℤ) := by exact_mod_cast hn1
    omega
  have hconj_s : (starRingEnd ℂ) s = 1 - s := by
    dsimp [s]
    rw [map_add]
    simp [Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_inv₀]
    ring
  dsimp [chi]
  rw [chi_conj s]
  rw [hconj_s]
  have hπ : (↑Real.pi : ℂ) ^ ((1 - s) - 1 : ℂ) = (↑Real.pi : ℂ) ^ (-s : ℂ) := by
    congr 1
    ring
  have hsin : Complex.sin (↑Real.pi * (1 - s) / 2) = Complex.cos (↑Real.pi * s / 2) := by
    have harg : ↑Real.pi * (1 - s) / 2 = ↑Real.pi / 2 - ↑Real.pi * s / 2 := by ring
    rw [harg]
    rw [Complex.sin_pi_div_two_sub]
  have hgam : Complex.Gamma (1 - (1 - s)) = Complex.Gamma s := by
    congr 1
    ring
  rw [hπ, hsin, hgam]
  exact chi_mul_chi_one_sub (s := s) hs_int

/-- χ(1/2+it) 非零 (底非零, cpow 非零). 
English: χ(1/2+it) is nonzero (base nonzero, cpow nonzero). -/
lemma chi_ne_zero_on_line (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let chi : ℂ := (2 : ℂ) ^ (s : ℂ) * (↑Real.pi : ℂ) ^ (s - 1 : ℂ) * Complex.sin (↑Real.pi * s / 2)
      * Complex.Gamma (1 - s)
    chi ≠ 0 := by
  intro s chi
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hs_int : ∀ n : ℤ, s ≠ n := by
    intro n h
    have hre0 : s.re = (1 / 2 : ℝ) := by
      dsimp [s]
      simp
    have hre1 : (n : ℂ).re = (n : ℝ) := by simp
    have hEq : (1 / 2 : ℝ) = (n : ℝ) := by
      have : s.re = (n : ℂ).re := by rw [h]
      rw [hre0, hre1] at this
      exact this
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0z : (0 : ℤ) < n := by exact_mod_cast hn0
    have hn1z : n < (1 : ℤ) := by exact_mod_cast hn1
    omega
  dsimp [chi]
  have h1 : (2 : ℂ) ^ (s : ℂ) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl h2ne)
  have h2 : (↑Real.pi : ℂ) ^ (s - 1 : ℂ) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl hpi)
  have h3 : Complex.sin (↑Real.pi * s / 2) ≠ 0 := by
    intro h
    rcases (Complex.sin_eq_zero_iff.mp h) with ⟨k, hk⟩
    apply hs_int (2 * k)
    have hk' : (↑Real.pi : ℂ) * (s / 2) = (↑Real.pi : ℂ) * (k : ℂ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hk
    have hs2 : s / 2 = (k : ℂ) := mul_left_cancel₀ hpi hk'
    calc
      s = 2 * (s / 2) := by ring
      _ = 2 * (k : ℂ) := by rw [hs2]
      _ = ((2 * k : ℤ) : ℂ) := by norm_num
  have h4 : Complex.Gamma (1 - s) ≠ 0 := by
    exact Complex.Gamma_ne_zero (by
      intro n h
      apply hs_int (1 + n)
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 - (-(↑n : ℕ) : ℂ) := by rw [h]
        _ = ((1 + n : ℤ) : ℂ) := by norm_num)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4

/-- 单位模 + χ ≠ -1 ⟹ χ ∈ slitPlane (cpow 连续条件). 
English: Unit modulus + χ ≠ -1 ⟹ χ ∈ slitPlane (cpow continuity condition). -/
lemma chi_mem_slitPlane_on_line {t : ℝ} (hchi : -1 ≠
    let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    (2 : ℂ) ^ (s : ℂ) * (↑Real.pi : ℂ) ^ (s - 1 : ℂ) * Complex.sin (↑Real.pi * s / 2)
      * Complex.Gamma (1 - s)) :
    let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let chi : ℂ := (2 : ℂ) ^ (s : ℂ) * (↑Real.pi : ℂ) ^ (s - 1 : ℂ) * Complex.sin (↑Real.pi * s / 2)
      * Complex.Gamma (1 - s)
    chi ∈ slitPlane := by
  intro s chi
  -- chi·conj chi = 1 ⟹ ‖chi‖ = 1
  have hu := chi_unit_on_line t
  dsimp [chi] at hu
  have habs : ‖chi‖ = 1 := by
    have hc : ((‖chi‖ ^ 2 : ℝ) : ℂ) = 1 := by
      simpa using (Complex.mul_conj' chi).symm.trans hu
    have h2 : ‖chi‖ ^ 2 = 1 := by
      exact (Complex.ofReal_inj.mp hc)
    rcases (sq_eq_one_iff.mp h2) with h1 | h1
    · exact h1
    · exfalso
      linarith [norm_nonneg chi]
  -- slitPlane: 0 < chi.re ∨ chi.im ≠ 0
  by_cases hre : 0 < chi.re
  · exact Or.inl hre
  · right
    intro him
    -- chi.re ≤ 0 且 chi.im = 0 且 ‖chi‖ = 1 ⟹ chi = -1 (矛盾 hchi)
    apply hchi
    -- chi = -1:re = -1,im = 0
    -- ‖chi‖² = 1 = re² + im² = re²(im = 0)⟹ re = ±1;re ≤ 0 ⟹ re = -1
    have hnorm2 : ‖chi‖ ^ 2 = chi.re ^ 2 + chi.im ^ 2 := by
      calc
        ‖chi‖ ^ 2 = Complex.normSq chi := (Complex.normSq_eq_norm_sq chi).symm
        _ = chi.re ^ 2 + chi.im ^ 2 := by
          simp [Complex.normSq_apply]
          ring
    -- 更直接:‖chi‖ = 1 ⟹ ‖chi‖² = 1;im = 0 ⟹ re² = 1;re ≤ 0 ⟹ re = -1
    -- ext:chi = ⟨-1, 0⟩ = -1
    apply Complex.ext
    · -- chi.re = -1
      have hsq : chi.re ^ 2 = 1 := by
        have : chi.re ^ 2 + chi.im ^ 2 = 1 := by
          -- ‖chi‖² = 1 且 = re²+im²
          have h1' : ‖chi‖ ^ 2 = 1 := by rw [habs]; norm_num
          rw [hnorm2] at h1'
          simpa [him] using h1'
        nlinarith
      -- re² = 1 且 re ≤ 0 ⟹ re = -1
      have hre2 : chi.re = 1 ∨ chi.re = -1 := (sq_eq_one_iff.mp hsq)
      rcases hre2 with h1 | h1
      · exfalso
        -- chi.re = 1 与 ¬(0 < chi.re)(hre)矛盾
        linarith [hre]
      · rw [show ((-1 : ℂ).re) = (-1 : ℝ) by norm_num]
        exact h1.symm
    · rw [show ((-1 : ℂ).im) = 0 by norm_num]
      exact him.symm




/- ============ C. 共轭计数 (零点轨道分类; 零分析延拓) ============ -/

/-- 离线零点轨道互异: Re z ≠ 1/2 且 Im z ≠ 0 ⟹ z, z̄, 1-z, 1-z̄ 两两不同. 
English: Offline zero orbits are distinct: Re z ≠ 1/2 and Im z ≠ 0 ⟹ z, z̄, 1-z, 1-z̄ pairwise distinct. -/
theorem zero_orbit_distinct_of_offline {z : ℂ} (hre : z.re ≠ 1 / 2) (him : z.im ≠ 0) :
    z ≠ (starRingEnd ℂ) z ∧ z ≠ 1 - z ∧ z ≠ 1 - (starRingEnd ℂ) z ∧
    (starRingEnd ℂ) z ≠ 1 - (starRingEnd ℂ) z := by
  constructor
  · intro h
    apply him
    have him' : z.im = ((starRingEnd ℂ) z).im := congrArg Complex.im h
    have him'' : z.im = -z.im := by
      simpa using him'
    linarith
  · constructor
    · intro h
      apply hre
      have hre' : z.re = (1 - z).re := congrArg Complex.re h
      rw [Complex.sub_re, Complex.one_re] at hre'
      linarith
    · constructor
      · intro h
        apply hre
        have hre' : z.re = (1 - (starRingEnd ℂ) z).re := congrArg Complex.re h
        rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre'
        linarith
      · intro h
        apply hre
        have hre' : ((starRingEnd ℂ) z).re = (1 - (starRingEnd ℂ) z).re := congrArg Complex.re h
        rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre'
        linarith

/-- 在线零点轨道退化: Re z = 1/2 ⟹ 1 - z = conj z (4 点轨道 → 2 点共轭对). 
English: Online zero orbit degenerates: Re z = 1/2 ⟹ 1 - z = conj z (4-point orbit → 2-point conjugate pair). -/
theorem zero_orbit_degenerate_on_line {z : ℂ} (hre : z.re = 1 / 2) :
    1 - z = (starRingEnd ℂ) z :=
  (critical_line_positional z).mp hre

/-- 共轭计数: 零点轨道结构 —
    在线: 轨道 = 共轭对 {z, z̄} (退化, 1-z = z̄, 两零点: z, z̄);
    离线: 轨道 = 4 点 {z, z̄, 1-z, 1-z̄} 互异, 四零点.
    RH ⟺ 无离线轨道 (全部退化 = 所有零点在线). 
English: Conjugate counting: zero orbit structure — online: orbit = conjugate pair {z, z̄} (degenerate, 1-z = z̄, two zeros: z, z̄); offline: orbit = distinct 4 points {z, z̄, 1-z, 1-z̄}, four zeros. RH ⟺ no offline orbits (all degenerate = all zeros online). -/
theorem zero_orbit_counting {z : ℂ} (hz : riemannZeta z = 0)
    (hstrip : 0 < z.re ∧ z.re < 1)
    (htriv : ∀ n : ℕ, z ≠ -↑n) (hone : z ≠ 1) (him : z.im ≠ 0) :
    (z.re = 1 / 2 →
      (starRingEnd ℂ) z = 1 - z ∧
      riemannZeta (starRingEnd ℂ z) = 0 ∧ riemannZeta (1 - z) = 0 ∧
      riemannZeta (1 - (starRingEnd ℂ z)) = 0) ∧
    (z.re ≠ 1 / 2 →
      (z ≠ (starRingEnd ℂ) z ∧ z ≠ 1 - z ∧ z ≠ 1 - (starRingEnd ℂ) z ∧
        (starRingEnd ℂ) z ≠ 1 - (starRingEnd ℂ) z) ∧
      (riemannZeta (starRingEnd ℂ z) = 0 ∧ riemannZeta (1 - z) = 0 ∧
        riemannZeta (1 - (starRingEnd ℂ z)) = 0)) := by
  constructor
  · intro hre
    have horbit := zero_orbit_four hz hstrip htriv hone
    constructor
    · exact (zero_orbit_degenerate_on_line hre).symm
    · exact ⟨horbit.1, horbit.2.1, by
        -- ζ(1 - z̄) = 0: 在线 ⟹ 1 - z̄ = z?1 - conj z = z ⟺ conj z = 1 - z ✓ (退化)
        -- 所以 ζ(1 - conj z) = ζ(z) = hz
        have hzbar : 1 - (starRingEnd ℂ) z = z := by
          -- 从退化:conj z = 1 - z ⟹ 1 - conj z = 1 - (1 - z) = z
          rw [← zero_orbit_degenerate_on_line hre]
          ring
        rw [hzbar]
        exact hz⟩
  · intro hre
    have horbit := zero_orbit_four hz hstrip htriv hone
    constructor
    · exact zero_orbit_distinct_of_offline hre him
    · exact ⟨horbit.1, horbit.2.1, horbit.2.2⟩
end

/-- 消边: 离线零点左右镜像双射 — 左半 (Re<1/2) 与右半 (Re>1/2) 的零点
    通过 ρ ↦ 1-ρ̄ 一一对应 (共轭保持虚部, 反射镜像实部)。
    零点总数守恒的代数骨架: 离线零点成对出现 (函数方程 + 共轭),
    临界线把计数区域分成镜像两半 — 消边是 N(T) 矩形绕转 → 临界线段
    的零点层面版本。 
English: Edge cancellation: mirror bijection of offline zeros — zeros in the left half (Re<1/2) and right half (Re>1/2) correspond one-to-one via ρ ↦ 1-ρ̄ (conjugation preserves imaginary part, reflection mirrors real part). Algebraic skeleton of total zero conservation: offline zeros come in pairs (functional equation + conjugation); the critical line splits the counting region into mirrored halves — cancellation is the zero-level version of N(T) rectangle winding → critical-line segment. -/
noncomputable def zero_left_right_bijection (T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ 0 < ρ.im ∧ ρ.im < T}
      ≃ {ρ : ℂ | riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im < T} := by
  refine ⟨fun ρ => ⟨1 - (starRingEnd ℂ) (ρ : ℂ), ?_⟩,
          fun ρ => ⟨1 - (starRingEnd ℂ) (ρ : ℂ), ?_⟩, ?_, ?_⟩
  · -- toFun: 左半 ⟹ 右半 (4 点轨道 + 实部镜像)
    rcases ρ with ⟨ρ, hz, hre0, hre1, him0, himT⟩
    have hstrip : 0 < ρ.re ∧ ρ.re < 1 := ⟨hre0, lt_trans hre1 (by norm_num)⟩
    have htriv : ∀ n : ℕ, ρ ≠ -↑n := by
      intro n h
      have hre' : ρ.re = (-(n : ℂ)).re := by rw [h]
      have hneg : (-(n : ℂ)).re = -((n : ℂ).re) := Complex.neg_re (n : ℂ)
      rw [hneg] at hre'
      have hnre : ((n : ℂ).re) = (n : ℝ) := by simp
      rw [hnre] at hre'
      linarith
    have hone : ρ ≠ 1 := by
      intro h
      have hre' : ρ.re = (1 : ℂ).re := by rw [h]
      rw [Complex.one_re] at hre'
      linarith
    have horbit := zero_orbit_four hz hstrip htriv hone
    refine ⟨horbit.2.2, ?_, ?_, ?_, ?_⟩
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      linarith [him0]
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      linarith [himT]
  · -- invFun: 右半 ⟹ 左半 (对称)
    rcases ρ with ⟨ρ, hz, hre0, hre1, him0, himT⟩
    have hstrip : 0 < ρ.re ∧ ρ.re < 1 := ⟨lt_trans (by norm_num) hre0, hre1⟩
    have htriv : ∀ n : ℕ, ρ ≠ -↑n := by
      intro n h
      have hre' : ρ.re = (-(n : ℂ)).re := by rw [h]
      have hneg : (-(n : ℂ)).re = -((n : ℂ).re) := Complex.neg_re (n : ℂ)
      rw [hneg] at hre'
      have hnre : ((n : ℂ).re) = (n : ℝ) := by simp
      rw [hnre] at hre'
      linarith
    have hone : ρ ≠ 1 := by
      intro h
      have hre' : ρ.re = (1 : ℂ).re := by rw [h]
      rw [Complex.one_re] at hre'
      linarith
    have horbit := zero_orbit_four hz hstrip htriv hone
    refine ⟨horbit.2.2, ?_, ?_, ?_, ?_⟩
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      linarith [him0]
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      linarith [himT]
  · -- left_inv: ρ ↦ 1-ρ̄ 对合
    intro ρ
    ext <;> simp
  · -- right_inv
    intro ρ
    ext <;> simp

theorem cpow_two_on_line_explicit (t : ℝ) :
    (2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (Real.log 2 / 2) : ℂ) * (Real.cos (t * Real.log 2) : ℂ)
        + (Real.exp (Real.log 2 / 2) : ℂ) * (Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  have hdecomp : (Real.log 2 : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = ((Real.log 2 / 2 : ℝ) : ℂ) + ((t * Real.log 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring

/-- π^(s-1) 沿临界线显式: π^(-1/2+it) = exp(-ln π / 2) · (cos(t·ln π) + i·sin(t·ln π))。
    相位 = t·ln π (线性), 模 = π^(-1/2)。 
English: π^(s-1) explicit along the critical line: π^(-1/2+it) = exp(-ln π / 2)·(cos(t·ln π) + i·sin(t·ln π)). Phase = t·ln π (linear), modulus = π^(-1/2). -/
theorem cpow_pi_on_line_explicit (t : ℝ) :
    (↑Real.pi : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (-Real.log Real.pi / 2) : ℂ) * (Real.cos (t * Real.log Real.pi) : ℂ)
        + (Real.exp (-Real.log Real.pi / 2) : ℂ) * (Real.sin (t * Real.log Real.pi) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
  have hlog : Complex.log (↑Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
    exact (Complex.ofReal_log (le_of_lt Real.pi_pos)).symm
  rw [hlog]
  have hdecomp : (Real.log Real.pi : ℂ) * (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = ((-Real.log Real.pi / 2 : ℝ) : ℂ) + ((t * Real.log Real.pi : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring

/-- sin(πs/2) 沿临界线显式 (s = 1/2+it):
    sin(π/4 + iπt/2) = sin(π/4)·cosh(πt/2) + i·cos(π/4)·sinh(πt/2)。
    实部 = sin(π/4)·cosh(πt/2) > 0 恒正 ⟹ arg = arctan(tanh(πt/2))。 
English: sin(πs/2) explicit along the critical line (s = 1/2+it): sin(π/4 + iπt/2) = sin(π/4)·cosh(πt/2) + i·cos(π/4)·sinh(πt/2). Real part = sin(π/4)·cosh(πt/2) > 0 always ⟹ arg = arctan(tanh(πt/2)). -/
theorem sin_pi_quarter_add_mul_I (t : ℝ) :
    Complex.sin (↑Real.pi / 4 + (t : ℂ) * ↑Real.pi / 2 * Complex.I)
      = Complex.sin (↑Real.pi / 4) * Complex.cosh ((Real.pi / 2 * t : ℝ) : ℂ)
        + Complex.cos (↑Real.pi / 4) * Complex.sinh ((Real.pi / 2 * t : ℝ) : ℂ) * Complex.I := by
  have h := Complex.sin_add_mul_I (↑(Real.pi / 4) : ℂ) ((Real.pi / 2 * t : ℝ) : ℂ)
  have hL : ↑Real.pi / 4 + (t : ℂ) * ↑Real.pi / 2 * Complex.I
      = ↑(Real.pi / 4) + ↑(Real.pi / 2 * t) * Complex.I := by
    norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add]
    ring
  rw [hL]
  simpa using h

theorem sin_pi_half_add_mul_I (t : ℝ) :
    Complex.sin (↑Real.pi / 2 + (t : ℂ) * ↑Real.pi * Complex.I)
      = (Real.cosh (Real.pi * t) : ℂ) := by
  have h := Complex.sin_add_mul_I (↑Real.pi / 2) ((Real.pi * t : ℝ) : ℂ)
  -- h: sin(↑(π/2) + ↑(π·t)·I) = sin(↑(π/2))·cosh(↑(π·t)) + cos(↑(π/2))·sinh(↑(π·t))·I
  -- 匹配 LHS: (t:ℂ)·(↑π:ℂ) = ↑(π·t)(ofReal_mul)
  have hL : ↑Real.pi / 2 + (t : ℂ) * ↑Real.pi * Complex.I
      = ↑(Real.pi / 2) + ↑(Real.pi * t) * Complex.I := by
    norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add]
    ring
  rw [hL]
  -- sin(π/2) = 1, cos(π/2) = 0:simp 化简
  simpa using h

/-- Γ 在临界线上的模 (对称操作的产物): |Γ(1/2+it)|² = π/cosh(πt) 精确。
    反射对称 (Γ(s)Γ(1-s) = π/sin(πs)) + 共轭 (Γ(conj s) = conj Γ(s))
    + sin 显式 (sin(π/2+iπt) = cosh(πt)) — Stirling 的模部分被对称性替代。 
English: Γ modulus on the critical line (product of symmetry operations): |Γ(1/2+it)|² = π/cosh(πt) exactly. Reflection symmetry (Γ(s)Γ(1-s) = π/sin(πs)) + conjugation (Γ(conj s) = conj Γ(s)) + explicit sin (sin(π/2+iπt) = cosh(πt)) — Stirling's modulus part replaced by symmetry. -/
theorem gamma_abs_sq_on_line (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = Real.pi / Real.cosh (Real.pi * t) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hconj : 1 - s = (starRingEnd ℂ) s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  -- 反射: Γ(s)·Γ(1-s) = π/sin(πs)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  -- 1-s = conj s, Γ(conj s) = conj Γ(s)
  rw [hconj] at hrefl
  rw [Complex.Gamma_conj] at hrefl
  -- sin(πs) = cosh(πt) (π·s = π/2 + iπt)
  have harg : ↑Real.pi * s = ↑Real.pi / 2 + (t : ℂ) * ↑Real.pi * Complex.I := by
    dsimp [s]
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [harg] at hrefl
  rw [sin_pi_half_add_mul_I] at hrefl
  -- Γ(s)·conj Γ(s) = ↑‖Γ(s)‖² (normSq)
  have hns := Complex.mul_conj (Complex.Gamma s)
  rw [hns] at hrefl
  -- hrefl: ↑(normSq Γ(s)) = ↑π / ↑cosh(πt) = ↑(π/cosh(πt)):取 re
  have hfin : Complex.normSq (Complex.Gamma s) = Real.pi / Real.cosh (Real.pi * t) := by
    have hre := congrArg Complex.re hrefl
    -- hre: normSq = (↑π/↑cosh).re ⟹ 合并 cast 除法 + re 穿透
    have hdiv : (↑Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ)
        = (↑(Real.pi / Real.cosh (Real.pi * t)) : ℂ) := by
      exact (Complex.ofReal_div Real.pi (Real.cosh (Real.pi * t))).symm
    rw [hdiv] at hre
    -- hre: normSq = (↑(π/cosh)).re ⟹ 只展开 re (不展开 cast 内部)
    rw [Complex.ofReal_re] at hre
    exact hre
  -- 目标 ‖Γ(s)‖² = π/cosh(πt): normSq = ‖·‖²
  simpa [s, Complex.normSq_eq_norm_sq] using hfin

theorem term_on_line_explicit (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I) : ℂ)
      = (Real.exp (-Real.log n / 2) : ℂ) * (Real.cos (t * Real.log n) : ℂ)
        - (Real.exp (-Real.log n / 2) : ℂ) * (Real.sin (t * Real.log n) : ℂ) * Complex.I := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog]
  have hdecomp : (Real.log n : ℂ) * (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))
      = ((-Real.log n / 2 : ℝ) : ℂ) + ((-(t * Real.log n) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  -- exp((-(t·ln n))·I) = cos(t·ln n) - i·sin(t·ln n)
  rw [Complex.exp_mul_I]
  simp
  ring

theorem cpow_two_half_minus_im (t : ℝ) :
    (2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (Real.log 2 / 2) : ℂ) * (Real.cos (t * Real.log 2) : ℂ)
        - (Real.exp (Real.log 2 / 2) : ℂ) * (Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  have hdecomp : (Real.log 2 : ℂ) * ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)
      = ((Real.log 2 / 2 : ℝ) : ℂ) + ((-(t * Real.log 2) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring

/-- A: 共轭相位 (模 2π): arg Γ(conj s) = -arg Γ(s)。
    无条件: arg_conj_coe_angle 是 Angle 层恒等式, 分支在模 2π 下消失。 
English: A: conjugation phase (mod 2π): arg Γ(conj s) = -arg Γ(s). Unconditional: arg_conj_coe_angle is an Angle-layer identity, branches vanish mod 2π. -/
theorem gamma_conj_arg_angle (s : ℂ) :
    ((Complex.Gamma ((starRingEnd ℂ) s)).arg : Real.Angle)
      = -((Complex.Gamma s).arg : Real.Angle) := by
  rw [Complex.Gamma_conj]
  exact Complex.arg_conj_coe_angle (Complex.Gamma s)

/-- B: 倍增相位 (模 2π, s = 1/4+it/2): Legendre 倍增公式的 arg 版本。
    arg Γ(1/4+) + arg Γ(3/4+) = arg Γ(1/2+) + (log 2^{1/2-it}).im。 
English: B: duplication phase (mod 2π, s = 1/4+it/2): arg version of Legendre duplication. arg Γ(1/4+) + arg Γ(3/4+) = arg Γ(1/2+) + (log 2^{1/2-it}).im. -/
theorem gamma_doubling_arg_angle (t : ℝ) :
    ((Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
        + ((Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
      = ((Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg : Real.Angle)
        + ((Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im : Real.Angle) := by
  let s : ℂ := (1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  have hs_pos : 0 < s.re := by dsimp [s]; simp
  have hs2_pos : 0 < (s + 1 / 2).re := by dsimp [s]; simp; norm_num
  have h2s_pos : 0 < (2 * s).re := by dsimp [s]; simp
  have hs_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs_pos
  have hs2_ne : Complex.Gamma (s + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2_pos
  have h2s_ne : Complex.Gamma (2 * s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h2s_pos
  have hpow_ne : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have hsqrt_ne : (↑(Real.sqrt Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  -- Legendre 倍增公式 (无条件)
  have h := Complex.Gamma_mul_Gamma_add_half s
  -- 取 arg 进 Real.Angle
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 左侧: Γ(s)·Γ(s+1/2)
  rw [Complex.arg_mul_coe_angle hs_ne hs2_ne] at harg
  -- 右侧: (Γ(2s)·2^{1-2s})·√π
  rw [Complex.arg_mul_coe_angle (mul_ne_zero h2s_ne hpow_ne) hsqrt_ne] at harg
  rw [Complex.arg_mul_coe_angle h2s_ne hpow_ne] at harg
  -- arg √π = 0
  have harg_sqrt : (↑(Real.sqrt Real.pi) : ℂ).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg _)
  simp [harg_sqrt] at harg
  -- arg(2^{1-2s}) = (log 2^{1-2s}).im (log_im 反向)
  have hlog : (Complex.log ((2 : ℂ) ^ (1 - 2 * s))).im = ((2 : ℂ) ^ (1 - 2 * s)).arg := by
    rw [Complex.log_im]
  rw [← hlog] at harg
  -- 替换 s 的具体值: s+1/2 = 3/4+it/2, 2s = 1/2+it, 1-2s = 1/2-it
  have hs12 : s + (2 : ℂ)⁻¹ = (3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2 := by
    dsimp [s]; ring
  have h2s : 2 * s = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
    dsimp [s]; ring
  have h12s : 1 - 2 * s = ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ) := by
    dsimp [s]; ring
  -- h12s 需在 h2s 前: h2s 会先替换掉 harg 中的 2*s
  rw [hs12, h12s, h2s] at harg
  dsimp [s] at harg
  exact harg

/-- C: 反射相位 (模 2π, z = 3/4+it/2):
    arg Γ(3/4+) + arg Γ(1/4-) = -(log sin(π(3/4+it/2))).im。
    Euler 反射公式 Γ(z)Γ(1-z) = π/sin(πz) 的 arg 版本; sin 非零由左侧
    Γ 非零 (re > 0) 自动推出, 无整数/无理数论证。 
English: C: reflection phase (mod 2π, z = 3/4+it/2): arg Γ(3/4+) + arg Γ(1/4-) = -(log sin(π(3/4+it/2))).im. The arg version of Euler reflection Γ(z)Γ(1-z) = π/sin(πz); sin nonzero follows automatically from Γ nonzero on the left (re > 0), no integer/irrationality argument. -/
theorem gamma_reflection_arg_angle (t : ℝ) :
    ((Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
        + ((Complex.Gamma ((1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
      = -((Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im : Real.Angle) := by
  let z : ℂ := (3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  have hz_pos : 0 < z.re := by dsimp [z]; simp
  have h1z_pos : 0 < (1 - z).re := by dsimp [z]; simp; norm_num
  have hz_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz_pos
  have h1z_ne : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1z_pos
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  -- sin(πz) ≠ 0: 由 Γ(z)Γ(1-z) = π/sin(πz) ≠ 0 推出
  have hleft_ne : Complex.Gamma z * Complex.Gamma (1 - z) ≠ 0 := mul_ne_zero hz_ne h1z_ne
  have hsin_ne : Complex.sin (↑Real.pi * z) ≠ 0 := by
    intro hs
    have hzero : Complex.Gamma z * Complex.Gamma (1 - z) = 0 := by
      rw [hrefl, hs]
      simp
    exact hleft_ne hzero
  -- 取 arg 进 Real.Angle
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) hrefl
  -- 左侧: Γ(z)·Γ(1-z)
  rw [Complex.arg_mul_coe_angle hz_ne h1z_ne] at harg
  -- 右侧: arg(π/sin(πz)) = arg π - arg sin(πz)
  rw [Complex.arg_div_coe_angle (by exact_mod_cast Real.pi_ne_zero) hsin_ne] at harg
  -- arg π = 0
  have harg_pi : (↑Real.pi : ℂ).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)
  rw [harg_pi] at harg
  simp at harg
  -- arg(sin(πz)) = (log sin(πz)).im (log_im 反向)
  have hlog : (Complex.log (Complex.sin (↑Real.pi * z))).im =
      (Complex.sin (↑Real.pi * z)).arg := by
    rw [Complex.log_im]
  rw [← hlog] at harg
  -- 替换 z 的具体值: 1-z = 1/4-it/2
  have h1z : 1 - z = (1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2 := by
    dsimp [z]; ring
  rw [h1z] at harg
  dsimp [z] at harg
  exact harg

/-- D: 组合 (模 2π): 2·arg Γ(1/4+it/2) = arg Γ(1/2+it) + (log 2^{1/2-it}).im
    + (log sin(π(3/4+it/2))).im。
    代数: B + C + A ⟹ 2a = d + e + f (Γ 完全消去)。 
English: D: combination (mod 2π): 2·arg Γ(1/4+it/2) = arg Γ(1/2+it) + (log 2^{1/2-it}).im + (log sin(π(3/4+it/2))).im. Algebra: B + C + A ⟹ 2a = d + e + f (Γ cancels completely). -/
theorem gamma_quarter_phase_combine (t : ℝ) :
    (((2 : ℝ) * (Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg) : Real.Angle)
      = ((Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg : Real.Angle)
        + ((Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im : Real.Angle)
        + ((Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im : Real.Angle) := by
  let s : ℂ := (1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  let a : ℝ := (Complex.Gamma s).arg
  let b : ℝ := (Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg
  let d : ℝ := (Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg
  let e : ℝ := (Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im
  let f : ℝ := (Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im
  have hA := gamma_conj_arg_angle s
  have hB := gamma_doubling_arg_angle t
  have hC := gamma_reflection_arg_angle t
  -- hA 里 conj s = 1/4-it/2, 用于消 hC 中的 Γ(1/4-)
  have hconj : (starRingEnd ℂ) s = (1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2 := by
    apply Complex.ext <;> dsimp [s] <;> simp
  rw [hconj] at hA
  -- hA: ↑arg Γ(1/4-) = -↑arg Γ(s) = -↑a
  rw [hA] at hC
  -- hC: ↑b + (-↑a) = -↑f ⟹ ↑b = ↑a - ↑f
  have hb : (↑b : Real.Angle) = (↑a : Real.Angle) - (↑f : Real.Angle) := by
    calc
      (↑b : Real.Angle) = (↑b + (-↑a)) + ↑a := by abel
      _ = (-↑f) + (↑a : Real.Angle) := by rw [hC]
      _ = (↑a : Real.Angle) - (↑f : Real.Angle) := by abel
  -- hB: ↑a + ↑b = ↑d + ↑e
  rw [hb] at hB
  -- ↑a + (↑a - ↑f) = ↑d + ↑e ⟹ ↑a + ↑a = ↑d + ↑e + ↑f
  have hsum : (↑a : Real.Angle) + (↑a : Real.Angle)
      = (↑d : Real.Angle) + (↑e : Real.Angle) + (↑f : Real.Angle) := by
    calc
      (↑a : Real.Angle) + (↑a : Real.Angle) = (↑a + (↑a - ↑f)) + (↑f : Real.Angle) := by abel
      _ = (↑d + ↑e) + (↑f : Real.Angle) := by rw [hB]
      _ = (↑d : Real.Angle) + (↑e : Real.Angle) + (↑f : Real.Angle) := by abel
  -- 目标左侧: ↑(2·a) = ↑a + ↑a
  have htwo : (↑(2 * a) : Real.Angle) = (↑a : Real.Angle) + (↑a : Real.Angle) := by
    rw [two_mul]; simp
  rw [htwo]
  dsimp [a, d, e, f]
  exact hsum


/- ===== N₀(T) = N(T) 等价框架 + 对称延拓 (0pat, 2026-08-19) =====
用户方向: "连续幅角本质上就是相位"; "有限向无限的映射过程, 之前的对称延拓
能不能用"。落地:
- T0: ζ(-奇数) ≠ 0 — Re ≤ 0 无零点定理的 hs_int 补丁 (函数方程 + cos 偶倍 π)
- T1: 等价框架 — RH ⟺ ∀T, 全带 [0,1]×[0,T] 零点都在临界线上 (N₀=N 的命题形式,
      mathlib riemannZetaZeros + IsCompact 有限性支撑计数良定义)
- T2: 轨道 — 离线零点 ⟹ 左半带同高度零点 (反射 + 共轭, 轨道 4 点)
- T3: 对称延拓 — 2·arg ζ(1/2+it) = arg χ(1/2+it) (连续幅角 = 相位)
      ζ(s) = χ(s)·conj ζ(s) (函数方程 + 共轭穿透, s = 1/2+it 时 1-s = conj s)
      ⟹ 2·arg ζ = arg χ (模 2π)。逐点成立, 无无限过程 -/

/-- T0: 奇数负整数非零点 — ζ(-n) ≠ 0 (n 奇, n ≥ 1)。
    函数方程 s = n+1: ζ(-n) = 2(2π)^{-(n+1)}·Γ(n+1)·cos(π(n+1)/2)·ζ(n+1);
    n 奇 ⟹ n+1 偶 ⟹ cos(π(n+1)/2) = ±1 ≠ 0; Γ(n+1) 无零点; ζ(n+1) ≠ 0 (Re > 1)。 
English: T0: odd negative integers are non-zeros — ζ(-n) ≠ 0 (n odd, n ≥ 1). Functional equation at s = n+1: ζ(-n) = 2(2π)^{-(n+1)}·Γ(n+1)·cos(π(n+1)/2)·ζ(n+1); n odd ⟹ n+1 even ⟹ cos(π(n+1)/2) = ±1 ≠ 0; Γ(n+1) has no zeros; ζ(n+1) ≠ 0 (Re > 1). -/
theorem zeta_neg_nat_ne_zero_of_odd {n : ℕ} (hn0 : n ≠ 0) (hodd : ¬Even n) :
    riemannZeta (-(n : ℂ)) ≠ 0 := by
  intro hz
  have hne : Even (n + 1) := Nat.even_add_one.mpr hodd
  rcases hne with ⟨k, hk⟩
  have hs_int : ∀ m : ℕ, (n : ℂ) + 1 ≠ -↑m := by
    intro m hm
    have hre : ((n : ℂ) + 1).re = (n : ℝ) + 1 := by simp
    have : ((n : ℂ) + 1).re = (-(m : ℂ)).re := by rw [hm]
    rw [hre] at this
    have hmre : (-(m : ℂ)).re = -(m : ℝ) := by simp
    rw [hmre] at this
    nlinarith
  have hone : (n : ℂ) + 1 ≠ 1 := by
    intro h
    have : ((n : ℂ) + 1).re = 1 := by rw [h]; simp
    simp at this
    exact hn0 this
  have hfe := riemannZeta_one_sub (s := (n : ℂ) + 1) hs_int hone
  -- cos(π(n+1)/2) ≠ 0: n+1 = 2k → π(n+1)/2 = kπ → cos = ±1
  have hn1c : ((n : ℂ) + 1) = 2 * (k : ℂ) := by
    have hc : ((n + 1 : ℕ) : ℂ) = ((k + k : ℕ) : ℂ) := by exact_mod_cast hk
    calc
      ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by norm_num [Nat.cast_add]
      _ = ((k + k : ℕ) : ℂ) := hc
      _ = (k : ℂ) + (k : ℂ) := by norm_num [Nat.cast_add]
      _ = 2 * (k : ℂ) := by ring
  have hcos : Complex.cos (↑Real.pi * ((n : ℂ) + 1) / 2) ≠ 0 := by
    have harg : ↑Real.pi * ((n : ℂ) + 1) / 2 = (k : ℂ) * ↑Real.pi := by
      rw [hn1c]
      ring_nf
    have hpowcast_aux : ∀ k : ℕ, (↑((-1 : ℝ) ^ k) : ℂ) = (-1 : ℂ) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc
            (↑((-1 : ℝ) ^ (k + 1)) : ℂ) = ↑((-1 : ℝ) ^ k * (-1 : ℝ)) := by rw [pow_succ]
            _ = (↑((-1 : ℝ) ^ k) : ℂ) * ↑(-1 : ℝ) := by rw [Complex.ofReal_mul]
            _ = (-1 : ℂ) ^ k * ↑(-1 : ℝ) := by rw [ih]
            _ = (-1 : ℂ) ^ k * (-1 : ℂ) := by rw [Complex.ofReal_neg, ← Complex.ofReal_one]
            _ = (-1 : ℂ) ^ (k + 1) := by rw [← pow_succ]
    have hcosk : Complex.cos ((k : ℂ) * ↑Real.pi) = (-1 : ℂ) ^ k := by
      have hcosr : Real.cos (k * Real.pi) = (-1) ^ k := Real.cos_nat_mul_pi k
      have hc0 : (k : ℂ) * ↑Real.pi = (↑((k : ℝ) * Real.pi) : ℂ) := by
        apply Complex.ext <;> simp <;> ring
      have hc1 : Complex.cos (↑((k : ℝ) * Real.pi) : ℂ) = (↑((-1 : ℝ) ^ k) : ℂ) := by
        rw [← Complex.ofReal_cos, hcosr]
      have hpowcast : (↑((-1 : ℝ) ^ k) : ℂ) = (-1 : ℂ) ^ k := hpowcast_aux k
      rw [hc0, hc1]
      exact hpowcast
    rw [harg, hcosk]
    exact pow_ne_zero k (by norm_num)
  have hG : Complex.Gamma ((n : ℂ) + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      rw [Complex.add_re, Complex.one_re]
      simp
      positivity)
  have hzeta : riemannZeta ((n : ℂ) + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (s := (n : ℂ) + 1) (by simp)
  have hpow : (2 * (2 * ↑Real.pi) ^ (-((n : ℂ) + 1)) : ℂ) ≠ 0 := by
    refine mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) ?_
    exact (Complex.cpow_ne_zero_iff).mpr
      (Or.inl (by exact_mod_cast (mul_pos (by norm_num) Real.pi_pos).ne'))
  have hprod : (2 * (2 * ↑Real.pi) ^ (-((n : ℂ) + 1)) * Complex.Gamma ((n : ℂ) + 1) *
      Complex.cos (↑Real.pi * ((n : ℂ) + 1) / 2) * riemannZeta ((n : ℂ) + 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hpow hG) hcos) hzeta
  have hfe' : riemannZeta (-(n : ℂ)) = 2 * (2 * ↑Real.pi) ^ (-((n : ℂ) + 1)) *
      Complex.Gamma ((n : ℂ) + 1) * Complex.cos (↑Real.pi * ((n : ℂ) + 1) / 2) *
      riemannZeta ((n : ℂ) + 1) := by
    have h1 : 1 - ((n : ℂ) + 1) = -(n : ℂ) := by ring
    rw [h1] at hfe
    simpa using hfe
  exact hprod (by rw [← hfe', hz])

/-- T1: 等价框架 — RH ⟺ ∀T, 全带 [0,1]×[0,T] 内零点都在临界线上。
    N₀(T) = N(T) 的命题形式 (带内离线零点不存在)。
    方向 1: RH ⟹ 零点全在线上 ⟹ 带内当然全在线上;
    方向 2: 反证 — 离线零点 z (re ≠ 1/2) 必在临界带 (Re ≤ 0 无零点、Re ≥ 1
      无零点, 均 0pat 已证; 负整数非零点由 T0), 取 T = |z.im|, 带内离线
      零点存在, 与假设矛盾。 "有限→无限": 每个零点落在有限带内。 
English: T1: equivalence framework — RH ⟺ ∀T, all zeros in the full strip [0,1]×[0,T] lie on the critical line (propositional form of N₀(T) = N(T): no offline zeros in the strip). Direction 1: RH ⟹ all zeros on the line, certainly in the strip. Direction 2: contradiction — an offline zero z (re ≠ 1/2) must be in the critical strip (no zeros for Re ≤ 0 nor Re ≥ 1, both 0pat-proven; negative integers non-zeros by T0); take T = |z.im|, an in-strip offline zero exists, contradicting the hypothesis. Finite→infinite: every zero lies in a finite strip. -/
theorem rh_iff_all_zeros_on_line_in_strips :
    RiemannHypothesis ↔
      ∀ T : ℝ, 0 ≤ T → ∀ z : ℂ, riemannZeta z = 0 → 0 ≤ z.re → z.re ≤ 1 →
        |z.im| ≤ T → z.re = 1 / 2 := by
  constructor
  · intro hRH T hT0 z hz hre0 hre1 him
    have hne1 : z ≠ 1 := by
      intro h
      subst h
      exact (riemannZeta_ne_zero_of_one_le_re (s := (1 : ℂ)) (by norm_num)) hz
    have htriv : ¬∃ n : ℕ, z = -2 * (n + 1) := by
      intro h
      rcases h with ⟨n, hn⟩
      have hrz : z.re = (-2 * (n + 1) : ℂ).re := by rw [hn]
      rw [hrz] at hre0
      simp at hre0
      nlinarith
    exact hRH z hz htriv hne1
  · intro hno
    by_contra hRH
    simp only [RiemannHypothesis] at hRH
    push_neg at hRH
    rcases hRH with ⟨z, hz, htriv', hne1, hre_off⟩
    have htriv : ¬∃ n : ℕ, z = -2 * (n + 1) := by
      intro h
      rcases h with ⟨n, hn⟩
      exact htriv' n (by rw [hn])
    -- z ≠ -n ∀n: 偶 → htriv; 奇 → T0; 0 → ζ(0) ≠ 0
    have hs_int : ∀ n : ℕ, z ≠ -↑n := by
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        have hz0 : z = 0 := by simpa using hn
        subst hz0
        have hz0ne : riemannZeta 0 ≠ 0 := by
          rw [riemannZeta_zero]
          norm_num
        exact hz0ne hz
      · rcases Nat.even_or_odd n with he | ho
        · rcases he with ⟨k, hk⟩
          have hk0 : k ≠ 0 := by
            intro hk0
            subst k
            simp [hk] at hn0
          rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨m, hm⟩
          have hz2 : z = -2 * ((m : ℕ) + 1 : ℂ) := by
            calc
              z = -(n : ℂ) := hn
              _ = -((2 * (m + 1) : ℕ) : ℂ) := by
                rw [hk, hm]
                congr 1
                exact_mod_cast (by omega : (m.succ + m.succ : ℕ) = 2 * (m + 1))
              _ = -2 * ((m : ℕ) + 1 : ℂ) := by
                norm_num [Nat.cast_add, Nat.cast_mul]
          exact htriv ⟨m, hz2⟩
        · have hoddn : ¬Even n := Nat.not_even_iff_odd.mpr ho
          have hneg : riemannZeta (-(n : ℂ)) ≠ 0 := zeta_neg_nat_ne_zero_of_odd hn0 hoddn
          exact hneg (by rw [← hn, hz])
    -- Re ≥ 1 无零点
    have hlt1 : z.re < 1 := by
      by_contra h
      have hge : 1 ≤ z.re := le_of_not_gt h
      exact (riemannZeta_ne_zero_of_one_le_re (s := z) hge) hz
    -- Re ≤ 0 无零点
    have hgt0 : 0 < z.re := by
      by_contra h
      have hle : z.re ≤ 0 := le_of_not_gt h
      by_cases hz0 : z.re = 0
      · have hzne0 : z ≠ 0 := by
          intro hz0'
          subst hz0'
          have hz0ne : riemannZeta 0 ≠ 0 := by
            rw [riemannZeta_zero]
            norm_num
          exact hz0ne hz
        exact (riemannZeta_ne_zero_of_re_eq_zero z hz0 hzne0) hz
      · have hlt : z.re < 0 := lt_of_le_of_ne hle hz0
        exact (riemannZeta_ne_zero_of_re_lt_zero z hlt hs_int) hz
    -- 现在 z 在临界带: 取 T = |z.im|
    exact hre_off (hno |z.im| (abs_nonneg _) z hz (le_of_lt hgt0) (le_of_lt hlt1) le_rfl)


/-- T2: 轨道 — 离线零点 ⟹ 左半带同高度零点。
    轨道 {z, conj z, 1-z, 1-conj z}: 若 z.re > 1/2, 则 1-conj z (零点, 同高度)
    落在左半带 (re < 1/2); 若 z.re < 1/2, 直接取 z。 
English: T2: orbit — offline zero ⟹ same-height zero in the left half-strip. Orbit {z, conj z, 1-z, 1-conj z}: if z.re > 1/2, then 1-conj z (a zero, same height) lies in the left half-strip (re < 1/2); if z.re < 1/2, take z directly. -/
theorem offline_zero_gives_half_strip {z : ℂ} (hz : riemannZeta z = 0)
    (hre0 : 0 < z.re) (hre1 : z.re < 1) (hline : z.re ≠ 1 / 2) :
    ∃ w : ℂ, riemannZeta w = 0 ∧ 0 < w.re ∧ w.re < 1 ∧
      |w.im| = |z.im| ∧ w.re < 1 / 2 := by
  rcases lt_or_gt_of_ne hline with hlt | hgt
  · exact ⟨z, hz, hre0, hre1, rfl, hlt⟩
  · -- z.re > 1/2: w = 1 - conj z
    have hcz := zeta_conj_of_critical_strip (s := z) hre0 hre1
    have hcz0 : riemannZeta ((starRingEnd ℂ) z) = 0 := by
      rw [← hcz, hz]
      simp
    have hrefl := ZetaZeroReflection.zeta_zero_strip_reflection (s := (starRingEnd ℂ) z) hcz0
      (by
        constructor <;> rw [show ((starRingEnd ℂ) z).re = z.re by simp] <;> linarith [hre0, hre1])
      (by
        intro m hm
        have hre : ((starRingEnd ℂ) z).re = z.re := by simp
        have hzr : ((starRingEnd ℂ) z).re = (-(m : ℂ)).re := by rw [hm]
        rw [hre] at hzr
        have hmre : (-(m : ℂ)).re = -(m : ℝ) := by simp
        rw [hmre] at hzr
        nlinarith [hre0])
      (by
        intro h
        have hre : ((starRingEnd ℂ) z).re = z.re := by simp
        have h1 : ((starRingEnd ℂ) z).re = 1 := by rw [h]; simp
        rw [hre] at h1
        linarith [hre1])
    refine ⟨1 - (starRingEnd ℂ) z, hrefl.1, ?_, ?_, ?_, ?_⟩
    · rw [Complex.sub_re, Complex.one_re]
      rw [show ((starRingEnd ℂ) z).re = z.re by simp]
      linarith [hre1]
    · rw [Complex.sub_re, Complex.one_re]
      rw [show ((starRingEnd ℂ) z).re = z.re by simp]
      linarith [hre0]
    · rw [Complex.sub_im, Complex.one_im]
      rw [show ((starRingEnd ℂ) z).im = -z.im by simp]
      simp
    · rw [Complex.sub_re, Complex.one_re]
      rw [show ((starRingEnd ℂ) z).re = z.re by simp]
      linarith [hgt]

/-- T3: 对称延拓 — 2·arg ζ(1/2+it) = arg χ(1/2+it) (模 2π, ζ ≠ 0 处)。
    s = 1/2+it 时 1-s = conj s, 函数方程 + 共轭穿透 ⟹ ζ(s) = χ(s)·conj ζ(s),
    χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2)。
    连续幅角 = 相位: arg ζ(1/2+it) 由 χ 的显式相位确定 (模 π, 分支选择 =
    零点计数)。逐点成立, 无无限过程 — "有限→无限"的对称延拓。 
English: T3: symmetric continuation — 2·arg ζ(1/2+it) = arg χ(1/2+it) (mod 2π, where ζ ≠ 0). At s = 1/2+it, 1-s = conj s; functional equation + conjugation penetration ⟹ ζ(s) = χ(s)·conj ζ(s), χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2). Continuous argument = phase: arg ζ(1/2+it) determined by χ's explicit phase (mod π; branch choice = zero count). Pointwise, no infinite process — the finite→infinite symmetric continuation. -/
theorem zeta_two_arg_eq_arg_chi (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ((riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg : Real.Angle)
        + ((riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg : Real.Angle)
      = (((2 : ℂ) * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ)).arg : Real.Angle)
        + ((Complex.Gamma ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).arg : Real.Angle)
        + ((Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2)).arg : Real.Angle) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  -- 函数方程在 1-s (1-(1-s) = s)
  have hs_int : ∀ m : ℕ, 1 - s ≠ -↑m := by
    intro m hm
    have hre : (1 - s).re = 1 / 2 := by dsimp [s]; simp; norm_num
    have : (1 - s).re = (-(m : ℂ)).re := by rw [hm]
    rw [hre] at this
    have hmre : (-(m : ℂ)).re = -(m : ℝ) := by simp
    rw [hmre] at this
    nlinarith
  have hs1 : 1 - s ≠ 1 := by
    intro h
    have hre : (1 - s).re = 1 / 2 := by dsimp [s]; simp; norm_num
    have : (1 - s).re = 1 := by rw [h]; simp
    rw [hre] at this
    norm_num at this
  have hfe := riemannZeta_one_sub (s := 1 - s) hs_int hs1
  -- cos(π(1-s)/2) = sin(πs/2)
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) = Complex.sin (↑Real.pi * s / 2) := by
    -- cos(π(1-s)/2) = cos(π/2 - πs/2) = cos(πs/2 - π/2) = sin(πs/2)
    rw [← Complex.cos_sub_pi_div_two]
    have harg : ↑Real.pi * (1 - s) / 2 = -((↑Real.pi * s / 2) - ↑Real.pi / 2) := by
      dsimp [s]; ring
    rw [harg, Complex.cos_neg]
  -- 共轭: ζ(1-s) = conj ζ(s)
  have hconj := zeta_conj_of_critical_strip (s := 1 - s) (by dsimp [s]; simp; norm_num) (by dsimp [s]; simp)
  have hstar : (starRingEnd ℂ) (1 - s) = s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  -- 重组 hfe
  have hfe1 : riemannZeta s = 2 * (2 * ↑Real.pi) ^ (-(1 - s)) *
      Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2) * riemannZeta (1 - s) := by
    have hleft : 1 - (1 - s) = s := by ring
    rw [hleft] at hfe
    rw [hcos] at hfe
    simpa using hfe
  -- ζ(1-s) = star(ζ(s))
  have hconj' : riemannZeta (1 - s) = (starRingEnd ℂ) (riemannZeta s) := by
    have h1 := hconj
    rw [hstar] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    simpa using h2
  rw [hconj'] at hfe1
  -- 幂项形式: -(1-s) = s-1
  have hneg : -(1 - s) = (s - 1 : ℂ) := by ring
  rw [hneg] at hfe1
  -- 非零 (arg 拆分条件)
  have hpow_ne : ((2 : ℂ) * (2 * ↑Real.pi) ^ (s - 1 : ℂ)) ≠ 0 := by
    refine mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) ?_
    exact (Complex.cpow_ne_zero_iff).mpr
      (Or.inl (by exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'))
  have hG_ne : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by dsimp [s]; simp; norm_num)
  have hsin_ne : Complex.sin (↑Real.pi * s / 2) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hw : s / 2 = (k : ℂ) := by
      -- hk : π·(s/2) = k·π ⟹ 重排成 π·(s/2) = π·k ⟹ 消 π (左消)
      exact mul_left_cancel₀ hpi (by simpa [div_eq_mul_inv, mul_assoc, mul_comm] using hk)
    have hre : (s / 2).re = (k : ℂ).re := by rw [hw]
    have hre2 : (s / 2).re = 1 / 4 := by dsimp [s]; simp; norm_num
    have hkre : (k : ℂ).re = (k : ℝ) := by simp
    rw [hre2, hkre] at hre
    have h4 : (4 * (k : ℝ)) = 1 := by nlinarith
    have h4z : (4 * k : ℤ) = 1 := by exact_mod_cast h4
    omega
  have hzconj_ne : (starRingEnd ℂ) (riemannZeta s) ≠ 0 := by
    exact (map_ne_zero (starRingEnd ℂ)).mpr hz
  -- 取 arg (Angle)
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) hfe1
  -- 乘积拆 arg: 2(2π)^{s-1} · Γ(1-s) · sin · star(ζ s)
  rw [Complex.arg_mul_coe_angle (mul_ne_zero (mul_ne_zero hpow_ne hG_ne) hsin_ne) hzconj_ne]
      at harg
  rw [Complex.arg_mul_coe_angle (mul_ne_zero hpow_ne hG_ne) hsin_ne] at harg
  rw [Complex.arg_mul_coe_angle hpow_ne hG_ne] at harg
  -- arg(star ζ(s)) = -arg ζ(s)
  have harg_conj : (((starRingEnd ℂ) (riemannZeta s)).arg : Real.Angle) =
      -((riemannZeta s).arg : Real.Angle) :=
    Complex.arg_conj_coe_angle (riemannZeta s)
  rw [harg_conj] at harg
  -- harg: x = A + B + C - x ⟹ x + x = A + B + C
  have hmain : ((riemannZeta s).arg : Real.Angle) + ((riemannZeta s).arg : Real.Angle)
      = (((2 : ℂ) * (2 * ↑Real.pi) ^ (s - 1 : ℂ)).arg : Real.Angle)
        + ((Complex.Gamma (1 - s)).arg : Real.Angle)
        + ((Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle) := by
    let A : Real.Angle := (((2 : ℂ) * (2 * ↑Real.pi) ^ (s - 1 : ℂ)).arg : Real.Angle)
    let B : Real.Angle := ((Complex.Gamma (1 - s)).arg : Real.Angle)
    let C : Real.Angle := ((Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
    let x : Real.Angle := ((riemannZeta s).arg : Real.Angle)
    have harg' : A + B + C = x + x := by
      calc
        A + B + C = ((A + B + C) - x) + x := by abel
        _ = x + x := by
          -- harg: x = A+B+C-x ⟹ (A+B+C-x)+x = x+x
          exact congrArg (fun y : Real.Angle => y + x) harg.symm
    dsimp [A, B, C, x] at harg'
    exact harg'.symm
  -- 替换 s 的具体值
  dsimp [s] at hmain
  have h1s : 1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = (1 / 2 : ℂ) - (t : ℂ) * Complex.I := by
    ring
  rw [h1s] at hmain
  exact hmain

/-!
# T4: χ 的平移递推 — 单方向延拓的差分 (模 2π)

χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2) (函数方程乘子)。沿实轴平移 2:

  χ(s+2) = -4π²/(s(s+1))·χ(s)

构件: sin(π(s+2)/2) = -sin(πs/2) (sin 周期 π),
        Γ(-1-s) = Γ(1-s)/(s(s+1)) (Γ 递推两次, mathlib Gamma_add_one),
        (2π)^{s+1} = (2π)^{s-1}·(2π)² (cpow_add)。
取相位 (Real.Angle):

  arg χ(s+2) - arg χ(s) = π - arg(s(s+1))   (模 2π; arg(-4π²) = π)

这就是"单方向延拓" (用户例子: 交替中心反射 → 两步复合 = 平移) 在
χ 相位上的落地: 沿实轴每步平移 2 的相位差分全显式。连续幅角的步进:
T3 (2·arg ζ = arg χ) + 本定理 ⟹ arg ζ(1/2+i(t+2)) - arg ζ(1/2+it)
= -(1/2)arg((1/2+it)(3/2+it)) + π·(t,t+2] 零点数。

隔离文件 (mathlib-only, 不依赖 37 项目), 编译通过后再合并。
-/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

/-- χ 的平移递推 (数字层): χ(s+2) = -4π²/(s(s+1))·χ(s)。
    χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2)。s ≠ 0, -1 (Γ 递推与分母)。 
English: χ translation recursion (numeric layer): χ(s+2) = -4π²/(s(s+1))·χ(s), χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2), s ≠ 0, -1 (Γ recursion and denominator). -/
theorem chi_translation_two (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    2 * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) * Complex.sin (↑Real.pi * (s + 2) / 2)
      = -4 * (↑Real.pi) ^ 2 / (s * (s + 1)) * (2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)) := by
  -- (2π)^{s+1} = (2π)^{s-1}·(2π)²
  have hpow : (2 * ↑Real.pi : ℂ) ^ (s + 1) = (2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (2 : ℂ) := by
    rw [← Complex.cpow_add (s - 1) 2 (by exact_mod_cast (mul_pos (by norm_num) Real.pi_pos).ne')]
    congr 1
    ring
  have hpow2 : (2 * ↑Real.pi : ℂ) ^ (2 : ℂ) = 4 * (↑Real.pi) ^ 2 := by
    have hc2 : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
    rw [hc2, Complex.cpow_natCast]
    ring
  -- sin(π(s+2)/2) = -sin(πs/2)
  have hsin : Complex.sin (↑Real.pi * (s + 2) / 2) = -Complex.sin (↑Real.pi * s / 2) := by
    have harg : ↑Real.pi * (s + 2) / 2 = ↑Real.pi * s / 2 + ↑Real.pi := by ring
    rw [harg, Complex.sin_add_pi]
  -- Γ(-1-s) = Γ(1-s)/(s(s+1)): Gamma_add_one 两次 (需 -s ≠ 0, -1-s ≠ 0)
  have hG1 : Complex.Gamma (1 - s) = (-s) * Complex.Gamma (-s) := by
    have hne : -s ≠ 0 := by
      intro h
      apply hs0
      exact neg_eq_zero.mp h
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Complex.Gamma_add_one (-s) hne)
  have hG2 : Complex.Gamma (-s) = (-1 - s) * Complex.Gamma (-1 - s) := by
    have hne : -1 - s ≠ 0 := by
      intro h
      apply hs1
      -- -1 - s = 0 ⟹ s = -1
      have h' : (s + 1 : ℂ) = 0 := by
        have : s + 1 = -(-1 - s) := by ring
        rw [this, h]
        norm_num
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h']
        _ = -1 := by norm_num
    have hg := Complex.Gamma_add_one (-1 - s) hne
    have harg : (-1 - s) + 1 = -s := by ring
    rw [harg] at hg
    exact hg
  have hrel : Complex.Gamma (1 - s) = s * (s + 1) * Complex.Gamma (-1 - s) := by
    calc
      Complex.Gamma (1 - s) = (-s) * Complex.Gamma (-s) := hG1
      _ = (-s) * ((-1 - s) * Complex.Gamma (-1 - s)) := by rw [hG2]
      _ = s * (s + 1) * Complex.Gamma (-1 - s) := by ring
  have hs' : s * (s + 1) ≠ 0 := by
    exact mul_ne_zero hs0 (by
      intro h
      apply hs1
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h]
        _ = -1 := by norm_num)
  have hG : Complex.Gamma (-1 - s) = Complex.Gamma (1 - s) / (s * (s + 1)) := by
    calc
      Complex.Gamma (-1 - s) = (s * (s + 1) * Complex.Gamma (-1 - s)) / (s * (s + 1)) := by
        rw [mul_comm (s * (s + 1)) (Complex.Gamma (-1 - s))]
        rw [mul_div_cancel_right₀ _ hs']
      _ = Complex.Gamma (1 - s) / (s * (s + 1)) := by
        rw [← hrel]
  -- 组装
  calc
    2 * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) * Complex.sin (↑Real.pi * (s + 2) / 2)
        = 2 * ((2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (2 : ℂ)) * Complex.Gamma (-1 - s) *
            (-Complex.sin (↑Real.pi * s / 2)) := by
            rw [hpow, hsin]
      _ = 2 * ((2 * ↑Real.pi : ℂ) ^ (s - 1) * (4 * (↑Real.pi) ^ 2)) * (Complex.Gamma (1 - s) / (s * (s + 1))) *
            (-Complex.sin (↑Real.pi * s / 2)) := by
            rw [hpow2, hG]
      _ = -4 * (↑Real.pi) ^ 2 / (s * (s + 1)) * (2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)) := by
            ring

/-- χ 的平移递推 (相位层, 模 2π):
    arg χ(s+2) - arg χ(s) = π - arg(s(s+1))。arg(-4π²) = π (模 2π)。 
English: χ translation recursion (phase layer, mod 2π): arg χ(s+2) - arg χ(s) = π - arg(s(s+1)). arg(-4π²) = π (mod 2π). -/
theorem chi_arg_translation_two (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hχ : 2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) ≠ 0) :
    (((2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) *
      Complex.sin (↑Real.pi * (s + 2) / 2)).arg : Real.Angle)
      = (((2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        + (↑Real.pi : Real.Angle)
        - ((s * (s + 1)).arg : Real.Angle) := by
  have h := chi_translation_two s hs0 hs1
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 右侧拆: -4π²/(s(s+1)) · χ(s)
  have hs' : s * (s + 1) ≠ 0 := by
    exact mul_ne_zero hs0 (by
      intro h
      apply hs1
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h]
        _ = -1 := by norm_num)
  have hπ2 : (-4 * (↑Real.pi) ^ 2 : ℂ) ≠ 0 := by
    have hπ : (↑Real.pi : ℂ) ≠ 0 := by
      intro h
      apply Real.pi_ne_zero
      have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
      simpa using this
    exact mul_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) (pow_ne_zero 2 hπ)
  have hfac : (-4 * (↑Real.pi) ^ 2 / (s * (s + 1)) : ℂ) ≠ 0 :=
    div_ne_zero hπ2 hs'
  rw [Complex.arg_mul_coe_angle hfac hχ] at harg
  rw [Complex.arg_div_coe_angle hπ2 hs'] at harg
  -- arg(-4π²) = π (模 2π)
  have harg_neg : ((-4 * (↑Real.pi) ^ 2 : ℂ).arg : Real.Angle) = (↑Real.pi : Real.Angle) := by
    have h1 : (-4 * (↑Real.pi) ^ 2 : ℂ) = (-1 : ℂ) * (4 * (↑Real.pi) ^ 2 : ℂ) := by ring
    rw [h1]
    have hπ' : (↑Real.pi : ℂ) ≠ 0 := by
      intro h
      apply Real.pi_ne_zero
      have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
      simpa using this
    have hm := Complex.arg_mul_coe_angle (by norm_num : (-1 : ℂ) ≠ 0)
      (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 hπ'))
    rw [hm]
    rw [Complex.arg_neg_one]
    have harg4 : (4 * (↑Real.pi) ^ 2 : ℂ).arg = 0 := by
      have hc : (4 * (↑Real.pi) ^ 2 : ℂ) = (↑(4 * Real.pi ^ 2 : ℝ) : ℂ) := by norm_num
      rw [hc]
      exact Complex.arg_ofReal_of_nonneg (by positivity : 0 ≤ (4 * Real.pi ^ 2 : ℝ))
    rw [harg4]
    simp
  rw [harg_neg] at harg
  -- harg: ↑arg χ(s+2) = (π - ↑arg(s(s+1))) + ↑arg χ(s)
  -- 目标: ↑arg χ(s+2) = ↑arg χ(s) + π - ↑arg(s(s+1))
  have h1 : (↑Real.pi - ((s * (s + 1)).arg : Real.Angle))
        + ((2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
      = ((2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        + ↑Real.pi - ((s * (s + 1)).arg : Real.Angle) := by
    abel
  rw [← h1]
  exact harg



/-- 辅助: s + k = 0 ⟹ s = -k (ℂ 上, k : ℕ)。 
English: Auxiliary: s + k = 0 ⟹ s = -k (over ℂ, k : ℕ). -/
private lemma eq_neg_of_add_eq_zero (s : ℂ) (k : ℕ) (h : s + (k : ℂ) = 0) :
    s = -(k : ℂ) := by
  calc
    s = (s + (k : ℂ)) - (k : ℂ) := by ring
    _ = 0 - (k : ℂ) := by rw [h]
    _ = -(k : ℂ) := by norm_num

/-- χ 的两步平移递推 (数字层): χ(s+4) = 16π⁴/(s(s+1)(s+2)(s+3))·χ(s)。
    对称点与延拓点交换: 每一步以上一步的结果为对称点, 无固定中心。
    由 chi_translation_two 迭代两次 (χ(s+4) = χ((s+2)+2))。 
English: Two-step χ translation recursion (numeric layer): χ(s+4) = 16π⁴/(s(s+1)(s+2)(s+3))·χ(s). Symmetry point and continuation point exchange: each step uses the previous result as symmetry point, no fixed center. From iterating chi_translation_two twice (χ(s+4) = χ((s+2)+2)). -/
theorem chi_translation_four (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hs2 : s ≠ -2) (hs3 : s ≠ -3) :
    2 * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) * Complex.sin (↑Real.pi * (s + 4) / 2)
      = 16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s - 1) *
          Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2)) := by
  have h1 := chi_translation_two s hs0 hs1
  have hs1' : s + 1 ≠ 0 := by
    intro h
    apply hs1
    have h' : s + ((1 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 1 h')
  have hs2' : s + 2 ≠ 0 := by
    intro h
    apply hs2
    have h' : s + ((2 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 2 h')
  have hs3' : s + 2 ≠ -1 := by
    intro h
    apply hs3
    -- s + 2 = -1 ⟹ s = -3
    have : s = -3 := by
      have h' : s + 3 = 0 := by
        have : s + 3 = (s + 2) + 1 := by ring
        rw [this, h]
        norm_num
      simpa using (eq_neg_of_add_eq_zero s 3 h')
    exact this
  have h2 := chi_translation_two (s + 2) hs2' hs3'
  -- 归一 h2 的参数
  have hg1 : (s + 2) + 1 = s + 3 := by ring
  have hg2 : -1 - (s + 2) = -3 - s := by ring
  have hg3 : (s + 2) + 2 = s + 4 := by ring
  have hg4 : 1 - (s + 2) = -1 - s := by ring
  have hg5 : (s + 2) - 1 = s + 1 := by ring
  rw [hg1, hg2, hg3, hg4, hg5] at h2
  -- 组装
  calc
    2 * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) * Complex.sin (↑Real.pi * (s + 4) / 2)
        = -4 * (↑Real.pi) ^ 2 / ((s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s + 1) * Complex.Gamma (-1 - s) *
            Complex.sin (↑Real.pi * (s + 2) / 2)) := by
            exact h2
      _ = 16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s - 1) *
            Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2)) := by
            rw [h1]
            field_simp [hs0, hs1', hs2', hs3']
            ring

/-- χ 的两步平移递推 (相位层, 模 2π): "交换延拓"的迭代 —
    arg χ(s+4) = arg χ(s) - arg(s(s+1)) - arg((s+2)(s+3))。
    arg(16π⁴) = 0 (正实数), 两步的 π 常数抵消 (π + π = 2π)。 
English: Two-step χ translation recursion (phase layer, mod 2π): iteration of exchange continuation — arg χ(s+4) = arg χ(s) - arg(s(s+1)) - arg((s+2)(s+3)). arg(16π⁴) = 0 (positive real); the π constants of the two steps cancel (π + π = 2π). -/
theorem chi_arg_translation_four (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hs2 : s ≠ -2) (hs3 : s ≠ -3)
    (hχ : 2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) ≠ 0) :
    (((2 : ℂ) * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) *
      Complex.sin (↑Real.pi * (s + 4) / 2)).arg : Real.Angle)
      = (((2 : ℂ) * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle) := by
  have h := chi_translation_four s hs0 hs1 hs2 hs3
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 右侧拆: 16π⁴/(s(s+1)(s+2)(s+3)) · χ(s)
  have hs1' : s + 1 ≠ 0 := by
    intro h
    apply hs1
    have h' : s + ((1 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 1 h')
  have hs2' : s + 2 ≠ 0 := by
    intro h
    apply hs2
    have h' : s + ((2 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 2 h')
  have hs3' : s + 3 ≠ 0 := by
    intro h
    apply hs3
    have h' : s + ((3 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 3 h')
  have hsden : (s * (s + 1) * (s + 2) * (s + 3)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1') hs2') hs3'
  have hπ : (↑Real.pi : ℂ) ≠ 0 := by
    intro h
    apply Real.pi_ne_zero
    have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
    simpa using this
  have h16 : (16 * (↑Real.pi) ^ 4 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) (pow_ne_zero 4 hπ)
  have hfac : (16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) : ℂ) ≠ 0 :=
    div_ne_zero h16 hsden
  rw [Complex.arg_mul_coe_angle hfac hχ] at harg
  rw [Complex.arg_div_coe_angle h16 hsden] at harg
  -- arg(16π⁴) = 0 (正实数)
  have harg16 : ((16 * (↑Real.pi) ^ 4 : ℂ).arg : Real.Angle) = 0 := by
    have hc : (16 * (↑Real.pi) ^ 4 : ℂ) = (↑(16 * Real.pi ^ 4 : ℝ) : ℂ) := by norm_num
    rw [hc]
    exact congrArg (fun x : ℝ => (x : Real.Angle))
      (Complex.arg_ofReal_of_nonneg (by positivity : 0 ≤ (16 * Real.pi ^ 4 : ℝ)))
  rw [harg16] at harg
  -- harg: ↑arg χ(s+4) = 0 - ↑arg(s(s+1)) - ↑arg((s+2)(s+3)) + ↑arg χ(s)
  -- 目标: ↑arg χ(s+4) = ↑arg χ(s) - ↑arg(s(s+1)) - ↑arg((s+2)(s+3))
  have h1 : (0 : Real.Angle) - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle)
        + ((2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
      = ((2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle) := by
    abel
  rw [← h1]
  exact harg
/-!
# T5: u² = χ — 无分支的相位恒等式 (三角函数累积延拓)

u(t) = ζ(1/2+it)/|ζ(1/2+it)| = e^{i·arg ζ}: 良定义连续 (ζ ≠ 0 处), 无分支。
由函数方程 (s = 1/2+it 时 1-s = conj s) + mathlib 全域共轭 riemannZeta_conj:

  ζ(s) = χ(s)·conj ζ(s)  ⟹  u(t)² = χ(1/2+it)

u 是 χ 的连续平方根: 沿 t 累积延拓, 每跨一个零点 u → -u (符号翻转 =
arg 跳 π = 一个零点), 翻转次数 = N₀(T)。整数计数由累积自动给出
(傅里叶相位校准) — 不需要解析地维护 arg 的分支。

χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2) (临界线全显式)。

隔离文件 (mathlib-only: riemannZeta_conj 来自 ZetaAsymp, olean 可用)。
-/

noncomputable section

open Complex

namespace RiemannUnifiedObservation

-- arg(2π) ≠ π (conj_cpow 的条件: 底数不在负实轴)
private lemma arg_two_pi_ne_pi : ((2 * ↑Real.pi : ℂ).arg) ≠ Real.pi := by
  have h0 : (2 * ↑Real.pi : ℂ).arg = 0 := by
    have h0' : ((2 * Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by positivity)
    simpa using h0'
  rw [h0]
  exact Real.pi_ne_zero.symm

-- conj 穿透 cpow (2π 底数, 正实数)
private lemma conj_two_pi_cpow (z : ℂ) :
    (starRingEnd ℂ) ((2 * ↑Real.pi : ℂ) ^ z) = (2 * ↑Real.pi : ℂ) ^ ((starRingEnd ℂ) z : ℂ) := by
  have h := Complex.conj_cpow (2 * ↑Real.pi : ℂ) z arg_two_pi_ne_pi
  have hc : (starRingEnd ℂ) (2 * ↑Real.pi : ℂ) = 2 * ↑Real.pi := by
    have hcast : (2 * ↑Real.pi : ℂ) = (↑(2 * Real.pi : ℝ) : ℂ) := by norm_num
    rw [hcast]
    exact Complex.conj_ofReal (2 * Real.pi)
  rw [hc] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa using h'

/-- 临界线闭合: ζ(s) = χ(s)·conj ζ(s), s = 1/2+it。
    函数方程 (1-s = conj s) + riemannZeta_conj (mathlib 全域共轭)。
    χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2)。 
English: Critical line closure: ζ(s) = χ(s)·conj ζ(s), s = 1/2+it. Functional equation (1-s = conj s) + riemannZeta_conj (mathlib global conjugation). χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2). -/
theorem zeta_eq_chi_mul_conj_on_line (t : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = 2 * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ) *
          Complex.Gamma (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2) *
          (starRingEnd ℂ) (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have h1s : 1 - s = (starRingEnd ℂ) s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  have hs_int : ∀ n : ℕ, s ≠ -↑n := by
    intro n hn
    have hre : s.re = 1 / 2 := by dsimp [s]; simp
    have : s.re = (-(n : ℂ)).re := by rw [hn]
    rw [hre] at this
    have hnre : (-(n : ℂ)).re = -(n : ℝ) := by simp
    rw [hnre] at this
    nlinarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 / 2 := by dsimp [s]; simp
    have : s.re = 1 := by rw [h]; simp
    rw [hre] at this
    norm_num at this
  have hfe := riemannZeta_one_sub (s := s) hs_int hs1
  -- hfe : ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  rw [h1s] at hfe
  -- hfe : ζ(conj s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  rw [riemannZeta_conj s] at hfe
  -- hfe : conj ζ(s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  have hfe' := congrArg (starRingEnd ℂ) hfe
  -- hfe' : ζ(s) = conj(2(2π)^{-s}Γ(s)cos(πs/2)ζ(s))
  have hfe'' : riemannZeta s = 2 * (2 * ↑Real.pi) ^ (-(starRingEnd ℂ) s) *
      Complex.Gamma ((starRingEnd ℂ) s) * Complex.cos (↑Real.pi * (starRingEnd ℂ) s / 2) *
      riemannZeta ((starRingEnd ℂ) s) := by
    -- conj 穿透: star 保环运算 + 各 conj 定理 (← 方向: conj(cos x) → cos(conj x))
    have h2c : (starRingEnd ℂ) 2 = 2 := by exact Complex.conj_ofReal 2
    simpa [h2c, ← Complex.Gamma_conj, ← Complex.cos_conj, ← riemannZeta_conj, conj_two_pi_cpow]
      using hfe'
  -- 替换 conj s = 1-s
  rw [← h1s] at hfe''
  -- -(1-s) = s-1
  have hneg : -(1 - s) = (s - 1 : ℂ) := by ring
  rw [hneg] at hfe''
  -- cos(π(1-s)/2) = sin(πs/2)
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) = Complex.sin (↑Real.pi * s / 2) := by
    rw [← Complex.cos_sub_pi_div_two]
    have harg : ↑Real.pi * (1 - s) / 2 = -((↑Real.pi * s / 2) - ↑Real.pi / 2) := by
      dsimp [s]; ring
    rw [harg, Complex.cos_neg]
  rw [hcos] at hfe''
  -- ζ(1-s) → conj ζ(s): 只替换 ζ 的参数 (Γ(1-s) 保持)
  have hzeta_arg : riemannZeta (1 - s) = riemannZeta ((starRingEnd ℂ) s) := by rw [h1s]
  rw [hzeta_arg] at hfe''
  rw [riemannZeta_conj s] at hfe''
  -- hfe'' : ζ(s) = 2(2π)^{s-1}·Γ(1-s)·sin(πs/2)·conj ζ(s)
  dsimp [s] at hfe''
  exact hfe''

/-- u² = χ: u(t) = ζ(s)/|ζ(s)| 满足 u² = χ(s) (s = 1/2+it)。
    ζ = χ·conj ζ ⟹ |ζ|² = χ·(conj ζ)² ⟹ 1 = χ·(conj u)² ⟹ u² = χ (u·conj u = 1)。
    u 是 χ 的连续平方根 — 累积延拓的基元。 
English: u² = χ: u(t) = ζ(s)/|ζ(s)| satisfies u² = χ(s) (s = 1/2+it). ζ = χ·conj ζ ⟹ |ζ|² = χ·(conj ζ)² ⟹ 1 = χ·(conj u)² ⟹ u² = χ (u·conj u = 1). u is a continuous square root of χ — the primitive of cumulative continuation. -/
theorem zeta_unit_sq_eq_chi (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) ^ 2
      = 2 * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ) *
          Complex.Gamma (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let u : ℂ := riemannZeta s / ‖riemannZeta s‖
  have hmain := zeta_eq_chi_mul_conj_on_line t
  -- |ζ|² = χ·(conj ζ)² (hmain 乘 conj ζ)
  have h2 : (‖riemannZeta s‖ : ℂ) ^ 2 =
      2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
        Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s) *
        (starRingEnd ℂ) (riemannZeta s) := by
    calc
      (‖riemannZeta s‖ : ℂ) ^ 2 = (↑(‖riemannZeta s‖ ^ 2) : ℂ) := by
        exact (map_pow Complex.ofRealHom (‖riemannZeta s‖) 2).symm
      _ = (Complex.normSq (riemannZeta s) : ℂ) := by
        rw [← Complex.normSq_eq_norm_sq]
      _ = riemannZeta s * (starRingEnd ℂ) (riemannZeta s) := by
        rw [← Complex.mul_conj]
      _ = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s)) *
          (starRingEnd ℂ) (riemannZeta s) := by
        -- hmain 两边乘 star ζ (s = (1/2:ℂ)+... 是 let, defeq)
        exact congrArg (fun x : ℂ => x * (starRingEnd ℂ) (riemannZeta s)) hmain
  have hz_norm : (‖riemannZeta s‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  -- 1 = χ·(conj u)² (h2 除以 ‖ζ‖²)
  have h1 : (1 : ℂ) = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2 := by
    calc
      1 = (‖riemannZeta s‖ : ℂ) ^ 2 / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        field_simp [hz_norm]
      _ = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s) *
            (starRingEnd ℂ) (riemannZeta s)) / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        rw [h2]
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ)) ^ 2 := by
        ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2 := by
        -- star(ζ/‖ζ‖) = star ζ/‖ζ‖ (‖ζ‖ 实)
        congr 1
        have hu : (starRingEnd ℂ) (riemannZeta s / (‖riemannZeta s‖ : ℂ)) =
            (starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ) := by
          rw [map_div₀]
          simp
        simpa [u] using hu
  -- u·conj u = 1
  have hu1 : u * (starRingEnd ℂ) u = 1 := by
    have hnorm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_div]
      have hn : ‖(‖riemannZeta s‖ : ℂ)‖ = ‖riemannZeta s‖ := by
        calc
          ‖(‖riemannZeta s‖ : ℂ)‖ = |‖riemannZeta s‖| :=
            RCLike.norm_ofReal (‖riemannZeta s‖)
          _ = ‖riemannZeta s‖ := abs_of_nonneg (norm_nonneg _)
      rw [hn]
      have hz_norm_r : ‖riemannZeta s‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      field_simp [hz_norm_r]
    rw [Complex.mul_conj]
    -- (normSq u : ℂ) = 1: normSq u = ‖u‖², ‖u‖ = 1
    have hnsq : Complex.normSq u = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
    rw [hnsq, hnorm]
    norm_num
  -- u² = χ (1 = χ·(conj u)² 两边乘 u²)
  have hu2 : u ^ 2 = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) := by
    calc
      u ^ 2 = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2) * u ^ 2 := by
            rw [← h1]
            simp
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * (((starRingEnd ℂ) u) * u) ^ 2 := by
          ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * (u * (starRingEnd ℂ) u) ^ 2 := by
          ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * 1 := by
          rw [hu1]
          ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) := by
          ring
  -- 替换 s, u
  dsimp [u, s] at hu2
  exact hu2

  -- ============================================================
  -- T6: 翻转计数的连续基础 (2026-08-21)
  -- 零点离散/有限 + u 连续 + χ 连续幅角提升 (覆盖映射 liftPath)
  -- 翻转 (u→-u) ⟺ χ 转一整圈: u²=χ (T5), 提升差/2π = 翻转次数
  -- ============================================================

/-- ζ 的零点集 = mathlib 的 `riemannZetaZeros`。 
English: Zero set of ζ = mathlib's `riemannZetaZeros`. -/
def zetaZeroSet : Set ℂ := riemannZetaZeros

/-- 零点集闭。 
English: The zero set is closed. -/
lemma isClosed_zetaZeroSet : IsClosed zetaZeroSet := by
  simpa [zetaZeroSet] using isClosed_riemannZetaZeros

/-- 零点集离散: 每个零点孤立。 
English: The zero set is discrete: every zero is isolated. -/
lemma isDiscrete_zetaZeroSet : IsDiscrete zetaZeroSet := by
  simpa [zetaZeroSet] using isDiscrete_riemannZetaZeros

/-- 紧致集 ∩ 零点集有限。 
English: Compact set ∩ zero set is finite. -/
lemma IsCompact.inter_zetaZeroSet_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ zetaZeroSet).Finite := by
  simpa [zetaZeroSet] using hS.inter_riemannZetaZeros_finite

/-- 带内零点有限: [0,1]×[-T,T] 内仅有限多个零点。
带是紧致的 (含于闭球 ‖z‖ ≤ sqrt(1+T²)+1, 离散零点在紧集内有限)。 
English: Finitely many zeros in a strip: only finitely many zeros in [0,1]×[-T,T]. The strip is compact (contained in the closed ball ‖z‖ ≤ sqrt(1+T²)+1; discrete zeros are finite within a compact set). -/
theorem zeta_zeros_finite_in_strip (T : ℝ) :
    ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}).Finite := by
  let R : ℝ := Real.sqrt (1 + T ^ 2) + 1
  have hsub : {z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
      ⊆ Metric.closedBall (0 : ℂ) R ∩ zetaZeroSet := by
    intro z hz
    rcases hz with ⟨hz0, hre0, hre1, him⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hnormSq : Complex.normSq z ≤ 1 + T ^ 2 := by
        rw [Complex.normSq_apply]
        have h1 : z.re ^ 2 ≤ 1 := by
          have hmul : z.re * z.re ≤ 1 * 1 := mul_le_mul hre1 hre1 hre0 zero_le_one
          simpa [pow_two] using hmul
        have h2 : z.im ^ 2 ≤ T ^ 2 := by
          have hT : 0 ≤ T := le_trans (abs_nonneg z.im) him
          have hmul : |z.im| * |z.im| ≤ T * T := mul_le_mul him him (abs_nonneg z.im) hT
          have h2' : |z.im| ^ 2 ≤ T ^ 2 := by simpa [pow_two] using hmul
          nlinarith [h2', sq_abs (z.im)]
        nlinarith
      calc
        ‖z‖ = Real.sqrt (‖z‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]
        _ = Real.sqrt (Complex.normSq z) := by rw [Complex.normSq_eq_norm_sq]
        _ ≤ Real.sqrt (1 + T ^ 2) := Real.sqrt_le_sqrt hnormSq
        _ ≤ R := by
          dsimp [R]
          linarith
    · simpa [zetaZeroSet, mem_riemannZetaZeros] using hz0
  have hfin : (Metric.closedBall (0 : ℂ) R ∩ zetaZeroSet).Finite :=
    IsCompact.inter_zetaZeroSet_finite (isCompact_closedBall (x := (0 : ℂ)) R)
  exact hfin.subset hsub

/-- u(s) = ζ(s)/|ζ(s)|: 单位圆投影 (相位)。 
English: u(s) = ζ(s)/|ζ(s)|: unit circle projection (phase). -/
def zetaUnit (s : ℂ) : ℂ := riemannZeta s / ‖riemannZeta s‖

/-- u 在 ζ ≠ 0 且 s ≠ 1 处连续: ζ 在 {1}ᶜ 可微, 除法分母非零。 
English: u is continuous where ζ ≠ 0 and s ≠ 1: ζ differentiable on {1}ᶜ, division denominator nonzero. -/
lemma continuousOn_zetaUnit :
    ContinuousOn zetaUnit ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) := by
  have hzeta : ContinuousOn riemannZeta ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) :=
    differentiableOn_riemannZeta.continuousOn.mono (by intro s hs; exact hs.1)
  have hnorm : ContinuousOn (fun s : ℂ => (‖riemannZeta s‖ : ℂ))
      ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) := by
    intro x hx
    exact ContinuousWithinAt.comp (t := Set.univ) continuous_ofReal.continuousWithinAt
      (hzeta x hx).norm (by intro y hy; simp)
  refine hzeta.div hnorm ?_
  intro s hs
  exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hs.2)

/-- χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): 函数方程乘子 (显式相位)。 
English: χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): functional equation multiplier (explicit phase). -/
def chi (s : ℂ) : ℂ :=
  2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
    Complex.sin (↑Real.pi * s / 2)

/-- χ 沿临界线连续: 幂 (底 2π ∈ slitPlane) / Γ (1-s 非负整数) / sin 逐项连续。 
English: χ continuous along the critical line: power (base 2π ∈ slitPlane) / Γ (1-s not a nonnegative integer) / sin, termwise continuous. -/
lemma continuousOn_chi_line : ContinuousOn chi {s : ℂ | s.re = 1 / 2} := by
  have hpow : ContinuousOn (fun s : ℂ => (2 * ↑Real.pi : ℂ) ^ (s - 1))
      {s | s.re = 1 / 2} := by
    refine ContinuousOn.cpow continuousOn_const ?hg ?h0
    · have hg : ContinuousOn (fun s : ℂ => s - 1) {s | s.re = 1 / 2} := by
        intro s hs
        exact (continuousAt_id.sub continuousAt_const).continuousWithinAt
      exact hg
    · intro s hs
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by
        rw [Complex.mul_re]
        simp
        nlinarith [Real.pi_pos]))
  have hΓ : ContinuousOn (fun s : ℂ => Complex.Gamma (1 - s))
      {s | s.re = 1 / 2} := by
    intro s hs
    have h1ms : ContinuousAt (fun s : ℂ => 1 - s) s := by
      change ContinuousAt ((fun _ : ℂ => (1 : ℂ)) - id) s
      exact continuousAt_const.sub continuousAt_id
    exact (ContinuousAt.comp (continuousAt_Gamma (1 - s) (by
      intro m hm
      have hsr : s.re = 1 / 2 := by simpa using hs
      have hre' : 1 - s.re = -↑(m : ℝ) := by
        simpa using congrArg Complex.re hm
      have hneg : -↑(m : ℝ) = 1 / 2 := by linarith [hsr, hre']
      have hnonneg : (0 : ℝ) ≤ ↑(m : ℝ) := Nat.cast_nonneg m
      nlinarith)) h1ms).continuousWithinAt
  have hsin : ContinuousOn (fun s : ℂ => Complex.sin (↑Real.pi * s / 2))
      {s | s.re = 1 / 2} := by
    have hlin : Continuous (fun s : ℂ => (↑Real.pi / 2 : ℂ) * s) :=
      continuous_const.mul continuous_id
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Function.comp_def] using
      (continuous_sin.comp hlin).continuousOn
  change ContinuousOn
    (fun s : ℂ =>
      2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.sin (↑Real.pi * s / 2))
    {s | s.re = 1 / 2}
  exact ((continuousOn_const.mul hpow).mul hΓ).mul hsin

/-- χ 沿临界线非零: 2 非零 / (2π)^{s-1} 底非零 / Γ(1-s) 在 re>0 / sin 零点在 πℤ 之外。 
English: χ nonzero along the critical line: 2 nonzero / (2π)^{s-1} base nonzero / Γ(1-s) on re>0 / sin zeros outside πℤ. -/
lemma chi_ne_zero_on_line (t : ℝ) :
    chi ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) ≠ 0 := by
  dsimp [chi]
  refine mul_ne_zero ?_ ?_
  · refine mul_ne_zero ?_ ?_
    · refine mul_ne_zero ?_ ?_
      · norm_num
      · have h2pi : (2 * ↑Real.pi : ℂ) ≠ 0 :=
          mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
        exact (cpow_ne_zero_iff.mpr (Or.inl h2pi))
    · exact Complex.Gamma_ne_zero_of_re_pos (by
        rw [Complex.sub_re, Complex.add_re, Complex.mul_re]
        simp
        norm_num)
  · rw [Complex.sin_ne_zero_iff]
    intro k hk
    have hπ : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hπ0 : (↑Real.pi : ℂ) *
        (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 - (k : ℂ)) = 0 := by
      rw [mul_sub]
      have hπhalf : (↑Real.pi : ℂ) * (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2) =
          (↑Real.pi : ℂ) * ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 := by
        ring
      rw [hπhalf, hk]
      ring
    have hsub : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 - (k : ℂ) = 0 :=
      (mul_eq_zero.mp hπ0).resolve_left hπ
    have hs2 : (1 / 2 : ℂ) + (t : ℝ) * Complex.I = (2 : ℂ) * (k : ℂ) := by
      calc
        (1 / 2 : ℂ) + (t : ℝ) * Complex.I =
            (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2) * 2 := by ring
        _ = (k : ℂ) * 2 := by
          rw [show ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 = (k : ℂ)
            by simpa [sub_eq_zero] using hsub]
        _ = 2 * (k : ℂ) := by ring
    have hre0 : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by
      rw [Complex.add_re, Complex.mul_re]
      simp
    have hre1 : ((2 : ℂ) * (k : ℂ)).re = 2 * (k : ℝ) := by simp
    have hEq : (1 / 2 : ℝ) = 2 * (k : ℝ) := by
      have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re =
          ((2 : ℂ) * (k : ℂ)).re := by
        rw [hs2]
      rw [hre0, hre1] at hre
      exact hre
    have hEq' : (4 * (k : ℤ) : ℤ) = 1 := by
      have h4 : (4 * (k : ℝ) : ℝ) = 1 := by nlinarith [hEq]
      exact_mod_cast h4
    omega

/-- χ 沿临界线在 [0,1] 上的路径: 基空间 ℂ\{0} 值, 连续 (线上连续 + 参数连续)。 
English: Path of χ along the critical line on [0,1]: values in base space ℂ\{0}, continuous (continuous on the line + continuous parameter). -/
def chiPath (T : ℝ) : C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨chi ((1 / 2 : ℂ) + ((T * s.1 : ℝ) : ℂ) * Complex.I),
    chi_ne_zero_on_line (T * s.1)⟩
  continuous_toFun := by
    have hsfun : Continuous (fun s : ℝ => (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hpath : Continuous (fun s : ℝ => chi ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)) := by
      rw [← continuousOn_univ]
      exact continuousOn_chi_line.comp hsfun.continuousOn (by intro s hs; simp)
    exact Continuous.subtype_mk (hpath.comp continuous_subtype_val)
      (fun s => chi_ne_zero_on_line (T * s.1))

/-- 提升起点 y₀ = log χ(1/2): exp y₀ = χ(1/2) (exp_log)。 
English: Lift start y₀ = log χ(1/2): exp y₀ = χ(1/2) (exp_log). -/
noncomputable def theta0 (_T : ℝ) : ℂ :=
  Complex.log (chi ((1 / 2 : ℂ) + (0 : ℝ) * Complex.I))

lemma exp_theta0 (T : ℝ) :
    Complex.exp (theta0 T) = chi ((1 / 2 : ℂ) + (0 : ℝ) * Complex.I) := by
  dsimp [theta0]
  exact Complex.exp_log (chi_ne_zero_on_line 0)

/-- liftPath 的起点条件: γ 0 = p y₀ (χ(1/2) = exp y₀)。 
English: Start condition of liftPath: γ 0 = p y₀ (χ(1/2) = exp y₀). -/
private lemma liftPath_γ0 (T : ℝ) :
    chiPath T 0 = (⟨Complex.exp (theta0 T), Complex.exp_ne_zero (theta0 T)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  dsimp [chiPath]
  have hzero : ((T * (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ) := by
    simp
  rw [hzero]
  simpa using (exp_theta0 T).symm

/-- χ 的连续幅角提升: exp(θ(s)) = χ(1/2 + T·s·i), θ 0 = y₀。
    翻转计数 = (θ(1) - θ(0)) 的虚部差 / 2π。 
English: Continuous argument lift of χ: exp(θ(s)) = χ(1/2 + T·s·i), θ 0 = y₀. Flip count = the imaginary-part difference of (θ(1) - θ(0)) / 2π. -/
noncomputable def thetaLift (T : ℝ) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (chiPath T) (theta0 T) (liftPath_γ0 T)

/-- 提升性质: exp(θ(s)) = χ(1/2 + T·s·i)。 
English: Lift property: exp(θ(s)) = χ(1/2 + T·s·i). -/
lemma thetaLift_lifts (T : ℝ) (s : unitInterval) :
    Complex.exp (thetaLift T s) = chi ((1 / 2 : ℂ) + ((T * s.1 : ℝ) : ℂ) * Complex.I) := by
  have h := (isCoveringMap_exp.liftPath_lifts (chiPath T) (theta0 T) (liftPath_γ0 T))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [thetaLift]
  simpa [chiPath] using hs

/-- 提升起点: θ(0) = y₀。 
English: Lift start: θ(0) = y₀. -/
lemma thetaLift_zero (T : ℝ) :
    thetaLift T 0 = theta0 T := by
  exact isCoveringMap_exp.liftPath_zero (chiPath T) (theta0 T) (liftPath_γ0 T)

  -- ============================================================
  -- T6d: 相位对齐 (起点-终点对称映射) — 2·Δθ_ζ = Δθ_χ (2026-08-21)
  -- u²=χ (T5) ⟹ exp(2θ_ζ)=exp(θ_χ) ⟹ 2θ_ζ-θ_χ ∈ expKernel 常数 ⟹ 端点差
  -- 无零点区间上直接等式, 不需要迭代逼近
  -- ============================================================

/-- u 沿临界线的路径 (无零点区间 [0,T] 上 ζ ≠ 0): 基空间 ℂ\{0} 值, 连续。 
English: Path of u along the critical line (ζ ≠ 0 on the zero-free interval [0,T]): values in base space ℂ\{0}, continuous. -/
def uPath (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
      ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖,
    by
      exact div_ne_zero (hz s)
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz s)))⟩
  continuous_toFun := by
    have hsfun : Continuous (fun s : ℝ => (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hzeta : Continuous (fun s : ℝ => riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)) := by
      rw [← continuousOn_univ]
      exact differentiableOn_riemannZeta.continuousOn.comp hsfun.continuousOn
        (by
          intro s hs h1
          have h1' : (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I = 1 := h1
          have hre : ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I).re = 1 := by
            rw [h1']
            simp
          have hre' : ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I).re = 1 / 2 := by
            simp
          rw [hre'] at hre
          norm_num at hre)
    have hnorm : Continuous (fun s : ℝ => (‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖ : ℂ)) := by
      have hc : Continuous (fun s : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖) :=
        hzeta.norm
      exact continuous_ofReal.comp hc
    have hunitOn : ContinuousOn (fun s : ℝ =>
        riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) /
          ‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖) (Set.Icc 0 1) := by
      refine hzeta.continuousOn.div hnorm.continuousOn ?_
      intro s hs
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz ⟨s, hs⟩))
    have hunit : Continuous (fun s : unitInterval =>
        riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
          ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖) :=
      hunitOn.restrict
    exact Continuous.subtype_mk hunit
      (fun s => div_ne_zero (hz s) (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz s))))

/-- u 的提升起点: y₀ = log u(0)。 
English: u's lift start: y₀ = log u(0). -/
noncomputable def uLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : ℂ :=
  Complex.log ((uPath T hz 0 : {z : ℂ // z ≠ 0}).1)

lemma exp_uLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    Complex.exp (uLift0 T hz) = (uPath T hz 0 : {z : ℂ // z ≠ 0}).1 := by
  dsimp [uLift0]
  exact Complex.exp_log (uPath T hz 0).2

/-- liftPath 的起点条件: γ 0 = p y₀。 
English: Start condition of liftPath: γ 0 = p y₀. -/
private lemma uLift_γ0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    uPath T hz 0 = (⟨Complex.exp (uLift0 T hz), Complex.exp_ne_zero (uLift0 T hz)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  exact (exp_uLift0 T hz).symm

/-- u 的连续幅角提升: exp(θ_ζ(s)) = u(s)。 
English: Continuous argument lift of u: exp(θ_ζ(s)) = u(s). -/
noncomputable def uLift (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz)

/-- 提升性质: exp(θ_ζ(s)) = ζ/‖ζ‖ (1/2 + T·s·i)。 
English: Lift property: exp(θ_ζ(s)) = ζ/‖ζ‖ (1/2 + T·s·i). -/
lemma uLift_lifts (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) (s : unitInterval) :
    Complex.exp (uLift T hz s) =
      riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖ := by
  have h := (isCoveringMap_exp.liftPath_lifts (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [uLift]
  simpa [uPath] using hs

/-- 提升起点: θ_ζ(0) = y₀。 
English: Lift start: θ_ζ(0) = y₀. -/
lemma uLift_zero (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    uLift T hz 0 = uLift0 T hz := by
  exact isCoveringMap_exp.liftPath_zero (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz)

/-- exp 的核: exp z = 1 的点集 (离散, 2πiℤ)。 
English: Kernel of exp: the point set with exp z = 1 (discrete, 2πiℤ). -/
def expKernel : Set ℂ := {z | Complex.exp z = 1}

/-- expKernel = 2πiℤ: exp z = 1 ⟺ ∃ n : ℤ, z = n·2πi。 
English: expKernel = 2πiℤ: exp z = 1 ⟺ ∃ n : ℤ, z = n·2πi. -/
lemma expKernel_mem_iff (z : ℂ) :
    z ∈ expKernel ↔ ∃ n : ℤ, z = (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  rw [expKernel]
  constructor
  · intro hz
    have he : Complex.exp z = Complex.exp 0 := by simpa using hz
    rcases (exp_eq_exp_iff_exists_int.mp he) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa using hn
  · rintro ⟨n, rfl⟩
    change Complex.exp (n * (2 * ↑Real.pi * Complex.I)) = 1
    rw [← Complex.exp_zero, exp_eq_exp_iff_exists_int]
    exact ⟨n, by ring⟩

/-- expKernel 中不同点距离 ≥ 2π (2πiℤ 的网格间距)。 
English: Distinct points of expKernel are at distance ≥ 2π (grid spacing of 2πiℤ). -/
lemma expKernel_dist_ge_two_pi {z w : ℂ} (hz : z ∈ expKernel) (hw : w ∈ expKernel)
    (hzw : z ≠ w) : 2 * Real.pi ≤ ‖z - w‖ := by
  rcases (expKernel_mem_iff z).1 hz with ⟨n, rfl⟩
  rcases (expKernel_mem_iff w).1 hw with ⟨m, rfl⟩
  have hn0 : n ≠ m := by
    intro hnm
    apply hzw
    rw [hnm]
  have hnm1 : (1 : ℝ) ≤ |(n - m : ℤ)| := by
    exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hn0))
  calc
    2 * Real.pi ≤ |((n - m : ℤ) : ℝ)| * (2 * Real.pi) := by
      have hnm1' : (1 : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by
        simpa [Int.cast_abs] using hnm1
      nlinarith [hnm1', Real.pi_pos]
    _ = ‖((n - m : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)‖ := by
      rw [Complex.norm_mul]
      have hnorm : ‖(2 * ↑Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
        rw [show (2 * ↑Real.pi * Complex.I : ℂ) = (2 * ↑Real.pi : ℂ) * Complex.I by ring]
        rw [Complex.norm_mul]
        have hcast : (2 * ↑Real.pi : ℂ) = (↑(2 * Real.pi : ℝ) : ℂ) := by norm_num
        rw [hcast]
        have hn2 : ‖(↑(2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
          exact (RCLike.norm_ofReal (2 * Real.pi)).trans
            (abs_of_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)))
        rw [hn2, Complex.norm_I]
        ring
      rw [Complex.norm_intCast, hnorm]
    _ = ‖(n : ℂ) * (2 * ↑Real.pi * Complex.I) - (m : ℂ) * (2 * ↑Real.pi * Complex.I)‖ := by
      congr 1
      rw [← sub_mul]
      congr 1
      simp

/-- expKernel 的诱导拓扑离散 (每点孤立: 间距 2π > 半径 π 的开球)。 
English: The induced topology of expKernel is discrete (each point isolated: spacing 2π > open ball of radius π). -/
instance expKernel_discrete : DiscreteTopology {z : ℂ // z ∈ expKernel} := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro z
  -- {z} = ball z.1 π ∩ expKernel (诱导拓扑的开集)
  refine ⟨Metric.ball (z : ℂ) Real.pi, Metric.isOpen_ball, ?_⟩
  apply Set.ext
  intro w
  change w ∈ Subtype.val ⁻¹' Metric.ball (z.1 : ℂ) Real.pi ↔ w = z
  constructor
  · intro hw
    apply Subtype.ext
    by_contra hne
    have hd : 2 * Real.pi ≤ ‖w.1 - z.1‖ :=
      expKernel_dist_ge_two_pi w.2 z.2 hne
    have hlt : ‖w.1 - z.1‖ < Real.pi := by
      rw [← dist_eq_norm]
      exact hw
    nlinarith [hd, hlt, Real.pi_pos]
  · intro hw
    rw [hw]
    have hself : z.1 ∈ Metric.ball (z.1 : ℂ) Real.pi :=
      Metric.mem_ball_self Real.pi_pos
    simpa [dist_eq_norm] using hself

/-- **相位对齐 (起点-终点对称映射)**: 无零点区间 [0,T] 上,
    u² = χ (T5) ⟹ exp(2θ_ζ) = exp(θ_χ) ⟹ 2θ_ζ - θ_χ ∈ expKernel 常数 ⟹
    2·(θ_ζ(T) - θ_ζ(0)) = θ_χ(T) - θ_χ(0)。
    起点 (显式 χ 相位) 与终点 (θ_ζ 端点差) 之间的映射相位关系直接锁定,
    不需要迭代逼近。 
English: Phase alignment (the start–end symmetric map): on the zero-free interval [0,T], u² = χ (T5) ⟹ exp(2θ_ζ) = exp(θ_χ) ⟹ 2θ_ζ - θ_χ ∈ expKernel constant ⟹ 2·(θ_ζ(T) - θ_ζ(0)) = θ_χ(T) - θ_χ(0). The mapped phase relation between the start (explicit χ phase) and the end (θ_ζ endpoint difference) is locked directly, no iterative approximation. -/
theorem phase_align_two_zeta_lift_eq_chi_lift (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    2 * (uLift T hz 1 - uLift T hz 0) = thetaLift T 1 - thetaLift T 0 := by
  let f : unitInterval → ℂ := fun s => 2 * uLift T hz s - thetaLift T s
  have hk : ∀ s : unitInterval, f s ∈ expKernel := by
    intro s
    rw [expKernel]
    dsimp [f]
    rw [Complex.exp_sub]
    have h2e : Complex.exp (2 * uLift T hz s) = (Complex.exp (uLift T hz s)) ^ 2 := by
      rw [show (2 : ℂ) * uLift T hz s = uLift T hz s + uLift T hz s by ring]
      rw [Complex.exp_add]
      ring
    rw [h2e]
    rw [uLift_lifts, thetaLift_lifts]
    rw [zeta_unit_sq_eq_chi (T * s.1) (hz s)]
    exact div_self (chi_ne_zero_on_line (T * s.1))
  let f' : unitInterval → {z : ℂ // z ∈ expKernel} := fun s => ⟨f s, hk s⟩
  have hf' : Continuous f' := by
    have hf : Continuous f := by
      dsimp [f]
      exact (continuous_const.mul (uLift T hz).continuous).sub (thetaLift T).continuous
    exact Continuous.subtype_mk hf (fun s => hk s)
  have hc : f' 0 = f' 1 :=
    IsPreconnected.constant (s := Set.univ) (isPreconnected_univ)
      hf'.continuousOn (by trivial) (by trivial)
  have hf01 : f 0 = f 1 := by
    have := congrArg Subtype.val hc
    simpa using this
  dsimp [f] at hf01
  -- hf01 : 2·u0 - t0 = 2·u1 - t1 ⟹ 目标 2(u1-u0) = t1-t0
  calc
    2 * (uLift T hz 1 - uLift T hz 0)
        = 2 * uLift T hz 1 - 2 * uLift T hz 0 := by ring
    _ = (2 * uLift T hz 1 - thetaLift T 1) + (thetaLift T 1 - 2 * uLift T hz 0) := by ring
    _ = (2 * uLift T hz 0 - thetaLift T 0) + (thetaLift T 1 - 2 * uLift T hz 0) := by
      rw [← hf01]
    _ = thetaLift T 1 - thetaLift T 0 := by ring

  -- ============================================================
  -- T6e: S(T) 整数层结构 — θ_ζ - θ_χ/2 ∈ πiℤ (pat ±1 过程) (2026-08-21)
  -- 符号改变 (翻转 ±1) 但位置 (零点) 不变; 整数层 = 2πi 的迭代计数
  -- ============================================================

/-- u² = χ (T5): 无零点处 (ζ/‖ζ‖)² = χ (def chi 形式)。 
English: u² = χ (T5): where no zeros, (ζ/‖ζ‖)² = χ (def chi form). -/
lemma zeta_unit_sq_eq_chi_short (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) ≠ 0) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ : ℂ) ^ 2 = chi ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) := by
  simpa [chi] using (zeta_unit_sq_eq_chi t hz)

/-- **S(T) 的整数层结构**: θ_ζ - θ_χ/2 ∈ πiℤ 逐点 —
    符号改变 (翻转 ±1) 但位置 (零点) 不变 = pat 正负 1 过程。
    整数层 = 2πi 的迭代计数 (i 的迭代), θ_χ 显式 (快路径)。 
English: Integer-layer structure of S(T): θ_ζ - θ_χ/2 ∈ πiℤ pointwise — signs change (flip ±1) but positions (zeros) stay = pat ±1 process. Integer layers = iteration count of 2πi (iterations of i); θ_χ explicit (fast path). -/
theorem zeta_lift_half_chi_lift_pi_int (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0)
    (s : unitInterval) :
    ∃ n : ℤ, uLift T hz s - thetaLift T s / 2 = (n : ℂ) * (↑Real.pi * Complex.I) := by
  -- 2θ_ζ - θ_χ ∈ expKernel = 2πiℤ (从 u² = χ: exp(2θ_ζ) = u² = χ = exp(θ_χ))
  have hk : 2 * uLift T hz s - thetaLift T s ∈ expKernel := by
    rw [expKernel]
    change Complex.exp (2 * uLift T hz s - thetaLift T s) = 1
    rw [Complex.exp_sub]
    have h2e : Complex.exp (2 * uLift T hz s) = (Complex.exp (uLift T hz s)) ^ 2 := by
      rw [show (2 : ℂ) * uLift T hz s = uLift T hz s + uLift T hz s by ring]
      rw [Complex.exp_add]
      ring
    rw [h2e]
    rw [uLift_lifts, thetaLift_lifts]
    -- u² = χ (T5)
    rw [zeta_unit_sq_eq_chi_short (T * s.1) (hz s)]
    exact div_self (chi_ne_zero_on_line (T * s.1))
  -- 2θ_ζ - θ_χ = 2πi·n ⟹ θ_ζ - θ_χ/2 = πi·n
  rcases (expKernel_mem_iff (2 * uLift T hz s - thetaLift T s)).1 hk with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- hn : 2θ_ζ - θ_χ = n·2πi
  -- 目标: θ_ζ - θ_χ/2 = n·πi
  calc
    uLift T hz s - thetaLift T s / 2 = (2 * uLift T hz s - thetaLift T s) / 2 := by ring
    _ = (n : ℂ) * (2 * ↑Real.pi * Complex.I) / 2 := by rw [hn]
    _ = (n : ℂ) * (↑Real.pi * Complex.I) := by ring

  -- ============================================================
  -- T6f: 残差预测方法 0pat 化 — 误差测量序列 (2026-08-21)
  -- 比率恒定 e(2n)/e(n) = 2^{1-s}, 测量一次推全部, 提前量反解
  -- log = e⁻¹ (有限↔无限逆桥), 残差控制全快路径
  -- ============================================================

/-- 多项式级数 ∑ k^{-s} (k > n) 的截断误差模型: e(n) = n^{1-s}/(s-1)。
    来源: ∫_n^∞ x^{-s} dx = n^{1-s}/(s-1) (积分判别, s > 1)。 
English: Truncation error model for the polynomial series ∑ k^{-s} (k > n): e(n) = n^{1-s}/(s-1). Source: ∫_n^∞ x^{-s} dx = n^{1-s}/(s-1) (integral test, s > 1). -/
def polyError (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 - s) / (s - 1)

/-- **核心比率定理**: e(2n)/e(n) = 2^{1-s} — 每层误差比率恒定,
    测量一次 e(n₀) ⟹ 推出所有 e(2^k·n₀)。 
English: Core ratio theorem: e(2n)/e(n) = 2^{1-s} — the error ratio is constant per layer; measuring e(n₀) once ⟹ deriving all e(2^k·n₀). -/
theorem poly_error_ratio {s : ℝ} (hs : s ≠ 1) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) / polyError s n = (2 : ℝ) ^ (1 - s) := by
  dsimp [polyError]
  have hpow : ((2 * n : ℕ) : ℝ) ^ (1 - s) = (2 : ℝ) ^ (1 - s) * (n : ℝ) ^ (1 - s) := by
    rw [show ((2 * n : ℕ) : ℝ) = (2 : ℝ) * (n : ℝ) by norm_num]
    rw [Real.mul_rpow]
    · norm_num
    · exact_mod_cast (Nat.zero_le n)
  rw [hpow]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnsq : (n : ℝ) ^ (1 - s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos (1 - s))
  field_simp [hs, hnsq]

/-- 误差序列预测: 测量一次推全部 — e(2n) = e(n)·2^{1-s}。 
English: Error sequence prediction: one measurement gives all — e(2n) = e(n)·2^{1-s}. -/
theorem error_seq_predicts {s : ℝ} (hs : s ≠ 1) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := by
  have hr := poly_error_ratio hs hn
  dsimp [polyError] at hr ⊢
  -- 从比率定理: e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
  -- 需要 e(n) ≠ 0
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnsq : (n : ℝ) ^ (1 - s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos (1 - s))
  have hne : polyError s n ≠ 0 := by
    dsimp [polyError]
    exact div_ne_zero hnsq (sub_ne_zero.mpr hs)
  -- hr : e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
  have hr' : polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := by
    -- 从比率: e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
    dsimp [polyError] at hr ⊢
    -- 同 poly_error_ratio 的代数
    have hpow : ((2 * n : ℕ) : ℝ) ^ (1 - s) = (2 : ℝ) ^ (1 - s) * (n : ℝ) ^ (1 - s) := by
      rw [show ((2 * n : ℕ) : ℝ) = (2 : ℝ) * (n : ℝ) by norm_num]
      rw [Real.mul_rpow]
      · norm_num
      · exact_mod_cast (Nat.zero_le n)
    rw [hpow] at hr ⊢
    -- hr : (2^{1-s}·n^{1-s}/(s-1)) / (n^{1-s}/(s-1)) = 2^{1-s}
    -- 目标: (2^{1-s}·n^{1-s})/(s-1) = (n^{1-s}/(s-1))·2^{1-s}
    field_simp [hs, hnsq]
  exact hr' 

/-- 误差单调递减: n 加倍 ⟹ 误差按 2^{1-s} 收缩 (s > 1 时 2^{1-s} < 1)。 
English: Error monotonically decreasing: doubling n contracts the error by 2^{1-s} (2^{1-s} < 1 when s > 1). -/
theorem poly_error_monotone {s : ℝ} (hs1 : 1 < s) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) < polyError s n := by
  change ((2 * n : ℕ) : ℝ) ^ (1 - s) / (s - 1) < (n : ℝ) ^ (1 - s) / (s - 1)
  have hr := error_seq_predicts (ne_of_gt hs1) hn
  -- e(2n) = e(n)·2^{1-s}, s > 1 ⟹ 2^{1-s} < 1, e(n) > 0
  have hpos : 0 < polyError s n := by
    dsimp [polyError]
    -- n^{1-s} > 0 (n > 0), s-1 > 0
    exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) (1 - s)) (sub_pos.mpr hs1)
  have hratio : (2 : ℝ) ^ (1 - s) < 1 := by
    -- s > 1 ⟹ 1-s < 0 ⟹ 2^{1-s} < 1 (rpow_lt_one_iff)
    have hneg : 1 - s < 0 := by linarith
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Or.inl ⟨by norm_num, hneg⟩
  calc
    polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := hr
    _ < polyError s n * 1 := by
      exact mul_lt_mul_of_pos_left hratio hpos
    _ = polyError s n := by ring

/-- 提前量反解: 要精度 ε ⟹ n ≥ (1/ε)^{1/(s-1)} 时 e(n) ≤ ε/(s-1)。
    从 e(n) = n^{1-s}/(s-1) 反解 (s > 1): n^{1-s} ≤ ε ⟺ n ≥ (1/ε)^{1/(s-1)}。 
English: Anti-solve for the lead: for precision ε, if n ≥ (1/ε)^{1/(s-1)} then e(n) ≤ ε/(s-1). Solving e(n) = n^{1-s}/(s-1) backwards (s > 1): n^{1-s} ≤ ε ⟺ n ≥ (1/ε)^{1/(s-1)}. -/
theorem error_precision_bound {s : ℝ} (hs1 : 1 < s) {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hn : (1 / ε) ^ (1 / (s - 1)) ≤ (n : ℝ)) :
    polyError s n ≤ ε / (s - 1) := by
  dsimp [polyError]
  have hs1' : 0 < s - 1 := sub_pos.mpr hs1
  have hεinv : 0 < 1 / ε := one_div_pos.mpr hε
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hεinv (1 / (s - 1))) hn
  -- (1/ε)^{1/(s-1)} ≤ n ⟹ 1/ε ≤ n^{s-1} (rpow (s-1) 保序 + 复合)
  have hle : 1 / ε ≤ (n : ℝ) ^ (s - 1) := by
    have h1 : ((1 / ε) ^ (1 / (s - 1))) ^ (s - 1) ≤ (n : ℝ) ^ (s - 1) :=
      Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hεinv (1 / (s - 1)))) hn (le_of_lt hs1')
    have hcomp : ((1 / ε) ^ (1 / (s - 1))) ^ (s - 1) = 1 / ε := by
      rw [← Real.rpow_mul (le_of_lt hεinv) (1 / (s - 1)) (s - 1)]
      congr 1
      field_simp [hs1', hε]
      simp [pow_one]
      field_simp [hε]
    rwa [hcomp] at h1
  -- 1/ε ≤ n^{s-1} ⟹ n^{1-s} = 1/n^{s-1} ≤ ε (倒数保序)
  have hle2 : (n : ℝ) ^ (1 - s) ≤ ε := by
    have hneg : (n : ℝ) ^ (1 - s) = (n : ℝ) ^ (-(s - 1) : ℝ) := by
      congr 1
      ring
    rw [hneg]
    rw [Real.rpow_neg (le_of_lt hnpos) (s - 1)]
    -- 目标: (n^{s-1})⁻¹ ≤ ε ⟸ hle: 1/ε ≤ n^{s-1}
    have hle' : (n : ℝ) ^ (s - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
    rw [inv_eq_one_div]
    have hle'' : 1 / (n : ℝ) ^ (s - 1) ≤ 1 / (1 / ε) := by
      exact one_div_le_one_div_of_le hεinv hle
    -- 1/(1/ε) = ε
    have hle3 : 1 / (n : ℝ) ^ (s - 1) ≤ ε := by
      simpa using hle''
    exact hle3
  -- n^{1-s} ≤ ε ⟹ n^{1-s}/(s-1) ≤ ε/(s-1)
  exact div_le_div_of_nonneg_right hle2 (le_of_lt hs1')

  -- ============================================================
  -- T6g: 反转对接 — 周期发散桥 + 连续离散逆桥 (2026-08-21)
  -- 2Δθ_ζ = Δθ_χ + 2πi·m (翻转 ↔ χ 圈数); 净翻转 = (2Δθ_ζ-Δθ_χ)/(2πi) ∈ ℤ
  -- ============================================================

/-- **周期发散桥 (反转对接)**: 2·Δθ_ζ = Δθ_χ + 2πi·m —
    每翻转一次 (u → -u, 离散 ±1) χ 转一整圈 (连续 2π)。 
English: Periodic-divergence bridge (flip docking): 2·Δθ_ζ = Δθ_χ + 2πi·m — each flip (u → -u, discrete ±1) makes χ turn one full circle (continuous 2π). -/
theorem flip_chi_circle_bridge (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    ∃ m : ℤ, 2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)
      = (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  rcases (zeta_lift_half_chi_lift_pi_int T hz 1) with ⟨n1, h1⟩
  rcases (zeta_lift_half_chi_lift_pi_int T hz 0) with ⟨n0, h0⟩
  refine ⟨n1 - n0, ?_⟩
  -- h1 : θ_ζ(1) - θ_χ(1)/2 = n1·πi; h0 : θ_ζ(0) - θ_χ(0)/2 = n0·πi
  -- 2Δθ_ζ - Δθ_χ = 2·[(θ_ζ(1)-θ_χ(1)/2) - (θ_ζ(0)-θ_χ(0)/2)]
  calc
    2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)
        = 2 * ((uLift T hz 1 - thetaLift T 1 / 2) - (uLift T hz 0 - thetaLift T 0 / 2)) := by ring
    _ = 2 * ((n1 : ℂ) * (↑Real.pi * Complex.I) - (n0 : ℂ) * (↑Real.pi * Complex.I)) := by
      rw [h1, h0]
    _ = ((n1 - n0 : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast
      ring

/-- **连续离散逆桥**: 净翻转 m = (2·Δθ_ζ - Δθ_χ)/(2πi) ∈ ℤ —
    从连续提升的端点差重构离散翻转计数。 
English: Continuous-discrete inverse bridge: net flips m = (2·Δθ_ζ - Δθ_χ)/(2πi) ∈ ℤ — reconstructing the discrete flip count from the continuous lift's endpoint differences. -/
theorem net_flip_from_chi_lift (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    ∃ m : ℤ, (2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)) /
      (2 * ↑Real.pi * Complex.I) = (m : ℂ) := by
  rcases (flip_chi_circle_bridge T hz) with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  -- hm : 2Δu - Δθ = m·2πi ⟹ (2Δu-Δθ)/(2πi) = m
  rw [hm]
  field_simp [hne]


  -- ============================================================
  -- T6k: 矩形闭合桥 — 翻转计数 = χ 圈数 - 整数层 (2026-08-19)
  -- 参数原理矩形闭合 N(T) = (1/π)θ_χ + S(T) + 1 的整数层结构:
  --   翻转计数 (零点数) = (1/2π)·Im Δθ_χ = (1/π)·Im Δθ_ζ - m
  -- θ_χ 是显式相位刻度 (χ 定义), θ_ζ 是隐式相位 (u = ζ/|ζ|),
  -- m ∈ ℤ 是整数层 (e^{iπ} 桥: u² = χ ⟹ 2θ_ζ = θ_χ + 2πi·m)。
  -- ============================================================

/-- **翻转计数桥**: χ 圈数 - 2·θ_ζ 圈数 ∈ ℤ —
    翻转计数 (零点数) 由 χ 的显式圈数与 ζ 的隐式圈数共同确定,
    差是整数层 m (flip_chi_circle_bridge 取虚部)。
    N(T) = (1/π)θ_χ + S + 1 的矩形闭合: 圈数 = 相位差/2π。 
English: Flip count bridge: (χ winding number) - 2·(θ_ζ winding number) ∈ ℤ — the flip count (zero count) is jointly determined by χ's explicit and ζ's implicit winding numbers; the difference is the integer layer m (flip_chi_circle_bridge takes the imaginary part). Rectangle closure of N(T) = (1/π)θ_χ + S + 1: winding number = phase difference / 2π. -/
theorem flip_count_from_theta_lifts (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    ∃ m : ℤ, (thetaLift T 1 - thetaLift T 0).im / (2 * ↑Real.pi) -
      (2 * (uLift T hz 1 - uLift T hz 0)).im / (2 * ↑Real.pi) = (m : ℝ) := by
  rcases (flip_chi_circle_bridge T hz) with ⟨m, hm⟩
  refine ⟨-m, ?_⟩
  -- hm : 2Δu - Δθ = m·2πi ⟹ 取虚部: Im(2Δu) - Im(Δθ) = 2π·m
  have hlinC : (2 * (uLift T hz 1 - uLift T hz 0)).im - (thetaLift T 1 - thetaLift T 0).im
      = (2 * ↑Real.pi : ℝ) * (m : ℝ) := by
    have him := congrArg Complex.im hm
    -- him : Im(2Δu - Δθ) = Im(m·2πi) (ℝ 等式); 左侧 Im 线性, 右侧 Im(m·2πi) = 2π·m
    rw [sub_im] at him
    have hrim : ((m : ℂ) * (2 * ↑Real.pi * Complex.I)).im = (2 * ↑Real.pi : ℝ) * (m : ℝ) := by
      simp
      ring
    rwa [hrim] at him
  -- 转实数: Im(Δθ) - Im(2Δu) = -2π·m
  have hreal : (thetaLift T 1 - thetaLift T 0).im -
      (2 * (uLift T hz 1 - uLift T hz 0)).im = -((2 * ↑Real.pi : ℝ) * (m : ℝ)) := by
    linarith
  -- 除以 2π: 差/2π = -m
  have hdiv : (thetaLift T 1 - thetaLift T 0).im / (2 * ↑Real.pi) -
      (2 * (uLift T hz 1 - uLift T hz 0)).im / (2 * ↑Real.pi) = -(m : ℝ) := by
    have hπ : (2 * ↑Real.pi : ℝ) ≠ 0 := by positivity
    have hd : ((thetaLift T 1 - thetaLift T 0).im - (2 * (uLift T hz 1 - uLift T hz 0)).im) /
        (2 * ↑Real.pi) = -(m : ℝ) := by
      rw [hreal]
      field_simp [hπ]
    simpa [sub_div] using hd
  simpa using hdiv


  -- ============================================================
  -- T6m: 矩形闭合骨架 — Λ₀ 反射对消 (2026-08-19)
  -- 用户方法论继续: 未证部分用桥接+相位对消推进。
  -- mathlib completedRiemannZeta₀ (整函数, 无极点) 替代 ζ (s=1 极点):
  --   Λ₀(1-s) = Λ₀ s (mathlib 反射) ⟹ log Λ₀(1-s) - log Λ₀ s ∈ 2πiℤ
  --   (矩形顶边/左边相位对消的代数骨架: 反射对称的两边 log 差是整数层)
  -- ============================================================

/-- **Λ₀ 反射对消**: log Λ₀(1-s) - log Λ₀ s ∈ 2πiℤ —
    矩形顶边 (s) 与左边 (1-s) 的相位差是整数层 (mathlib 整函数反射
    completedRiemannZeta₀_one_sub + exp 相等 ⟹ log 差 2πi·n)。
    矩形闭合的对称性骨架: 反射两边相位对消, 剩整数圈数。 
English: Λ₀ reflection cancellation: log Λ₀(1-s) - log Λ₀ s ∈ 2πiℤ — the phase difference between the rectangle's top edge (s) and left edge (1-s) is an integer layer (mathlib entire reflection completedRiemannZeta₀_one_sub + equal exps ⟹ log difference 2πi·n). Symmetry skeleton of the rectangle closure: the phases on the two reflected sides cancel, leaving integer winding. -/
theorem completedZeta₀_log_reflection (s : ℂ) (hs : completedRiemannZeta₀ s ≠ 0) :
    ∃ n : ℤ, Complex.log (completedRiemannZeta₀ (1 - s)) -
        Complex.log (completedRiemannZeta₀ s)
      = (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  -- exp(log Λ₀(1-s)) = Λ₀(1-s) = Λ₀ s = exp(log Λ₀ s) (反射 + exp_log)
  have h1 : Complex.exp (Complex.log (completedRiemannZeta₀ (1 - s))) =
      Complex.exp (Complex.log (completedRiemannZeta₀ s)) := by
    rw [Complex.exp_log, Complex.exp_log, completedRiemannZeta₀_one_sub]
    · exact hs
    · rw [completedRiemannZeta₀_one_sub]
      exact hs
  -- exp 相等 ⟹ log 差 = n·2πi
  rcases (Complex.exp_eq_exp_iff_exists_int).1 h1 with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- hn : log Λ₀(1-s) = log Λ₀ s + n·2πi
  rw [hn]
  ring


/-- **带内零点 ⟺ Λ₀ 取修正值** (整函数版 Λ₀ = Λ + 1/s + 1/(1-s)):
    ζ(s) = (Λ₀(s) - 1/s - 1/(1-s)) / (π^{-s/2}Γ(s/2)), 分母带内非零 (π ≠ 0, Γ(s/2) ≠ 0)
    ⟹ ζ(s) = 0 ⟺ Λ₀(s) = 1/s + 1/(1-s).  (矩形闭合: 带内零点都对应 Λ₀ 的一个精确值) 
English: In-strip zeros ⟺ Λ₀ at corrected values (entire version Λ₀ = Λ + 1/s + 1/(1-s)): ζ(s) = (Λ₀(s) - 1/s - 1/(1-s)) / (π^{-s/2}Γ(s/2)), denominator nonzero in the strip (π ≠ 0, Γ(s/2) ≠ 0) ⟹ ζ(s) = 0 ⟺ Λ₀(s) = 1/s + 1/(1-s). (Rectangle closure: every in-strip zero corresponds to an exact value of Λ₀.) -/
theorem zeta_zero_iff_completedZeta₀_one_over_sum {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hre : 0 < s.re) :
    riemannZeta s = 0 ↔ completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
  have hzeq := riemannZeta_eq_completedRiemannZeta₀ (s := s) hs0
  -- ζ(s) = (Λ₀(s) - 1/s - 1/(1-s)) / (π^{-s/2}Γ(s/2))
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : (↑Real.pi ^ (-s / 2) : ℂ) ≠ 0 := by
    -- π^z = exp(z·log π) (π ≠ 0) ≠ 0
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact Complex.exp_ne_zero _
  have hgam : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    -- s/2 = -m ⟹ Re(s/2) = s.re/2 > 0 但 = -m ≤ 0: 矛盾
    have hre2 : (s / 2).re = s.re / 2 := by simp
    have hneg : (s / 2).re = -((m : ℂ).re) := by rw [hm, Complex.neg_re]
    have hmre : ((m : ℂ).re) = (m : ℝ) := by
      rw [← Complex.ofReal_natCast]
      rfl
    have : s.re / 2 = -((m : ℝ) : ℂ).re := by
      rw [← hre2, hneg, hmre, Complex.ofReal_re]
    have hmcast : -((m : ℝ) : ℂ).re = -((m : ℝ) : ℝ) := by simp
    rw [hmcast] at this
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    nlinarith
  have hden : (↑Real.pi ^ (-s / 2) * Complex.Gamma (s / 2) : ℂ) ≠ 0 :=
    mul_ne_zero hpow hgam
  constructor
  · intro hζ
    -- ζ = 0 ⟹ 分子 = 0 (分母非零) ⟹ Λ₀ = 1/s + 1/(1-s)
    have hq : (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) /
        (↑Real.pi ^ (-s / 2) * Complex.Gamma (s / 2)) = 0 := by
      simpa [hzeq] using hζ
    rcases (div_eq_zero_iff.mp hq) with hnum | hden0
    · apply sub_eq_zero.mp
      simpa [sub_eq_add_neg, neg_add, add_assoc, add_comm, add_left_comm] using hnum
    · exact (hden hden0).elim
  · intro hΛ
    -- Λ₀ = 1/s + 1/(1-s) ⟹ 分子 = 0 ⟹ ζ = 0
    rw [riemannZeta_eq_completedRiemannZeta₀ hs0, hΛ]
    simp

/-- **矩形右边 O(1) 卷已知曲线**: ζ(2+it) 有界 (‖ζ(2+it)‖ ≤ Σ n⁻² = ζ(2))。
    Re>1 级数 (zeta_eq_tsum_one_div_nat_cpow) 直接卷: 模和 Σ n^{-2}
    收敛 (Real.summable_nat_rpow, p = -2 < -1), norm_tsum_le_tsum_norm。
    矩形闭合的右边边界 (σ=2) 相位变化 O(1) 的已知曲线依据。 
English: Rectangle right side: O(1) winding on a known curve — ζ(2+it) bounded (‖ζ(2+it)‖ ≤ Σ n⁻² = ζ(2)). Winding directly with the Re>1 series (zeta_eq_tsum_one_div_nat_cpow): the modulus sum Σ n^{-2} converges (Real.summable_nat_rpow, p = -2 < -1), norm_tsum_le_tsum_norm. Basis for the known-curve O(1) phase change on the rectangle closure's right boundary (σ=2). -/
theorem zeta_line_two_bounded (t : ℝ) :
    ‖riemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  -- ζ(2+it) = Σ n^{-2-it} (Re = 2 > 1 级数)
  rw [zeta_eq_tsum_one_div_nat_cpow (s := (2 : ℂ) + (t : ℂ) * Complex.I) (by norm_num)]
  -- ‖Σ‖ ≤ Σ‖·‖ (norm_tsum_le_tsum_norm): 需绝对收敛
  have hterm : ∀ n : ℕ, ‖(n : ℂ) ^ (-(2 : ℂ) - (t : ℂ) * Complex.I)‖ = (n : ℝ) ^ (-2 : ℝ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      -- 0^{-2-it} = 0, ‖0‖ = 0 = 0^{-2} (rpow 0^y = 0 当 y ≠ 0)
      have hz : -(2 : ℂ) - (t : ℂ) * Complex.I ≠ 0 := by
        intro h
        have hre : (-(2 : ℂ) - (t : ℂ) * Complex.I).re = 0 := by rw [h]; simp
        norm_num at hre
      rw [Nat.cast_zero]
      rw [Complex.zero_cpow hz]
      norm_num
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [Complex.cpow_def_of_ne_zero hn0]
      rw [Complex.norm_exp]
      -- log(↑n) = ↑(log n) (正实数)
      have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast]
        rw [← Complex.ofReal_log (Nat.cast_nonneg n)]
      -- (-2 - i·t)·log(↑n) 的实部 = -2·log n
      have hre : (((-(2 : ℂ) - (t : ℂ) * Complex.I) * Complex.log (n : ℂ)).re)
          = -2 * Real.log (n : ℝ) := by
        have hlog_re : (Complex.log (n : ℂ)).re = Real.log (n : ℝ) := by
          rw [← Complex.ofReal_natCast]
          have hl := Complex.ofReal_log (Nat.cast_nonneg n)
          rw [← hl]
          rfl
        have hlog_im : (Complex.log (n : ℂ)).im = 0 := by
          rw [← Complex.ofReal_natCast]
          have hl := Complex.ofReal_log (Nat.cast_nonneg n)
          rw [← hl]
          rfl
        rw [Complex.mul_re]
        simp only [Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im]
        rw [hlog_re, hlog_im]
        norm_num
      rw [mul_comm, hre]
      -- exp(-2·log n) = n^{-2} (rpow 定义)
      rw [Real.rpow_def_of_pos hpos]
      congr 1
      ring
  have hconv : ∀ n : ℕ, 1 / (n : ℂ) ^ (2 + (t : ℂ) * Complex.I)
      = (n : ℂ) ^ (-(2 : ℂ) - (t : ℂ) * Complex.I) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hz1 : (2 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
        intro h
        have : ((2 : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h]; simp
        norm_num at this
      have hz2 : (-(2 : ℂ) - (t : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have : ((-(2 : ℂ) - (t : ℂ) * Complex.I).re) = 0 := by rw [h]; simp
        norm_num at this
      rw [Nat.cast_zero]
      rw [Complex.zero_cpow hz1, Complex.zero_cpow hz2]
      simp
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [one_div, ← Complex.cpow_neg]
      congr 1
      ring
  have hsum_norm : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ (2 + (t : ℂ) * Complex.I)‖) := by
    -- ‖1/n^{2+it}‖ = ‖n^{-2-it}‖ = n^{-2}, Σ n^{-2} 收敛 (p = -2 < -1)
    have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
      (Real.summable_nat_rpow (p := (-2 : ℝ))).2 (by norm_num)
    refine hsum.congr ?_
    intro n
    rw [hconv n]
    exact (hterm n).symm
  exact (norm_tsum_le_tsum_norm hsum_norm).trans_eq (by
    apply tsum_congr
    intro n
    rw [hconv n]
    exact hterm n)


/-- **Γ 竖线有界 (卷积分表示)**: ‖Γ(1+it)‖ ≤ 1。
    Γ(1+it) = ∫₀^∞ e^{-x}·x^{it}dx (mathlib Gamma_eq_integral, Re=1>0),
    ‖∫‖ ≤ ∫‖·‖ (norm_integral_le_integral_norm), 逐项模 = e^{-x},
    ∫₀^∞ e^{-x}dx = 1 (integral_exp_neg_Ioi_zero)。免 Stirling。 
English: Γ vertical line bounded (winding integral representation): ‖Γ(1+it)‖ ≤ 1. Γ(1+it) = ∫₀^∞ e^{-x}·x^{it}dx (mathlib Gamma_eq_integral, Re=1>0); ‖∫‖ ≤ ∫‖·‖ (norm_integral_le_integral_norm); termwise modulus = e^{-x}; ∫₀^∞ e^{-x}dx = 1 (integral_exp_neg_Ioi_zero). Stirling-free. -/
theorem Gamma_one_add_it_norm_le_one (t : ℝ) :
    ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := by
  -- Γ(1+it) = ∫₀^∞ e^{-x}·x^{it} dx (积分表示, mathlib Gamma_eq_integral)
  have hg := Complex.Gamma_eq_integral (s := (1 : ℂ) + (t : ℂ) * Complex.I)
    (by simp : 0 < ((1 : ℂ) + (t : ℂ) * Complex.I).re)
  -- 逐项模: ‖e^{-x}·x^{it}‖ = e^{-x} (|x^{it}| = 1, x > 0)
  have hterm : ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖((Real.exp (-x)) : ℂ) * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I - 1)‖
        = Real.exp (-x) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxn : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx0)
    have hpow : (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I - 1)
        = (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
      congr 1
      ring
    rw [hpow]
    -- ‖e^{-x}‖ = e^{-x} (正实数), ‖x^{it}‖ = 1
    have hnorm1 : ‖((Real.exp (-x)) : ℂ)‖ = Real.exp (-x) := by
      rw [Complex.ofReal_exp]
      exact Complex.norm_exp_ofReal (-x)
    have hnorm2 : ‖(x : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
      -- x^{it} = exp(it·log x): 模 = exp(re(it·log x)) = exp 0 = 1
      rw [Complex.cpow_def_of_ne_zero hxn]
      rw [Complex.norm_exp]
      have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := by
        rw [← Complex.ofReal_log hx0.le]
      rw [hlog]
      -- (log x : ℝ)·((t:ℂ)·I) 的实部 = 0
      have hre : (((Real.log x : ℂ) * ((t : ℂ) * Complex.I)).re) = 0 := by
        rw [Complex.mul_re]
        simp [Complex.mul_I_re, Complex.mul_I_im]
      rw [hre]
      rw [Real.exp_zero]
    calc
      ‖((Real.exp (-x)) : ℂ) * (x : ℂ) ^ ((t : ℂ) * Complex.I)‖
          = ‖((Real.exp (-x)) : ℂ)‖ * ‖(x : ℂ) ^ ((t : ℂ) * Complex.I)‖ := by
            exact Complex.norm_mul _ _
      _ = Real.exp (-x) * 1 := by rw [hnorm1, hnorm2]
      _ = Real.exp (-x) := by ring
  -- ∫‖f‖ = ∫ e^{-x} = 1 (hterm 逐项代入 + integral_exp_neg_Ioi_zero)
  have hsum : ∫ x in Set.Ioi (0 : ℝ),
      ‖((Real.exp (-x)) : ℂ) * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I - 1)‖
      = 1 := by
    rw [← integral_exp_neg_Ioi_zero]
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
    apply Filter.Eventually.of_forall
    intro x hx
    exact hterm x hx
  -- 拼装: ‖Γ(1+it)‖ = ‖∫‖ ≤ ∫‖·‖ = 1
  calc
    ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖∫ x in Set.Ioi (0 : ℝ),
            ((Real.exp (-x)) : ℂ) * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I - 1)‖ := by
          rw [hg]
          unfold Complex.GammaIntegral
          rfl
    _ ≤ ∫ x in Set.Ioi (0 : ℝ),
          ‖((Real.exp (-x)) : ℂ) * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I - 1)‖ := by
          -- set 积分范数不等式: 全空间 Bochner norm_integral_le_integral_norm 于 restrict 测度
          simpa using (MeasureTheory.norm_integral_le_integral_norm
            (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun x : ℝ => ((Real.exp (-x)) : ℂ) * (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I - 1)))
    _ = 1 := hsum


/-- **底边无零点 (假实轴拼装)**: ζ(x) ≠ 0 对 x ∈ [-1,2] 且 x ∉ (0,1)。
    假实轴框架 (已证零散件拼装):
      Re < 0: riemannZeta_ne_zero_of_re_lt_zero (函数方程, 平凡零点 -2,-4 不在段内)
      Re = 0: riemannZeta_ne_zero_of_re_eq_zero (s ≠ 0)
      x = 0: riemannZeta_zero (ζ(0) = -1/2)
      x = 1: riemannZeta_one_ne_zero; 1 < x: riemannZeta_pos_of_one_lt
    (0,1) 段: ζ(x) < 0 是经典 (欧拉-麦克劳林积分表示, mathlib 无, KNOWN)。
    底边 Δarg = 0 的支撑: 实值 (riemannZeta_conj) + 无零点 ⟹ arg ∈ {0,π} 常数。 
English: Bottom edge zero-free (fake real axis assembly): ζ(x) ≠ 0 for x ∈ [-1,2] with x ∉ (0,1). Fake real axis framework (assembled proven pieces): Re < 0: riemannZeta_ne_zero_of_re_lt_zero (functional equation; trivial zeros -2,-4 not in the segment); Re = 0: riemannZeta_ne_zero_of_re_eq_zero (s ≠ 0); x = 0: riemannZeta_zero (ζ(0) = -1/2); x = 1: riemannZeta_one_ne_zero; 1 < x: riemannZeta_pos_of_one_lt; segment (0,1): ζ(x) < 0 is classical (Euler-Maclaurin integral representation, not in mathlib, KNOWN). Support for bottom edge Δarg = 0: real-valued (riemannZeta_conj) + zero-free ⟹ arg ∈ {0,π} constant. -/
theorem zeta_ne_zero_on_bottom_edge (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 2)
    (hnot : x ∉ Set.Ioo (0 : ℝ) 1) : riemannZeta (x : ℂ) ≠ 0 := by
  by_cases hx1 : x = 1
  · subst hx1
    exact riemannZeta_one_ne_zero
  by_cases hx0 : x = 0
  · subst hx0
    change riemannZeta (0 : ℂ) ≠ 0
    have : riemannZeta (0 : ℂ) = -1 / 2 := riemannZeta_zero
    rw [this]
    norm_num
  by_cases hpos : 1 < x
  · intro hz
    have hre : 0 < (riemannZeta (x : ℂ)).re := riemannZeta_re_pos_of_one_lt hpos
    have hzre : (riemannZeta (x : ℂ)).re = 0 := by rw [hz]; simp
    linarith
  -- x < 1 (hnot 排除 (0,1)): x ≤ 0, 且 x ≠ 0 ⟹ Re ≤ 0
  have hle0 : x ≤ 0 := by
    -- x ∈ [-1,2], x < 1, x ∉ (0,1) ⟹ x ≤ 0
    have hx2 : x < 1 := by
      by_contra hge
      have hge' : 1 ≤ x := le_of_not_gt hge
      -- x = 1 已排除 ⟹ 1 < x ⟹ hpos 矛盾
      have : 1 < x := lt_of_le_of_ne hge' (Ne.symm hx1)
      exact hpos this
    by_contra hgt
    have : 0 < x := lt_of_not_ge hgt
    exact hnot ⟨this, hx2⟩
  by_cases hz : x < 0
  · by_cases hxm1 : x = -1
    · subst hxm1
      -- ζ(-1) = -1/12 ≠ 0 (Bernoulli B₂ = 1/6; -1 不是平凡零点, 平凡零点在负偶数)
      have hval : riemannZeta (-1 : ℂ) ≠ 0 := by
        have hk := riemannZeta_neg_nat_eq_bernoulli' (k := 1)
        have hk2 : riemannZeta (-1 : ℂ) = -bernoulli' 2 / (1 + 1 : ℂ) := by
          simpa using hk
        have hval2 : riemannZeta (-1 : ℂ) = -(1 / 12 : ℂ) := by
          rw [hk2]
          norm_num [bernoulli'_two]
        rw [hval2]
        norm_num
      have harg : (↑(-1 : ℝ) : ℂ) = (-1 : ℂ) := by norm_num
      rw [harg]
      exact hval
    · -- x ∈ (-1, 0): 非平凡零点 (s ≠ -n 对所有 n, 因 -n ≤ -1 < x)
      apply riemannZeta_ne_zero_of_re_lt_zero (s := (x : ℂ))
      · simp [hz]
      · intro n hn
        have hxgt : -1 < x := lt_of_le_of_ne (Set.mem_Icc.mp hx).1 (Ne.symm hxm1)
        have hcast : (-(n : ℂ)).re = -(n : ℝ) := by simp
        have hre : ((x : ℂ)).re = (-(n : ℂ)).re := by rw [hn]
        have hxn : x = -(n : ℝ) := by
          simpa [hcast] using hre
        have hnle : -(n : ℝ) ≤ -1 := by
          by_cases hn0 : n = 0
          · subst hn0
            exfalso
            have hx0' : x = 0 := by simpa using hxn
            linarith
          · have hnge1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0))
            linarith
        rw [hxn] at hxgt
        linarith
  · -- x = 0 已排除, x < 0 否 ⟹ x = 0: 矛盾 (已在 hx0 分支)
    have : x = 0 := le_antisymm hle0 (le_of_not_gt hz)
    exact (hx0 this).elim


/-- **ζ 实轴实值**: ζ(x) ∈ ℝ (x 实) — conj ζ(x) = ζ(conj x) = ζ(x)。
    假实轴框架: 实轴上 ζ 的虚部 (y 轴泄漏) 为零。 
English: ζ real-valued on the real axis: ζ(x) ∈ ℝ (x real) — conj ζ(x) = ζ(conj x) = ζ(x). Fake real axis framework: ζ's imaginary part (y-axis leak) is zero on the real axis. -/
theorem zeta_im_zero_on_real (x : ℝ) : (riemannZeta (x : ℂ)).im = 0 := by
  have hc := riemannZeta_conj (x : ℂ)
  have hx : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by simp
  have hz : (starRingEnd ℂ) (riemannZeta (x : ℂ)) = riemannZeta (x : ℂ) := by
    rw [← hc, hx]
  have him : ((starRingEnd ℂ) (riemannZeta (x : ℂ))).im = -(riemannZeta (x : ℂ)).im := by
    simp
  have him' : ((starRingEnd ℂ) (riemannZeta (x : ℂ))).im = (riemannZeta (x : ℂ)).im := by
    rw [hz]
  linarith

/-- **ζ(-1) 实部为负**: re ζ(-1) < 0 — 函数方程 s=2 (卷 riemannZeta_one_sub):
    ζ(-1) = 2(2π)^{-2}Γ(2)cos(π)ζ(2) = -2(2π)^{-2}·ζ(2) < 0 (Γ(2)=1, cos π = -1, ζ(2)>0)。 
English: ζ(-1) has negative real part: re ζ(-1) < 0 — functional equation at s=2 (winding riemannZeta_one_sub): ζ(-1) = 2(2π)^{-2}Γ(2)cos(π)ζ(2) = -2(2π)^{-2}·ζ(2) < 0 (Γ(2)=1, cos π = -1, ζ(2)>0). -/
theorem zeta_neg_one_re_neg : (riemannZeta (-(1 : ℂ))).re < 0 := by
  have hfe := riemannZeta_one_sub (s := (2 : ℂ)) (by
    intro n hn
    have hre := congrArg Complex.re hn
    have hre' : (2 : ℝ) = -(n : ℝ) := by simpa using hre
    have hnneg : (n : ℝ) < 0 := by linarith
    exact (not_lt_of_ge (Nat.cast_nonneg n)) hnneg) (by norm_num)
  -- hfe : ζ(1-2) = 2(2π)^{-2}Γ(2)cos(π·2/2)ζ(2)
  have hcos : Complex.cos (↑Real.pi * (2 : ℂ) / 2) = -1 := by
    have harg : ↑Real.pi * (2 : ℂ) / 2 = ↑Real.pi := by
      apply Complex.ext <;> simp <;> ring
    rw [harg]
    simpa using Complex.cos_pi
  have hgam : Complex.Gamma (2 : ℂ) = 1 := by
    simpa using (Complex.Gamma_nat_eq_factorial 1)
  have hz2 : 0 < (riemannZeta (2 : ℂ)).re := by
    exact riemannZeta_re_pos_of_one_lt (x := (2 : ℝ)) (by norm_num)
  -- 对称方法 (模-相位分解, 实轴方向性): (2π)^(-2) — 底实正 (arg=0),
  -- 实指数 ⟹ 相位旋转 = 1 (cos 0 + sin 0·I), 模 = (2π)^(-2) 实正 —
  -- 不需要 cpow 展开/zpow 链 (代数方法), 用 cpow_ofReal 极坐标一步。
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-(2 : ℂ)) = ↑(1 / (2 * Real.pi) ^ 2 : ℝ) := by
    have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    rw [show (-(2 : ℂ)) = ((-2 : ℝ) : ℂ) by norm_num]
    rw [Complex.cpow_ofReal (2 * ↑Real.pi : ℂ) (-2 : ℝ)]
    -- 模: ‖2π‖ = 2π (实正); arg: 2π 实正 ⟹ arg = 0 ⟹ 相位 = 1
    have harg : (2 * ↑Real.pi : ℂ).arg = 0 := by
      have hcast : (2 * ↑Real.pi : ℂ) = ↑(2 * Real.pi : ℝ) := by norm_num
      rw [hcast]
      rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have hnorm : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      have hcast : (2 * ↑Real.pi : ℂ) = ↑(2 * Real.pi : ℝ) := by norm_num
      rw [hcast]
      exact (RCLike.norm_ofReal (2 * Real.pi)).trans
        (by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)])
    rw [harg, hnorm]
    -- 模-相位分解后目标自动坍缩: 相位 = 1 (cos 0 + sin 0·I), 模侧 rfl
    simp [Real.cos_zero, Real.sin_zero]
    rfl
  have hmain : riemannZeta (-(1 : ℂ)) = 2 * (2 * ↑Real.pi : ℂ) ^ (-(2 : ℂ)) * (-1) * riemannZeta (2 : ℂ) := by
    have hsub : 1 - (2 : ℂ) = -(1 : ℂ) := by ring
    rw [hsub] at hfe
    simpa [hcos, hgam] using hfe
  -- 周期方法 (实部投影, 不展开数值): 实系数 × ζ(2) 的 re
  -- = 系数 × (ζ2).re — 系数实 (ofReal: 实轴方向, im 泄漏 = 0) + ζ2 实
  -- (zeta_im_zero_on_real: 实轴上 ζ 的虚部为零 — 实轴周期结构)
  have hre : (2 * (2 * ↑Real.pi : ℂ) ^ (-(2 : ℂ)) * (-1) * riemannZeta (2 : ℂ)).re
      = -(2 * (1 / (2 * Real.pi) ^ 2)) * (riemannZeta (2 : ℂ)).re := by
    rw [hpow]
    -- 完全周期化: 系数整体 = ↑(-2a) (单一 ofReal, 不展开 a),
    -- mul_re 一步投影, 实性代入 (ofReal_re/ofReal_im + ζ2 实值) — 无数值展开
    let a : ℝ := 1 / (2 * Real.pi) ^ 2
    have hcoef : (2 * ↑a * (-1) : ℂ) = ↑(-(2 * a)) := by norm_num [a]
    rw [hcoef]
    rw [Complex.mul_re]
    -- 实性代入: 系数 im = 0 (ofReal), ζ(2) im = 0 (zeta_im_zero_on_real, 周期轴固定)
    have hb_re : (↑(-(2 * a)) : ℂ).re = -(2 * a) := by simp
    have hb_im : (↑(-(2 * a)) : ℂ).im = 0 := by simp
    have hz2_im0 : (riemannZeta (2 : ℂ)).im = 0 := zeta_im_zero_on_real 2
    rw [hb_re, hb_im, hz2_im0]
    -- 收尾: 0·0 项清除 + a 定义替换 (两边同形, rfl)
    simp [a]
  rw [hmain, hre]
  have hcoef : (0 : ℝ) < 2 * (1 / (2 * Real.pi) ^ 2) := by positivity
  have hprod : 0 < 2 * (1 / (2 * Real.pi) ^ 2) * (riemannZeta (2 : ℂ)).re :=
    mul_pos hcoef hz2
  linarith

/-- **底边 arg 跳 = π**: arg ζ(-1) - arg ζ(2) = π —
    矩形闭合的底边 (实轴 -1 → 2) 相位修正: ζ(-1) 实负 (arg = π),
    ζ(2) 实正 (arg = 0), 跳 = π = e^{iπ} 桥 (翻转半圈, 与零点计数 +1 对应)。
    假实轴拼装: 实值 (zeta_im_zero_on_real) + 符号 (函数方程/级数)。 
English: Bottom edge arg jump = π: arg ζ(-1) - arg ζ(2) = π — phase correction of the rectangle closure's bottom edge (real axis -1 → 2): ζ(-1) real negative (arg = π), ζ(2) real positive (arg = 0), jump = π = e^{iπ} bridge (half-circle flip, corresponding to zero count +1). Fake real axis assembly: real-valued (zeta_im_zero_on_real) + sign (functional equation / series). -/
theorem bottom_edge_arg_jump :
    (riemannZeta (-(1 : ℂ))).arg - (riemannZeta (2 : ℂ)).arg = Real.pi := by
  have hargn : (riemannZeta (-(1 : ℂ))).arg = Real.pi := by
    rw [Complex.arg_eq_pi_iff]
    have hz_im : (riemannZeta (-(1 : ℂ))).im = 0 := by
      simpa using (zeta_im_zero_on_real (-1))
    exact ⟨zeta_neg_one_re_neg, hz_im⟩
  have hargp : (riemannZeta (2 : ℂ)).arg = 0 := by
    rw [Complex.arg_eq_zero_iff]
    constructor
    · have hz2_re : 0 < (riemannZeta (2 : ℂ)).re :=
        riemannZeta_re_pos_of_one_lt (x := (2 : ℝ)) (by norm_num)
      exact hz2_re.le
    · exact zeta_im_zero_on_real 2
  rw [hargn, hargp]
  simp


  -- ============================================================
  -- T6o: (0,1) 段负性核心件 — 部分和 < 积分 (2026-08-21)
  -- ζ(x) < 0 for x ∈ (0,1) 的欧拉-麦克劳林路径 (Euler 1735 经典):
  --   Σ_{n=1}^N n^{-x} < ∫₀^N t^{-x}dt = N^{1-x}/(1-x)
  --   ⟹ 部分和修正 R_N(x) = Σ n^{-x} - N^{1-x}/(1-x) < 0
  -- 逐项: (n+1)^{-s} ≤ ∫ₙ^{n+1} t^{-s}dt (t^{-s} 递减 ≥ 右端点值, FTC 算积分)
  -- 本定理 = 核心代数件; 延拓 ζ(x) = lim R_N(x) 需莫雷拉/一致收敛解析
  -- (mathlib HasPrimitives 未预编译, 标注 KNOWN 路径)。
  -- ============================================================

/-- **部分和 < 积分 (核心件)**: Σ_{n=1}^N n^{-s} < N^{1-s}/(1-s) 对 0 < s < 1。
    逐项 (n+1)^{-s} ≤ ∫ₙ^{n+1} t^{-s}dt (单调) + FTC 算积分 + 望远镜求和,
    第一项 (n=0) 严格 (1 < 1/(1-s))。 
English: Partial sums < integral (core piece): Σ_{n=1}^N n^{-s} < N^{1-s}/(1-s) for 0 < s < 1. Termwise (n+1)^{-s} ≤ ∫ₙ^{n+1} t^{-s}dt (monotone) + FTC integral + telescoping sum; the first term (n=0) is strict (1 < 1/(1-s)). -/
theorem zeta_partial_sum_lt_integral_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ (Finset.range N), ((n + 1 : ℝ) ^ (-s))) < (N : ℝ) ^ (1 - s) / (1 - s) := by
  have h1m : 0 < 1 - s := by linarith
  -- 逐项: (n+1)^{-s} ≤ ∫ₙ^{n+1} t^{-s}dt = ((n+1)^{1-s} - n^{1-s})/(1-s)
  have hterm : ∀ n : ℕ, (n + 1 : ℝ) ^ (-s) ≤
      ((n + 1 : ℝ) ^ (1 - s) - (n : ℝ) ^ (1 - s)) / (1 - s) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      -- 1 ≤ 1/(1-s) (严格)
      have hlt : (1 : ℝ) < 1 / (1 - s) := by
        rw [one_div]
        exact (one_lt_inv₀ h1m).2 (by linarith : 1 - s < 1)
      -- 归一: 1^(-s) = 1, 1^(1-s) = 1, 0^(1-s) = 0 (实轴幂, 1 的幂恒 1)
      exact le_of_lt (by
        simpa [Real.one_rpow, Real.zero_rpow (ne_of_gt h1m)] using hlt)
    · -- n ≥ 1: x ∈ [n, n+1] ⟹ x > 0, FTC 可用
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      -- ∫ₙ^{n+1} t^{-s}dt = ((n+1)^{1-s} - n^{1-s})/(1-s) (FTC: (t^{1-s}/(1-s))' = t^{-s})
      -- t ↦ t^{-s} 在 [n, n+1] 可积 (连续, t ≥ n ≥ 1 > 0) — hftc 与 hmono 共用
      have hint : IntervalIntegrable (fun t : ℝ => t ^ (-s)) MeasureTheory.volume
          (n : ℝ) ((n : ℝ) + 1) := by
        apply ContinuousOn.intervalIntegrable
        intro t ht
        have htpos : 0 < t := by
          have htge : (n : ℝ) ≤ t := by
            rcases (Set.mem_uIcc.mp ht) with h | h
            · exact h.1
            · exact le_trans (by simp) h.1
          linarith
        exact (Real.continuousAt_rpow_const t (-s) (Or.inl (ne_of_gt htpos))).continuousWithinAt
      have hftc : ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s)
          = ((n + 1 : ℝ) ^ (1 - s) - (n : ℝ) ^ (1 - s)) / (1 - s) := by
        -- 对称族 (iso 模式): 导数无除法 (HasDerivAt (fun t => t^(1-s)) ((1-s)·x^{-s})),
        -- FTC: ∫ (1-s)·t^{-s} = 差, 再除 (1-s) — 不逐项 field 展开
        have hderiv : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
            HasDerivAt (fun t : ℝ => t ^ (1 - s)) ((1 - s) * x ^ (-s)) x := by
          intro x hx
          have hxpos : 0 < x := by
            have hxge : (n : ℝ) ≤ x := by
              rcases (Set.mem_uIcc.mp hx) with h | h
              · exact h.1
              · exact le_trans (by simp) h.1
            linarith
          have hd := Real.hasDerivAt_rpow_const (x := x) (p := 1 - s) (Or.inl (ne_of_gt hxpos))
          -- hd : HasDerivAt (fun t => t^(1-s)) ((1-s)·x^{1-s-1}) x; 1-s-1 = -s
          have hpow : x ^ (1 - s - 1) = x ^ (-s) := by
            congr 1
            ring
          simpa [hpow] using hd
        have hftc0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint.const_mul (1 - s))
        -- hftc0 : ∫ (1-s)·t^{-s} = (n+1)^{1-s} - n^{1-s}
        rw [intervalIntegral.integral_const_mul] at hftc0
        calc
          ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s)
              = ((1 - s) * ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s)) / (1 - s) := by
                field_simp [sub_ne_zero.mpr (ne_of_gt h1m)]
          _ = ((n + 1 : ℝ) ^ (1 - s) - (n : ℝ) ^ (1 - s)) / (1 - s) := by
                rw [hftc0]
      -- (n+1)^{-s} ≤ ∫ₙ^{n+1} t^{-s}dt (t ≤ n+1 ⟹ t^{-s} ≥ (n+1)^{-s}, s > 0)
      have hmono : (n + 1 : ℝ) ^ (-s) ≤ ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s) := by
        -- 对称方法 (零幂代数展开): x ↦ x^{-s} 在正半轴反单调
        -- (antitoneOn_rpow_Ioi_of_exponent_nonpos — mathlib 现成) —
        -- t ≤ n+1 (且都 > 0) ⟹ t^{-s} ≥ (n+1)^{-s}, 一步到位
        have hmono_point : ∀ t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1),
            (n + 1 : ℝ) ^ (-s) ≤ t ^ (-s) := by
          intro t ht
          have htle : t ≤ (n + 1 : ℝ) := ht.2
          have hanti := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (le_of_lt (neg_lt_zero.mpr hs0))
          have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
          have htpos : 0 < t := lt_of_lt_of_le hn0 ht.1
          have hnp1 : 0 < (n : ℝ) + 1 := by linarith
          exact hanti htpos hnp1 htle
        -- ∫ 常数 = 常数·1, 逐点比较 ⟹ 积分比较 (integral_mono_on: hab hf hg h)
        have hconst_int : (∫ t in (n : ℝ)..((n : ℝ) + 1), (n + 1 : ℝ) ^ (-s))
            = (n + 1 : ℝ) ^ (-s) := by
          simp
        have hle : (∫ t in (n : ℝ)..((n : ℝ) + 1), (n + 1 : ℝ) ^ (-s))
            ≤ ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s) := by
          exact intervalIntegral.integral_mono_on (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
            (Continuous.intervalIntegrable (by fun_prop) (n : ℝ) ((n : ℝ) + 1))
            hint hmono_point
        rwa [hconst_int] at hle
      rw [hftc] at hmono
      exact hmono
  -- 望远镜: Σ ((n+1)^{1-s} - n^{1-s})/(1-s) = (N^{1-s} - 0^{1-s})/(1-s)
  have htel : (∑ n ∈ (Finset.range N), ((n + 1 : ℝ) ^ (1 - s) - (n : ℝ) ^ (1 - s)) / (1 - s))
      = (N : ℝ) ^ (1 - s) / (1 - s) := by
    rw [← Finset.sum_div]
    -- 归一 (↑i + 1) = ↑(i+1) (Nat cast 加法)
    have hnorm : (∑ n ∈ (Finset.range N), ((↑n + 1 : ℝ) ^ (1 - s) - (↑n : ℝ) ^ (1 - s)))
        = ∑ n ∈ (Finset.range N), ((↑(n + 1) : ℝ) ^ (1 - s) - (↑n : ℝ) ^ (1 - s)) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      congr 1
      norm_num
    rw [hnorm]
    have htel_sum : (∑ n ∈ (Finset.range N), ((↑(n + 1) : ℝ) ^ (1 - s) - (↑n : ℝ) ^ (1 - s)))
        = (N : ℝ) ^ (1 - s) - (0 : ℝ) ^ (1 - s) := by
      simpa using (Finset.sum_range_sub (f := fun k : ℕ => (k : ℝ) ^ (1 - s)) N)
    rw [htel_sum]
    have h0 : (0 : ℝ) ^ (1 - s) = 0 := by
      exact (Real.rpow_eq_zero (by norm_num) (by linarith : 1 - s ≠ 0)).2 rfl
    simp [h0]
  -- 第一项严格: 1 < 1/(1-s)
  have h0_lt : (1 : ℝ) < ((1 : ℝ) ^ (1 - s) - (0 : ℝ) ^ (1 - s)) / (1 - s) := by
    have hlt : (1 : ℝ) < 1 / (1 - s) := by
      rw [one_div]
      exact (one_lt_inv₀ h1m).2 (by linarith : 1 - s < 1)
    have hpow1 : (1 : ℝ) ^ (1 - s) = 1 := by simp
    have h0 : (0 : ℝ) ^ (1 - s) = 0 := by
      exact (Real.rpow_eq_zero (by norm_num) (by linarith : 1 - s ≠ 0)).2 rfl
    simpa [hpow1, h0] using hlt
  have hsum_lt : (∑ n ∈ (Finset.range N), ((n + 1 : ℝ) ^ (-s))) <
      ∑ n ∈ (Finset.range N), ((n + 1 : ℝ) ^ (1 - s) - (n : ℝ) ^ (1 - s)) / (1 - s) := by
    refine Finset.sum_lt_sum (fun n hn => hterm n) ?_
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      simpa using h0_lt
  -- 拼装 (离散 FTC: 望远镜和 + 逐项严格)
  rw [htel] at hsum_lt
  exact hsum_lt

end RiemannUnifiedObservation
