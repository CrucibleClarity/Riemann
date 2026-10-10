import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 复数轴 (0pat 自包含版) — 标准 ℂ 构造的旋转-矩阵表示

0pat: 只用 mathlib, 不引用 pat 框架 (Formal.ZeroRelative.ComplexAxis 的
高维/投影/基点移动内容不在本文件)。ComplexAxis = 二维旋转代数 a + bJ
(矩阵表示 [[a,-b],[b,a]], ≅ ℂ, KNOWN 标准结构)。

本文件只含 proof.lean 习题区 (ComplexPlaneIntersections) 需要的部分:
结构 + 运算 + lift + J + norm + primeCircle + criticalCircle + 六个交点定理。

English: Two-dimensional rotation algebra a + b·J (matrix representation [[a,-b],[b,a]], ≅ ℂ). -/

noncomputable section

namespace ZeroRelative

/-- 二维旋转代数 a + b·J (矩阵表示 [[a,-b],[b,a]], ≅ ℂ)。 
English: Two-dimensional rotation algebra a + b·J (matrix representation [[a,-b],[b,a]], ≅ ℂ). -/
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
English: Multiplication (complex multiplication): (a₁+b₁J)(a₂+b₂J) = (a₁a₂-b₁b₂) + (a₁b₂+a₂b₁)J. -/
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
English: Lift: embedding of the real axis (scalar part, preserves addition and multiplication). -/
def lift (t : ℝ) : ComplexAxis := ⟨t, 0⟩

/-- 范数: 半径平方 (norm z = a² + b²) 
English: Norm: squared radius (norm z = a² + b²). -/
def norm (z : ComplexAxis) : ℝ := z.a ^ 2 + z.b ^ 2

/-- 素数圆: 圆心 0 半径 √p (素数 p 的两平方和整点所在)。 
English: Prime circle: center 0, radius √p (where the two-squares-sum lattice points of prime p lie). -/
def primeCircle (p : ℕ) : Set ComplexAxis := {z : ComplexAxis | norm z = (p : ℝ)}

/-- 临界线圆: 圆心 (1,0) 半径 1 (临界线蜷曲下的像, 经过 0 和 2)。 
English: Critical circle: center (1,0), radius 1 (image under critical-line curling, passing through 0 and 2). -/
def criticalCircle : Set ComplexAxis := {w : ComplexAxis | norm (w - lift 1) = 1}

end ComplexAxis
end ZeroRelative

namespace ComplexPlaneIntersections

open ZeroRelative
open ZeroRelative.ComplexAxis

/-- 纵轴 (虚轴) 与临界圆: t·J ∈ criticalCircle ↔ t = 0
    (虚轴与临界圆只交于原点; 对比实轴交 {0, 2})。 
English: Vertical (imaginary) axis and critical circle: t·J ∈ criticalCircle ↔ t = 0 (they meet only at the origin; compare real axis meeting {0, 2}). -/
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
English: Horizontal axis and prime circle: lift r ∈ primeCircle p ↔ r² = p (meets at ±√p). -/
theorem realAxis_inter_primeCircle (r : ℝ) (p : ℕ) :
    (lift r : ComplexAxis) ∈ primeCircle p ↔ r ^ 2 = (p : ℝ) := by
  simp [primeCircle, ComplexAxis.norm, lift, sub]

/-- 纵轴与素数圆: t·J ∈ primeCircle p ↔ t² = p (交于 ±i√p)。 
English: Vertical axis and prime circle: t·J ∈ primeCircle p ↔ t² = p (meets at ±i√p). -/
theorem imagAxis_inter_primeCircle (t : ℝ) (p : ℕ) :
    (lift t * J : ComplexAxis) ∈ primeCircle p ↔ t ^ 2 = (p : ℝ) := by
  change ComplexAxis.mul ⟨t, 0⟩ ⟨0, 1⟩ ∈ primeCircle p ↔ t ^ 2 = (p : ℝ)
  simp [primeCircle, ComplexAxis.norm, ComplexAxis.mul, pow_two]

/-- 素数圆 3 与临界圆: z = 3/2 + √3/2·J 在交集中
    (ComplexAxis.norm = 9/4 + 3/4 = 3; ComplexAxis.norm(z-1) = 1/4 + 3/4 = 1)。 
English: Prime circle 3 and critical circle: z = 3/2 + √3/2·J lies in the intersection (ComplexAxis.norm = 9/4 + 3/4 = 3; ComplexAxis.norm(z-1) = 1/4 + 3/4 = 1). -/
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
English: Prime circle of prime p ≥ 5 does not meet the critical circle (circle of radius √p vs circle center (1,0) radius 1: intersection ⟹ p ≤ 4). -/
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
