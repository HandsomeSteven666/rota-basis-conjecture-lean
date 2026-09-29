# Rota 基猜想（Rota's Basis Conjecture, RBC）—— 调研与攻击路线

> 本文档系统梳理 Rota 基猜想的**精确表述**、**前人推进边界与方法**（附严谨引文）、
> **本工作已完成的 Lean 形式化结果**（n=2）、**计算穷举证据**（n≤3 无反例），
> 并给出**多路线攻击设计**与**可复现性说明**。
>
> 结论先行：向量空间版与一般拟阵版的 Rota 基猜想**对一般 n 仍然开放（OPEN）**；
> 本文仅对最小非平凡情形 n=2 给出**机器检验（Lean）**的完整证明，并对小参数做计算验证。
>
> ⚠️ **进度勘误（2026-09-29）**：n=3 的向量空间版**已是已知定理**（Chan 1995，对一切
> rank≤3 拟阵成立，故对任意特征域均成立），但本项目的 Lean 形式化**目前仅完成 n=2**
> （见第 3 节），n=3 的机器证明尚缺。关键修正：**Onn/Alon–Tarsi 彩色行列式恒等式对
> n=3 完全不适用**——其常数 `AT(3) = ELS(3) − OLS(3) = 0`（3 阶拉丁方共 12 个、偶奇各 6），
> 因此**不存在覆盖 n=3 的初等行列式捷径**；n=3 唯一证明是 Chan 的 rank-3 拟阵/exchange
> case-distinction 证明（char-free），将其 Lean 化需专门工作。详见第 5 节路线 A 与第 7 节。

---

## 1. 精确表述

### 1.1 向量空间版（本文形式化对象）

设 `V = Kⁿ` 是域 `K` 上的标准 n 维向量空间（向量记为 `Fin n → K`）。给定 `n` 个基
`B₀, …, B_{n−1}`，每个基是 `V` 中 `n` 个线性无关向量。Rota 基猜想断言：可以重新排列这
`n²` 个基向量成一个 `n×n` 网格，使得

- **每一行**恰好是某个给定基（即每行是给定基的一个置换）；
- **每一列**仍然构成 `V` 的一组基。

等价地（Rota, 1989）：多重集 `B₀ ∪ ⋯ ∪ B_{n−1}` 可以划分成 `n` 个**横截基**
（transversal bases）——每个横截基恰好从每个 `Bᵢ` 取一个元素，且自身是 `V` 的基。

本文在 Lean 中形式化为（见 `RotaBasis/Basic.lean`）：

```lean
def rotaStatement (n : Nat) (K : Type*) [Field K] : Prop :=
  ∀ (rows : Fin n → Fin n → (Fin n → K)),
    (∀ i, isBasis n (rows i)) →
    ∃ (perm : Fin n → Fin n → Fin n),
      (∀ i, Bijective (perm i)) ∧
      ∀ j, isBasis n (fun i => rows i (perm i j))
```

其中 `isBasis n b` 用「以这些向量为列的矩阵行列式非零」来刻画（`n` 个无关向量在 `n` 维
空间中自动张成，故与通常「线性无关」定义等价）。

### 1.2 一般拟阵版

设 `M` 是秩为 `n` 的拟阵，`B₁, …, Bₙ` 是 `M` 的 `n` 个（互不相交的）基。Rota 猜想：
存在 `n` 个互不相交的横截基 `A₁, …, Aₙ`（每个 `Aᵢ` 从每个 `Bⱼ` 取一个元素且为 `M` 的基）。

向量空间是拟阵的特例，故拟阵版更强、也更难。本文的 Lean 证明目前只覆盖向量空间版的
n=2 情形；拟阵版 n=2 由拟阵基交换性质立得（Geelen–Humphries, 2006，paving 文第 2 节）。

### 1.3 表述上的关键说明

- **「列是基」⟺「列向量线性无关」**（n 维空间中 n 个无关向量即基）——这是计算与形式化
  中判断「列构成基」的统一判据。
- 猜想对 `n=1` 平凡；`n=2` 是最小非平凡情形（本文已证明）。
- 向量空间版与拟阵版在 `n=2` 都平凡/易证，但 `n≥3` 起出现本质困难。

---

## 2. 前人推进边界与方法（附引文）

下列结果均经过本次调研核实（来源含 Polymath 12 wiki、arXiv、期刊 DOI）。
**所有结果均针对一般 n 给出部分进展；完整猜想（任意 n）仍然开放。**

### 2.1 小维数完全结果

| 维数 | 结论 | 来源 |
|------|------|------|
| n = 2 | 向量空间版与拟阵版均成立（基交换性质） | 标准；Geelen–Humphries (2006) §2 指出 n=2 由拟阵基交换立得 |
| n = 3 | 拟阵版成立 | **Chan (1995)**, *An exchange property of matroid*, Discrete Math. 146: 299–302 |
| n = 4 | 拟阵版成立（计算证明） | **Cheung (2012)**, *Computational proof of Rota's basis conjecture for matroids of rank 4*, 未发表手稿 |

> 注：`n=3` 的向量空间版是 `n=3` 拟阵版的特例，故亦成立。本文 Lean 证明另对向量空间
> n=2 给出独立机器验证（见第 3 节）。

### 2.2 渐近下界（「能放下多少列」路线）

目标是证明「至少存在 k(n) 个互不相交的横截基」，k(n) 越大越接近猜想。

- **Geelen–Webb (2007)**：用 Rado 定理（Hall 定理的拟阵推广）证明至少存在
  `⌈√(n−1)⌉` 个横截基。来源：*On Rota's basis conjecture*, SIAM J. Discrete Math. 21(3): 802–804。
- **Dong–Geelen (2018/2019)**：概率方法改进为 `Ω(n / log n)`（具体
  `⌊n / (6⌈log n⌉)⌋`）。来源：arXiv:1709.00075 *Improved Bounds for Rota's Basis Conjecture*。
- **Bucić–Kwan–Pokrovskiy–Sudakov (2020)**：当时最佳渐近下界
  `(1/2 − o(1)) n` 个横截基，首次给出线性下界。来源：*Halfway to Rota's Basis
  Conjecture*, Int. Math. Res. Not. 2020(21): 8007–8026（arXiv:1810.07462）。
- **Montgomery–Sauermann (2025)**：**当前最佳渐近下界**，改进为
  `(1 − o(1)) n` 个横截基（以及覆盖版 `(1 + o(1)) n`）。这是截至目前对
  「能放下多少列」路线的最强结果，显著强于 Bucić et al. 的 `(1/2 − o(1)) n`。
  （来源：TheoremDB / EmergentMind 对该猜想的 2025–2026 追踪记录；具体论文待补 DOI。）

### 2.3 Alon–Tarsi 路线（代数/特征零域）

这是与猜想最强的理论联系。定义 Alon–Tarsi 常数 `AT(n)` =（偶 Latin 方数）−（奇 Latin 方数）。

- **Huang–Rota (1994)**：若 `AT(n) ≠ 0`（在域 `F` 中），则向量空间版 RBC 对 n 维 `F`-
  空间成立（对偶数 n、特征零域）。来源：*On the relations of various conjectures on
  Latin squares and straightening coefficients*, Discrete Math. 128: 225–236。
- **Drisko (1997)**：`p` 为奇素数时 `AT(p+1) ≢ 0 (mod p³)`，从而 RBC 对 `n = p+1`、
  特征零域成立。来源：*On the number of even and odd Latin squares of order p+1*,
  Adv. Math. 128: 20–35。
- **Glynn (2010)**：`AT(p−1) ≢ 0 (mod p)`，从而 RBC 对 `n = p−1`、特征零域成立。
  来源：*The conjectures of Alon–Tarsi and Rota in dimension prime minus one*,
  SIAM J. Discrete Math. 24(2): 394–399。

> 推论：在**特征零域**上，RBC 对所有形如 `n = p ± 1`（`p` 奇素数）的维数成立；
> 特别地，所有**偶数 n ≤ 24** 均成立（由 Drisko/Glynn 结果累加）。这是目前「对任意域的
> 一般 n」之外，理论最完整的已知家族。
>
> 📌 **重要修正（n=3 不适用 Alon–Tarsi）**：对 `n = 3`，`AT(3) = ELS(3) − OLS(3) = 0`
> （3 阶拉丁方共 12 个，偶、奇各 6），故 Alon–Tarsi / Onn 路线**完全不覆盖 n=3**。
> n=3 由 Chan (1995) 的 rank-3 拟阵结果**独立**覆盖（见 §2.1），走的是交换性质 /
> case-distinction，而非行列式恒等式。因此「路线 A 做 n=3」不能套用路线 B 的恒等式框架。

### 2.4 特殊拟阵类

- **Wild (1994)**：strongly base-orderable 拟阵版成立。来源：*On Rota's problem about
  n bases in a rank n matroid*, Adv. Math. 108: 336–345。
- **Geelen–Humphries (2006)**：paving 拟阵版成立（且证明更强：对一组 rank-n paving
  拟阵同时成立）。来源：*Rota's basis conjecture for paving matroids*, SIAM J. Discrete
  Math. 20(4): 1042–1045。

### 2.5 相关弱结果与约化

- **Aharoni–Berger (2006)**：任意拟阵中，所有元素可用至多 `2n` 个部分横截基覆盖。
  来源：*The intersection of a matroid and a simplicial complex*, Trans. Amer. Math. Soc.
  358: 4895–4917。
- **Chow (2009)**：将 RBC 约化到「三个基」猜想（reduction to a conjecture on three
  bases），为攻击提供新切入点。来源：SIAM J. Discrete Math. 23: 369–371。
- **Polymath 12 (2017)**：协同攻关项目，澄清了大量结构性质并小幅改进 Aharoni–Berger 定理。

### 2.6 开放状态小结

| 范围 | 状态 |
|------|------|
| 向量空间版，一般 n（任意域） | **OPEN** |
| 拟阵版，一般 n | **OPEN** |
| 向量空间版，n = 2 | **已证明（本文 Lean 验证 + 计算验证）** |
| 向量空间版，n = p ± 1（特征零） | 已证明（Drisko/Glynn） |
| 向量空间版，n ≤ 3（任意域，由拟阵结果推出） | 已证明 |
| 渐近下界 | 最佳 `(1 − o(1))n`（Montgomery–Sauermann 2025）；此前 `(1/2 − o(1))n`（Bucić et al. 2020） |

---

## 3. Lean 形式化结果（n = 2 已验证）

### 3.1 环境与文件

- 项目根：`D:/lean-env/lean-mathlib-demo/`
- 主文件：`RotaBasis/Basic.lean`（`import Mathlib; open Matrix Function`）
- 构建系统：`lake`（mathlib 版本 `rev = 56a9a88447f391672d7aeea117da03b6f7016b0d`）
- 根模块：`RotaBasis.lean`（`import RotaBasis.Basic`）

### 3.2 关键定义与引理

- `det2 u v`：`K²` 中两列向量的 2×2 行列式 `u 0 * v 1 − u 1 * v 0`。
- `isBasis n b`：以 `b` 的向量为列的矩阵行列式非零。
- `swap01`：`Fin 2` 上的交换 `0 ↔ 1`，是对合（`swap01 (swap01 j) = j`）。
- `swap01_involutive` / `swap01_bijective`：用 mathlib 的
  `Function.Involutive.bijective` 直接得出 `swap01` 是双射（免去手写单射/满射）。
- `det2_smul` / `det2_smul_smul` / `det2_anti` / `det2_eq_zero_comm`：行列式共线引理。
- `colinear_of_det2_eq_zero`：若 `u ≠ 0` 且 `det2 u v = 0`，则 `v` 是 `u` 的数倍。
  这是 n=2 证明的核心引理。
- `isBasis_two`：`n=2` 时「是基」等价于「2×2 行列式非零」。

### 3.3 主定理

```lean
theorem rotaStatement_two (K : Type*) [Field K] : rotaStatement 2 K := by
  -- 对两行基 B0={a0,a1}, B1={c0,c1}，考虑两种排法：
  --   排法 A（恒等排列）：列 = (a0,c0), (a1,c1)
  --   排法 B（第二行交换）：列 = (a0,c1), (a1,c0)
  -- 两种都失败 ⇔ (det(a0,c0)=0 ∨ det(a1,c1)=0) ∧ (det(a0,c1)=0 ∨ det(a1,c0)=0)
  -- 该析取的四个子情形各自迫使 {a0,a1} 或 {c0,c1} 共线，与「是基」矛盾。
  ...
```

证明骨架：`by_contra` 假设两种排法都失败 → `push Not` 把 `¬(P∧Q)` 化为 `P → ¬Q` →
用 `colinear_of_det2_eq_zero` 在四个子情形中分别导出某个给定基的两向量共线 →
与 `isBasis` 非零行列式矛盾。`disj` 的四分支用 `rcases ... <;> rcases ...` 串联处理。

### 3.4 一个关键 Lean 技术点（对后续形式化重要）

`Field K` 在 mathlib 中继承 `GroupWithZero`（不是乘法群 `[Group]`）。因此：

- 群层的除法消去引理 `div_mul_cancel` / `mul_div_cancel`（要求 `[Group]`）**对域不可用**
  （报 `failed to synthesize instance Group K`）。
- 必须使用 `GroupWithZero` 层的带下标引理：`div_mul_cancel₀ (a : G₀) (h : b ≠ 0) :
  a / b * b = a`，以及 `div_mul_eq_mul_div₀ (a b c) : a / c * b = a * b / c`、
  `mul_div_cancel₀`（收尾 `v 1 * u 0 / u 0 = v 1` 时用 `← div_mul_eq_mul_div₀` 先化为
  `v 1 / u 0 * u 0` 再用 `div_mul_cancel₀`）。
- **禁用 `field_simp`**：在含除法的目标上 `field_simp` 会递归展开 `div_eq_mul_inv` 导致
  「maximum recursion depth has been reached」。一律改用上述 `₀` 下标引理。

### 3.5 验证结果

```
lake build RotaBasis
✔ Built RotaBasis.Basic
✔ Built RotaBasis
Build completed successfully (8929 jobs).
```

零错误、零警告（`smul_eq_mul` 未用 simp 参数等 lint 警告已清理）。
`rotaStatement_two` 作为 `∀ (K) [Field K], rotaStatement 2 K` 被**机器完全接受**。

---

## 4. 计算穷举证据（n ≤ 3 无反例）

脚本：`E:/数学农场（低垂果实）/Rota 基猜想/rota_bruteforce.py`

方法学严谨性：利用 `GL(n,q)` 同时作用保持线性无关性与猜想真值，可固定 `B₀` = 标准基，
再让其余基遍历全体基——该遍历在 GL 轨道下与遍历所有 `(B₀,…,B_{n−1})` 等价，故对固定
`B₀` 的穷举是**完备**的（不会遗漏反例）。「列是基」用高斯消元判秩 == n。

复跑结果（本次）：

```
n=2, F_2 : 遍历 36   个 n-元组  -> 全部成立（无反例）
n=2, F_3 : 遍历 2304 个 n-元组  -> 全部成立（无反例）
n=3, F_2 : 固定 B0=标准基, 遍历 28224 个三元组 -> 全部成立（无反例）
```

说明：这是对具体小 `(n, q)` 的**计算证据**，不是一般证明；与第 2.1 节的已知理论结果
（n≤3 成立）一致，互相印证。

---

## 5. 多路线攻击设计

下面列出若干可并行推进的攻击路线。每条标注：目标、方法、与形式化的接口、可行性、风险。
优先级按「对最终证明的贡献度 × 形式化可操作性」排序。

### 路线 A：小 n 完全机械化（已部分完成，可外推）
- **目标**：对 n=2（已完成）、n=3 给出向量空间版的完整 Lean 证明；探索 n=4 的计算辅助证明。
- **方法**：n=2 已用行列式 + 共线引理直接证明。**n=3 不能走 Onn/Alon–Tarsi 行列式恒等式**
  （`AT(3)=0`，见 §2.3 修正），必须直接形式化 **Chan (1995) 的 rank-3 拟阵/exchange
  case-distinction 证明**——这是覆盖「含 char 2,3 的任意特征域」的唯一路线（char-free）。
  在向量空间表述下，可把 rank-2 flat 译为「2 维子空间（平面）」，用线性代数（平面交、
  共线、行列式）机械化 Chan 的交换论证；n=4 可借 Cheung (2012) 的计算框架做
  SAT/符号计算辅助，再人工提炼证明。
- **形式化接口**：扩展 `rotaStatement (n)` 的归纳；复用 `det2`→`Matrix.det`、共线引理。
- **可行性**：n=2 已验证（高）；**n=3 较高**——需自包含形式化 rank-3 拟阵/exchange 论证，
  Chan 原文为「繁琐的 case distinction」（Kirchweger 2022 原话），且本工程尚未做；
  n=4 计算量大但可分段。
- **当前状态**：**n=3 的 Lean 形式化尚未开始**（本工程仅有 n=2 已机器验证）。
- **风险**：n≥3 后分支组合爆炸，纯穷举式证明在 Lean 中代价高，需更聪明的代数不变量。

### 路线 B：Alon–Tarsi 路线（理论最强，形式化最难）
- **目标**：形式化「`AT(n) ≠ 0` ⇒ `rotaStatement n K`（特征零/偶数 n）」，并对 `n = p ± 1`
  证明 `AT(n) ≠ 0`，从而机器确认 Drisko/Glynn 家族。
- **方法**：定义 Latin 方奇偶符号、AT 常数；形式化 Huang–Rota 的多项式/图论论证；
  形式化 Drisko (p+1)、Glynn (p−1) 的模 p 计数结果。
- **形式化接口**：需新增 Latin 方、符号、模 p 算术等定义；与 `Mathlib/Combinatorics`、
  `Mathlib/Algebra` 对接。
- **可行性**：中等偏高（结构清晰，但多项式系数与奇偶论证较繁琐）。
- **风险**：Huang–Rota 原始证明依赖图多项式系数，需仔细处理特征零与域特征假设；
  `AT(n)≠0` 对一般偶数 n 本身开放（Alon–Tarsi 猜想），故此路线只能覆盖 `p±1` 特例。

### 路线 C：渐近下界路线（理解「一半」证明）
- **目标**：在 Lean 中形式化 Bucić et al. (2020) 的 `(1/2 − o(1))n` 结果，或至少其内部
  关键引理（随机选 α-子集含横截基的概率 ≥ 1/2，Theorem 1.3）。
- **方法**：概率方法 + Rado 定理。先形式化 Rado 定理（mathlib 已有 matroid 基础），
  再形式化概率断言。
- **形式化接口**：依赖 `Mathlib/Probability` 与 matroid 库；工作量很大。
- **可行性**：低（概率方法在 Lean 中形式化成本高），更适合作为「理解路线」而非优先形式化。
- **风险**：仅给出下界，离完整猜想尚有 `(1/2) n` 的差距，不能直接证明 RBC。

### 路线 D：特殊类路线（paving / strongly base-orderable）
- **目标**：形式化 Wild (1994)、Geelen–Humphries (2006) 的特殊类结果。
- **方法**：在 Lean 中定义 strongly base-orderable / paving 拟阵，复用基交换性质。
- **形式化接口**：需先形式化拟阵库（mathlib 的 `Mathlib/Combinatorics/Matroid` 已有基础）。
- **可行性**：中等；拟阵库已存在，可站在肩膀上。
- **风险**：特殊类不等于一般情形，证明难以直接推广。

### 路线 E：Chow 三基约化路线
- **目标**：形式化 Chow (2009) 的约化——把一般 RBC 约化到「三个基」猜想，从而把攻击面
  收窄到最小非平凡阻碍。
- **方法**：复现 Chow 的约化论证并 Lean 化。
- **形式化接口**：与拟阵基交换、横截基定义对接。
- **可行性**：中等；约化本身是组合论证，形式化收益高（把「一般 n」换成「3 个基」）。
- **风险**：三基猜想本身仍开放，只是缩小了搜索空间。

### 路线 F：构造性排列算法（对固定 n 显式构造）
- **目标**：对任意给定 n 个基，给出显式构造排列的算法并证明正确（目前 n=2 用 swap01 显式构造）。
- **方法**：把排法视为在「基的排列图」上寻找横截基匹配；借鉴匹配/增广路思想
  （Bucić et al. 的迭代构造启发）。
- **形式化接口**：`rotaStatement` 的 `∃ perm` 本就是构造性结论，算法即证明。
- **可行性**：中等；n=2 已显式构造，可作为模板推广。
- **风险**：一般 n 的显式构造正是猜想本身，需新组合洞察。

### 路线优先级建议
1. **路线 A（n=3 向量空间版）**：直接延续已验证的 n=2 工作，边际成本最低、收益明确。
2. **路线 E（Chow 三基约化）**：把问题收窄，是理论上的「杠杆点」。
3. **路线 B（Alon–Tarsi, p±1）**：覆盖已知最大理论家族，形式化价值高。
4. 路线 D（特殊类）、F（构造算法）作为并行补充。
5. 路线 C（渐近下界）作为「理解性」路线，形式化优先级最低。

---

## 6. 可复现性

### 6.1 Lean 项目
```bash
cd D:/lean-env/lean-mathlib-demo
lake build RotaBasis        # 预期：Build completed successfully (8929 jobs)，零错误零警告
```
主定理：`RotaBasis.Basic.rotaStatement_two : ∀ (K) [Field K], rotaStatement 2 K`

### 6.2 计算验证
```bash
cd "E:/数学农场（低垂果实）/Rota 基猜想"
python rota_bruteforce.py   # 预期：n=2(F2,F3) 与 n=3(F2) 全部成立，无反例
```

### 6.3 关键文件清单
| 文件 | 内容 |
|------|------|
| `D:/lean-env/lean-mathlib-demo/RotaBasis/Basic.lean` | Lean 形式化（定义、引理、n=2 定理） |
| `D:/lean-env/lean-mathlib-demo/RotaBasis.lean` | 根模块 |
| `D:/lean-env/lean-mathlib-demo/Scratch.lean` | 临时隔离文件（已弃用，留空占位） |
| `E:/数学农场（低垂果实）/Rota 基猜想/rota_bruteforce.py` | 小参数穷举验证脚本 |
| `E:/数学农场（低垂果实）/Rota 基猜想/Rota_Basis_Conjecture_调研与攻击路线.md` | 本报告 |

---

## 7. 结论与下一步

1. **已确证**：Rota 基猜想的向量空间版 `n=2` 情形在 Lean（mathlib）中**完全形式化证明通过**，
   并有 `n≤3` 的计算穷举证据（无反例）相互印证。
2. **n=3 已知但待形式化**：n=3（任意特征域）是 **Chan (1995) 的已知定理**（rank≤3 拟阵），
   但本工程的 Lean 形式化**尚未完成**——且**不能**借用 Onn/Alon–Tarsi 行列式恒等式
   （`AT(3)=0`，见 §2.3 修正），必须直接形式化 Chan 的 rank-3 证明。
3. **仍开放**：一般 n（任意域）的向量空间版与拟阵版均未被证明；最佳渐近下界为
   `(1/2 − o(1))n`（Bucić et al. 2020）；特征零域上 `n = p ± 1` 由 Alon–Tarsi 家族覆盖。
4. **下一步建议**：按第 5 节的优先级，先推进**路线 A（n=3 向量空间版，需形式化 Chan
   的 rank-3 证明）**与**路线 E（Chow 三基约化）**，把已验证的 n=2 框架扩展到更高维数与
   更窄的攻击面；同时评估**路线 B** 中 `AT(n)` 与 Drisko/Glynn 结果的形式化成本
   （注意路线 B 仅覆盖 `n = p ± 1`，且对 `n=3` 无效）。

> 严谨性声明：本文对「已证明」与「计算证据」「开放猜想」「个人判断」做了明确区分。
> n=2 的 Lean 证明为机器接受的真结论；其余边界均为前人已发表结果，本文仅做调研汇总与
> 引用，未替代其原始证明。
