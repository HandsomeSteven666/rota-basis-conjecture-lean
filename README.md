# Rota 基猜想（Rota's Basis Conjecture, RBC）—— 形式化框架与研究笔记

> **诚实定位（务必先读）**：本仓库目前**不是一项数学成果**，而是一个
> **形式化基础设施 + 调研笔记**。RBC 的 n=2 情形在数学上是**显然的已知结论**
> （直接由拟阵基交换性质 / 向量空间交换引理推出，可追溯到 Whitney 1935 的
> 拟阵公理），早已被人证明。本仓库用 Lean（mathlib）把它**机器验证**了一遍，
> 目的是搭好后续攻击（n=3、Alon–Tarsi 的 n=p±1、渐近下界等）可复用的形式化
> 地基，**并非声称证明了新东西**。
>
> 一般 n 的 RBC（向量空间版与拟阵版）**仍然开放（OPEN）**。

---

## 1. 仓库内容

| 路径 | 内容 |
|------|------|
| `lean/RotaBasis/Basic.lean` | Lean 形式化：**n=2 向量空间版的机器证明** + 可复用引理（`det2`、`isBasis`、横截基表述、`colinear_of_det2_eq_zero`、`swap01_bijective`、`disj` 四分支模式） |
| `lean/RotaBasis.lean` | 根模块（`import RotaBasis.Basic`） |
| `lean/lakefile.toml` | Lean 包配置（mathlib rev 固定为 `56a9a88447f391672d7aeea117da03b6f7016b0d`） |
| `Rota_Basis_Conjecture_调研与攻击路线.md` | 中文调研报告：精确表述 + 前人边界与核实引文 + 多路线攻击设计（A–F）+ 可复现说明 |
| `rota_bruteforce.py` | 小参数穷举验证脚本（n≤3 无反例的计算证据） |

> 原始 Lean 开发工程在 `D:/lean-env/lean-mathlib-demo/`（mathlib 已缓存）；
> 本仓库是其**发布快照**，`lean/` 子目录为自包含、可独立 `lake build` 的源码。

---

## 2. 构建与验证

```bash
cd lean
lake build RotaBasis
# 预期：Build completed successfully，零错误零警告
# 主定理：RotaBasis.Basic.rotaStatement_two : ∀ (K) [Field K], rotaStatement 2 K
```

计算验证（无需 GPU，纯 CPU）：

```bash
python rota_bruteforce.py
# n=2 (F2, F3) 与 n=3 (F2, 固定 B0=标准基完备遍历) 全部成立，无反例
```

---

## 3. 已知边界（摘要，详见报告）

- **n ≤ 3（所有拟阵类）**：已证明（Chan 1995 证 n=3）。
- **paving 拟阵**：已证明（Geelen–Humphries 2006）。
- **strongly base-orderable 拟阵**：已证明（Wild 1994）。
- **特征零域 n = p ± 1**（p 奇素数）：由 Alon–Tarsi 路线（Drisko 1997 / Glynn 2010）推出。
- **渐近下界**：当前最佳为 **(1 − o(1)) n**（Montgomery–Sauermann 2025），
  此前为 (1/2 − o(1)) n（Bucić–Kwan–Pokrovskiy–Sudakov 2020）。
- **一般 n（任意域）**：**开放**。

### 形式化现状（截至本仓库）
公开追踪（TheoremDB / ProofAtlas）显示 RBC 的 **Lean 形式化工作为 0**；
Cheung (2012) 的 n=4 是**穷举式计算机搜索**，非证明助手形式化。
本仓库的 n=2 是迄今可查的**第一个 RBC 片段的 Lean 形式化**——但仅是最平凡片段。

---

## 4. 下一步攻击路线（详见报告第 5 节）

优先级建议：

1. **路线 A：n=3 向量空间版**（延续 n=2 框架，边际成本最低）
2. **路线 E：Chow (2009) 三基约化**（把攻击面收窄到最小非平凡阻碍）
3. **路线 B：Alon–Tarsi 的 n=p±1 家族形式化**（覆盖已知最大家族）
4. 路线 D（特殊类）/ F（构造算法）作为并行补充

> 完成上述任一**非平凡**片段后，本仓库才算有实质内容，可正式发布 / 引用于
> Zenodo（DOI）或 arXiv note；通用引理亦可 PR 进 mathlib。

---

## 5. 引用与致谢

- Rota, G.-C. (1989，据 Huang–Rota 1994 记载)；Huang, R.; Rota, G.-C. (1994).
- Chan (1995); Cheung (2012); Geelen–Humphries (2006); Geelen–Webb (2007);
  Dong–Geelen (2018, arXiv:1709.00075); Bucić et al. (2020, arXiv:1810.07462);
  Drisko (1997); Glynn (2010); Wild (1994); Chow (2009); Montgomery–Sauermann (2025).
- 形式化基于 [Lean](https://lean-lang.org/) 与 [mathlib](https://github.com/leanprover-community/mathlib4)。
