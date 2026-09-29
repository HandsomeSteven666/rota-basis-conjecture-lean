#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Rota 基猜想 —— 小参数穷举验证 (computational route)

对有限域 F_q 上的小维数 n，穷举验证 Rota 基猜想 (向量空间版本):
  给定 n 个基 B_0,...,B_{n-1} (每个是 F_q^n 的一组基)，是否存在对每一行的
  一个置换，使得排成的 n×n 矩阵的每一列仍是 F_q^n 的基。

方法学严谨性说明
---------------
*   "列是基" 等价于 "该列 n 个向量线性无关" (n 维空间中 n 个无关向量即基)。
*   用高斯消元计算秩。
*   完备性: 由 GL(n,q) 同时作用在全部向量上保持线性无关性与猜想真值，
    可把第一个基 B_0 固定为标准基，再让其余基遍历全部基 —— 这样遍历与遍历
    所有 (B_0,...,B_{n-1}) 在 GL 轨道下等价，故对固定 B_0=标准基的穷举是
    *完全* 的 (不丢任何反例)。

注意: 这是对具体 (n, q) 的穷举证据，不是一般证明；一般猜想仍开放。
"""
import itertools
import time

def mod_inv(a, q):
    a %= q
    for x in range(1, q):
        if (a * x) % q == 1:
            return x
    raise ValueError(f"no inverse for {a} mod {q}")

def rank(mat_rows, q):
    """Return rank of a matrix given as a list of rows (each a list of ints mod q)."""
    m = len(mat_rows)
    if m == 0:
        return 0
    n = len(mat_rows[0])
    A = [row[:] for row in mat_rows]
    r = 0
    for col in range(n):
        pivot = None
        for i in range(r, m):
            if A[i][col] % q != 0:
                pivot = i
                break
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        inv = mod_inv(A[r][col], q)
        A[r] = [(x * inv) % q for x in A[r]]
        for i in range(m):
            if i != r and A[i][col] % q != 0:
                f = A[i][col]
                A[i] = [((A[i][j] - f * A[r][j]) % q) for j in range(n)]
        r += 1
        if r == m:
            break
    return r

def is_indep(cols, q):
    """cols: list of n vectors (each a tuple/list of length n). Independent iff rank == n."""
    n = len(cols)
    mat_rows = [list(c) for c in zip(*cols)]  # transpose: columns -> rows
    return rank(mat_rows, q) == n

def all_vectors(n, q):
    return [tuple(v) for v in itertools.product(range(q), repeat=n)]

def all_bases(n, q):
    vecs = all_vectors(n, q)
    out = []
    for cols in itertools.product(vecs, repeat=n):
        if is_indep(list(cols), q):
            out.append(list(cols))
    return out

def rota_holds(rows, q):
    """rows: list of n bases (each a list of n vectors). Return True if some
    choice of per-row permutations makes every column a basis."""
    n = len(rows)
    perms = list(itertools.permutations(range(n)))
    for chosen in itertools.product(perms, repeat=n):
        ok = True
        for j in range(n):
            col = [rows[i][chosen[i][j]] for i in range(n)]
            if not is_indep(col, q):
                ok = False
                break
        if ok:
            return True
    return False

def standard_basis(n):
    return [tuple(1 if i == j else 0 for i in range(n)) for j in range(n)]

def check(n, q, fix_first=True):
    bases = all_bases(n, q)
    print(f"  n={n}, q={q}: 基的个数 |GL({n},{q})| = {len(bases)}")
    if n >= 3 and fix_first:
        # Exploit GL-invariance: fix B_0 = standard basis.
        std = standard_basis(n)
        total = 0
        checked = 0
        t0 = time.time()
        for B2 in bases:
            for B3 in bases:
                total += 1
                checked += 1
                if not rota_holds([std, B2, B3], q):
                    return False, [std, B2, B3], total
        dt = time.time() - t0
        print(f"    固定 B_0=标准基, 遍历 {total} 个三元组, 用时 {dt:.1f}s -> 全部成立")
        return True, None, total
    else:
        total = 0
        t0 = time.time()
        for rows in itertools.product(bases, repeat=n):
            total += 1
            if not rota_holds(list(rows), q):
                return False, list(rows), total
        dt = time.time() - t0
        print(f"    遍历 {total} 个 n-元组, 用时 {dt:.1f}s -> 全部成立")
        return True, None, total

def main():
    print("=" * 60)
    print("Rota 基猜想 穷举验证 (向量空间版本)")
    print("=" * 60)
    results = []
    # n = 2 sanity (F_2, F_3)
    results.append(("n=2, F_2", check(2, 2, fix_first=False)))
    results.append(("n=2, F_3", check(2, 3, fix_first=False)))
    # n = 3 over F_2 (complete up to GL-invariance)
    results.append(("n=3, F_2 (fixed B0)", check(3, 2, fix_first=True)))

    print("\n汇总:")
    all_ok = True
    for name, (ok, cex, total) in results:
        status = "成立 (无反例)" if ok else "发现反例!"
        print(f"  {name}: {status}  (检查 {total} 例)")
        if not ok:
            all_ok = False
            print(f"    反例: {cex}")
    print("\n结论:", "所有检查的小参数实例均支持 Rota 基猜想 (与已知 n<=3 结果一致)."
          if all_ok else "出现反例，需进一步分析!")

if __name__ == "__main__":
    main()
