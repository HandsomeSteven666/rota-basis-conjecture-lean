import Mathlib
set_option linter.unnecessarySeqFocus false

/-!
# Rota's Basis Conjecture — formalization (vector-space version)

We formalize the **vector-space version** of Rota's basis conjecture over an
arbitrary field `K` and dimension `n`, and we prove the non-trivial `n = 2`
case constructively.

The general `n` remains open.  **Status (2026-09-29):** `n = 2` is formally
proven below.  `n = 3` is a known theorem (Chan 1995, all rank-≤3 matroids, hence
every field) but is **not** yet formalized in this file.  Note: the Onn/Alon–Tarsi
colored-determinant identity does **not** apply to `n = 3` (its constant
`AT(3) = ELS(3) − OLS(3) = 0`), so no elementary determinant shortcut exists for
`n = 3`; the only proof is Chan's rank-3 matroid/exchange case-distinction.

The `n = 3` case is scaffolded in `RotaBasis.Three` following Geelen–Humphries
(2006), *Rota's Basis Conjecture for Paving Matroids*, Theorem 2.1 (the paving
subclass; the general vector-space case reduces to it via Chan's "relax lines"
technique).  As of 2026-09-29 `RotaBasis.Three` compiles but is a `sorry`
skeleton: the explicit 9-point model, `paving`, `transversal`, `independent`
and the proven `vec_injective_of_paving` are in place, while the case-analysis
lemmas (`sub_2_1_1`, `sub_2_1_2`, `sub_2_1_3`, …) and the prime `rotaStatement_three`
remain unproven.

## Statement

Let `V = Kⁿ` be the standard `n`-dimensional vector space over a field `K`.
Given `n` bases `B₀,…,Bₙ₋₁` of `V`, the conjecture asserts that one can
rearrange the `n²` basis elements into an `n × n` grid whose rows are exactly
the given bases (each row a permutation of one `Bᵢ`) and whose columns are
again bases of `V`.

Equivalently (Rota, 1989): the multiset `B₀ ∪ ⋯ ∪ Bₙ₋₁` can be partitioned
into `n` **transversal bases** — `n` bases each containing exactly one element
from each `Bᵢ`.

The general statement `∀ (K) [Field K], rotaStatement n K` is **open**.  This
file verifies the smallest non-vacuous case `n = 2`.  See the accompanying
report `Rota_Basis_Conjecture_调研与攻击路线.md` for the full survey of prior
work and attack routes.
-/

open Matrix Function

/-! We identify `Kⁿ` with `Fin n → K` (functions from `Fin n` to `K`). This is a
plain function type, so application `v i` and the `Module K` instance are always
available without any unfolding steps. -/

/-- The 2×2 determinant of two column vectors `u, v ∈ K²` (written as functions
`Fin 2 → K`). -/
def det2 {K : Type*} [Field K] (u v : Fin 2 → K) : K := u 0 * v 1 - u 1 * v 0

/-- Whether `n` vectors in `Kⁿ` form a basis, characterized by a non-zero
determinant of the matrix whose columns are those vectors.  (Over `Kⁿ` this is
equivalent to the usual linear-independence notion, since `n` independent
vectors in an `n`-dimensional space automatically span.) -/
def isBasis {K : Type*} [Field K] (n : Nat) (b : Fin n → (Fin n → K)) : Prop :=
  Matrix.det (Matrix.of fun i j => b j i) ≠ 0

/-- Rota's basis conjecture for dimension `n` over the field `K`: every
`n`-tuple of bases can be permuted row-by-row so that every column is again a
basis. -/
def rotaStatement (n : Nat) (K : Type*) [Field K] : Prop :=
  ∀ (rows : Fin n → Fin n → (Fin n → K)),
    (∀ i, isBasis n (rows i)) →
    ∃ (perm : Fin n → Fin n → Fin n),
      (∀ i, Bijective (perm i)) ∧
      ∀ j, isBasis n (fun i => rows i (perm i j))

/-- The swap of the two columns on `Fin 2`: `0 ↦ 1`, `1 ↦ 0`. It is its own
inverse, hence bijective. -/
def swap01 : Fin 2 → Fin 2 := fun j => if j = 0 then 1 else 0

/-- `swap01` is its own inverse (`swap01 (swap01 j) = j`), hence a bijection on
`Fin 2`.  We use the mathlib lemma `Function.Involutive.bijective`. -/
lemma swap01_involutive : Involutive swap01 := by intro j; fin_cases j <;> simp [swap01]
lemma swap01_bijective : Bijective swap01 := Involutive.bijective swap01_involutive

section det2_lemmas

/-- If `v` is a scalar multiple of `u`, then `det2 u v = 0`. -/
lemma det2_smul {K : Type*} [Field K] (u : Fin 2 → K) (a : K) : det2 u (a • u) = 0 := by
  simp [det2, smul_eq_mul]
  ring

/-- If both `u` and `v` are scalar multiples of the same vector `w`, then
`det2 u v = 0`. -/
lemma det2_smul_smul {K : Type*} [Field K] (a b : K) (w : Fin 2 → K) : det2 (a • w) (b • w) = 0 := by
  simp [det2, smul_eq_mul]
  ring

/-- Antisymmetry up to sign: `det2 u v = -det2 v u`. -/
lemma det2_anti {K : Type*} [Field K] (u v : Fin 2 → K) : det2 u v = -det2 v u := by simp [det2]; ring

/-- Collinearity is symmetric: `det2 u v = 0` implies `det2 v u = 0`. -/
lemma det2_eq_zero_comm {K : Type*} [Field K] {u v : Fin 2 → K} (h : det2 u v = 0) : det2 v u = 0 := by
  rw [det2_anti] at h
  exact neg_eq_zero.mp h

/-- Colinearity criterion: for `u ≠ 0`, `det2 u v = 0` implies `v` is a scalar
multiple of `u`. This is the direction needed for the `n = 2` proof. -/
lemma colinear_of_det2_eq_zero {K : Type*} [Field K] {u v : Fin 2 → K}
    (hu : u ≠ 0) (h : det2 u v = 0) :
    ∃ (c : K), v = c • u := by
  by_cases hu0 : u 0 = 0
  · -- `u 0 = 0`, so `u 1 ≠ 0` (else `u = 0`), and `h` forces `v 0 = 0`.
    have hu1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      ext i <;> fin_cases i <;> simp [hu0, h1]
    have v0_eq : v 0 = 0 := by
      rw [det2, hu0] at h
      simp at h
      exact Or.resolve_left h hu1
    -- Choose `c = v 1 / u 1`.  A `Field K` is *not* a multiplicative group, so the
    -- `Group`-layer `div_mul_cancel` is unavailable; we use the `GroupWithZero`
    -- cancellation lemma `div_mul_cancel₀` instead.
    have hc0 : v 0 = (v 1 / u 1) * u 0 := by simp [hu0, v0_eq]
    have hc1 : v 1 = (v 1 / u 1) * u 1 := by rw [div_mul_cancel₀ (v 1) hu1]
    use (v 1 / u 1)
    ext i <;> fin_cases i
    · simpa [smul_eq_mul] using hc0
    · simpa [smul_eq_mul] using hc1
  · -- `u 0 ≠ 0`; choose `c = v 0 / u 0`.
    have hc0 : v 0 = (v 0 / u 0) * u 0 := by rw [div_mul_cancel₀ (v 0) hu0]
    have hc1 : v 1 = (v 0 / u 0) * u 1 := by
      rw [div_mul_eq_mul_div₀ (v 0) (u 1) (u 0), mul_comm (v 0) (u 1),
        ← sub_eq_zero.mp h, mul_comm (u 0) (v 1), ← div_mul_eq_mul_div₀ (v 1) (u 0) (u 0),
        div_mul_cancel₀ (v 1) hu0]
    use (v 0 / u 0)
    ext i <;> fin_cases i
    · simpa [smul_eq_mul] using hc0
    · simpa [smul_eq_mul] using hc1

end det2_lemmas

/-- For `n = 2`, a pair of vectors is a basis iff its 2×2 determinant is
non-zero. -/
lemma isBasis_two {K : Type*} [Field K] (b : Fin 2 → (Fin 2 → K)) :
    isBasis 2 b ↔ det2 (b 0) (b 1) ≠ 0 := by
  rw [isBasis, Matrix.det_fin_two]
  simp only [Matrix.of_apply, det2]
  rw [mul_comm (b 1 0) (b 0 1)]

/--
**Rota's basis conjecture holds for `n = 2` over every field `K`.**

Given two bases `{a₀, a₁}` and `{c₀, c₁}` of `K²`, at least one of the two
natural arrangements places independent vectors in both columns.

Proof idea: the two arrangements fail exactly when
`(det(a₀,c₀)=0 ∨ det(a₁,c₁)=0) ∧ (det(a₀,c₁)=0 ∨ det(a₁,c₀)=0)`.
Each of the four resulting subcases forces either `{a₀,a₁}` or `{c₀,c₁}` to be
collinear, contradicting that they are bases.
-/
theorem rotaStatement_two (K : Type*) [Field K] : rotaStatement 2 K := by
  intro rows hrows
  have ha : det2 (rows 0 0) (rows 0 1) ≠ 0 := (isBasis_two (rows 0)).mp (hrows 0)
  have hc : det2 (rows 1 0) (rows 1 1) ≠ 0 := (isBasis_two (rows 1)).mp (hrows 1)
  -- The two arrangements succeed iff (d00≠0 ∧ d11≠0) or (d01≠0 ∧ d10≠0).
  have disj :
      (det2 (rows 0 0) (rows 1 0) ≠ 0 ∧ det2 (rows 0 1) (rows 1 1) ≠ 0)
      ∨ (det2 (rows 0 0) (rows 1 1) ≠ 0 ∧ det2 (rows 0 1) (rows 1 0) ≠ 0) := by
    by_contra h
    push Not at h
    rcases h with ⟨hA, hB⟩
    -- `push Not` rewrites `¬(P ∧ Q)` as `P → ¬Q`; convert back to the disjunction
    -- `A = 0 ∨ C = 0` (and similarly for `hB`) by a short contrapositive argument.
    have hA' : det2 (rows 0 0) (rows 1 0) = 0 ∨ det2 (rows 0 1) (rows 1 1) = 0 := by
      by_contra h'
      push Not at h'
      rcases h' with ⟨ha', hc'⟩
      exact hc' (hA ha')
    have hB' : det2 (rows 0 0) (rows 1 1) = 0 ∨ det2 (rows 0 1) (rows 1 0) = 0 := by
      by_contra h'
      push Not at h'
      rcases h' with ⟨hb', hd'⟩
      exact hd' (hB hb')
    rcases hA' with hd00 | hd11 <;> rcases hB' with hd01 | hd10
    · -- det(a₀,c₀)=0 and det(a₀,c₁)=0  ⇒  c₀ ∥ c₁  ⇒  contradicts `hc`.
      have a0nz : rows 0 0 ≠ 0 := by
        intro h0; apply ha; rw [h0, det2]; simp
      rcases colinear_of_det2_eq_zero a0nz hd00 with ⟨α, hα⟩
      rcases colinear_of_det2_eq_zero a0nz hd01 with ⟨β, hβ⟩
      rw [hα, hβ] at hc
      exact hc (det2_smul_smul α β (rows 0 0))
    · -- det(a₀,c₀)=0 and det(a₁,c₀)=0  ⇒  a₀ ∥ a₁  ⇒  contradicts `ha`.
      have c0nz : rows 1 0 ≠ 0 := by
        intro h0; apply hc; rw [h0, det2]; simp
      rcases colinear_of_det2_eq_zero c0nz (det2_eq_zero_comm hd00) with ⟨α, hα⟩
      rcases colinear_of_det2_eq_zero c0nz (det2_eq_zero_comm hd10) with ⟨β, hβ⟩
      rw [hα, hβ] at ha
      exact ha (det2_smul_smul α β (rows 1 0))
    · -- det(a₁,c₁)=0 and det(a₀,c₁)=0  ⇒  a₀ ∥ a₁  ⇒  contradicts `ha`.
      have c1nz : rows 1 1 ≠ 0 := by
        intro h0; apply hc; rw [h0, det2]; simp
      rcases colinear_of_det2_eq_zero c1nz (det2_eq_zero_comm hd11) with ⟨α, hα⟩
      rcases colinear_of_det2_eq_zero c1nz (det2_eq_zero_comm hd01) with ⟨β, hβ⟩
      rw [hβ, hα] at ha
      exact ha (det2_smul_smul β α (rows 1 1))
    · -- det(a₁,c₁)=0 and det(a₁,c₀)=0  ⇒  c₀ ∥ c₁  ⇒  contradicts `hc`.
      have a1nz : rows 0 1 ≠ 0 := by
        intro h0; apply ha; rw [h0, det2]; simp
      rcases colinear_of_det2_eq_zero a1nz hd11 with ⟨α, hα⟩
      rcases colinear_of_det2_eq_zero a1nz hd10 with ⟨β, hβ⟩
      rw [hβ, hα] at hc
      exact hc (det2_smul_smul β α (rows 0 1))
  -- Build the corresponding row-permutations.
  rcases disj with hA | hB
  · -- inl branch: the identity permutation already makes both columns bases.
    use fun i j => j
    constructor
    · intro i; exact bijective_id
    · intro j; fin_cases j
      · simpa [isBasis_two, det2] using hA.1
      · simpa [isBasis_two, det2] using hA.2
  · -- inr branch: row 1 swaps column 0 and column 1, the other rows stay fixed.
    use fun i j => if i = 0 then j else swap01 j
    constructor
    · intro i; fin_cases i
      · exact bijective_id
      · exact swap01_bijective
    · intro j; fin_cases j
      · simpa [isBasis_two, det2, swap01] using hB.1
      · simpa [isBasis_two, det2, swap01] using hB.2
