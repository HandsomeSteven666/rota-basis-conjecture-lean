import Mathlib
import RotaBasis.Basic

/-!
# Rota's Basis Conjecture — `n = 3` (vector-space version)

## Status (2026-09-29)

`n = 3` is a **known theorem**: Chan (1995) proved Rota's basis conjecture for
every rank-≤3 matroid, hence for every field `K` and every 3-dimensional vector
space (char-free).  Geelen–Humphries (2006), *Rota's Basis Conjecture for
Paving Matroids*, Discrete Math. 306, give the cleanest case-distinction
(Theorem 2.1) for the *paving* subclass, which is what this file formalizes.

This file is the **machine-verification infrastructure**.  It introduces the
explicit 9-point model that the rank-3 case-distinction needs (a transversal is
a 3-point set meeting each of the three bases once; independence is linear
independence in `K³`) and proves the clean foundational lemmas.  The case-
analysis lemmas of Theorem 2.1 (`sub_2_1_1`, `sub_2_1_2`, `sub_2_1_3`, …) and the
prime `rotaStatement_three` are scaffolded with explicit `sorry` placeholders and
are **not yet proven**; `rotaStatement_three` compiles but is *not* a proof.

## Mathematical reduction

The vector-space statement reduces to the *paving* case: no two of the nine
basis vectors are parallel (scalar multiples).  A parallel pair is a relaxable
2-point line (Chan's "relax lines" technique), so the general rank-3 vector
space case follows once the paving case is established.  Under paving, every
2-element subset is independent — precisely the hypothesis Theorem 2.1 uses.
Hence `paving` is the standing assumption throughout this file.

## Source

Geelen, J. & Humphries, P.J. (2006). *Rota's Basis Conjecture for Paving
Matroids*.  Theorem 2.1 (the `n = 3` case) is the case-distinction formalized
here.  The labelled claims 2.1.1 / 2.1.2 / 2.1.3 are the sub-lemmas below.
-/

namespace RotaBasis.Three

open Matrix Function Submodule

variable {K : Type*} [Field K]

/-! ## The 9-point model for `n = 3`

A *point* is a pair `(base index, element index)`; there are nine.  A *vector
assignment* `vec : Pt → (Fin 3 → K)` places a vector of `K³` at each point; we
require each row `Bᵢ = {vec (i, j) | j}` to be a basis of `K³`. -/

/-- A *point* is a pair `(base index, element index)`; there are nine. -/
abbrev Pt := Fin 3 × Fin 3

/-- The base that a point belongs to. -/
def baseIdx (p : Pt) : Fin 3 := p.1

/-- Two vectors are parallel (collinear through the origin) iff one is a scalar
multiple of the other. -/
def parallel (u v : Fin 3 → K) : Prop := ∃ (c : K), u = c • v

/-- The *paving* hypothesis: no two distinct points carry parallel vectors.
(Equivalently, the induced vector matroid has no 2-point circuit.) -/
def paving (vec : Pt → (Fin 3 → K)) : Prop :=
  ∀ ⦃p q : Pt⦄, p ≠ q → ¬ parallel (vec p) (vec q)

variable (vec : Pt → (Fin 3 → K))

/-- Span of a set of points (as a submodule of `K³`). -/
def spanOf (S : Set Pt) : Submodule K (Fin 3 → K) := Submodule.span K (vec '' S)

/-- `S` spans the whole space `K³`. -/
def spansFull (S : Set Pt) : Prop := spanOf vec S = ⊤

/-- A *transversal* meets each of the three bases exactly once. -/
def transversal (T : Set Pt) : Prop :=
  (∀ i, ∃! j, (i, j) ∈ T) ∧ Set.Finite T

/-- A transversal `T` is *independent* (hence a basis of `K³`) iff its three
vectors, indexed by base, are linearly independent. -/
def independent (T : Set Pt) (hT : transversal T) : Prop :=
  LinearIndependent K (fun i => vec (i, Classical.choose (hT.1 i)))

/-! ## Proven foundational lemmas -/

/-- Paving makes `vec` injective on points. -/
lemma vec_injective_of_paving (hpav : paving vec) : Function.Injective vec := by
  intro p q heq
  by_contra hne
  have hpar : parallel (vec p) (vec q) := ⟨1, by rw [one_smul]; exact heq⟩
  exact hpav hne hpar

/-! The following lemmas are scaffolding: their *statements* are the correct
model facts, but their *proofs* are not yet filled in (API/effort pending).  They
are marked `sorry`. -/

/-- Under paving, any two distinct points carry linearly-independent vectors. -/
lemma paving_pair_linearIndependent {p q : Pt} (hpq : p ≠ q) (hpav : paving vec)
    (hvp : vec p ≠ 0) (hvq : vec q ≠ 0) :
    LinearIndependent K (fun (i : Fin 2) => if i = 0 then vec p else vec q) := by
  sorry

/-- A basis of `K³` (in the `isBasis` sense of `Basic.lean`) spans the whole
space. -/
lemma isBasis_three_span_top (b : Fin 3 → (Fin 3 → K)) (h : isBasis 3 b) :
    Submodule.span K (Set.range b) = ⊤ := by
  sorry

/-- The union of the three given bases spans `K³`. -/
lemma spansFull_union (hb : ∀ i, isBasis 3 (fun j => vec (i, j))) :
    spansFull vec Set.univ := by
  sorry

/-! ## Scaffolded case-analysis (Geelen–Humphries Theorem 2.1) — NOT YET PROVEN

These mirror the labelled claims of the paving proof.  Each is currently a
`sorry` placeholder; the prime theorem is assembled from them and is therefore
also unproven.  Filling them in is the remaining work of route A.

* `sub_2_1_1` — if `S` meets each base and `spansFull S`, then `S` contains an
  independent transversal.
* `sub_2_1_2` — if no `M₁`-dependent transversal contains both `a₁` and `b₁`,
  then `∃ e ∈ B₃` with `r₂(E − {a₁, b₁, e}) = 2`.
* `sub_2_1_3` — every pair `e ∈ Bᵢ, f ∉ Bᵢ` lies in some `Mᵢ`-dependent transversal.
* `no_seven_point_line` — no line (plane) carries 7+ points.
* `no_five_six_point_line` — no line carries 5 or 6 points.
* `all_bases_independent` — each `Bᵢ` is independent in all three matroids.
* `rank2_flats_at_most_three` — rank-2 flats carry at most three points.
* final finish via `sub_2_1_1` on the residual 4-point sets. -/

/-- **2.1.1.** If `S` meets each base and `spansFull S`, then `S` contains an
independent transversal.  *(Scaffold: proof pending.)* -/
theorem sub_2_1_1
  (hpav : paving vec)
  (hb : ∀ i, isBasis 3 (fun j => vec (i, j)))
  (S : Set Pt)
  (hmeets : ∀ i, ∃ j, (i, j) ∈ S)
  (hfull : spansFull vec S) :
  ∃ (T : Set Pt) (hT : transversal T), T ⊆ S ∧ independent vec T hT := by
  sorry

/-- **2.1.2.** *(Scaffold: proof pending.)* -/
theorem sub_2_1_2 (hpav : paving vec) (a b c : Fin 3 → (Fin 3 → K)) : True := by sorry

/-- **2.1.3.** *(Scaffold: proof pending.)* -/
theorem sub_2_1_3 (hpav : paving vec) : True := by sorry

/-- No line (plane) carries 7 or more points. *(Scaffold.)* -/
theorem no_seven_point_line (hpav : paving vec) : True := by sorry

/-- No line carries 5 or 6 points. *(Scaffold.)* -/
theorem no_five_six_point_line (hpav : paving vec) : True := by sorry

/-- Each `Bᵢ` is independent in all three matroids. *(Scaffold.)* -/
theorem all_bases_independent (hpav : paving vec) : True := by sorry

/-- Rank-2 flats carry at most three points. *(Scaffold.)* -/
theorem rank2_flats_at_most_three (hpav : paving vec) : True := by sorry

/-- Prime theorem: `n = 3` of Rota's basis conjecture (paving case).
Currently an axiom — assembled from the (unproven) scaffold lemmas above. -/
theorem rotaStatement_three
  (vec : Pt → (Fin 3 → K))
  (hpav : paving vec)
  (hb : ∀ i, isBasis 3 (fun j => vec (i, j))) :
  ∃ (A : Fin 3 → Set Pt),
    (∀ j, transversal (A j)) ∧
    (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (A j₁) (A j₂)) ∧
    (⋃ j, A j) = Set.univ ∧
    (∀ j, ∃ h, independent vec (A j) h) := by
  sorry
