/-
JSP-000690 — Erdős–Lovász: is there a 3-uniform, 3-chromatic-critical hypergraph
with minimum degree at least 7?

Answer: **yes**.  This file formalises the explicit 9-vertex, 22-edge witness of

  [Li25] *On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7*,
  arXiv:2512.24850, Theorem 4.1 and the edge list displayed in §4.1.

Every verification step is a kernel-checked `decide`; no `native_decide`, no `sorry`.
-/
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace JSP000690

/-! ## General definitions

A hypergraph on a finite vertex type `V` is recorded by its edge set
`E : Finset (Finset V)`.  All notions below are the standard ones from the
Property-B / weak-colouring literature, as set up in [Li25, §2].
-/

section Defs

variable {V : Type*} [DecidableEq V]

/-- `E` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (r : ℕ) (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e.card = r

instance decIsUniform (r : ℕ) (E : Finset (Finset V)) : Decidable (IsUniform r E) := by
  unfold IsUniform; infer_instance

/-- The degree of `v`: the number of edges containing `v`. -/
def degree (E : Finset (Finset V)) (v : V) : ℕ :=
  (E.filter fun e => v ∈ e).card

/-- `φ` is a proper *weak* `k`-colouring of `E`: no edge is monochromatic,
i.e. every edge carries at least two distinct colours. -/
def IsProperColouring {k : ℕ} (E : Finset (Finset V)) (φ : V → Fin k) : Prop :=
  ∀ e ∈ E, ∃ x ∈ e, ∃ y ∈ e, φ x ≠ φ y

instance decIsProperColouring {k : ℕ} [Fintype V] (E : Finset (Finset V))
    (φ : V → Fin k) : Decidable (IsProperColouring E φ) := by
  unfold IsProperColouring; infer_instance

/-- `E` admits a proper weak `k`-colouring, i.e. `χ(E) ≤ k`. -/
def Colourable (k : ℕ) (E : Finset (Finset V)) : Prop :=
  ∃ φ : V → Fin k, IsProperColouring E φ

instance decColourable (k : ℕ) [Fintype V] (E : Finset (Finset V)) :
    Decidable (Colourable k E) := by unfold Colourable; infer_instance

/-- Edge deletion `H - e`. -/
def deleteEdge (E : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  E.erase e

/-- Vertex deletion `H - v`: delete `v` together with every edge through it.
The surviving edges are exactly those avoiding `v`. -/
def deleteVertex (E : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  E.filter fun e => v ∉ e

/-- Critically 3-chromatic, in the sense of [Li25, Def. 2.6]: the hypergraph
needs three colours, three colours suffice, and deleting *any* single edge or
*any* single vertex drops the chromatic number to 2. -/
def CriticallyThreeChromatic (E : Finset (Finset V)) : Prop :=
  ¬ Colourable 2 E ∧
  Colourable 3 E ∧
  (∀ e ∈ E, Colourable 2 (deleteEdge E e)) ∧
  (∀ v : V, Colourable 2 (deleteVertex E v))

/-- Sanity check on `deleteVertex`: since no surviving edge contains `v`, the
colour assigned to `v` is irrelevant.  Hence colouring `deleteVertex E v` by a
map defined on all of `V` carries exactly the same information as colouring the
genuinely smaller vertex set `V \ {v}`. -/
theorem isProperColouring_deleteVertex_congr {k : ℕ} (E : Finset (Finset V))
    (v : V) (φ ψ : V → Fin k) (h : ∀ u, u ≠ v → φ u = ψ u) :
    IsProperColouring (deleteVertex E v) φ ↔ IsProperColouring (deleteVertex E v) ψ := by
  have key : ∀ (α β : V → Fin k), (∀ u, u ≠ v → α u = β u) →
      IsProperColouring (deleteVertex E v) α → IsProperColouring (deleteVertex E v) β := by
    intro α β hαβ hα e he
    obtain ⟨x, hx, y, hy, hxy⟩ := hα e he
    simp only [deleteVertex, Finset.mem_filter] at he
    refine ⟨x, hx, y, hy, ?_⟩
    rw [← hαβ x (fun hxv => he.2 (hxv ▸ hx)), ← hαβ y (fun hyv => he.2 (hyv ▸ hy))]
    exact hxy
  exact ⟨key φ ψ h, key ψ φ fun u hu => (h u hu).symm⟩

end Defs

/-! ## The witness

Vertices are `Fin 9`, i.e. `0,…,8`; the paper writes `1,…,9`, so every label
here is the paper's label minus one.  The 22 edges are [Li25, §4.1]. -/

abbrev V : Type := Fin 9

/-- The 22-edge 3-graph of [Li25, §4.1] (0-indexed). -/
def H : Finset (Finset V) :=
  {{0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5}, {0, 3, 7}, {0, 3, 8},
    {0, 4, 6}, {0, 4, 7}, {0, 4, 8}, {0, 5, 6}, {1, 2, 5}, {1, 2, 6},
    {1, 3, 8}, {1, 4, 8}, {1, 5, 6}, {2, 3, 7}, {2, 4, 7}, {2, 5, 6},
    {3, 5, 7}, {3, 5, 8}, {4, 6, 7}, {4, 6, 8}}

/-- The 22 listed triples are pairwise distinct, so `H` really has 22 edges. -/
theorem H_card : H.card = 22 := by decide

/-- `H` is 3-uniform. -/
theorem H_uniform : IsUniform 3 H := by decide

/-- Degrees: vertex `0` (the paper's vertex 1) has degree 10, all others 7. -/
theorem H_degree (v : V) : degree H v = if v = 0 then 10 else 7 := by
  revert v; decide

/-- Minimum degree is at least 7 — the requirement of the Erdős–Lovász question. -/
theorem H_min_degree : ∀ v : V, 7 ≤ degree H v := by decide

/-- Minimum degree is exactly 7. -/
theorem H_min_degree_eq : (∃ v : V, degree H v = 7) ∧ ∀ v : V, 7 ≤ degree H v := by
  decide

/-- `H` has no proper weak 2-colouring: all `2 ^ 9 = 512` maps `Fin 9 → Fin 2`
leave some edge monochromatic.  Hence `χ(H) ≥ 3`. -/
theorem H_not_two_colourable : ¬ Colourable 2 H := by decide

/-- An explicit proper weak 3-colouring, so `χ(H) ≤ 3`; with the previous
theorem, `χ(H) = 3`. -/
theorem H_three_colourable : Colourable 3 H :=
  ⟨![0, 0, 1, 0, 0, 1, 2, 1, 1], by decide⟩

/-- Edge-criticality: deleting any one of the 22 edges makes `H` 2-colourable. -/
theorem H_edge_critical : ∀ e ∈ H, Colourable 2 (deleteEdge H e) := by decide

/-- Vertex-criticality: deleting any one of the 9 vertices makes `H` 2-colourable. -/
theorem H_vertex_critical : ∀ v : V, Colourable 2 (deleteVertex H v) := by decide

/-- `H` is critically 3-chromatic. -/
theorem H_criticallyThreeChromatic : CriticallyThreeChromatic H :=
  ⟨H_not_two_colourable, H_three_colourable, H_edge_critical, H_vertex_critical⟩

/-! ## The answer to JSP-000690 -/

/-- A finite hypergraph, bundled with its vertex type. -/
structure Hypergraph where
  /-- the vertex type -/
  V : Type
  /-- the vertex type is finite -/
  fintypeV : Fintype V
  /-- vertices can be compared -/
  decEqV : DecidableEq V
  /-- the edge set -/
  edges : Finset (Finset V)

attribute [instance] Hypergraph.fintypeV Hypergraph.decEqV

/-- **JSP-000690.**  There is a 3-uniform hypergraph that is critically
3-chromatic and has minimum degree at least 7.  (Erdős–Lovász, answered
affirmatively by [Li25] under the chromatic reading of "3-critical".) -/
theorem jsp_000690 :
    ∃ G : Hypergraph,
      IsUniform 3 G.edges ∧
      CriticallyThreeChromatic G.edges ∧
      ∀ v : G.V, 7 ≤ degree G.edges v :=
  ⟨⟨V, inferInstance, inferInstance, H⟩, H_uniform, H_criticallyThreeChromatic,
    H_min_degree⟩

/-- The same statement with the witness spelled out on `Fin 9`. -/
theorem jsp_000690_explicit :
    ∃ E : Finset (Finset (Fin 9)),
      IsUniform 3 E ∧
      CriticallyThreeChromatic E ∧
      (∀ v : Fin 9, 7 ≤ degree E v) ∧
      E.card = 22 :=
  ⟨H, H_uniform, H_criticallyThreeChromatic, H_min_degree, H_card⟩

end JSP000690
