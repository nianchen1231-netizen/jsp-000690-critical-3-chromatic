# JSP-000690 — a 3-uniform, critically 3-chromatic hypergraph of minimum degree 7

Lean 4 formalization of the affirmative answer to the Erdős–Lovász question

> *Is there a three-uniform, three-chromatic-critical hypergraph with minimum degree at least seven?*

recorded as **JSP-000690** in [TheJustinSunPrize/awards](https://github.com/TheJustinSunPrize/awards).

**Mathematical source.** Ruiliang Li, *On an Erdős–Lovász problem: 3-critical 3-graphs
of minimum degree 7*, [arXiv:2512.24850](https://arxiv.org/abs/2512.24850) (2025).
The witness formalized here is the explicit 9-vertex, 22-edge 3-graph of that paper
(Theorem 4.1 and the edge list displayed in §4.1).

## Main theorem

`JspLean690/Critical3Chromatic.lean`:

```lean
theorem jsp_000690 :
    ∃ G : Hypergraph,
      IsUniform 3 G.edges ∧
      CriticallyThreeChromatic G.edges ∧
      ∀ v : G.V, 7 ≤ degree G.edges v
```

where

```lean
def IsProperColouring {k : ℕ} (E : Finset (Finset V)) (φ : V → Fin k) : Prop :=
  ∀ e ∈ E, ∃ x ∈ e, ∃ y ∈ e, φ x ≠ φ y      -- weak colouring: no edge monochromatic

def Colourable (k : ℕ) (E : Finset (Finset V)) : Prop :=
  ∃ φ : V → Fin k, IsProperColouring E φ

def CriticallyThreeChromatic (E : Finset (Finset V)) : Prop :=
  ¬ Colourable 2 E ∧ Colourable 3 E ∧
  (∀ e ∈ E, Colourable 2 (deleteEdge E e)) ∧
  (∀ v : V, Colourable 2 (deleteVertex E v))
```

## What is actually verified

| Theorem | Content |
| --- | --- |
| `H_card` | the 22 listed triples are pairwise distinct |
| `H_uniform` | every edge has exactly 3 vertices |
| `H_degree` | `degree H 0 = 10`, `degree H v = 7` for `v ≠ 0` |
| `H_min_degree` | `∀ v, 7 ≤ degree H v` |
| `H_not_two_colourable` | none of the `2^9 = 512` maps `Fin 9 → Fin 2` is proper, so `χ(H) ≥ 3` |
| `H_three_colourable` | explicit witness `![0,0,1,0,0,1,2,1,1]`, so `χ(H) = 3` |
| `H_edge_critical` | each of the 22 edge-deleted hypergraphs is 2-colourable |
| `H_vertex_critical` | each of the 9 vertex-deleted hypergraphs is 2-colourable |
| `isProperColouring_deleteVertex_congr` | colours at a deleted vertex are irrelevant, so colouring `H - v` over all of `V` is the same data as colouring `V \ {v}` |

Every finite check is discharged by `decide`, i.e. by the Lean **kernel**.
There is no `native_decide`, no `sorry`, no custom `axiom`.

## Axiom audit

`JspLean690/Audit.lean` prints, for all 13 declarations:

```
'JSP000690.jsp_000690' depends on axioms: [propext, Classical.choice, Quot.sound]
```

— only the three standard Lean axioms.

## Build

```
lake exe cache get
lake build JspLean690
```

Lean `v4.34.0`, Mathlib `v4.34.0` (pinned in `lean-toolchain` / `lake-manifest.json`).
`JspLean690.Critical3Chromatic` takes about 85 s to elaborate; the exhaustive
`decide` calls are the cost.

## Indexing convention

The paper labels vertices `1,…,9`; this file uses `Fin 9`, so every label here is
the paper's label minus one.
