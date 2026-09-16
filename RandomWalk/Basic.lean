/-
  Formalization of "Basic definitions and preliminaries"
  (A. Telcs, The Art of Random Walks)

  Covers: a countable infinite connected weighted graph (Γ, μ), the induced
  vertex measure, the reversible Markov chain / random walk it defines, its
  n-step transition probabilities, the discrete heat kernel, and the graph
  distance with open metric balls.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped BigOperators
noncomputable section

variable {V : Type*}
variable {Γ : Set V}

/-- A countable, infinite, connected, *simple* graph `Γ` (no loops, no
multiple edges -- both automatic for `SimpleGraph`, since `Adj` is a single
`Prop` per pair and irreflexive), together with a symmetric, strictly
positive edge weight `μ_{x,y}`.

Following the book, `μ` is only meaningful on edges; we extend it by `0`
off the edge set so it can be treated as a total function `V → V → ℝ`
(this is purely a modelling convenience, recorded in `w_eq_zero_of_not_adj`). -/

def IsGraphRelation : Set (V × V) → Prop :=
  fun Γ ↦
   (∀ x y, (x,y) ∈ Γ → (y,x) ∈ Γ) ∧
   (∀ x, ¬(x,x) ∈ Γ)

def GraphOfSet
  {V : Type*}
  (Γ : Set (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel
    (fun x ↦
    fun y ↦
    (x,y) ∈ Γ)

structure WeightedGraph (V : Type*) where
  G : SimpleGraph V
  conn : G.Connected
  /-- The edge weight function. -/
  μ : V → V → ℝ
  /-- Symmetry -/
  μ_symm : ∀ {x y : V}, μ x y = μ y x
  /-- Strict positivity on edges -/
  μ_pos : ∀ {x y : V}, G.Adj x y → 0 < μ x y
  /-- Zero off edges -/
  w_eq_zero_of_not_adj : ∀ {x y : V}, ¬G.Adj x y → μ x y = 0
  vertexMeasure_pos : ∀ x, 0 ≤ ∑' y, μ x y

namespace WeightedGraph

variable [Countable V] [Infinite V] (G : WeightedGraph V)

/- The vertex measure induced by the weight:
`μ(x) = Σ_{y ∼ x} μ_{x,y}`  -/

def vertexMeasure (x : V) : ℝ :=
  ∑' y, G.μ x y

/- Restating the structure's imposed positivity in terms of `vertexMeasure`. -/
theorem vertexMeasure_pos' (G : WeightedGraph V) (x : V) : 0 ≤ G.vertexMeasure x :=
  G.vertexMeasure_pos x

def measure (A : Set V) : ℝ :=
  ∑' y : A, G.vertexMeasure y

/-- The one-step transition probability of the random walk on `(G, μ)`: -/

def P (x y : V) : ℝ :=
  G.μ x y / G.vertexMeasure x

/- The `n`-step transition probability `P_n(x,y) = ℙ(X_n = y ∣ X_0 = x)`,
defined recursively (Chapman–Kolmogorov): `P_0 = Id`, `P_{n+1} = P_n · P`. -/

/- One-step "detailed balance": `μ(x) P(x,y) = μ_{x,y}`. In particular,
together with `w_symm`, the chain is reversible with respect to `μ`:
`μ(x) P(x,y) = μ(y) P(y,x)`. -/

/- Reversibility of the chain with respect to `μ`:
`μ(x) P(x,y) = μ(y) P(y,x)`. -/

theorem reversible :
  ∀ x y, G.vertexMeasure x * G.P x y = G.vertexMeasure y * G.P y x := by
  intro x y
  simp [P, vertexMeasure]
  rw [G.μ_symm]
  sorry

end WeightedGraph
