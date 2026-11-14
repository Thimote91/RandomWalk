import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- 2 Basic definitions and preliminaries -/

def support {V : Type*} : (V → ℝ) → Set V :=
  fun f ↦
  {y | f y ≠ 0}

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
  graph : SimpleGraph V
  conn : graph.Connected
  /-- The edge weight function. -/
  μ : V → V → ℝ
  /-- Symmetry -/
  μ_symm : ∀ {x y : V}, μ x y = μ y x
  /-- Strict positivity on edges -/
  μ_pos : ∀ {x y : V}, graph.Adj x y → 0 < μ x y
  /-- Zero off edges -/
  w_eq_zero_of_not_adj : ∀ {x y : V}, ¬graph.Adj x y → μ x y = 0
  vertexMeasure_pos : ∀ x, 0 < ∑' y, μ x y

namespace WeightedGraph

variable [Countable V] [Infinite V] (G : WeightedGraph V)

/- The vertex measure induced by the weight:
`μ(x) = Σ_{y ∼ x} μ_{x,y}`  -/

def VertexMeasure (G : WeightedGraph V) (x : V) : ℝ :=
  ∑' y, G.μ x y

def Measure (G : WeightedGraph V) (A : Set V) : ℝ :=
  ∑' y : A, G.VertexMeasure y

def P (G : WeightedGraph V) (x y : V) : ℝ :=
  G.μ x y / G.VertexMeasure x

def p0 {V : Type*} (G : WeightedGraph V) : Prop :=
  have Γ := G.graph
  ∃ p₀ : ℝ, p₀ > 0 ∧ (∀ x y : V, Γ.Adj x y → P G x y ≥ p₀)

def Innerproduct (G : WeightedGraph V) : (V → ℝ) × (V → ℝ) →  ℝ :=
  have μ := VertexMeasure G
  fun (f,g) ↦ ∑' x : V, (f x) * (g x) * (μ x)

def Greenfunction (G : WeightedGraph V) : V → V → ℝ :=
  fun x y ↦
  sorry

def GreenKernel (G : WeightedGraph V) : V → V → ℝ :=
  fun x y ↦
  sorry

def Istransient (G : WeightedGraph V) : Prop :=
  sorry

#check SimpleGraph.dist


def Ball (G : WeightedGraph V) (x : V) (R : ℕ) : Set V :=
  {y : V | G.graph.dist x y < R}

theorem refBall :
    ∀ x : V, ∀ R : ℕ, R > 0 → x ∈ Ball G x R := by
  intro x R hR
  simp [Ball, hR]


def boundary (G : WeightedGraph V) : Set V → Set V :=
  fun A ↦
    { z | z ∉ A ∧ (∃ y ∈ A, G.graph.Adj z y) }

def closure (G : WeightedGraph V) : Set V → Set V :=
  fun A ↦
    A ∪ (boundary G A)

/- Modifier les contraintes sur R > 0 -/
def volume (G : WeightedGraph V) (x : V) (R : ℕ) : ℝ :=
  Measure G (Ball G x R)

theorem volumePos (G : WeightedGraph V) :
    ∀ x : V, ∀ R : ℕ, volume G x R ≥ 0 :=
  sorry

theorem volumeStrictPos (G : WeightedGraph V) :
  ∀ x : V, ∀ R : ℕ, R > 0 → volume G x R > 0 :=
  sorry

theorem volumeGrowth (G : WeightedGraph V) (x : V) :
  ∀ n m : ℕ, n ≤ m → volume G x n ≤ volume G x m := by
  intro n m hnm
  have h1 : Ball G x n ⊆ Ball G x m := by
    intro u hu
    unfold Ball
    have h2 : G.graph.dist x u < n := by
      exact hu
    exact lt_of_lt_of_le h2 hnm
  unfold volume Measure
  sorry

/- Diamètre d'un graphe -/
#check SimpleGraph.diam

/- à modifier prendre en compte n < m < G.diam -/
theorem volumeStrictGrowth (G : WeightedGraph V) : ∀ x : V,
  ∀ n m : ℕ, n < m → volume G x n < volume G x m := by
  intro x n m hnm
  sorry

#check Real.rpow

def polynomialGrowth (G : WeightedGraph V) : Prop :=
  ∃ α > 0, ∀ x : V, ∃ C ≥ 1, ∀ R ≥ 0,
  (volume G x R)/C ≤ R ^ α ∧ R ^ α ≤ C * (volume G x R)

/- The volume comparison principle noted VC-/
def VC (G : WeightedGraph V) : Prop :=
  ∃ Cv > 1, ∀ x : V, ∀ R > 0,
  ∀ y ∈ Ball G x R,
  volume G x (2*R) / volume G y R ≤ Cv

/- The doubling property noted VD-/
def VD (G : WeightedGraph V) : Prop :=
  ∃ Dv > 0, ∀ x : V, ∀ R > 0,
  volume G x (2*R) ≤ Dv * (volume G x R)

/- The weak volume comparison principle noted wVC-/
def wVC (G : WeightedGraph V) : Prop :=
  ∃ C > 0, ∀ x : V, ∀ R > 0,
  ∀ y ∈ Ball G x R,
  volume G x R / volume G y R ≤ C

/- The anti-doubling condition for the volume noted aDV -/
def aDV (G : WeightedGraph V) : Prop :=
  ∃ Av > 0, ∀ x : V, ∀ R > 0,
  2 * (volume G x R) ≤ volume G x (Av * R)

theorem VCtowVC (G : WeightedGraph V) : VC G → wVC G := by
  intro ⟨Cv,⟨h1,h2⟩⟩
  use Cv
  constructor
  · exact gt_trans h1 zero_lt_one
  · intro x R hypR y hypy
    let h2' := h2 x R hypR y hypy
    have tmp : R ≤ 2 * R := by simp [Nat.two_mul]
    have hc : G.volume x R ≤ G.volume x (2*R) := by
      exact volumeGrowth G x R (2*R) tmp
    have hf : G.volume x R / G.volume y R ≤ G.volume x (2 * R) / G.volume y R := by
      apply div_le_div_of_nonneg_right
      · exact volumeGrowth G x R (2*R) tmp
      · exact volumePos G y R
    apply le_trans hf h2'

theorem VCequivVD (G : WeightedGraph V) : VC G ↔ VD G := by
  constructor
  · intro ⟨Cv,⟨h1,h2⟩⟩
    use Cv
    constructor
    · exact gt_trans h1 zero_lt_one
    · intro x R hypR
      let h2' := h2 x R hypR x (refBall G x R hypR)
      have volpos : 0 < G.volume x R := by
        exact volumeStrictPos G x R hypR
      apply (div_le_iff₀ volpos).mp h2'
  · intro ⟨Dv,⟨h1,h2⟩⟩
    unfold VC
    have h :
      ∀ x : V, ∀ R : ℕ, R > 0 → (∀ y ∈ Ball G x R,
      volume G x (2*R) / volume G y R < Dv * volume G x (2*R) / volume G y R) := by
      intro x R hypR y hypy
      let a := volume G x (2*R)
      let b := volume G y R
      let c := volume G x R
      have hyp2R : 2*R > 0 := by
        exact mul_pos sorry hypR
      have apos : a > 0 := volumeStrictPos G x (2*R) hyp2R
      have bpos : b > 0 := volumeStrictPos G y R hypR
      have cpos : c > 0 := volumeStrictPos G x R hypR
      have h2' : a / c ≤ Dv := by
        have u : a ≤ Dv * c :=
          h2 x R hypR
        exact (div_le_iff₀ cpos).2 u
      have tmp : R < 2*R := by
        sorry
      have tmp2 : c < a := by
        exact volumeStrictGrowth G x R (2*R) tmp
      have tmp3 : (c / b) < (a / b) := by
        exact div_lt_div_of_pos_right tmp2 bpos
      calc
        a / b = (a / c) * (c / b) := by field_simp
            _ ≤ Dv * (c / b) :=
              by exact mul_le_mul_of_nonneg_right h2' (div_nonneg (le_of_lt cpos) (le_of_lt bpos))
            _  < Dv * (a / b) :=
              by exact mul_lt_mul_of_pos_left tmp3 h1
    use Dv
    constructor
    · sorry
    · intro x R hypR y hypy
      sorry

lemma p0andVDtowVC (G : WeightedGraph V) : p0 G ∧ VD G → wVC G := by
  sorry

lemma p0andVDtoaDV (G : WeightedGraph V) : p0 G ∧ VD G → aDV G := by
  intro ⟨⟨p0,⟨hp1,hp2⟩⟩,⟨Dv,⟨hD1,hD2⟩⟩⟩
  sorry

/- The bounded covering principle noted BC -/
def BC (G : WeightedGraph V) : Prop :=
  ∃ K : ℕ, ∀ x : V, ∀ R : ℕ,
    R > 0 →
    ∃ s : Finset V, s.card = K ∧
    Ball G x (2* R) ⊆ ⋃ γ ∈ s, Ball G γ R

theorem p0andVDtoBC (G : WeightedGraph V) : (p0 G ∧ VD G) → BC G := by
    intro ⟨hp0,hVD⟩
    sorry

end WeightedGraph
