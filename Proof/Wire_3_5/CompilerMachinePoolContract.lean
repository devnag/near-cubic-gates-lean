import Proof.Wire_3_5.CompilerMachinePoolLabels

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary (frame)

/-- The pool builder's request: the carrier gates of the call, the side of each original coordinate,
the dense width, the flip patterns (`4·rowIdx + k`), the P/N field width `h`, the lift precision `Q'`, the load. -/
structure PoolReq where
  n : ℕ
  gates : List (SupportedNormalizedGate n)
  side : List Bool
  width : ℕ
  flips : List (List Bool)
  h : ℕ
  Q : ℕ
  psi : ℕ

/-- The admissible requests: sides and flips of length `n`, both sides fit the width. -/
def PoolReq.Pre (R : PoolReq) : Prop :=
  R.side.length = R.n ∧ (∀ f ∈ R.flips, f.length = R.n) ∧ nLeft R.side R.n ≤ R.width ∧ nRight R.side R.n ≤ R.width

/-- A dense child (weights, target) holds at the center assignment `(a_L, a_R)`. -/
def holdsL (w aL aR : ℕ) (c : List ℤ × ℤ) : Bool :=
  decide ((((List.range c.1.length).map fun j =>
    c.1.getD j 0 * (if (if j < w then aL.testBit j else aR.testBit (j - w)) then (1 : ℤ) else 0))).sum = c.2)

theorem list_sum_range (f : ℕ → ℤ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]; simp

theorem eval_eq_holdsL (w aL aR : ℕ) (e : ExactThresholdGate (w + w)) :
    e.eval (centerInput w aL aR) = holdsL w aL aR (List.ofFn e.weight, e.target) := by
  unfold ExactThresholdGate.eval holdsL
  apply decide_eq_decide.mpr
  simp only [List.length_ofFn]
  rw [list_sum_range, ← Fin.sum_univ_eq_sum_range]
  have : ∀ j : Fin (w + w), e.weight j * (if centerInput w aL aR j then (1 : ℤ) else 0) =
      (List.ofFn e.weight).getD j.val 0 * (if (if j.val < w then aL.testBit j.val else aR.testBit (j.val - w)) then 1 else 0) := by
    intro j
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    rfl
  rw [Finset.sum_congr rfl (fun j _ => this j)]

theorem getD_map_map {α β : Type} (f : α → β) (l : List (List α)) (i : ℕ) :
    (l.map (List.map f)).getD i [] = (l.getD i []).map f := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rfl

variable (a : DecompositionAlgorithm)

/-- The reference pool with each dense child as its weights and target. -/
def denseRef (R : PoolReq) : List (List (List ℤ × ℤ)) :=
  (densePool a R.gates R.side R.width R.flips).map (List.map fun e => (List.ofFn e.weight, e.target))

/-- **The C3a pool-builder contract.** -/
def c3a (E : Envelope) (inputWord : PoolReq → List Bool) (coef : ℕ) : MachineContract E where
  Req := PoolReq
  input := inputWord
  pre := fun R => R.Pre ∧ (inputWord R).length ≤ 2 ^ R.psi
  Out := List (List (List ℤ × ℤ)) × PoolReq
  ref := fun R => (denseRef a R, R)
  encode := fun o => (poolRecs a o.2.h o.2.gates o.2.side o.2.width o.2.flips).flatMap frame ++
    false :: (childTable o.2.Q (shapeOf (densePool a o.2.gates o.2.side o.2.width o.2.flips))).flatMap atomStream
  cls := .preprocessing
  q := fun R => R.n
  k := fun R => R.width
  psi := fun R => R.psi
  coef := coef

  errSpec := fun R o => o.1.length = R.flips.length * R.gates.length ∧
    ∀ aL aR i gi (hi : i < R.flips.length) (hg : gi < R.gates.length),
      (if R.gates[gi].gate.eval (pullPoint R.side R.flips[i] aL aR) then (1 : ℤ) else 0) =
        ((o.1.getD (i * R.gates.length + gi) []).map fun c => if holdsL R.width aL aR c then (1 : ℤ) else 0).sum

/-- **The error field holds for the reference** on every admissible request. -/
theorem c3a_err (E : Envelope) (inputWord : PoolReq → List Bool) (coef : ℕ) :
    ∀ R, (c3a a E inputWord coef).pre R → (c3a a E inputWord coef).errSpec R ((c3a a E inputWord coef).ref R) := by
  intro R hpre
  change PoolReq at R
  obtain ⟨⟨_, _, hL, hR⟩, _⟩ := hpre
  change (denseRef a R).length = R.flips.length * R.gates.length ∧
    ∀ aL aR i gi (hi : i < R.flips.length) (hg : gi < R.gates.length),
      (if R.gates[gi].gate.eval (pullPoint R.side R.flips[i] aL aR) then (1 : ℤ) else 0) =
        (((denseRef a R).getD (i * R.gates.length + gi) []).map fun c => if holdsL R.width aL aR c then (1 : ℤ) else 0).sum
  refine ⟨by simp [denseRef, densePool_length], ?_⟩
  intro aL aR i gi hi hg
  have hL' : ((List.ofFn fun j : Fin R.n => R.side.getD j false).filter id).length ≤ R.width := hL
  have hR' : ((List.ofFn fun j : Fin R.n => R.side.getD j false).filter (fun b => !b)).length ≤ R.width := hR
  rw [densePool_exact a R.gates R.side R.width R.flips aL aR hL' hR' i gi hi hg]
  unfold denseRef
  rw [getD_map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp, eval_eq_holdsL]

/-- The request of the useless-inhabitant check: one always-true gate on one coordinate, one flip pattern. -/
def trueGate : SupportedNormalizedGate 1 := ⟨⟨fun _ => 0, 0⟩, ∅, fun _ _ => rfl⟩

def uselessPool : PoolReq := ⟨1, [trueGate], [true], 1, [[false]], 1, 1, 0⟩

/-- **The useless inhabitant fails**: the empty pool does not meet C3a's error field (the always-true gate needs a
holding child). -/
theorem c3a_not_nil (E : Envelope) (inputWord : PoolReq → List Bool) (coef : ℕ) :
    ¬ (c3a a E inputWord coef).errSpec uselessPool ([], uselessPool) := by
  rintro ⟨_, h⟩
  have := h 0 0 0 0 (by decide) (by decide)
  simp [uselessPool, trueGate, NormalizedThresholdGate.eval] at this

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
