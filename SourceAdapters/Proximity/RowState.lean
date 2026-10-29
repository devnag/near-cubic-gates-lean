import SourceAdapters.Proximity.RowQueries
import SourceAdapters.Proximity.RowTable
import SourceAdapters.Proximity.RenderBlock

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": explicit width, request and mutable-state bounds
for a single row. These are run preconditions; actual initialization and
polynomial allocation must discharge them before extracting a word function. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script)
open QueryStep (rowReg countReg boundReg paddedAddress)

def rowScratch : List (Fin VV) := queryScratch ++ DecisionCalls.scratch ++ LiteralStep.scratch

def rowProgram (q : ℕ) (queries truth : Fin MM) : Script :=
  .seq (queryStage queries) (.seq (tableStage q truth) (renderBlock q queries truth))

def rowCost (q L Lk Bk Λ : ℕ) : ℕ :=
  q * (15 * L + Lk + Bk + 30 * Λ + 64) + 15 * L + Lk + Bk + 20 * Λ + 2 * q + 50 +
  (2 ^ q * (15 * L + 10 * Λ + 6 * q + Lk + Bk + 45) + 3) +
  (9 * 2 ^ q + Lk + Bk + 3 * predicateBlockSize q * (LiteralStep.stepCost q Λ + 1) + 22) + 2

structure RowState (q sourceLength inputCursor : ℕ) (queries truth : Fin MM) (a : State) : Prop where
  constants : Cst a
  bound_eq : a.env boundReg = q
  truth_length : a.env truthLengthReg = 2 ^ q
  source_length : a.env SourceRequests.lengthReg = sourceLength
  input_cursor : a.ip = inputCursor
  kin_nil : a.kin = []
  query_length : (a.ram queries).length ≤ 2 * q
  query_cursor : a.rc queries ≤ 2 * q
  truth_size : (a.ram truth).length ≤ 2 ^ q
  truth_cursor : a.rc truth ≤ 2 ^ q

structure RowBounds {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (budget : ProofCall V → ℕ) (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (Wd Lk Bk Λ : ℕ) : Prop where
  width_two : 2 ≤ Wd
  width_bits : Λ + 1 ≤ Wd
  query_width : q < 2 ^ Wd
  truth_width : 2 ^ q < 2 ^ Wd
  positions : 2 * q ≤ 2 ^ Wd
  row_bits : coins.val.bits.length ≤ Λ
  count_bits : ((V S).queryCount coins).bits.length ≤ Λ
  query_bits : ∀ j < q, j.bits.length ≤ Λ
  address_bits : ∀ i, (addressPair ((V S).query coins i)).2.bits.length ≤ Λ
  count_room : (proofCallInput V (countRequest V ⟨S, coins⟩)).length ≤ Lk
  count_budget : budget (countRequest V ⟨S, coins⟩) ≤ Bk
  query_room : ∀ i, (proofCallInput V (queryRequest V ⟨S, coins, i⟩)).length ≤ Lk
  query_budget : ∀ i, budget (queryRequest V ⟨S, coins, i⟩) ≤ Bk
  decision_room : ∀ bits : BitInput q, (proofCallInput V (decisionRequest V ⟨S, coins,
    fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩)).length ≤ Lk
  decision_budget : ∀ bits : BitInput q, budget (decisionRequest V ⟨S, coins,
    fun i => bits (Fin.castLE ((V S).queryCount_le coins) i)⟩) ≤ Bk
  block_room : 5 + 2 ^ q ≤ Lk
  block_budget : budget (blockRequest V (predicateTable (rowPredicate (V S) coins))) ≤ Bk
  local_width : ∀ index < blockVariableBound q, index.bits.length + 1 ≤ Wd
  doubled_source : ∀ j < q, 2 * (paddedAddress (fun i => addressPair ((V S).query coins i)) j).2 < 2 ^ Wd
  auxiliary : ∀ index < blockVariableBound q, 2 * Nat.pair coins.val (index - q) + 1 < 2 ^ Wd
  output_width : ∀ index < blockVariableBound q,
    natBitLength (addressPair (localAddress (V S) coins index)).2 + 2 < 2 ^ Wd
  local_bits : ∀ index < blockVariableBound q, index.bits.length ≤ Λ
  output_bits : ∀ index < blockVariableBound q,
    natBitLength (addressPair (localAddress (V S) coins index)).2 ≤ Λ

theorem RowBounds.width_four {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    {budget : ProofCall V → ℕ} {S : SourceCircuit} {coins : Fin (2 ^ (V S).randomBits)}
    {Wd Lk Bk Λ : ℕ} (h : RowBounds V budget S coins Wd Lk Bk Λ) : 4 ≤ 2 ^ Wd := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h.width_two
  exact hp

end NearCubicGates.Adapters.Proximity.SourceCallee
