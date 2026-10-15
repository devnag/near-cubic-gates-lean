import Proof.MachineModel.ClosureRadixFamily

/-! A.12's compact request in the physical writer's shared digit order.
The permutation keeps every occurrence, including repeated monomials. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.RepairOrdinary.P1CompactInput
open RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
open MatrixScoreBatch RowBinLift P1CompactCloseoutRowsCacheInput

theorem family_degree {l r : Nat} (gs : List (ExactThresholdGate (l+r))) [P1Radix gs]
    (bank : List (List (List Bool))) [P1BankDegree gs bank]
    (ms : List (List (Equation l r))) (hm : ms∈family gs bank)
    (m : List (Equation l r)) (hmem : m∈ms) : m.length ≤ P1Radix.effectiveDegree gs := by
  obtain ⟨rows,hr,rfl⟩ := List.mem_map.mp hm
  obtain ⟨bits,hb,rfl⟩ := List.mem_map.mp hmem
  letI := P1BankDegree.bound (gs := gs) rows hr
  have hc := P1MaskDegree.bound (gs := gs) bits hb
  simp only [monomial,P1CompactRowCachedEquation.equations,List.length_map]
  unfold P1CompactRowTupleCommonEquation.one
  split_ifs with h
  · simpa only [RowMaskMeaning.typed_length] using hc
  · simp

def input (s Q w : Nat) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [P1Radix gs]
    (bank : List (List (List Bool))) [P1BankDegree gs bank] (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100 ≤ 2^s)
    (hw : ∀ rows∈bank, rows.length ≤ 2^w) : EquationRow.Input :=
  let base := CloseoutRows.commonInput s (P1Radix.bits gs) (P1Radix.effectiveDegree gs) Q
    (family gs bank) hs hg (family_degree gs bank) (family_fit gs bank)
  let hp := (P1CompactCloseoutRowsSharedDigits.batch_perm gs Q w bank hw).trans
    (CloseoutRows.ordered_batch_perm (P1Radix.bits gs) Q (family gs bank)).symm
  { d := base.d, p := base.p, odd := base.odd
    cuts := bank.flatMap (P1CompactCloseoutRowsSharedDigits.cuts gs Q w)
    lengths := fun c hc => base.lengths c (hp.mem_iff.mp hc)
    fits := fun c hc => base.fits c (hp.mem_iff.mp hc)
    oddPositive := base.oddPositive
    gateSquare := by rw [hp.length_eq]; exact base.gateSquare }

theorem count_modEq (s Q w : Nat) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [P1Radix gs]
    (bank : List (List (List Bool))) [P1BankDegree gs bank] (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100 ≤ 2^s)
    (hw : ∀ rows∈bank, rows.length ≤ 2^w)
    (i j : Fin (EquationRow.request (input s Q w gs bank hs hg hw)).U) :
    Int.ModEq ((2 : Int)^Q)
      (SupplierPrinter.weightedDominance
        (leftScore (EquationRow.request (input s Q w gs bank hs hg hw)))
        (rightScore (EquationRow.request (input s Q w gs bank hs hg hw)))
        (weight (EquationRow.request (input s Q w gs bank hs hg hw))) i j)
      (CompetitorCountTable.rowValues (family gs bank) (input s Q w gs bank hs hg hw) i j) :=
  CompetitorRowCountMeaning.request_modEq_perm (P1Radix.bits gs) Q
    (family gs bank) (input s Q w gs bank hs hg hw)
    (P1CompactCloseoutRowsSharedDigits.batch_perm gs Q w bank hw) (family_fit gs bank) i j

end NearCubicWires.RepairOrdinary.P1CompactInput
