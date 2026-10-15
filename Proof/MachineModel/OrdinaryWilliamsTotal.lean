import Proof.MachineModel.OrdinaryWilliamsDispatch

/-! One finite ordinary wrapper handles every canonical request. The zero
branch stops with the untouched fresh output; the positive branch executes
the full source/crop computation. Every branch and return is charged. -/
namespace NearCubicWires.RepairOrdinary.WilliamsCall
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation SourceInterfaces ExecutableInterfaces
open WilliamsLoaderForms WilliamsProductCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes (a : WilliamsAlgorithm) : Fin 2 → ℕ := ![16,(prefixStates+2)+sourceStates a]
noncomputable def programs (a : WilliamsAlgorithm) : (j : Fin 2) → Machine (tapeCount a) (sizes a j) := by
  intro j
  refine Fin.cases (motive := fun j => Machine (tapeCount a) (sizes a j)) (gateMachine a) ?_ j
  intro i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  exact positiveMachine a

def next (a : WilliamsAlgorithm) (j : Fin 2) (q : Fin (sizes a j)) (_ : Fin (tapeCount a) → Bool) : Option (Fin 2) :=
  if j.val=0 ∧ q.val=10 then some 1 else none
noncomputable def totalMachine (a : WilliamsAlgorithm) := RecoveryCalls.machine (sizes a) (programs a) 0 (next a)
def coefficient (a : WilliamsAlgorithm) := positiveCoefficient a+12
def budget (a : WilliamsAlgorithm) (r : RectangularProductRequest) :=
  coefficient a*(r.dimension+1)^2*(logScale r.dimension+1)^(a.logExponent+1)

theorem gate_budget (a : WilliamsAlgorithm) (r : RectangularProductRequest) : 12 ≤ budget a r := by
  have hp : 1 ≤ (r.dimension+1)^2*(logScale r.dimension+1)^(a.logExponent+1) := by
    exact Nat.mul_pos (by positivity) (pow_pos (by omega) _)
  unfold budget coefficient
  nlinarith

theorem total_budget (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    positiveBudget a r hr+12 ≤ budget a r := by
  have h := positive_budget a r hr
  have hp : 1 ≤ (r.dimension+1)^2*(logScale r.dimension+1)^(a.logExponent+1) := by
    exact Nat.mul_pos (by positivity) (pow_pos (by omega) _)
  unfold budget coefficient
  nlinarith

theorem zero_output (r : RectangularProductRequest) (hr : r.dimension=0) :
    encodedNatCellTape (natBitLength r.dimension) (rowMajorNatMatrix (integerMatrixProduct r.left r.right))=[] := by
  apply List.eq_nil_of_length_eq_zero
  simp [encodedNatCellTape,fixedWidthNatBits,List.length_flatMap,rowMajorNatMatrix_length,hr]

theorem total_run (a : WilliamsAlgorithm) (r : RectangularProductRequest) :
    ∃ actual : ExecutionReceipt (tapeCount a) (Fintype.card (RecoveryCalls.Control (sizes a))),
      run (totalMachine a) (budget a r) (input a r)=some actual ∧
      actual.final.tapes (outputTape a)=encodedNatCellTape (natBitLength r.dimension)
        (rowMajorNatMatrix (integerMatrixProduct r.left r.right)) := by
  obtain ⟨gate,hg,hgt,hgh,hgc,_⟩ := gate_run a r
  have hg' : runFrom (programs a 0) 10 (initialConfiguration (programs a 0) (input a r))=some gate := hg
  have hin : controlConfig (RecoveryCalls.code (sizes a) 0)
      (initialConfiguration (programs a 0) (input a r))=initialConfiguration (totalMachine a) (input a r) := rfl
  by_cases hz : r.dimension=0
  · have hn : next a 0 gate.final.control gate.final.scanned=none := by simp [next,hgc,hz]
    obtain ⟨n,hn,hpath⟩ := stop_receipt (sizes a) (programs a) 0 (next a) 0 10 _ gate hg' hn
    rw [hin] at hpath
    obtain ⟨actual,ha,hf,_⟩ := hpath.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hbound : n ≤ budget a r := by have := gate_budget a r; omega
    have hm := run_moreFuel (totalMachine a) n (budget a r-n) (input a r) actual ha
    rw [Nat.add_sub_of_le hbound] at hm
    refine ⟨actual,hm,?_⟩
    rw [hf,zero_output r hz]
    change gate.final.tapes (outputTape a)=[]
    rw [hgt]
    simp [input,outputTape,extraSlot]
  · have hr : 1 ≤ r.dimension := by omega
    have hn : next a 0 gate.final.control gate.final.scanned=some 1 := by simp [next,hgc,hz]
    obtain ⟨ng,hng,gatePath⟩ := call_receipt (sizes a) (programs a) 0 (next a) 0 1 10 _ gate hg' hn
    have hi : RecoveryCalls.restarted (programs a 1) gate.final.heads gate.final.tapes=
        initialConfiguration (programs a 1) (input a r) := by
      apply configuration_ext
      · rfl
      · exact funext hgh
      · exact hgt
    rw [hi,hin] at gatePath
    obtain ⟨positive,hp,ho,_⟩ := positive_run a r hr
    have hp' : runFrom (programs a 1) (positiveBudget a r hr)
        (initialConfiguration (programs a 1) (input a r))=some positive := hp
    obtain ⟨np,hnp,posPath⟩ := stop_receipt (sizes a) (programs a) 0 (next a) 1
      (positiveBudget a r hr) _ positive hp' (by simp [next])
    have whole := gatePath.trans posPath
    obtain ⟨actual,ha,hf,_⟩ := whole.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hbound : ng+np ≤ budget a r := by have := total_budget a r hr; omega
    have hm := run_moreFuel (totalMachine a) (ng+np) (budget a r-(ng+np)) (input a r) actual ha
    rw [Nat.add_sub_of_le hbound] at hm
    refine ⟨actual,hm,?_⟩
    rw [hf]
    exact ho

end NearCubicWires.RepairOrdinary.WilliamsCall
