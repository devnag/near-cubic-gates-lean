import Proof.CaseAnalysis.CommonPrefixFields
import Proof.CaseAnalysis.CommonPrepareBudget

/-! The actual common prefix: execute the selected ordinary refuter program,
then the paid final-address capacity and hierarchy-request preparation. -/
namespace NearCubicWires.RepairSource.CloseoutCommonPrefix
open LocalBitMultitape RepairOrdinary CloseoutSchedule CloseoutRetainedRefuter
open OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def query (w : ℕ) (r : OrdinaryOracleProgram) : Fin (base w r):=
  (CloseoutRetainedRefuter.ports r (RefuterPrefix.sourcePort w)).queryTape

theorem query_ne_address (w : ℕ) (r : OrdinaryOracleProgram) : query w r≠address w r:=
  bank_old r (RefuterPrefix.sourcePort w) (RefuterPrefix.addressPort w)
    (Guarded.old_fresh w (Cold.extra w 0) 8) (clocked r).queryTape

def ports (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) : Ports (tapes w r k) where
  twoTapes:=by unfold tapes base CloseoutRetainedRefuter.tapes; omega
  outputTape:=firstSlots w r k (answer w r)
  outputFresh:=by rw [first_answer]; omega
  queryTape:=firstSlots w r k (query w r)
  queryFresh:=by
    simp only [firstSlots,if_neg (query_ne_address w r)]
    omega

def pieces (sources : EightSources) (k D copies As Bs onset Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (r : OrdinaryOracleProgram)
    (j : Fin 2) : Piece (tapes (Step.workTapes sources k D) r k):=
  if j.val=0 then
    focused (RefuterPrefix.selectedProgram sources k D copies clock As Bs onset r)
      (firstSlots (Step.workTapes sources k D) r k)
  else ordinary (RecoveryFocus.machine (prepareSlots (Step.workTapes sources k D) r k)
    (CloseoutCommonPrepare.machine k
      (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy.coefficient Aw Bw))

def next (sources : EightSources) (k D copies As Bs onset Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (r : OrdinaryOracleProgram)
    (j : Fin 2) (_ : Fin (pieces sources k D copies As Bs onset Aw Bw clock r j).states)
    (_ : Fin (tapes (Step.workTapes sources k D) r k)→Bool) : Option (Fin 2):=
  if j.val=0 then some 1 else none

def program (sources : EightSources) (k D copies As Bs onset Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (r : OrdinaryOracleProgram):=
  (ports (Step.workTapes sources k D) r k).program
    (graph (pieces sources k D copies As Bs onset Aw Bw clock r) 0
      (next sources k D copies As Bs onset Aw Bw clock r))

end
end NearCubicWires.RepairSource.CloseoutCommonPrefix
