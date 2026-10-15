import Proof.MachineModel.ClosureRawRelabelMachine

/-! Syntactic relabelling cost is linear in the written address expansion,
with one polynomial factor in the maximum pool offset, and no residual table.
These bounds choose a uniform reset log for every live-assignment index. -/
namespace NearCubicWires.P1Closure.RawRelabelCost
open ExtIncidence
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem block_bound (offset c : ℕ) :
    RawRelabelMachine.blockCost offset c≤(2*offset+4)*(block c).length := by
  simp only [RawRelabelMachine.blockCost,block_length]
  nlinarith

theorem body_bound (offset : ℕ) (m : List ℕ) :
    (m.map (RawRelabelMachine.blockCost offset)).sum≤(2*offset+4)*(m.flatMap block).length := by
  induction m with
  | nil=>simp
  | cons c m ih=>
    have h:=block_bound offset c
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
    nlinarith

theorem mono_bound (offset : ℕ) (m : List ℕ) :
    RawRelabelMachine.monoCost offset m≤(2*offset+4)*(monomialWord m).length := by
  have h:=body_bound offset m
  simp only [RawRelabelMachine.monoCost,monomialWord_length]
  nlinarith

theorem scan_bound (offset : ℕ) (P : List (List ℕ)) :
    RawRelabelMachine.budget offset P≤(2*offset+4)*(stream P).length := by
  induction P with
  | nil=>simp [RawRelabelMachine.budget,stream]
  | cons m P ih=>
    have h:=mono_bound offset m
    simp only [RawRelabelMachine.budget,List.map_cons,List.sum_cons,stream_cons,List.length_append]
    unfold RawRelabelMachine.budget at ih
    nlinarith

end NearCubicWires.P1Closure.RawRelabelCost
