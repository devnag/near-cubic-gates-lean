import Proof.CaseAnalysis.RowsTouchingGateFoldLayout

/-! The cancelled touching comparison uses multipliers at most q. Reuse
its actual unary counters in the existing counted accumulator, avoiding a
second numeric representation and a binary multiplier. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.UnaryProduct
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratch (w x j : ℕ) (backing : List Bool):=if j=0 then backing else frame (binary w (j*x))
noncomputable def entry (w x : ℕ) (backing : List Bool) (j : ℕ) (_out : List Bool):=
  (⟨MatrixScoreAccumulate.machine.start,fun _=>0,MatrixScoreAccumulate.input w x (j*x) (scratch w x j backing)⟩:
    Configuration 5 13)
noncomputable def machine:=CloseoutRowsDegreeLoop.machine MatrixScoreAccumulate.machine
def budget (w n : ℕ):=n*(12*w+16)+3

theorem product_run (w x n : ℕ) (backing : List Bool)
    (hb:backing.length≤2*w+1) (hfit:n*x<2^w):
    ∃ r,runFrom machine (budget w n)
      (RepeatMachine.cfg 0 (entry w x backing 0 []) n 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (entry w x backing n []) n 1 ∧ r.steps≤budget w n:=by
  have supplier:∀ j<n,∀ out,∃ r,
      runFrom MatrixScoreAccumulate.machine (12*w+13) (entry w x backing j out)=some r ∧
      r.final.heads=(entry w x backing (j+1) (out++[])).heads ∧
      r.final.tapes=(entry w x backing (j+1) (out++[])).tapes ∧ r.steps≤12*w+13:=by
    intro j hj out
    have fit:x+j*x<2^w:=by
      have bound: (j+1)*x≤n*x:=Nat.mul_le_mul_right x (by omega)
      have eq:x+j*x=(j+1)*x:=by ring
      rw [eq];exact bound.trans_lt hfit
    have scratchFit:(scratch w x j backing).length≤2*w+1:=by
      unfold scratch
      split
      · exact hb
      · simp
    have actual:=Step.of_ready (MatrixScoreAccumulate.accumulate_ready w x (j*x) (scratch w x j backing) fit scratchFit)
    refine actual.congr rfl ?_
    change MatrixScoreAccumulate.output w x (j*x)=MatrixScoreAccumulate.input w x ((j+1)*x) (scratch w x (j+1) backing)
    have eq:x+j*x=(j+1)*x:=by ring
    simp only [MatrixScoreAccumulate.output,MatrixScoreAccumulate.input,scratch,Nat.add_eq_zero_iff,
      Nat.one_ne_zero,and_false,ite_false,eq]
  obtain ⟨r,run,rf,rs⟩:=CloseoutRowsDegreeLoop.loop_run MatrixScoreAccumulate.machine
    (entry w x backing) (fun _=>[]) (12*w+13) n (by intro j hj out;rfl) supplier []
  have emitted:(List.range n).flatMap (fun _ : ℕ=>([] : List Bool))=[]:=by simp
  rw [emitted,List.nil_append] at rf
  exact ⟨r,run,rf,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.UnaryProduct
