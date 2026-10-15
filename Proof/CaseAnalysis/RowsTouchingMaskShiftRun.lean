import Proof.CaseAnalysis.RowsTouchingMaskShiftBody

/-! One existing counted pass updates all three original coordinate masks.
The output carry is retained explicitly; its later use requires its exact
singleton-marker meaning, never an erased scratch assumption. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loop:=CloseoutRowsDegreeLoop.machine body
def selected (i : Fin 6):Bool:=decide (i.val<3)
noncomputable def machine:=MaskedReset.machine loop selected
def readyHeads : Fin 7→ℕ:=![0,0,0,0,0,1,0]
def readyData (picked : Bool) (xs : List Cell) (carry : Bool) (q C : ℕ):Fin 7→List Bool:=
  ![xs.map live,xs.map current,xs.map remaining,[picked],[carry],CompareMachine.word q,List.replicate C false]

theorem loop_run (picked : Bool) (xs : List Cell):
    ∃ r,runFrom loop (4*xs.length+3)
      (RepeatMachine.cfg 0 (entry picked xs 0 []) xs.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (entry picked xs xs.length []) xs.length 1 ∧ r.steps≤4*xs.length+3:=by
  obtain ⟨r,run,rf,rs⟩:=CloseoutRowsDegreeLoop.loop_run body (entry picked xs) (fun _=>[]) 1 xs.length
    (by intro j hj out;rfl) (by intro j hj out;exact body_run picked xs j hj out) []
  have emitted:(List.range xs.length).flatMap (fun _ : ℕ=>([] : List Bool))=[]:=by simp
  rw [emitted,List.nil_append] at rf
  refine ⟨r,?_,rf,?_⟩
  · simpa only [loop,Nat.mul_comm] using run
  · simpa only [Nat.mul_comm] using rs

theorem initial_data (picked : Bool) (xs : List Cell) (C : ℕ):
    (fun i=>Fin.addCases
      (RepeatMachine.cfg 0 (entry picked xs 0 []) xs.length 1).tapes
      (fun _ : Fin 1=>List.replicate C false) i)=readyData picked xs false xs.length C:=by
  funext i;fin_cases i <;> simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,entry,data,mixed,readyData,carry]

theorem output_data (picked : Bool) (xs : List Cell) (C : ℕ):
    (fun i=>Fin.addCases
      (RepeatMachine.cfg 3 (entry picked xs xs.length []) xs.length 1).tapes
      (fun _ : Fin 1=>List.replicate C false) i)=
      readyData picked (transformed picked xs) (carry xs xs.length) xs.length C:=by
  funext i;fin_cases i <;> simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,entry,data,mixed,readyData,
    List.take_of_length_le (transformed_length picked xs).le]

theorem shift_run (picked : Bool) (xs : List Cell) (C : ℕ) (hC:4*xs.length+3≤C):
    Step machine (8*xs.length+8) readyHeads (readyData picked xs false xs.length C) readyHeads
      (readyData picked (transformed picked xs) (carry xs xs.length) xs.length C):=by
  obtain ⟨r,run,rf,_⟩:=loop_run picked xs
  have actual:=Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have reset:=actual.mask selected (by intro i hi;fin_cases i <;> simp_all [selected,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,entry,heads]) hC
  refine (reset.enlarge (by omega)).congr_in ?_ (initial_data picked xs C) |>.congr ?_ (output_data picked xs C)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
