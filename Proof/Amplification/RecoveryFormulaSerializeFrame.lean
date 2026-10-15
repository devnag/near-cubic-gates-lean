import Proof.Amplification.RecoveryFormulaSerializeRetained
import Proof.Amplification.RecoveryFocusDock

/-! Copy the original serializer's retained frame onto a fresh output tape.
The fixed copy reads its delimiter and executes its own rewind. No capacity
or output length is supplied to the program. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaFrame
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3→Fin 133 := ![78,131,132]
theorem injective : Function.Injective slots := by decide
noncomputable def copyMachine := RecoveryFocus.machine slots PCPFieldMoves.readyMachine
noncomputable def firstMachine := TapeEmbedding.machine 2 RecoveryFormulaSerialize.machine
noncomputable def machine := Composition.machine firstMachine copyMachine

def input (fields : List (List Bool)) : Fin 133→List Bool :=
  fun i=>Fin.addCases (motive:=fun _=>List Bool) (RecoveryFormulaSerialize.input fields) (fun _ : Fin 2=>[]) i
def rawBudget (fields : List (List Bool)) := RecoveryFormulaSerialize.rawBudget fields+1+
  (4*(PCPTraversal.code fields).bits.length+4)

private theorem embedded_initial {s : Nat} (p : Machine 131 s) (t : Fin 131→List Bool) :
    TapeEmbedding.config (fun _ : Fin 2=>0) (fun _ : Fin 2=>[]) (initialConfiguration p t)=
      initialConfiguration (TapeEmbedding.machine 2 p) (Fin.addCases t (fun _ : Fin 2=>[])) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;>
      simp only [TapeEmbedding.config,Fin.addCases_left,Fin.addCases_right,initialConfiguration]
  · rfl

theorem copy_run {s : Nat} (r : ExecutionReceipt 131 s) (bits padding : List Bool)
    (ht : r.final.tapes 78=frame bits++padding) (hh : r.final.heads 78=0) : ∃ last,
    runFrom copyMachine (4*bits.length+4)
      (Composition.restart (TapeEmbedding.receipt (fun _ : Fin 2=>0) (fun _ : Fin 2=>[]) r).final
        copyMachine.start)=some last ∧ last.final.tapes 131=frame bits ∧ last.steps=4*bits.length+4 := by
  let first := TapeEmbedding.receipt (fun _ : Fin 2=>0) (fun _ : Fin 2=>[]) r
  obtain ⟨localOut,hlocal,hlt,hlh,hls⟩ := PCPFieldMoves.ready_run bits padding 0 0
  have hs : ∀ j,first.final.heads (slots j)=
      (initialConfiguration PCPFieldMoves.readyMachine ![frame bits++padding,[],[]]).heads j := by
    intro j
    fin_cases j
    · exact hh
    · rfl
    · rfl
  have hd : ∀ j,first.final.tapes (slots j)=
      (initialConfiguration PCPFieldMoves.readyMachine ![frame bits++padding,[],[]]).tapes j := by
    intro j
    fin_cases j
    · exact ht
    · rfl
    · rfl
  obtain ⟨last,hr,_hc,hsteps,_hheads,htapes,_hkeep⟩ := RecoveryFocus.dock slots injective
    PCPFieldMoves.readyMachine (4*bits.length+4) first.final.heads first.final.tapes
    (initialConfiguration PCPFieldMoves.readyMachine ![frame bits++padding,[],[]]) hs hd localOut hlocal
  refine ⟨last,hr,?_,hsteps.trans hls⟩
  have hout := htapes 1
  rw [hlt] at hout
  change last.final.tapes 131=RepairOrdinary.frame bits
  simpa only [slots,PCPFieldMoves.output,Matrix.cons_val_one,Matrix.cons_val_zero,ZeroPadding.pad_zero] using hout

private theorem framed_of_run {s : Nat} (p : Machine 131 s) (t : Fin 131→List Bool)
    (fuel : Nat) (base : ExecutionReceipt 131 s) (hbase : run p fuel t=some base)
    (bits : List Bool) (cap : Nat)
    (ht : base.final.tapes 78=ZeroPadding.pad cap (frame bits)) (hh : base.final.heads 78=0)
    (hs : base.steps ≤ fuel) : ∃ r,
    run (Composition.machine (TapeEmbedding.machine 2 p) copyMachine)
      (fuel+1+(4*bits.length+4)) (fun i=>Fin.addCases t (fun _ : Fin 2=>[]) i)=some r ∧
      r.final.tapes 131=frame bits ∧ r.steps ≤ fuel+1+(4*bits.length+4) := by
  let first := TapeEmbedding.receipt (fun _ : Fin 2=>0) (fun _ : Fin 2=>[]) base
  have hfirst := TapeEmbedding.run_embed p (fun _ : Fin 2=>0) (fun _ : Fin 2=>[]) _ _ base hbase
  rw [embedded_initial] at hfirst
  obtain ⟨last,hlast,hout,hsteps⟩ := copy_run base bits
    (List.replicate (cap-(frame bits).length) false) ht hh
  have hall := Composition.run_join (TapeEmbedding.machine 2 p) copyMachine fuel (4*bits.length+4)
    _ first last hfirst hlast
  refine ⟨_,hall,hout,?_⟩
  change first.steps+1+last.steps ≤ _
  dsimp only [first,TapeEmbedding.receipt]
  omega

theorem raw_run (fields : List (List Bool)) : ∃ r,
    run machine (rawBudget fields) (input fields)=some r ∧
      r.final.tapes 131=frame (PCPTraversal.code fields).bits ∧ r.steps ≤ rawBudget fields := by
  obtain ⟨base,hbase,ht,hh,hs⟩ := RecoveryFormulaSerialize.retained_run fields
  exact framed_of_run RecoveryFormulaSerialize.machine (RecoveryFormulaSerialize.input fields)
    (RecoveryFormulaSerialize.rawBudget fields) base hbase (PCPTraversal.code fields).bits
    (PCPPairReusable.capacity (mass fields)) ht hh hs

def budget (fields : List (List Bool)) := 1000000000064*((FieldList.stream fields).length+1)^12

theorem budget_bound (fields : List (List Bool)) : rawBudget fields ≤ budget fields := by
  have hb := PCPSerializerMass.code_bits fields
  change (PCPTraversal.code fields).bits.length ≤ 3*(mass fields+1)^5 at hb
  have hm := PCPTraversal.stream_mass fields
  rw [←hm] at hb
  have hp : 1 ≤ ((FieldList.stream fields).length+1)^12 := Nat.one_le_pow _ _ (by omega)
  have hl : (FieldList.stream fields).length+1 ≤ ((FieldList.stream fields).length+1)^12 :=
    Nat.le_self_pow (by decide) _
  have h5 : ((FieldList.stream fields).length+1)^5 ≤ ((FieldList.stream fields).length+1)^12 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  simp only [rawBudget,RecoveryFormulaSerialize.rawBudget,RecoveryFormulaSerialize.prepareBudget,
    PCPTraversal.budget,budget,←hm]
  omega

end NearCubicWires.RepairSource.RecoveryFormulaFrame
