import Proof.Amplification.RecoveryRowCountAutomaton

/-! Four-tape ordinary carry checker for parent, left and right counts. Each
iteration reads one bit of all three retained fixed-width words; six Boolean
registers are finite control, not uncharged arithmetic operations. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowCounts
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Control := (State×Bool)⊕Unit
noncomputable def code : Control≃Fin (Fintype.card Control) := Fintype.equivFin _
noncomputable def scanCode (s : State) := code (.inl (s,false))
noncomputable def bitCode (s : State) := code (.inl (s,true))
noncomputable def haltCode := code (.inr ())
noncomputable def machine : Machine 4 (Fintype.card Control) where
  descriptionBits := 0
  start := scanCode initial
  halted := fun q=>(code.symm q).isRight
  rule := fun q scanned=>match code.symm q with
    | .inl (s,false)=>if scanned 0 then
        some ⟨bitCode s,fun _=>none,fun i=>if i=3 then .stay else .right⟩
      else some ⟨haltCode,fun i=>if i=3 then some (finish s) else none,fun _=>.stay⟩
    | .inl (s,true)=>some ⟨scanCode (advance s (scanned 0) (scanned 1) (scanned 2)),
        fun _=>none,fun i=>if i=3 then .stay else .right⟩
    | .inr _=>none

def cfg (q : Fin (Fintype.card Control)) (parent left right : List Bool)
    (p l r : Nat) (old : Bool) : Configuration 4 (Fintype.card Control) :=
  ⟨q,![p,l,r,0],![parent,left,right,[old]]⟩

theorem scan_halted (s : State) : machine.halted (scanCode s)=false := by
  simp [machine,scanCode]
theorem bit_halted (s : State) : machine.halted (bitCode s)=false := by
  simp [machine,bitCode]
theorem halt_halted : machine.halted haltCode=true := by simp [machine,haltCode]

theorem marker_step (s : State) (parent left right : List Bool) (p l r : Nat) (old : Bool)
    (h : readTapeBit parent p=true) :
    step machine (cfg (scanCode s) parent left right p l r old)=
      some (cfg (bitCode s) parent left right (p+1) (l+1) (r+1) old) := by
  simp only [step,machine,scanCode,Equiv.symm_apply_apply,Configuration.scanned,cfg,Matrix.cons_val_zero,h,↓reduceIte,Option.map_some]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem bit_step (s : State) (parent left right : List Bool) (p l r : Nat) (old a b c : Bool)
    (hp : readTapeBit parent p=a) (hl : readTapeBit left l=b) (hr : readTapeBit right r=c) :
    step machine (cfg (bitCode s) parent left right p l r old)=
      some (cfg (scanCode (advance s a b c)) parent left right (p+1) (l+1) (r+1) old) := by
  simp [step,machine,bitCode,Configuration.scanned,cfg,hp,hl,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem stop_step (s : State) (parent left right : List Bool) (p l r : Nat) (old : Bool)
    (h : readTapeBit parent p=false) :
    step machine (cfg (scanCode s) parent left right p l r old)=
      some (cfg haltCode parent left right p l r (finish s)) := by
  simp only [step,machine,scanCode,Equiv.symm_apply_apply,Configuration.scanned,cfg,Matrix.cons_val_zero,h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryRowCounts
