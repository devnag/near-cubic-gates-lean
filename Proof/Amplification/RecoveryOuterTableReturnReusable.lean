import Proof.Amplification.RecoveryOuterTableReturnKernel

/-! Abstract reusable endpoint for the actual Boolean-return wrapper. All
source execution, result and data-update premises are consumed explicitly. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterTableReturn
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reusable_run {α : Type} {s : Nat} (p : Machine 85 s) (result : Fin s → Bool)
    (fuel : Nat) (source : Configuration 85 s) (first : ExecutionReceipt 85 s)
    (hr : runFrom p fuel source=some first) (old answer : Bool)
    (hh : first.final.heads 50=0) (ht : first.final.tapes 50=[old])
    (ha : result first.final.control=answer)
    (heads : α → Fin 85 → Nat) (tapes : α → Fin 85 → List Bool) (update : α → α) (Inv : α → Prop)
    (huH : ∀ x,heads (update x)=heads x)
    (huT : ∀ x,tapes (update x)=Function.update (tapes x) 50 [true])
    (huI : ∀ x,Inv x → Inv (update x))
    (hout : answer=true → ∃ x,first.final.heads=heads x ∧ first.final.tapes=tapes x ∧ Inv x) :
    ∃ r,runFrom (machine p result) (fuel+3)
        (controlConfig (RecoveryCalls.code (sizes s) 0) source)=some r ∧
      r.steps ≤ fuel+3 ∧ r.final.heads 50=0 ∧ r.final.tapes 50=[answer] ∧
      (answer=true → ∃ x,r.final=⟨r.final.control,heads x,tapes x⟩ ∧ Inv x) := by
  obtain ⟨r,hrun,hb,hf⟩ := return_run p result fuel source first hr old hh ht
  have hheads : r.final.heads=first.final.heads := congrArg Configuration.heads hf
  have htapes : r.final.tapes=Function.update first.final.tapes 50 [answer] :=
    (congrArg Configuration.tapes hf).trans (congrArg (fun b=>Function.update first.final.tapes 50 [b]) ha)
  refine ⟨r,hrun,hb,?_,?_,?_⟩
  · rw [hheads]; exact hh
  · rw [htapes]; simp only [Function.update_self]
  · intro htrue
    obtain ⟨x,hxH,hxT,hxI⟩ := hout htrue
    refine ⟨update x,?_,huI x hxI⟩
    apply configuration_ext
    · rfl
    · change r.final.heads=heads (update x)
      rw [huH]
      exact hheads.trans hxH
    · change r.final.tapes=tapes (update x)
      rw [huT,←hxT,htapes,htrue]

end NearCubicWires.RepairOrdinary.RecoveryOuterTableReturn
