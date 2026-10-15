import Proof.Amplification.RecoveryTseitinNativeRead

/-! Convert both original native operand templates to the physical unary
inputs of the ordinary reference producer, retaining the source and tag. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def argMachine (right : Bool) := RecoveryFocus.machine (argSlots right) PCPPNativeTemplateRaw.machine
theorem arg_disjoint (right : Bool) : ∀ i j,argSlots right i≠argSlots (!right) j := by cases right <;> decide

theorem arg_run {s : Nat} (right : Bool) (n : Nat) (ambient : Configuration 1099 s)
    (h0 : ambient.tapes (argSlots right 0)=UnaryTemplate.tape n)
    (hh0 : ambient.heads (argSlots right 0)=1)
    (hb : ∀ j,j≠0 → ambient.tapes (argSlots right j)=[] ∧ ambient.heads (argSlots right j)=0) :
    ∃ r,runFrom (argMachine right) (4*n+16) (Composition.restart ambient (argMachine right).start)=some r ∧
      r.steps=4*n+16 ∧ r.final.tapes (argSlots right 0)=UnaryTemplate.tape n ∧
      r.final.tapes (argSlots right 1)=List.replicate n true ∧
      (∀ j,r.final.heads (argSlots right j)=PCPPNativeTemplateRaw.heads j) ∧
      (∀ i,(∀ j,argSlots right j≠i) → r.final.tapes i=ambient.tapes i ∧ r.final.heads i=ambient.heads i) := by
  obtain ⟨base,hbase,bs,b0,b1,_b2,_b3,bh⟩:=PCPPNativeTemplateRaw.template_run n
  obtain ⟨r,hr,_rc,rs,rh,rt,ro⟩:=RecoveryFocus.dock (argSlots right) (arg_injective right)
    PCPPNativeTemplateRaw.machine _ ambient.heads ambient.tapes _
    (by
      intro j
      fin_cases j
      · exact hh0
      all_goals exact (hb _ (by decide)).2)
    (by
      intro j
      fin_cases j
      · exact h0
      all_goals exact (hb _ (by decide)).1) base hbase
  refine ⟨r,hr,rs.trans bs,(rt 0).trans b0,(rt 1).trans b1,?_,?_⟩
  · intro j
    rw [rh,bh]
  · intro i hi
    have h:=ro i hi
    exact ⟨h.2,h.1⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative
