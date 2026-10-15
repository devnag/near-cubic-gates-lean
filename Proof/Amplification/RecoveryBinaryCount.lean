import Proof.Amplification.RecoveryWidthEntry
import Proof.Hierarchy.HierarchyInputLength

/-! Execute the accepted binary length counter beside the physically
produced width driver. The original code and width-head1 cursor are
retained, and all counter scratch and rewinds are paid. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdBinaryCount
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4→Fin 5 := ![2,3,0,4]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_eq (i : Fin 5) : RecoveryFocus.pick slots i=![some 2,none,some 0,some 1,some 3] i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot slots slots_injective 2
  · have hn : ¬∃ j,slots j=(1 : Fin 5) := by decide
    simp [RecoveryFocus.pick,hn]
  · exact RecoveryFocus.pick_slot slots slots_injective 0
  · exact RecoveryFocus.pick_slot slots slots_injective 1
  · exact RecoveryFocus.pick_slot slots slots_injective 3
noncomputable def machine := RecoveryFocus.machine slots HierarchyInputLength.machine
def heads : Fin 5→Nat := ![0,1,0,0,0]
def input (bits : List Bool) : Fin 5→List Bool :=
  ![frame bits,RecoveryColdWidth.word (RecoveryColdWidth.width bits.length),[],[],[]]
def output (bits : List Bool) (cap scratch : Nat) : Fin 5→List Bool :=
  ![frame bits,RecoveryColdWidth.word (RecoveryColdWidth.width bits.length),
    frame (ClockBinary.word bits.length),List.replicate cap false,List.replicate scratch false]

theorem count_run (bits : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
    ∃ r,runFrom machine (HierarchyInputLength.budget bits) ⟨machine.start,heads,input bits⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=output bits cap scratch ∧ r.steps ≤ HierarchyInputLength.budget bits := by
  obtain ⟨cap,scratch,hcap,hscratch,base,hbase,h0,h1,h2,h3,hh,ht⟩ := HierarchyInputLength.count_run bits
  obtain ⟨r,hr,hf,hsteps⟩ := RecoveryFocus.run_config slots slots_injective HierarchyInputLength.machine
    heads (input bits) (HierarchyInputLength.budget bits) _ base hbase
  have hi : RecoveryFocus.config slots heads (input bits)
      (initialConfiguration HierarchyInputLength.machine (HierarchyInputLength.input bits))=
      (⟨machine.start,heads,input bits⟩ : Configuration 5 _) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [RecoveryFocus.config,pick_eq,heads,initialConfiguration]
    · funext i
      fin_cases i <;> simp [RecoveryFocus.config,pick_eq,input,initialConfiguration,
        HierarchyInputLength.input,ClockLengthReady.source,ClockLengthReady.input,Fin.addCases]
  rw [hi] at hr
  refine ⟨cap,scratch,hcap,hscratch,r,hr,?_,?_,hsteps.le.trans ht⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_eq,heads,hh]
  · rw [hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_eq,input,output,h0,h1,h2,h3]

end NearCubicWires.RepairOrdinary.RecoveryColdBinaryCount
