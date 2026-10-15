import Proof.PCP.PCPPNativeQueryAdvance

/-! One query body followed by actual shared-DAG base advancement. Both
base and current-position counters become the first node of the next query. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryStep
open LocalBitMultitape SourceInterfaces RecoveryRootRound PCPPNativeQuery PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advanceSlots : Fin 3 → Fin 168 := ![3,2,6]
theorem advance_injective : Function.Injective advanceSlots := by decide
noncomputable def advance := RecoveryFocus.machine advanceSlots PCPPNativeQueryAdvance.machine
noncomputable def machine := Composition.machine PCPPNativeQuery.body advance
def budget {n : ℕ} (base C F : ℕ) (oracle : BooleanCircuit n) :=
  PCPPNativeQuery.budget base C F oracle+1+(2*(base+2*oracle.size)+4)
noncomputable def entry (bits queries : List Bool) (base C F : ℕ) (out : List Bool) :=
  (⟨machine.start,PCPPNativeQuery.heads 0 out,PCPPNativeQuery.data bits queries base base C F out⟩ : Configuration 168 _)

theorem advance_install (bits queries : List Bool) (cursor base position C F : ℕ) (out : List Bool)
    (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool)
    (hlow : lowFrame bits queries cursor base position C F out ah atapes) :
    lowFrame bits queries cursor (position+1) (position+1) C F out ah
      (install advanceSlots atapes ![List.replicate (position+1) true,List.replicate (position+1) true,List.replicate F false]) := by
  intro i
  refine ⟨(hlow i).1,?_⟩
  by_cases h2 : i=2
  · subst i
    change install advanceSlots _ _ (advanceSlots 1)=_
    rw [install_slot advanceSlots advance_injective]
    rfl
  · by_cases h3 : i=3
    · subst i
      change install advanceSlots _ _ (advanceSlots 0)=_
      rw [install_slot advanceSlots advance_injective]
      rfl
    · by_cases h6 : i=6
      · subst i
        change install advanceSlots _ _ (advanceSlots 2)=_
        rw [install_slot advanceSlots advance_injective]
        rfl
      · rw [install_other advanceSlots _ _ (i.castAdd 46) (by
          intro j
          fin_cases j
          · intro h; apply h3; apply Fin.ext; exact (congrArg (fun k : Fin 168 => k.val) h).symm
          · intro h; apply h2; apply Fin.ext; exact (congrArg (fun k : Fin 168 => k.val) h).symm
          · intro h; apply h6; apply Fin.ext; exact (congrArg (fun k : Fin 168 => k.val) h).symm)]
        simpa only [PCPPNativeNodeReusable.data,h2,h3,ite_false] using (hlow i).2

theorem advance_run (bits queries : List Bool) (cursor base position C F : ℕ) (out : List Bool)
    (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool)
    (hlow : lowFrame bits queries cursor base position C F out ah atapes)
    (hbase : base ≤ position) (hF : position+1 ≤ F) :
    ∃ result,runFrom advance (2*position+4) ⟨advance.start,ah,atapes⟩=some result ∧
      result.steps=2*position+4 ∧
      lowFrame bits queries cursor (position+1) (position+1) C F out result.final.heads result.final.tapes := by
  have ready := PCPPNativeQueryAdvance.advance_ready position base F hbase hF
  obtain ⟨result,run,rh,rt,rs⟩ := ready.focus_at advanceSlots advance_injective ah atapes
    (by intro j; fin_cases j
        · exact (hlow 3).2
        · exact (hlow 2).2
        · exact (hlow 6).2)
    (by intro j; fin_cases j
        · exact (hlow 3).1
        · exact (hlow 2).1
        · exact (hlow 6).1)
  refine ⟨result,run,rs,?_⟩
  rw [rh,rt]
  exact advance_install bits queries cursor base position C F out ah atapes hlow

theorem step_run {n r : ℕ} (base C F : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hw : PCPPNativeNodeLoop.workspace base 0 C F projection oracle.nodes)
    (hC : PCPPNativeAddressAppend.budget base oracle.output.val+1 ≤ C) (hF : base+2*oracle.size+1 ≤ F) :
    ∃ result,runFrom machine (budget base C F oracle)
      (entry (PCPPNative.descriptor oracle) (rowCache projection) base C F out)=some result ∧
      result.steps ≤ budget base C F oracle ∧
      lowFrame (PCPPNative.descriptor oracle) (rowCache projection) (PCPPNative.descriptor oracle).length
        (base+2*oracle.size+1) (base+2*oracle.size+1) C F (out++emitted base oracle projection)
        result.final.heads result.final.tapes := by
  obtain ⟨a,ha,as,alow,_ai,_aih,_aa,_aah,_ac,_ach⟩ := body_run base C F oracle projection out hCF hw hC
  obtain ⟨b,hb,bs,blow⟩ := advance_run (PCPPNative.descriptor oracle) (rowCache projection)
    (PCPPNative.descriptor oracle).length base (base+2*oracle.size) C F (out++emitted base oracle projection)
    a.final.heads a.final.tapes alow (by omega) hF
  let result := Composition.joinedReceipt a b
  have hr := Composition.run_join PCPPNativeQuery.body advance _ _ _ a b ha hb
  refine ⟨result,hr,?_,blow⟩
  change a.steps+1+b.steps ≤ _
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.PCPPNativeQueryStep
