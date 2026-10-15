import Proof.SourceAssembly.SourceNativeList

/- The actual decomposition loop already manufactures and retains the count
needed by the exact native-field copy. Expose it from the same executed code. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyCountDriver
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
noncomputable section
attribute [local irreducible] Cold.machine Cold.entryMachine Cold.batch batchMachine Prelude.occurrences FinalLayout.machine

theorem batch_driver (a : DecompositionAlgorithm) {q : Nat} (C : Nat)
    (occ : List (SupportedNormalizedGate q)) (top : List Bool)
    (hheader : PCPPQueryNatural.budget occ.length<C)
    (hbody : ∀g∈occ,bodyCost a q g<C)
    (hn : ExtDecompositionBatch.B a occ+2≤C)
    (hh : PCPPNativeNaturalAppend.budget (ExtDecompositionBatch.B a occ)≤C)
    (hb : (bodyWord a occ).length≤C) (hc : (exactListWord (GS a occ)).length≤C) :
    ∃ H O,Step (batchMachine a) (batchBudget a C occ top)
      (Prelude.inputHeads a) (Prelude.inputTapes a C q (segment occ top)) H O ∧
      H (Prelude.driverSlot a)=1 ∧ O (Prelude.driverSlot a)=UnaryTemplate.tape occ.length := by
  have first:=Prelude.occurrences_run a C q occ top hheader hbody
  obtain ⟨O,finish,_⟩:=final_state_run a C occ (segment occ top).length
    (segment occ top) hn hh hb hc
  have second:=(finish.embed (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate C false)).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>UnaryTemplate.tape occ.length)
  refine ⟨Fin.addCases (Fin.addCases (FinalLayout.finishedHeads a (GS a occ)
    (loopHeads a (segment occ top).length (countWord a occ) (bodyWord a occ) (totalWord a occ)))
    (fun _ : Fin 1=>0)) (fun _ : Fin 1=>1),
    Fin.addCases (Fin.addCases O (fun _ : Fin 1=>List.replicate C false))
      (fun _ : Fin 1=>UnaryTemplate.tape occ.length),?_,?_,?_⟩
  · simpa only [batchMachine,batchBudget,finalMachine] using first.seq second
  all_goals simp only [show Prelude.driverSlot a=(0 : Fin 1).natAdd (CT a) from by apply Fin.ext;rfl,Fin.addCases_right]

def port (a : DecompositionAlgorithm) := Cold.old a (Prelude.driverSlot a)

theorem cold_driver (a : DecompositionAlgorithm) {q : Nat} (P : Nat)
    (occ : List (SupportedNormalizedGate q)) (top : List Bool)
    (hq : q≤P) (hi : (segment occ top).length≤1000*(P+2)^2) :
    ∃ H O,Step (Cold.machine a) (Cold.budget a P occ top)
      (Cold.heads a (segment occ top).length) (Cold.data a P q (segment occ top)) H O ∧
      H (port a)=1 ∧ O (port a)=UnaryTemplate.tape occ.length := by
  obtain ⟨A,entry,ea⟩:=Cold.entry_run a P q (segment occ top).length (segment occ top)
    (SourceEnvelope.source_position a occ top P hi)
  obtain ⟨body,hn,hh,hb,hc,header⟩:=SourceEnvelope.actual_capacity a occ top P hq hi
  obtain ⟨H,O,run,dh,dt⟩:=batch_driver a (SourceEnvelope.capacity a P) occ top header body hn hh hb hc
  have worker:=run.dock (Cold.old a) (Cold.old_injective a) (Cold.heads a 0) A (Cold.entry_heads a) ea
  refine ⟨dockH (Cold.old a) (Cold.heads a 0) H,install (Cold.old a) A O,?_,?_,?_⟩
  · simpa only [Cold.machine,Cold.batch,Cold.budget] using entry.seq worker
  · exact (dockH_slot (Cold.old a) (Cold.old_injective a) _ _ (Prelude.driverSlot a)).trans dh
  · exact (install_slot (Cold.old a) (Cold.old_injective a) _ _ (Prelude.driverSlot a)).trans dt

theorem retained (a : DecompositionAlgorithm) {q : Nat} (P : Nat)
    (occ : List (SupportedNormalizedGate q)) (top : List Bool)
    (hq : q≤P) (hi : (segment occ top).length≤1000*(P+2)^2)
    (H : Fin (Cold.tapes a)→Nat) (O : Fin (Cold.tapes a)→List Bool)
    (paid : Step (Cold.machine a) (Cold.budget a P occ top)
      (Cold.heads a (segment occ top).length) (Cold.data a P q (segment occ top)) H O) :
    H (port a)=1 ∧ O (port a)=UnaryTemplate.tape occ.length := by
  obtain ⟨HH,OO,run,dh,dt⟩:=cold_driver a P occ top hq hi
  obtain ⟨r₁,hr₁,rh₁,rt₁,_⟩:=paid
  obtain ⟨r₂,hr₂,rh₂,rt₂,_⟩:=run
  have he : r₁=r₂ := Option.some.inj (hr₁.symm.trans hr₂)
  subst r₂
  have hh := rh₁.symm.trans rh₂
  have ht := rt₁.symm.trans rt₂
  rw [hh,ht]
  exact ⟨dh,dt⟩

end
end SourceAssemblyCountDriver
