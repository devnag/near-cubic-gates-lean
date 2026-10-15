import Proof.SourceAssembly.SourceSymmetricTopReady

/- The actual selected count prints both native TOP and native bottom-count
header. Only the selected Compare driver is nonblank at entry. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricHeader
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound RepairSource.VerifierDecoding
noncomputable section

def slots (i : Fin 22) : Fin 26:=if i=0 then 2 else ⟨i.val+4,by omega⟩
theorem slots_inj : Function.Injective slots:=by decide
def first:=TapeEmbedding.machine 21 SourceAssemblySymmetricTopReady.machine
def last:=RecoveryFocus.machine slots Natural.machine
def machine:=Composition.machine first last
def heads (i : Fin 26):=if i=3 then 1 else 0
def input (n : Nat) : Fin 26→List Bool:=fun i=>if i=3 then CompareMachine.word n else []
def budget (n : Nat):=SourceAssemblySymmetricTopReady.budget n+1+Natural.budget n

theorem run (n : Nat) : ∃ A,Step machine (budget n) heads (input n) (fun _=>0) A ∧
    A 1=frame (SourceAssemblySymmetricTop.table n) ∧A 21=natWord n ∧
    A 24=frame (natWord n) ∧A 3=CompareMachine.word n := by
  obtain ⟨B,hb,top,raw,count⟩:=SourceAssemblySymmetricTopReady.run n
  let bank : Fin 26→List Bool:=Fin.addCases (motive:=fun _=>List Bool) B (fun _ : Fin 21=>[])
  have stepB : Step first (SourceAssemblySymmetricTopReady.budget n)
      heads (input n) (fun _=>0) bank :=
    ((hb.embed (fun _ : Fin 21=>0) (fun _=>[])).congr_in
      (by funext i;fin_cases i <;>rfl) (by funext i;fin_cases i <;>rfl)).congr
      (by funext i;fin_cases i <;>rfl) rfl
  obtain ⟨D,hd,d20,d17⟩:=SourceAssemblyParityNatural.cold_run n
  have selected : ∀ i,bank (slots i)=Natural.source n i := by
    intro i;fin_cases i
    · exact raw
    all_goals rfl
  obtain ⟨r,hr,rt,rh,rs⟩:=hd.focus slots slots_inj bank selected
  have stepD : Step last (Natural.budget n) (fun _=>0) bank (fun _=>0) (install slots bank D):=
    ⟨r,hr,funext rh,rt,rs⟩
  refine ⟨install slots bank D,stepB.seq stepD,?_,?_,?_,?_⟩
  · exact (install_other slots bank D 1 (by decide)).trans top
  · exact (install_slot slots slots_inj bank D 17).trans d17
  · exact (install_slot slots slots_inj bank D 20).trans d20
  · exact (install_other slots bank D 3 (by decide)).trans count

end
end SourceAssemblySymmetricHeader
