import Proof.CaseAnalysis.CommonPrefixProgram

/-! All-input composition of the actual ordinary refuter prefix with the
paid common preparation. The original flag/query bank is retained by sparse
focus; the final address enters on literal ordinary tape zero. -/
namespace NearCubicWires.RepairSource.CloseoutCommonPrefix
open LocalBitMultitape RepairOrdinary CloseoutSchedule CloseoutRetainedRefuter
open OrdinaryOracleCompose RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem prefix_run (sources : EightSources) (k D copies As Bs onset Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (r : OrdinaryOracleProgram)
    (bits result : List Bool) (fuel : ℕ)
    (a : Fin (base (Step.workTapes sources k D) r)→List Bool)
    (hpre : Ready RecoveryOracle.correctedSat
      (RefuterPrefix.selectedProgram sources k D copies clock As Bs onset r) fuel
      (CloseoutRetainedRefuter.input r (Guarded.input (Step.workTapes sources k D) bits)) a)
    (ha : a (address (Step.workTapes sources k D) r)=frame bits)
    (hb : a (answer (Step.workTapes sources k D) r)=frame result) :
    let w:=Step.workTapes sources k D
    let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
    ∃ cost≤fuel+CloseoutCommonPrepare.budget k H.coefficient Aw Bw bits result+2,∃ out,
      Ready RecoveryOracle.correctedSat (program sources k D copies As Bs onset Aw Bw clock r)
        cost (input w r k bits) out ∧
      out (firstSlots w r k (address w r))=frame bits ∧
      out (prepareSlots w r k (CloseoutCommonPrepare.capacitySlot k))=
        List.replicate (CloseoutCapacity.capacity Aw Bw bits.length) true ∧
      out (prepareSlots w r k (CloseoutCommonPrepare.hierarchySlot k))=
        frame result++frame (H.time result.length).bits ∧
      ∀ i : Fin (base w r),i≠address w r → i≠answer w r →
        out (firstSlots w r k i)=a i:=by
  let w:=Step.workTapes sources k D
  let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
  let ps:=ports w r k
  let parts:=pieces sources k D copies As Bs onset Aw Bw clock r
  let follow:=next sources k D copies As Bs onset Aw Bw clock r
  let middle:=install (firstSlots w r k) (input w r k bits) a
  have hfirst:=hpre.focus ps (firstSlots w r k) (first_injective w r k) rfl
    (input w r k bits) (initial_first w r k bits)
  obtain ⟨prepared,hp,haddress,hW,hword⟩:=CloseoutCommonPrepare.run H Aw Bw bits result
  have hfocus:=hp.focus (prepareSlots w r k) (prepare_injective w r k) middle
    (middle_input w r k bits result a ha hb)
  obtain ⟨c,hc,hlast⟩:=RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat)
    ps _ _ _ hfocus
  have ta:=hfirst.call ps parts 0 follow 0 1 (by intro q; rfl)
  have tb:=hlast.stop ps parts 0 follow 1 (by intro q; rfl)
  have ht:=trans ta tb
  have hi : controlConfig (RecoveryCalls.code (fun j=>(parts j).states) 0)
      (initialConfiguration (parts 0).machine (input w r k bits))=
      initialConfiguration (program sources k D copies As Bs onset Aw Bw clock r).base.machine
        (input w r k bits):=rfl
  rw [hi] at ht
  refine ⟨(fuel+1)+(c+1),by dsimp only [H] at hc; omega,_,⟨_,ht,?_,fun _=>rfl,rfl⟩,?_,?_,?_,?_⟩
  · simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped,parts]
  · rw [←prepare_address]
    exact (install_slot _ (prepare_injective w r k) _ _ _).trans haddress
  · exact (install_slot _ (prepare_injective w r k) _ _ _).trans hW
  · exact (install_slot _ (prepare_injective w r k) _ _ _).trans hword
  · intro i hai hbi
    exact (install_other _ _ _ _ (prepare_ne_old w r k i hai hbi)).trans
      (install_slot _ (first_injective w r k) _ _ i)

end
end NearCubicWires.RepairSource.CloseoutCommonPrefix
