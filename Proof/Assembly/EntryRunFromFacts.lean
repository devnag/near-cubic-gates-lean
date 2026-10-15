import Proof.MachineModel.TopDownWorkspaceSelectedEntryReady

/-! Factor the existing physical entry execution through its actual input
facts. The fixed program, execution budget, output heads and installed bank
are unchanged; no admission or entry Step is added as a premise. -/
namespace EntryRunFactoring
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration CanonicalWitnessCodec
open WorkspaceSelectedAdmission (originalTapes capacity)
open WorkspaceSelectedProgram (finalBank)
open WorkspaceSelectedEntry (size output outputHeads)
open RecoveryRootRound
open WorkspaceSelectedEntryReady
open private NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.cache_injective from Proof.CaseAnalysis.FinalAdmittedEntry
open private NearCubicWires.P1TopDown.WorkspaceSelectedOriginals.tapes_unique from Proof.MachineModel.TopDownWorkspaceSelectedOriginals
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem run_from_facts :
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.P1TopDown NearCubicWires.P1TopDown.WorkspaceSelectedEntryReady NearCubicWires.P1TopDown.WorkspaceSelectedAdmission NearCubicWires.P1TopDown.WorkspaceSelectedProgram NearCubicWires.RepairSource.SelectedRecoveryIntegration NearCubicWires.RepairOrdinary.CloseoutWitness NearCubicWires.CanonicalWitnessCodec NearCubicWires.RepairRepresentation in
∀ (sources : EightSources) (gamma : Real) (p : Parameters sources gamma) (k r extra : Nat) (hspace : WorkspaceSelectedEntry.size sources k r p.clauseDegree+96≤extra)
    (n : Nat) (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k)→List Bool) (L : Nat)
    (_ho : WorkspaceSelectedOriginals.Originals sources p k x bits A)
    (_hc : WorkspaceSelectedAdmission.Cached sources p k (PolynomialClock.ordinaryClock k) x bits A),
    let source:=fixedProjection sources
    let a:=CloseoutLanguage.selectedPCPP sources
    let CH:=(SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
    let Cpad:=padding sources k (PolynomialClock.ordinaryClock k)
    let code:=SelectedSource.code sources k (PolynomialClock.ordinaryClock k)
    ∃ oracle,decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
        (RadixSemantics.value (BoundedFields.oracle bits))=some oracle ∧
      oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound p.degree
        (SelectedOracle.width source k CH Cpad code (List.ofFn x)) ∧
      let rq:=ColdNative.request source a k CH Cpad code x (Nat.le_max_right _ _) oracle
      ∃ w out,Step (WorkspaceSelectedEntryReady.program sources p k r extra hspace).2
        (C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n+
          WorkspaceSelectedEntryCount.budget a rq (C10PartsSchedule.entryWidthSchedule sources k r n)+5)
        (fun _=>0) (finalBank A L extra) (finalHeads sources p k r extra hspace)
        (RecoveryRootRound.install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
          (post sources p k r extra hspace A L n (List.ofFn x) bits w) out) ∧
      RecoveryRootRound.install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
        (post sources p k r extra hspace A L n (List.ofFn x) bits w) out
        (driver sources p k r extra hspace)=UnaryTemplate.tape (2^(a.output rq).clauseBits) ∧
      (∀j,RecoveryRootRound.install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
        (post sources p k r extra hspace A L n (List.ofFn x) bits w) out
        (initPort sources p k r extra hspace (BoundedFields.symmetric bits) (WorkspaceSelectedEntryCount.cache j))=
          WorkspaceSelectedEntryCount.cacheData a rq j) ∧
      out (WorkspaceSelectedEntryCount.count 28)=UnaryTemplate.tape (a.output rq).systematicBits ∧
      out (WorkspaceSelectedEntryCount.count 72)=List.replicate (2^(a.output rq).clauseBits) true ∧
      out (WorkspaceSelectedEntryCount.append 0)=List.replicate (C10PartsSchedule.entryWidthSchedule sources k r n) true ∧
      out (WorkspaceSelectedEntryCount.append 20)=UnaryTemplate.tape (20*C10PartsSchedule.entryWidthSchedule sources k r n+22) ∧
      out (WorkspaceSelectedEntryCount.append 39)=List.replicate
        (CloseoutFinalC10AppendWorkspaceInit.capacity (C10PartsSchedule.entryWidthSchedule sources k r n)) false ∧
      out (WorkspaceSelectedEntryCount.append 40)=List.replicate
        (CloseoutFinalC10AppendWorkspaceInit.capacity (C10PartsSchedule.entryWidthSchedule sources k r n)) false := by
  intro sources gamma p k r extra hspace n x bits A L ho hc source a CH Cpad code
  obtain ⟨_oldH,oracle,hdecode,hsize,fields⟩:=hc
  let rq:=ColdNative.request source a k CH Cpad code x (Nat.le_max_right _ _) oracle
  have cacheBytes:∀j,A (cache sources p k (BoundedFields.symmetric bits) j)=WorkspaceSelectedEntryCount.cacheData a rq j :=
    fun j=>(fields j).1
  obtain ⟨w,hpre,_keep⟩:=WorkspaceSelectedEntry.run sources p k r extra (by omega) n x bits A L ho
  have ci:=NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.cache_injective source a k p.clauseDegree p.degree
    (capacity sources p).E (BoundedFields.symmetric bits)
  obtain ⟨out,hin,cacheKeep,actualCount,_raw,_recordWidth,_keep⟩:=WorkspaceSelectedEntryInit.run_init
    sources k r p.clauseDegree n (originalTapes sources p k) extra (old_size sources p k) hspace
    A L (List.ofFn x) bits w (cache sources p k (BoundedFields.symmetric bits)) ci a rq ho.1 ho.2.1 cacheBytes
  obtain ⟨rich,hrich,_richCache,sys,_template,raw,width,recordWidth,log1,log2,_richOther⟩:=
    WorkspaceSelectedEntryCount.run a rq (C10PartsSchedule.entryWidthSchedule sources k r n)
  have ready:=WorkspaceSelectedEntryInit.input_ready sources k r p.clauseDegree n
    (originalTapes sources p k) extra (old_size sources p k) hspace A L (List.ofFn x) bits w
    (cache sources p k (BoundedFields.symmetric bits)) (WorkspaceSelectedEntryCount.cacheData a rq)
    ho.1 ho.2.1 cacheBytes
  have mapInj:=WorkspaceSelectedEntryInit.ports_injective (size sources k r p.clauseDegree)
    (by dsimp [size];omega) hspace (cache sources p k (BoundedFields.symmetric bits)) ci
  have replay:=(hrich.dock (initPort sources p k r extra hspace (BoundedFields.symmetric bits)) mapInj
    (heads sources p k r extra hspace) (post sources p k r extra hspace A L n (List.ofFn x) bits w)
    (fun i=>(ready i).1) (fun i=>(ready i).2)).congr
      (dockH_existing _ _ _ (fun i=>(ready i).1)) rfl
  have same:=NearCubicWires.P1TopDown.WorkspaceSelectedOriginals.tapes_unique hin replay
  have outEq:out=rich:=by
    funext i
    exact (install_slot _ mapInj _ out i).symm.trans ((congrFun same _).trans (install_slot _ mapInj _ rich i))
  have modeTape : post sources p k r extra hspace A L n (List.ofFn x) bits w (modePort sources p k extra)=
      [BoundedFields.symmetric bits] :=
    (WorkspaceSelectedEntryFacts.old_bank_retained sources k r p.clauseDegree n _ extra (old_size sources p k)
      (by omega) A L (List.ofFn x) bits w ho.1 ho.2.1 _).trans ho.2.2
  have modeHead : heads sources p k r extra hspace (modePort sources p k extra)=0 :=
    WorkspaceSelectedEntryInit.old_heads_zero sources k r p.clauseDegree _ extra (old_size sources p k) (by omega) _
  have readMode : readTapeBit (post sources p k r extra hspace A L n (List.ofFn x) bits w (modePort sources p k extra))
      (heads sources p k r extra hspace (modePort sources p k extra))=BoundedFields.symmetric bits := by
    rw [modeTape,modeHead];rfl
  have switched : Step (initializer sources p k r extra hspace)
      (WorkspaceSelectedEntryCount.budget a rq (C10PartsSchedule.entryWidthSchedule sources k r n)+2)
      (heads sources p k r extra hspace) (post sources p k r extra hspace A L n (List.ofFn x) bits w)
      (heads sources p k r extra hspace)
      (install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
        (post sources p k r extra hspace A L n (List.ofFn x) bits w) out) := by
    cases hm:BoundedFields.symmetric bits
    · rw [hm] at hin readMode
      exact CloseoutRowsOriginalSwitch.false_run _ _ _ hin readMode
    · rw [hm] at hin readMode
      exact CloseoutRowsOriginalSwitch.true_run _ _ _ hin readMode
  have last:=switched.seq (bump_run sources p k r extra hspace _)
  have whole:=hpre.seq last
  refine ⟨oracle,hdecode,hsize,w,out,?_,?_,cacheKeep,?_,?_,?_,?_,?_,?_⟩
  · unfold program
    exact whole.enlarge (by dsimp only [rq];omega)
  · exact (congrArg (fun i=>install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
      (post sources p k r extra hspace A L n (List.ofFn x) bits w) out i)
      (driver_at_init sources p k r extra hspace (BoundedFields.symmetric bits)).symm).trans actualCount
  all_goals rw [outEq]
  · exact sys
  · exact raw
  · exact width
  · exact recordWidth
  · exact log1
  · exact log2

end
end EntryRunFactoring
