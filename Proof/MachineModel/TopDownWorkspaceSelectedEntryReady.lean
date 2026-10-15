import Proof.MachineModel.TopDownWorkspaceSelectedEntryInit
import Proof.CaseAnalysis.RowsOriginalSwitch

/-! Original admitted data supplies one fixed prologue plus physically selected
cache-count/append initializer. The count comes from the original PCPP header,
not the prologue's envelope. The repeat driver receives its paid head bump. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryReady
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration CanonicalWitnessCodec
open WorkspaceGuardedWorker (entry reference)
open WorkspaceSelectedAdmission (originalTapes preFuel coldCutoff capacity)
open WorkspaceSelectedProgram (finalBank lengthFlag)
open WorkspaceSelectedEntry (size output outputHeads)
open RecoveryRootRound
open private NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.cache_injective from Proof.CaseAnalysis.FinalAdmittedEntry
open private NearCubicWires.P1TopDown.WorkspaceSelectedOriginals.tapes_unique from Proof.MachineModel.TopDownWorkspaceSelectedOriginals
noncomputable section
attribute [local irreducible] WorkspaceSelectedProgram.admission

theorem cached_of_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k extra : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (n : Nat) (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k)→List Bool) (L : Nat)
    (hr : Step (WorkspaceSelectedProgram.admission sources p k clock extra) (preFuel sources p k clock n)
      (fun _=>0) (entry (lengthFlag sources p k extra) (List.ofFn x) bits) (fun _=>0) (finalBank A L extra))
    (hp : C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits=true) :
    WorkspaceSelectedAdmission.Cached sources p k clock x bits A := by
  obtain ⟨B,J,hB,_pass,cache,_fresh⟩:=WorkspaceSelectedProgram.selected_run sources p k clock extra n x bits
  have same:=NearCubicWires.P1TopDown.WorkspaceSelectedOriginals.tapes_unique hr hB
  have eqA:A=B:=by
    funext i
    exact (WorkspaceSelectedProgram.finalBank_original A L extra i).symm.trans
      ((congrFun same _).trans (WorkspaceSelectedProgram.finalBank_original B J extra i))
  exact eqA.symm ▸ cache hp

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r extra : Nat)

theorem old_size : 2≤originalTapes sources p k := by
  dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
  omega

def cache (mode : Bool) : Fin 19→Fin (originalTapes sources p k) :=
  CloseoutFinalC10ColdCacheAtAdmission.cacheSlot (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k p.clauseDegree p.degree (capacity sources p).E mode

def proPort (hspace : size sources k r p.clauseDegree+96≤extra) :=
  WorkspaceSelectedEntry.slots (old_size sources p k) (show size sources k r p.clauseDegree≤extra by omega)

def initPort (hspace : size sources k r p.clauseDegree+96≤extra) (mode : Bool) :=
  WorkspaceSelectedEntryInit.ports (size sources k r p.clauseDegree)
    (by dsimp [size];omega) hspace (cache sources p k mode)

def modePort : Fin (originalTapes sources p k+1+1+extra) :=
  (((WorkspaceSelectedOriginals.headerPort sources p k 142).castAdd 1).castAdd 1).castAdd extra

def heads (hspace : size sources k r p.clauseDegree+96≤extra) :=
  dockH (proPort sources p k r extra hspace) (fun _=>0) (outputHeads sources k r p.clauseDegree)

def post (hspace : size sources k r p.clauseDegree+96≤extra)
    (A : Fin (originalTapes sources p k)→List Bool) (L n : Nat) (x bits : List Bool) (w : Nat→List Bool) :=
  install (proPort sources p k r extra hspace) (finalBank A L extra)
    (output sources k r p.clauseDegree n x bits w)

def initializer (hspace : size sources k r p.clauseDegree+96≤extra) :=
  CloseoutRowsOriginalSwitch.machine
    (RecoveryFocus.machine (initPort sources p k r extra hspace true) WorkspaceSelectedEntryCount.machine)
    (RecoveryFocus.machine (initPort sources p k r extra hspace false) WorkspaceSelectedEntryCount.machine)
    (modePort sources p k extra)

def driver (hspace : size sources k r p.clauseDegree+96≤extra) :
    Fin (originalTapes sources p k+1+1+extra) :=
  ⟨originalTapes sources p k+2+(size sources k r p.clauseDegree+51),by omega⟩

def bump (hspace : size sources k r p.clauseDegree+96≤extra) :=
  DecompositionCountPosition.move (fun i=>if i=driver sources p k r extra hspace then .right else .stay)

def finalHeads (hspace : size sources k r p.clauseDegree+96≤extra)
    (i : Fin (originalTapes sources p k+1+1+extra)) :=
  if i=driver sources p k r extra hspace then heads sources p k r extra hspace i+1
    else heads sources p k r extra hspace i

@[irreducible] def program (hspace : size sources k r p.clauseDegree+96≤extra) :
    Σ s,Machine (originalTapes sources p k+1+1+extra) s :=
  ⟨_,Composition.machine
    (RecoveryFocus.machine (proPort sources p k r extra hspace) (WorkspaceSelectedEntry.program sources k r p.clauseDegree).2)
    (Composition.machine (initializer sources p k r extra hspace) (bump sources p k r extra hspace))⟩

theorem driver_at_init (hspace : size sources k r p.clauseDegree+96≤extra) (mode : Bool) :
    initPort sources p k r extra hspace mode (WorkspaceSelectedEntryCount.count 70)=
      driver sources p k r extra hspace := by
  apply Fin.ext
  simp [initPort,WorkspaceSelectedEntryInit.ports,WorkspaceSelectedEntryCount.count,driver]

theorem driver_head (hspace : size sources k r p.clauseDegree+96≤extra) :
    finalHeads sources p k r extra hspace (driver sources p k r extra hspace)=1 := by
  have hz : heads sources p k r extra hspace (driver sources p k r extra hspace)=0 := by
    apply dockH_other
    intro i he
    have hv:=congrArg Fin.val he
    have hi:=i.isLt
    dsimp only [proPort,WorkspaceSelectedEntry.slots,driver] at hv
    split_ifs at hv <;>omega
  simp [finalHeads,hz]

theorem bump_run (hspace : size sources k r p.clauseDegree+96≤extra)
    (A : Fin (originalTapes sources p k+1+1+extra)→List Bool) :
    Step (bump sources p k r extra hspace) 1 (heads sources p k r extra hspace) A
      (finalHeads sources p k r extra hspace) A := by
  obtain ⟨rr,hr,hf,_hs⟩:=DecompositionCountPosition.move_run
    (fun i=>if i=driver sources p k r extra hspace then .right else .stay)
    (heads sources p k r extra hspace) A
  apply Step.of_run hr
  · rw [hf]
    funext i
    simp only [finalHeads]
    split_ifs <;>rfl
  · exact congrArg Configuration.tapes hf

/-- Concrete admitted-bank to actual source-count entry. All source and cache
facts are recovered from the same admission receipt. The program is fixed;
mode is read from the retained physical header, not passed as machine advice. -/
theorem run (hspace : size sources k r p.clauseDegree+96≤extra)
    (n : Nat) (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k)→List Bool) (L : Nat)
    (hr : Step (WorkspaceSelectedProgram.admission sources p k (PolynomialClock.ordinaryClock k) extra)
      (preFuel sources p k (PolynomialClock.ordinaryClock k) n) (fun _=>0)
      (entry (lengthFlag sources p k extra) (List.ofFn x) bits) (fun _=>0) (finalBank A L extra))
    (hp : C10LegalAdmission.passed sources p (reference k (PolynomialClock.ordinaryClock k)) (coldCutoff sources) n x bits=true) :
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
      ∃ w out,Step (program sources p k r extra hspace).2
        (C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n+
          WorkspaceSelectedEntryCount.budget a rq (C10PartsSchedule.entryWidthSchedule sources k r n)+5)
        (fun _=>0) (finalBank A L extra) (finalHeads sources p k r extra hspace)
        (install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
          (post sources p k r extra hspace A L n (List.ofFn x) bits w) out) ∧
      install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
        (post sources p k r extra hspace A L n (List.ofFn x) bits w) out
        (driver sources p k r extra hspace)=UnaryTemplate.tape (2^(a.output rq).clauseBits) ∧
      (∀j,install (initPort sources p k r extra hspace (BoundedFields.symmetric bits))
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
  intro source a CH Cpad code
  have ho:=WorkspaceSelectedOriginals.originals_of_run sources p k (PolynomialClock.ordinaryClock k) extra n x bits A L hr hp
  have hc:=cached_of_run sources p k extra (PolynomialClock.ordinaryClock k) n x bits A L hr hp
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
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryReady
