import Proof.MachineModel.CappedLegalAdmission
import Proof.MachineModel.TopDownSelectedAssembly

/-! Paper A.8 chooses a positive wire coefficient after the saving parameter
(paper.tex:2310-2324). Keep that choice in the actual parser as well as the
headline consumer. Reuse the existing tape layout, retained cache, cold parser,
rewind, ordinary rejection runs, and caller's SAME continuation. No supplier
execution or whole-machine cost is inferred from these construction choices. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.ControllerCappedSelected
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.SelectedRecoveryIntegration
open P1Independent.CappedConsumer
open WorkspaceGuardedWorker (input entry below_run rejected_run)
open WorkspaceSelectedAdmission (capacity originalTapes coldCutoff Cached input_blank zero_heads)
open WorkspaceSelectedProgram (finalBank lengthFlag)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine

/-- The reference is used only to select a legal-witness onset, never executed. -/
def reference (den : Nat) (hden : 0<den) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) : WorkerData where
  den := den
  hden := hden
  k := k
  clock := clock
  tapes := 2
  states := 2
  worker := C10LengthGate.counter 0 0 1
  result := 1
  fuel := fun _=>0
  onset := 0
  passed := fun _ _ _=>false

def workerData (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0<den) (D : GuardedAssembly.ProgramData) : WorkerData :=
  let ref:=reference den hden D.k D.clock
  let onset:=max (max D.baseOnset (Soundness.cutoff (constantsOf sources)))
    (Classical.choose (P1Independent.CappedLegalAdmission.passed_legal_eventually sources p ref D.coldCutoff))
  { den:=den, hden:=hden, k:=D.k, clock:=D.clock, tapes:=D.tapes, states:=_,
    worker:=C10GuardedStageConsumer.admittedWorker onset D.admission D.continuation
      D.inputTape D.lengthFlag D.admissionFlag D.result,
    result:=D.result, fuel:=fun n=>4*onset+5+D.preFuel n+D.bodyFuel n, onset:=onset,
    passed:=P1Independent.CappedLegalAdmission.passed sources p ref D.coldCutoff }

@[irreducible] def originalProgram (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :
    Σ states, Machine (originalTapes sources p k) states :=
  ⟨_,(WorkspaceBoundedAdmission.program (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k (SelectedSource.hierarchy sources k clock).coefficient (padding sources k clock)
    (coldCutoff sources) p.clauseDegree p.degree p.copies (capacity sources p).E
    (capacity sources p).K den den (CompetitorRationalGap.zeta (constantsOf sources))
    (SelectedSource.code sources k clock)).2⟩

def coldFuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) : Nat→Nat :=
  WorkspaceBoundedAdmission.uniformFuel (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    (SelectedSource.hierarchy sources k clock) (padding sources k clock) (coldCutoff sources)
    p.clauseDegree p.degree p.copies (capacity sources p).E (capacity sources p).K den den
    (CompetitorRationalGap.zeta (constantsOf sources))

def admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (extra : Nat) :=
  TapeEmbedding.machine extra (TapeEmbedding.machine 1
    (CloseoutFinalC10ColdCacheRewind.machine (originalProgram sources p den k clock).2))

def preFuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (n : Nat) :=
  2*coldFuel sources p den k clock n+2

/-- An actual run from the two original inputs, with every extra tape fresh.
Only the denominator changes; the cache and continuation tape types are reused. -/
theorem selected_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0<den) (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (extra n : Nat) (x : BitInput n) (bits : List Bool) :
    ∃ (A : Fin (originalTapes sources p k)→List Bool) (L : Nat),
      Step (admission sources p den k clock extra) (preFuel sources p den k clock n)
        (fun _=>0) (entry (lengthFlag sources p k extra) (List.ofFn x) bits)
        (fun _=>0) (finalBank A L extra) ∧
      readTapeBit (finalBank A L extra (WorkspaceSelectedProgram.flag sources p k extra)) 0 =
        P1Independent.CappedLegalAdmission.passed sources p (reference den hden k clock)
          (coldCutoff sources) n x bits ∧
      (P1Independent.CappedLegalAdmission.passed sources p (reference den hden k clock)
          (coldCutoff sources) n x bits=true → Cached sources p k clock x bits A) ∧
      ∀ i : Fin extra,finalBank A L extra (i.natAdd (originalTapes sources p k+1+1))=[] := by
  let cap:=capacity sources p
  let source:=fixedProjection sources
  let a:=CloseoutLanguage.selectedPCPP sources
  let H:=SelectedSource.hierarchy sources k clock
  let Cpad:=padding sources k clock
  let delta:=CompetitorRationalGap.zeta (constantsOf sources)
  have hcopies : 1≤p.copies :=
    (selectedAmplifier sources.amplification p.degree).arityCoefficientPositive.trans p.hcopies
  obtain ⟨A,L,hL,hr,hpass,hcache⟩:=CloseoutFinalC10ColdCacheRewind.bounded_zero source a
    k H.coefficient Cpad (coldCutoff sources) p.clauseDegree p.degree p.copies cap.E cap.K den den
    delta (SelectedSource.code sources k clock) x bits (Nat.le_max_right _ _) p.hD
    hden hden cap.positive (by rfl) p.hd p.hh hcopies cap.bound
  have hb:=Nat.mul_le_mul_left 2 (BoundedFamily.budget_le source a H Cpad (coldCutoff sources)
    p.clauseDegree p.degree p.copies cap.E cap.K den den delta (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (by rfl) cap.bound ⟨n,x⟩ bits)
  have hp : Step (CloseoutFinalC10ColdCacheRewind.machine (originalProgram sources p den k clock).2)
      (preFuel sources p den k clock n) (fun _=>0)
      (Fin.addCases (BoundedFamilySupport.input source a k p.clauseDegree p.degree cap.E (List.ofFn x) bits)
        (fun _ : Fin 1=>[])) (fun _=>0)
      (Fin.addCases A (fun _ : Fin 1=>List.replicate L false)) := by
    unfold originalProgram WorkspaceBoundedAdmission.program
    exact hr.enlarge (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hb) 2)
  have ht : 2≤originalTapes sources p k := by
    dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
    omega
  rw [WorkspaceBoundedAdmission.input_eq] at hp
  have hp':=hp.congr_in rfl (input_blank ht (List.ofFn x) bits)
  have lifted:=((hp'.embed (fun _ : Fin 1=>0) (fun _ : Fin 1=>[true])).congr_in
    (zero_heads _) (WorkspaceBoundedGateEntry.entry_embed (t:=originalTapes sources p k+1)
      (by omega) (List.ofFn x) bits)).congr (zero_heads _) rfl
  have extended:=((lifted.embed (fun _ : Fin extra=>0) (fun _ : Fin extra=>[])).congr_in
    (WorkspaceSelectedProgram.zero_heads _ extra)
    (WorkspaceSelectedProgram.input_extra (t:=originalTapes sources p k+1+1) (by omega)
      extra _ (List.ofFn x) bits)).congr (WorkspaceSelectedProgram.zero_heads _ extra) rfl
  refine ⟨A,L,extended,?_,hcache,?_⟩
  · exact (congrArg (fun word=>readTapeBit word 0) (WorkspaceSelectedProgram.finalBank_original A L extra
      (BoundedFamilySupport.flag source a k p.clauseDegree p.degree cap.E))).trans hpass
  · intro i
    exact Fin.addCases_right i

def programData {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (den : Nat) (C : SelectedAssembly.ContinuationData sources p) : GuardedAssembly.ProgramData :=
  { SelectedAssembly.programData C with
    admissionStates:=_, admission:=admission sources p den C.k C.clock C.extra,
    preFuel:=preFuel sources p den C.k C.clock }

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes admission

/-- Requirements concern the same supplied continuation and capped parser. -/
structure Remaining {sources : EightSources} {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0<den) (C : SelectedAssembly.ContinuationData sources p) : Type 1 where
  admitted : ∀ n x bits, (workerData sources p den hden (programData den C)).onset≤n →
    (workerData sources p den hden (programData den C)).passed n x bits=true →
    DecodedVerdictAt sources p (workerData sources p den hden (programData den C))
      (by change 2≤originalTapes sources p C.k+1+1+C.extra; omega) n x bits
  runtime : Runtime sources C.k C.clock (workerData sources p den hden (programData den C)).fuel

/-- Reuse generic physical rejection; obtain legal capped admission from the
already proved CappedLegalAdmission theorem at the selected enlarged onset. -/
def requirements {sources : EightSources} {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0<den) (C : SelectedAssembly.ContinuationData sources p)
    (R : Remaining p den hden C) : Requirements sources p (workerData sources p den hden (programData den C)) := by
  let D:=programData den C
  let W:=workerData sources p den hden D
  have ht : 2≤W.tapes := by change 2≤originalTapes sources p C.k+1+1+C.extra; omega
  refine ⟨ht,?_,?_,R.admitted,?_⟩
  · exact (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  · intro n x bits hrej
    have hinput : D.inputTape.val=0 := rfl
    have hflag : D.lengthFlag≠D.inputTape := by
      intro h
      have hv:=congrArg Fin.val h
      change originalTapes sources p C.k+1=0 at hv
      omega
    have hbank : (UAcceptanceCarrier.verifier W.worker ht W.result).inputTapes (List.ofFn x) bits=
        input (List.ofFn x) bits := UAcceptanceCarrier.inputTapes_eq _ _ _ _ _
    by_cases hn : n<W.onset
    · obtain ⟨H,A,hr,hfalse⟩:=below_run W.onset D.admission D.continuation D.inputTape
        D.lengthFlag D.admissionFlag D.result hinput hflag x bits hn
      refine ⟨H,A,?_,hfalse⟩
      rw [hbank]
      exact hr.enlarge (by
        change 2*n+3≤4*W.onset+5+D.preFuel n+D.bodyFuel n
        omega)
    · have hp : W.passed n x bits=false := hrej.resolve_left hn
      obtain ⟨A,L,hr,hpass,_cache,_fresh⟩:=selected_run sources p den hden C.k C.clock C.extra n x bits
      have hfalse : readTapeBit (finalBank A L C.extra D.admissionFlag) 0=false := hpass.trans hp
      have run:=rejected_run W.onset D.admission D.continuation D.inputTape D.lengthFlag
        D.admissionFlag D.result hinput x bits (by omega) (D.preFuel n) (fun _=>0)
        (finalBank A L C.extra) hr hfalse
      refine ⟨(fun _=>0),C10LengthGate.exitTapes D.result (finalBank A L C.extra) 0 false,?_,?_⟩
      · rw [hbank]
        exact run.enlarge (by
          change 4*W.onset+5+D.preFuel n≤4*W.onset+5+D.preFuel n+D.bodyFuel n
          omega)
      · change readTapeBit (C10LengthGate.exitTapes D.result (finalBank A L C.extra) 0 false D.result) 0=false
        simp [C10LengthGate.exitTapes,MemoryTransition.read_write]
  · intro s hs x guess hlegal
    exact Classical.choose_spec
      (P1Independent.CappedLegalAdmission.passed_legal_eventually sources p
        (reference den hden D.k D.clock) D.coldCutoff)
      s ((Nat.le_max_right _ _).trans hs) x guess hlegal

theorem close
    (den : (sources : EightSources) → ∀ gamma : Real, 0<gamma → gamma<1/2 → Parameters sources gamma → Nat)
    (hden : ∀ sources gamma hg hh p,0<den sources gamma hg hh p)
    (choose : (sources : EightSources) → ∀ gamma : Real, 0<gamma → gamma<1/2 →
      (p : Parameters sources gamma) → SelectedAssembly.ContinuationData sources p)
    (construct : ∀ sources gamma hg hh p,
      Remaining p (den sources gamma hg hh p) (hden sources gamma hg hh p) (choose sources gamma hg hh p)) :
    EightSources → OrdinaryHeadlineTheorem25 := by
  exact P1Independent.CappedConsumer.theorem25_of_guarded
    (fun sources gamma hg hh p=>workerData sources p (den sources gamma hg hh p)
      (hden sources gamma hg hh p) (programData (den sources gamma hg hh p) (choose sources gamma hg hh p)))
    (fun sources gamma hg hh p=>requirements p (den sources gamma hg hh p)
      (hden sources gamma hg hh p) (choose sources gamma hg hh p) (construct sources gamma hg hh p))
    (fun sources gamma hg hh p=>(construct sources gamma hg hh p).runtime)

end
end NearCubicWires.P1TopDown.ControllerCappedSelected
