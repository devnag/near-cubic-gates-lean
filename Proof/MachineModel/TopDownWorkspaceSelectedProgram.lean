import Proof.MachineModel.TopDownWorkspaceSelectedAdmission
import Proof.MachineModel.TopDownGuardedAssembly

/-! Actual guarded ProgramData with a caller-chosen fixed continuation tape
count. Admission preserves its original cache and initializes every added tape
to [] at head zero. The endpoint's admission_run field is supplied here; the
admitted continuation and Runtime remain the two substantive proof regions. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedProgram
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal
open RepairSource.CloseoutFinal.C10LengthGate (exitTapes)
open WorkspaceGuardedWorker (input entry reference)
open WorkspaceSelectedAdmission (originalTapes coldCutoff preFuel)
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.admission

theorem input_extra {t : Nat} (ht : 2≤t) (extra : Nat) (lengthFlag : Fin t) (x bits : List Bool) :
    Fin.addCases (entry lengthFlag x bits) (fun _ : Fin extra => []) =
      entry (lengthFlag.castAdd extra) x bits := by
  funext i
  refine Fin.addCases (m:=t) (n:=extra) ?_ ?_ i
  · intro j
    simp only [Fin.addCases_left,entry,exitTapes,Fin.castAdd_inj,input,Fin.val_castAdd]
    rfl
  · intro j
    have hne : j.natAdd t ≠ lengthFlag.castAdd extra := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp only [Fin.addCases_right,entry,exitTapes,hne,if_false,input,Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega)]

theorem zero_heads (t extra : Nat) :
    Fin.addCases (fun _ : Fin t => 0) (fun _ : Fin extra => 0) = (fun _ => 0) := by
  funext i
  exact Fin.addCases (fun _ => by rw [Fin.addCases_left]) (fun _ => by rw [Fin.addCases_right]) i

def admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (extra : Nat) :=
  TapeEmbedding.machine extra (WorkspaceSelectedAdmission.admission sources p k clock)

def flag (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k extra : Nat) :
    Fin (originalTapes sources p k+1+1+extra) :=
  (WorkspaceSelectedAdmission.flag sources p k).castAdd extra

def lengthFlag (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k extra : Nat) :
    Fin (originalTapes sources p k+1+1+extra) :=
  (Fin.last (originalTapes sources p k+1)).castAdd extra

def finalBank {t : Nat} (A : Fin t → List Bool) (L extra : Nat) :
    Fin (t+1+1+extra) → List Bool :=
  Fin.addCases (Fin.addCases (Fin.addCases A (fun _ : Fin 1 => List.replicate L false))
    (fun _ : Fin 1 => [true])) (fun _ : Fin extra => [])

theorem finalBank_original {t : Nat} (A : Fin t → List Bool) (L extra : Nat) (i : Fin t) :
    finalBank A L extra (((i.castAdd 1).castAdd 1).castAdd extra) = A i := by
  simp only [finalBank,Fin.addCases_left]

/-- Full retained source, fresh continuation bank and exact pass flag all come
from this single original-input run. No abstract admitted-cache premise. -/
theorem selected_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (extra n : Nat)
    (x : BitInput n) (bits : List Bool) :
    ∃ (A : Fin (originalTapes sources p k) → List Bool) (L : Nat),
      Step (admission sources p k clock extra) (preFuel sources p k clock n) (fun _ => 0)
        (entry (lengthFlag sources p k extra) (List.ofFn x) bits) (fun _ => 0) (finalBank A L extra) ∧
      readTapeBit (finalBank A L extra (flag sources p k extra)) 0 =
        C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits ∧
      (C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits=true →
        WorkspaceSelectedAdmission.Cached sources p k clock x bits A) ∧
      ∀ i : Fin extra,finalBank A L extra (i.natAdd (originalTapes sources p k+1+1))=[] := by
  obtain ⟨A,L,_hL,hr,hpass,hcache⟩ := WorkspaceSelectedAdmission.selected_run sources p k clock n x bits
  have extended := ((hr.embed (fun _ : Fin extra => 0) (fun _ : Fin extra => [])).congr_in
    (zero_heads _ extra) (input_extra (t:=originalTapes sources p k+1+1) (by omega)
      extra _ (List.ofFn x) bits)).congr
      (zero_heads _ extra) rfl
  refine ⟨A,L,extended,?_,hcache,?_⟩
  · exact (congrArg (fun word => readTapeBit word 0) (finalBank_original A L extra
      (BoundedFamilySupport.flag (SelectedRecoveryIntegration.fixedProjection sources)
        (CloseoutLanguage.selectedPCPP sources) k p.clauseDegree p.degree
        (WorkspaceSelectedAdmission.capacity sources p).E))).trans hpass
  · intro i
    exact Fin.addCases_right i

def programData (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (base extra : Nat)
    {bs : Nat} (continuation : Machine (originalTapes sources p k+1+1+extra) bs)
    (result : Fin (originalTapes sources p k+1+1+extra)) (bodyFuel : Nat → Nat) : GuardedAssembly.ProgramData where
  k := k
  clock := clock
  coldCutoff := coldCutoff sources
  baseOnset := base
  tapes := originalTapes sources p k+1+1+extra
  admissionStates := _
  bodyStates := bs
  admission := admission sources p k clock extra
  continuation := continuation
  inputTape := ⟨0,by omega⟩
  lengthFlag := lengthFlag sources p k extra
  admissionFlag := flag sources p k extra
  result := result
  preFuel := preFuel sources p k clock
  bodyFuel := bodyFuel

theorem admission_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (base extra : Nat)
    {bs : Nat} (continuation : Machine (originalTapes sources p k+1+1+extra) bs)
    (result : Fin (originalTapes sources p k+1+1+extra)) (bodyFuel : Nat → Nat) :
    let D := programData sources p k clock base extra continuation result bodyFuel
    ∀ n x bits,(GuardedAssembly.workerData sources p D).onset≤n →
      ∃ H A,Step D.admission (D.preFuel n) (fun _ => 0)
        (entry D.lengthFlag (List.ofFn x) bits) H A ∧
        readTapeBit (A D.admissionFlag) (H D.admissionFlag)=
          C10LegalAdmission.passed sources p (reference D.k D.clock) D.coldCutoff n x bits := by
  intro D n x bits _hn
  obtain ⟨A,L,hr,hpass,_hcache,_hfresh⟩ := selected_run sources p k clock extra n x bits
  exact ⟨(fun _ => 0),finalBank A L extra,hr,hpass⟩

end
end NearCubicWires.P1TopDown.WorkspaceSelectedProgram
