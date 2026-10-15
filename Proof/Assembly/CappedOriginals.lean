import Proof.MachineModel.ControllerCappedSelected
import Proof.MachineModel.TopDownWorkspaceSelectedOriginals

/-! Recover the original header words at the exact capped admission boundary.
The proof uses the same denominator and deterministic run, retaining the original
Originals predicate and the caller's final bank. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace OriginalHeaderRecovery
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceGuardedWorker (input entry)
open WorkspaceSelectedAdmission (originalTapes coldCutoff capacity)
open WorkspaceSelectedProgram (finalBank lengthFlag)
open WorkspaceSelectedOriginals (headerPort Originals)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine ControllerCappedSelected.admission

/-- Capped admission preserves the exact original input, witness and mode words. -/
theorem originals_of_run :
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.P1TopDown in
∀ (sources : EightSources) (gamma : Real) (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (extra n : Nat) (x : BitInput n) (bits : List Bool)
 (A : Fin (WorkspaceSelectedAdmission.originalTapes sources p k)→List Bool) (L : Nat),
 Step (ControllerCappedSelected.admission sources p den k clock extra)
  (ControllerCappedSelected.preFuel sources p den k clock n) (fun _=>0)
  (WorkspaceGuardedWorker.entry (WorkspaceSelectedProgram.lengthFlag sources p k extra) (List.ofFn x) bits)
  (fun _=>0) (WorkspaceSelectedProgram.finalBank A L extra) →
 P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference den hden k clock)
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true →
 WorkspaceSelectedOriginals.Originals sources p k x bits A := by
  intro sources gamma p den hden k clock extra n x bits A L hr admitted
  let cap := capacity sources p
  let source := fixedProjection sources
  let a := CloseoutLanguage.selectedPCPP sources
  let H := SelectedSource.hierarchy sources k clock
  let Cpad := padding sources k clock
  let delta := CompetitorRationalGap.zeta (constantsOf sources)
  have hcopies : 1≤p.copies :=
    (selectedAmplifier sources.amplification p.degree).arityCoefficientPositive.trans p.hcopies
  obtain ⟨old,hold,hsteps,_hhead,_hpass,_hselected,_hcache⟩ :=
    CloseoutFinalC10ColdCacheAtAdmission.bounded_cache source a k H.coefficient Cpad
      (coldCutoff sources) p.clauseDegree p.degree p.copies cap.E cap.K den den delta
      (SelectedSource.code sources k clock) x bits (Nat.le_max_right _ _) p.hD
      hden hden cap.positive (by rfl) p.hd p.hh hcopies cap.bound
  have originals := CloseoutFinalC10ColdOriginalFrame.bounded_originals
    (source:=source) (a:=a) (k:=k) (CH:=H.coefficient) (Cpad:=Cpad)
    (cutoff:=coldCutoff sources) (D:=p.clauseDegree) (G:=p.degree) (copies:=p.copies)
    (delta:=delta) (code:=SelectedSource.code sources k clock) (n:=n) (x:=x)
    (hpad:=Nat.le_max_right _ _) (hD:=p.hD) (E:=cap.E) (K:=cap.K) (bits:=bits)
    (hK:=cap.positive) (hcut:=by rfl) (hd:=p.hd) (hh:=p.hh) (hc:=hcopies)
    (hbudget:=cap.bound) (symDen:=den) (thrDen:=den) (hsym:=hden) (hthr:=hden)
    old hold admitted
  have rewind := CloseoutFinalC10ColdCacheRewind.rewind_run _ _ _ old hold hsteps
  have hb := Nat.mul_le_mul_left 2 (BoundedFamily.budget_le source a H Cpad (coldCutoff sources)
    p.clauseDegree p.degree p.copies cap.E cap.K den den delta (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (by rfl) cap.bound ⟨n,x⟩ bits)
  have hp : Step (CloseoutFinalC10ColdCacheRewind.machine
      (ControllerCappedSelected.originalProgram sources p den k clock).2)
      (ControllerCappedSelected.preFuel sources p den k clock n) (fun _ => 0)
      (Fin.addCases (BoundedFamilySupport.input source a k p.clauseDegree p.degree cap.E (List.ofFn x) bits)
        (fun _ : Fin 1 => [])) (fun _ => 0)
      (Fin.addCases old.final.tapes (fun _ : Fin 1 => List.replicate old.steps false)) := by
    unfold ControllerCappedSelected.originalProgram WorkspaceBoundedAdmission.program
    exact rewind.enlarge (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hb) 2)
  have ht : 2≤originalTapes sources p k := by
    dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
    omega
  have hin := congrArg (fun f : Fin (originalTapes sources p k) → List Bool =>
    Fin.addCases (motive:=fun _ => List Bool) f (fun _ : Fin 1 => []))
    (WorkspaceBoundedAdmission.input_eq source a k p.clauseDegree p.degree cap.E (List.ofFn x) bits)
  have hp' := hp.congr_in rfl (hin.trans (WorkspaceSelectedAdmission.input_blank ht (List.ofFn x) bits))
  have lifted := ((hp'.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [true])).congr_in
    (WorkspaceSelectedAdmission.zero_heads _) (WorkspaceBoundedGateEntry.entry_embed
      (t:=originalTapes sources p k+1) (by omega) (List.ofFn x) bits)).congr
      (WorkspaceSelectedAdmission.zero_heads _) rfl
  have extended := ((lifted.embed (fun _ : Fin extra => 0) (fun _ : Fin extra => [])).congr_in
    (WorkspaceSelectedProgram.zero_heads _ extra) (WorkspaceSelectedProgram.input_extra
      (t:=originalTapes sources p k+1+1) (by omega) extra _ (List.ofFn x) bits)).congr
      (WorkspaceSelectedProgram.zero_heads _ extra) rfl
  have actual : Step (ControllerCappedSelected.admission sources p den k clock extra)
      (ControllerCappedSelected.preFuel sources p den k clock n) (fun _ => 0)
      (entry (lengthFlag sources p k extra) (List.ofFn x) bits) (fun _ => 0)
      (finalBank old.final.tapes old.steps extra) := by
    unfold ControllerCappedSelected.admission
    exact extended
  have same : finalBank A L extra=finalBank old.final.tapes old.steps extra := by
    obtain ⟨r,hrun,_hh,htapes,_hs⟩ := hr
    obtain ⟨r',hrun',_hh',htapes',_hs'⟩ := actual
    have sameRun : r=r' := Option.some.inj (hrun.symm.trans hrun')
    exact htapes.symm.trans ((congrArg (fun e => e.final.tapes) sameRun).trans htapes')
  have retained (i : Fin 150) : A (headerPort sources p k i)=old.final.tapes (headerPort sources p k i) :=
    (WorkspaceSelectedProgram.finalBank_original A L extra (headerPort sources p k i)).symm.trans
      ((congrFun same _).trans (WorkspaceSelectedProgram.finalBank_original old.final.tapes old.steps extra
        (headerPort sources p k i)))
  exact ⟨(retained 0).trans originals.1,(retained 1).trans originals.2.1,
    (retained 142).trans originals.2.2⟩

end
end OriginalHeaderRecovery
