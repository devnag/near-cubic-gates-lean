import Proof.MachineModel.TopDownWorkspaceSelectedProgram
import Proof.CaseAnalysis.FinalOriginalFrame

/-! The actual admitted parser exit retains the original input, witness and
mode words. This enriches the same selected physical admission run by
receipt determinism; it does not execute the source a second time. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedOriginals
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceGuardedWorker (input entry reference)
open WorkspaceSelectedAdmission (originalTapes coldCutoff preFuel capacity)
open WorkspaceSelectedProgram (finalBank lengthFlag)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine WorkspaceSelectedProgram.admission
  WorkspaceSelectedAdmission.admission

def headerPort (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (i : Fin 150) : Fin (originalTapes sources p k) :=
  (HeaderDock.old (BoundedFamily.workspace (fixedProjection sources)
    (CloseoutLanguage.selectedPCPP sources) k p.clauseDegree p.degree (capacity sources p).E) i).castAdd 1

def Originals (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) {n : Nat} (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k) → List Bool) : Prop :=
  A (headerPort sources p k 0)=RepairOrdinary.frame (List.ofFn x) ∧
  A (headerPort sources p k 1)=RepairOrdinary.frame bits ∧
  A (headerPort sources p k 142)=[BoundedFields.symmetric bits]

theorem headerPort_val (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (i : Fin 150) : (headerPort sources p k i).val=i.val := rfl

private theorem tapes_unique {t s : Nat} {m : Machine t s} {fuel : Nat}
    {H J J' : Fin t → Nat} {A B B' : Fin t → List Bool}
    (h : Step m fuel H A J B) (h' : Step m fuel H A J' B') : B=B' := by
  obtain ⟨r,hr,_hh,ht,_hs⟩ := h
  obtain ⟨r',hr',_hh',ht',_hs'⟩ := h'
  have same : r=r' := Option.some.inj (hr.symm.trans hr')
  exact ht.symm.trans ((congrArg (fun e => e.final.tapes) same).trans ht')

/-- Any receipt at the selected admission boundary inherits the exact admitted
original words, including the header mode, from the one underlying source run. -/
theorem originals_of_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (extra n : Nat)
    (x : BitInput n) (bits : List Bool) (A : Fin (originalTapes sources p k) → List Bool) (L : Nat)
    (hr : Step (WorkspaceSelectedProgram.admission sources p k clock extra)
      (preFuel sources p k clock n) (fun _ => 0)
      (entry (lengthFlag sources p k extra) (List.ofFn x) bits) (fun _ => 0) (finalBank A L extra))
    (admitted : C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits=true) :
    Originals sources p k x bits A := by
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
      (coldCutoff sources) p.clauseDegree p.degree p.copies cap.E cap.K 1 1 delta
      (SelectedSource.code sources k clock) x bits (Nat.le_max_right _ _) p.hD
      (by omega) (by omega) cap.positive (by rfl) p.hd p.hh hcopies cap.bound
  have originals := CloseoutFinalC10ColdOriginalFrame.bounded_originals
    (source:=source) (a:=a) (k:=k) (CH:=H.coefficient) (Cpad:=Cpad)
    (cutoff:=coldCutoff sources) (D:=p.clauseDegree) (G:=p.degree) (copies:=p.copies)
    (delta:=delta) (code:=SelectedSource.code sources k clock) (n:=n) (x:=x)
    (hpad:=Nat.le_max_right _ _) (hD:=p.hD) (E:=cap.E) (K:=cap.K) (bits:=bits)
    (hK:=cap.positive) (hcut:=by rfl) (hd:=p.hd) (hh:=p.hh) (hc:=hcopies)
    (hbudget:=cap.bound) (symDen:=1) (thrDen:=1) (hsym:=by omega) (hthr:=by omega)
    old hold admitted
  have rewind := CloseoutFinalC10ColdCacheRewind.rewind_run _ _ _ old hold hsteps
  have hb := Nat.mul_le_mul_left 2 (BoundedFamily.budget_le source a H Cpad (coldCutoff sources)
    p.clauseDegree p.degree p.copies cap.E cap.K 1 1 delta (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (by rfl) cap.bound ⟨n,x⟩ bits)
  have hp : Step (CloseoutFinalC10ColdCacheRewind.machine
      (WorkspaceSelectedAdmission.originalProgram sources p k clock).2)
      (preFuel sources p k clock n) (fun _ => 0)
      (Fin.addCases (BoundedFamilySupport.input source a k p.clauseDegree p.degree cap.E (List.ofFn x) bits)
        (fun _ : Fin 1 => [])) (fun _ => 0)
      (Fin.addCases old.final.tapes (fun _ : Fin 1 => List.replicate old.steps false)) := by
    unfold WorkspaceSelectedAdmission.originalProgram WorkspaceBoundedGateEntry.originalProgram WorkspaceBoundedAdmission.program
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
  have actual : Step (WorkspaceSelectedProgram.admission sources p k clock extra)
      (preFuel sources p k clock n) (fun _ => 0)
      (entry (lengthFlag sources p k extra) (List.ofFn x) bits) (fun _ => 0)
      (finalBank old.final.tapes old.steps extra) := by
    unfold WorkspaceSelectedProgram.admission WorkspaceSelectedAdmission.admission
    exact extended
  have same : finalBank A L extra=finalBank old.final.tapes old.steps extra := tapes_unique hr actual
  have retained (i : Fin 150) : A (headerPort sources p k i)=old.final.tapes (headerPort sources p k i) :=
    (WorkspaceSelectedProgram.finalBank_original A L extra (headerPort sources p k i)).symm.trans
      ((congrFun same _).trans (WorkspaceSelectedProgram.finalBank_original old.final.tapes old.steps extra
        (headerPort sources p k i)))
  exact ⟨(retained 0).trans originals.1,(retained 1).trans originals.2.1,
    (retained 142).trans originals.2.2⟩

/-- Selected admission with the cache, header and fresh bank from the same
complete exit state. Admission of the witness is the only original-word guard. -/
theorem selected_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (extra n : Nat)
    (x : BitInput n) (bits : List Bool) :
    ∃ (A : Fin (originalTapes sources p k) → List Bool) (L : Nat),
      Step (WorkspaceSelectedProgram.admission sources p k clock extra) (preFuel sources p k clock n)
        (fun _ => 0) (entry (lengthFlag sources p k extra) (List.ofFn x) bits)
        (fun _ => 0) (finalBank A L extra) ∧
      readTapeBit (finalBank A L extra (WorkspaceSelectedProgram.flag sources p k extra)) 0 =
        C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits ∧
      (C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits=true →
        WorkspaceSelectedAdmission.Cached sources p k clock x bits A ∧ Originals sources p k x bits A) ∧
      ∀ i : Fin extra,finalBank A L extra (i.natAdd (originalTapes sources p k+1+1))=[] := by
  obtain ⟨A,L,hr,hpass,hcache,hfresh⟩ := WorkspaceSelectedProgram.selected_run sources p k clock extra n x bits
  exact ⟨A,L,hr,hpass,fun h => ⟨hcache h,originals_of_run sources p k clock extra n x bits A L hr h⟩,hfresh⟩

end
end NearCubicWires.P1TopDown.WorkspaceSelectedOriginals
