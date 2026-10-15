import Proof.MachineModel.TopDownWorkspaceBoundedAdmission
import Proof.CaseAnalysis.FinalCacheRewind

/-! The existing bounded parser inhabits the guarded worker's exact admission
entry. A distinct final tape holds the outer gate flag and is retained. All
original parser output heads and tapes remain visible in the receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceBoundedGateEntry
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open RepairSource.CloseoutFinal.C10LengthGate (exitTapes)
open WorkspaceGuardedWorker (input entry reference)
noncomputable section

theorem entry_embed {t : Nat} (ht : 2≤t) (x bits : List Bool) :
    Fin.addCases (input x bits : Fin t → List Bool) (fun _ : Fin 1 => [true]) =
      entry (Fin.last t) x bits := by
  funext i
  refine Fin.addCases (m:=t) (n:=1) ?_ ?_ i
  · intro j
    have hne : j.castAdd 1 ≠ Fin.last t := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_last] at this
      omega
    simp only [Fin.addCases_left,entry,exitTapes,hne,if_false,input,Fin.val_castAdd]
    rfl
  · intro j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    have hv : (0 : Fin 1).natAdd t=Fin.last t := Fin.ext (by simp)
    rw [Fin.addCases_right,hv]
    simp [entry,exitTapes,input,Fin.val_last,Nat.ne_of_gt (show 0<t by omega),
      Nat.ne_of_gt (show 1<t by omega),writeTapeBit]

theorem embed_run {t s : Nat} (p : Machine t s) (ht : 2≤t)
    (flag : Fin t) (budget : Nat) (x bits : List Bool) (passed : Bool)
    (H : Fin t → Nat) (A : Fin t → List Bool)
    (hr : Step p budget (fun _ => 0) (input x bits) H A)
    (hp : readTapeBit (A flag) (H flag)=passed) :
    ∃ heads bank,Step (TapeEmbedding.machine 1 p) budget (fun _ => 0)
      (entry (Fin.last t) x bits) heads bank ∧
      readTapeBit (bank (flag.castAdd 1)) (heads (flag.castAdd 1))=passed ∧
      (∀ i,heads (i.castAdd 1)=H i ∧ bank (i.castAdd 1)=A i) ∧
      heads (Fin.last t)=0 ∧ bank (Fin.last t)=[true] := by
  let heads : Fin (t+1) → Nat := Fin.addCases H (fun _ : Fin 1 => 0)
  let bank : Fin (t+1) → List Bool := Fin.addCases A (fun _ : Fin 1 => [true])
  have hh : Fin.addCases (fun _ : Fin t => 0) (fun _ : Fin 1 => 0) = (fun _ => 0) := by
    funext i
    exact Fin.addCases (fun _ => by rw [Fin.addCases_left])
      (fun _ => by rw [Fin.addCases_right]) i
  have ready := (hr.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [true])).congr_in
    hh (entry_embed ht x bits)
  refine ⟨heads,bank,ready,?_,?_,?_,?_⟩
  · simpa only [heads,bank,Fin.addCases_left] using hp
  · intro i
    exact ⟨Fin.addCases_left _,Fin.addCases_left _⟩
  · change Fin.addCases H (fun _ : Fin 1 => 0) ((0 : Fin 1).natAdd t)=0
    exact Fin.addCases_right _
  · change Fin.addCases A (fun _ : Fin 1 => [true]) ((0 : Fin 1).natAdd t)=[true]
    exact Fin.addCases_right _

def originalTapes (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k E : Nat) :=
  WorkspaceBoundedAdmission.tapes (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k p.clauseDegree p.degree E

def originalProgram (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff E K : Nat) :=
  WorkspaceBoundedAdmission.program (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k (SelectedSource.hierarchy sources k clock).coefficient (padding sources k clock)
    coldCutoff p.clauseDegree p.degree p.copies E K 1 1
    (CompetitorRationalGap.zeta (constantsOf sources)) (SelectedSource.code sources k clock)

def admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff E K : Nat) :=
  TapeEmbedding.machine 1 (originalProgram sources p k clock coldCutoff E K).2

def flag (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k E : Nat) :
    Fin (originalTapes sources p k E+1) :=
  (BoundedFamilySupport.flag (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k p.clauseDegree p.degree E).castAdd 1

def fuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff E K : Nat) : Nat → Nat :=
  WorkspaceBoundedAdmission.uniformFuel (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    (SelectedSource.hierarchy sources k clock) (padding sources k clock) coldCutoff
    p.clauseDegree p.degree p.copies E K 1 1 (CompetitorRationalGap.zeta (constantsOf sources))

/-- Exact physical admission premise of WorkspaceGuardedWorker.rejected.
The capacity exponent/coefficient and minimum-arity cutoff are the remaining
fixed resource choices; no decoded description or prepared cache is assumed. -/
theorem selected_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff E K : Nat)
    (hK : 0<K) (hcut : 2^(CloseoutLanguage.selectedPCPP sources).minimumArity ≤ coldCutoff)
    (hbudget : ∀ N,FamilyResources.capacity
      (ColdFamily.scale (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
        p.degree p.clauseDegree p.copies (CompetitorRationalGap.zeta (constantsOf sources)) N)
      ≤ K*(N+1)^E) (n : Nat) (x : BitInput n) (bits : List Bool) :
    ∃ H A,Step (admission sources p k clock coldCutoff E K)
      (fuel sources p k clock coldCutoff E K n) (fun _ => 0)
      (entry (Fin.last (originalTapes sources p k E)) (List.ofFn x) bits) H A ∧
      readTapeBit (A (flag sources p k E)) (H (flag sources p k E))=
        C10LegalAdmission.passed sources p (reference k clock) coldCutoff n x bits := by
  have hcopies : 1≤p.copies :=
    (selectedAmplifier sources.amplification p.degree).arityCoefficientPositive.trans p.hcopies
  obtain ⟨H,A,hr,hp⟩ := WorkspaceBoundedAdmission.uniform_run
    (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) (SelectedSource.hierarchy sources k clock)
    (padding sources k clock) coldCutoff p.clauseDegree p.degree p.copies E K 1 1
    (CompetitorRationalGap.zeta (constantsOf sources)) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    p.hD (by omega) (by omega) hK hcut p.hd p.hh hcopies hbudget n x bits
  obtain ⟨heads,bank,run,pass,_keep,_head,_word⟩ := embed_run _
    (by dsimp [WorkspaceBoundedAdmission.tapes,HeaderDock.tapes];omega)
    (BoundedFamilySupport.flag (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
      k p.clauseDegree p.degree E) _ (List.ofFn x) bits _ H A hr hp
  exact ⟨heads,bank,run,pass⟩

end
end NearCubicWires.P1TopDown.WorkspaceBoundedGateEntry
