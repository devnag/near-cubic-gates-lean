import Proof.MachineModel.TopDownWorkspaceBoundedGateEntry
import Proof.CaseAnalysis.CloseoutWitnessFamilyResources

/-! Concrete admission data for the literal guarded endpoint. The capacity
parameters and cold cutoff are produced before k; the actual parser, paid
zero-head rewind, outer gate flag and original-input budget are fixed here.
The complete retained parser bank and admitted original-cache fact are exported.
The estimator continuation and its Runtime are not supplied by this module. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedAdmission
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceGuardedWorker (input entry reference)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine

structure Capacity (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) where
  K : Nat
  E : Nat
  positive : 0<K
  bound : ∀ N, FamilyResources.capacity
    (ColdFamily.scale (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
      p.degree p.clauseDegree p.copies (CompetitorRationalGap.zeta (constantsOf sources)) N)
    ≤ K*(N+1)^E

@[irreducible] def capacity (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) : Capacity sources p := by
  let h := FamilyResources.source_envelope (CloseoutLanguage.selectedPCPP sources)
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries
    p.degree p.clauseDegree (CompetitorRationalGap.zeta (constantsOf sources)) p.copies
  exact ⟨Classical.choose h,Classical.choose (Classical.choose_spec h),
    (Classical.choose_spec (Classical.choose_spec h)).1,
    (Classical.choose_spec (Classical.choose_spec h)).2⟩

def coldCutoff (sources : EightSources) : Nat := 2^(CloseoutLanguage.selectedPCPP sources).minimumArity

def originalTapes (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k : Nat) : Nat :=
  WorkspaceBoundedGateEntry.originalTapes sources p k (capacity sources p).E

def originalProgram (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) :=
  WorkspaceBoundedGateEntry.originalProgram sources p k clock (coldCutoff sources)
    (capacity sources p).E (capacity sources p).K

def admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) :=
  TapeEmbedding.machine 1 (CloseoutFinalC10ColdCacheRewind.machine (originalProgram sources p k clock).2)

def preFuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) : Nat :=
  2*WorkspaceBoundedGateEntry.fuel sources p k clock (coldCutoff sources)
    (capacity sources p).E (capacity sources p).K n+2

def flag (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k : Nat) :
    Fin (originalTapes sources p k+1+1) :=
  (WorkspaceBoundedGateEntry.flag sources p k (capacity sources p).E).castAdd 1

def Cached (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) {n : Nat} (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k) → List Bool) : Prop :=
  ∃ H,CloseoutFinalC10ColdCacheAtAdmission.Cached (fixedProjection sources)
    (CloseoutLanguage.selectedPCPP sources) k (SelectedSource.hierarchy sources k clock).coefficient
    (padding sources k clock) p.clauseDegree p.degree (capacity sources p).E
    (SelectedSource.code sources k clock) x bits (Nat.le_max_right _ _) H A

theorem input_blank {t : Nat} (ht : 2≤t) (x bits : List Bool) :
    Fin.addCases (input x bits : Fin t → List Bool) (fun _ : Fin 1 => []) = input x bits := by
  funext i
  refine Fin.addCases (m:=t) (n:=1) ?_ ?_ i
  · intro j
    simp only [Fin.addCases_left,input,Fin.val_castAdd]
    rfl
  · intro j
    simp only [Fin.addCases_right,input,Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega)]

theorem zero_heads (t : Nat) :
    Fin.addCases (fun _ : Fin t => 0) (fun _ : Fin 1 => 0) = (fun _ => 0) := by
  funext i
  exact Fin.addCases (fun _ => by rw [Fin.addCases_left]) (fun _ => by rw [Fin.addCases_right]) i

/-- Full physical exit, not just its pass flag. The cache words are preserved
while every current head is zero; old cache-head facts are kept only as witnesses. -/
theorem selected_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    (n : Nat) (x : BitInput n) (bits : List Bool) :
    ∃ (A : Fin (originalTapes sources p k) → List Bool) (logSize : Nat),
      logSize ≤ WorkspaceBoundedGateEntry.fuel sources p k clock (coldCutoff sources)
        (capacity sources p).E (capacity sources p).K n ∧
      Step (admission sources p k clock) (preFuel sources p k clock n) (fun _ => 0)
        (entry (Fin.last (originalTapes sources p k+1)) (List.ofFn x) bits) (fun _ => 0)
        (Fin.addCases (Fin.addCases A (fun _ : Fin 1 => List.replicate logSize false))
          (fun _ : Fin 1 => [true])) ∧
      readTapeBit (A (BoundedFamilySupport.flag (fixedProjection sources)
        (CloseoutLanguage.selectedPCPP sources) k p.clauseDegree p.degree (capacity sources p).E)) 0 =
        C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits ∧
      (C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits=true →
        Cached sources p k clock x bits A) := by
  let cap := capacity sources p
  let source := fixedProjection sources
  let a := CloseoutLanguage.selectedPCPP sources
  let H := SelectedSource.hierarchy sources k clock
  let Cpad := padding sources k clock
  let delta := CompetitorRationalGap.zeta (constantsOf sources)
  have hcopies : 1≤p.copies :=
    (selectedAmplifier sources.amplification p.degree).arityCoefficientPositive.trans p.hcopies
  obtain ⟨A,L,hL,hr,hpass,hcache⟩ := CloseoutFinalC10ColdCacheRewind.bounded_zero source a
    k H.coefficient Cpad (coldCutoff sources) p.clauseDegree p.degree p.copies cap.E cap.K 1 1
    delta (SelectedSource.code sources k clock) x bits (Nat.le_max_right _ _) p.hD
    (by omega) (by omega) cap.positive (by rfl) p.hd p.hh hcopies cap.bound
  have hb := Nat.mul_le_mul_left 2 (BoundedFamily.budget_le source a H Cpad (coldCutoff sources)
    p.clauseDegree p.degree p.copies cap.E cap.K 1 1 delta (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (by rfl) cap.bound ⟨n,x⟩ bits)
  have hp : Step (CloseoutFinalC10ColdCacheRewind.machine (originalProgram sources p k clock).2)
      (preFuel sources p k clock n) (fun _ => 0)
      (Fin.addCases (BoundedFamilySupport.input source a k p.clauseDegree p.degree cap.E (List.ofFn x) bits)
        (fun _ : Fin 1 => [])) (fun _ => 0)
      (Fin.addCases A (fun _ : Fin 1 => List.replicate L false)) := by
    unfold originalProgram WorkspaceBoundedGateEntry.originalProgram WorkspaceBoundedAdmission.program
    exact hr.enlarge (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hb) 2)
  have ht : 2≤originalTapes sources p k := by
    dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
    omega
  rw [WorkspaceBoundedAdmission.input_eq] at hp
  have hp' := hp.congr_in rfl (input_blank ht (List.ofFn x) bits)
  have lifted := ((hp'.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [true])).congr_in
    (zero_heads _) (WorkspaceBoundedGateEntry.entry_embed (t:=originalTapes sources p k+1)
      (by omega) (List.ofFn x) bits)).congr
      (zero_heads _) rfl
  exact ⟨A,L,hL.trans hb,lifted,hpass,hcache⟩

end
end NearCubicWires.P1TopDown.WorkspaceSelectedAdmission
