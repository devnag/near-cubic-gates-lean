import Proof.MachineModel.TopDownWorkspaceSelectedEntryReady
import Proof.CaseAnalysis.RowsOriginalClauseLoop

/-! The actual initialized source count drives the existing clause Repeat.
Its final false cell is retained physically. The local body layout and its
round receipt remain explicit, while all tapes outside the focus are kept. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryRepeat
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource CloseoutWitness RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open WorkspaceSelectedEntry (size)
noncomputable section

theorem template_run {B s : Nat} (p : Machine B s) (N cost : Nat)
    (H : Nat→Fin B→Nat) (A : Nat→Fin B→List Bool)
    (hround : ∀j<N,Step p cost (H j) (A j) (H (j+1)) (A (j+1))) :
    Step (RepeatMachine.machine p (fun _ _=>true)) (N*(cost+3)+3)
      (Fin.addCases (H 0) (fun _ : Fin 1=>1))
      (Fin.addCases (A 0) (fun _ : Fin 1=>UnaryTemplate.tape N))
      (Fin.addCases (H N) (fun _ : Fin 1=>1))
      (Fin.addCases (A N) (fun _ : Fin 1=>UnaryTemplate.tape N)) := by
  let cap : Fin (B+1)→Nat:=Fin.addCases (fun _ : Fin B=>0) (fun _ : Fin 1=>N+2)
  have word : ZeroPadding.pad (N+2) (CompareMachine.word N)=UnaryTemplate.tape N := by
    simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
  have eq (bank : Fin B→List Bool) :
      (fun i=>ZeroPadding.pad (cap i) (Fin.addCases bank (fun _ : Fin 1=>CompareMachine.word N) i))=
        Fin.addCases bank (fun _ : Fin 1=>UnaryTemplate.tape N) := by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp only [cap,Fin.addCases_left,ZeroPadding.pad_zero]
    · simpa only [cap,Fin.addCases_right] using word
  exact ((CloseoutRowsOriginalClauseLoop.run p N cost H A hround).pad cap).congr_in rfl (eq (A 0)) |>.congr rfl (eq (A N))

def slots {t B : Nat} (body : Fin B→Fin t) (driver : Fin t) : Fin (B+1)→Fin t :=
  Fin.addCases body (fun _ : Fin 1=>driver)

theorem slots_injective {t B : Nat} (body : Fin B→Fin t) (driver : Fin t)
    (hi : Function.Injective body) (hd : ∀i,body i≠driver) : Function.Injective (slots body driver) := by
  intro i
  refine Fin.addCases (fun a=>?_) (fun a=>?_) i
  · intro j
    refine Fin.addCases (fun b=>?_) (fun b=>?_) j
    · intro he
      simp only [slots,Fin.addCases_left] at he
      exact congrArg (Fin.castAdd 1) (hi he)
    · intro he
      simp only [slots,Fin.addCases_left,Fin.addCases_right] at he
      exact False.elim (hd a he)
  · intro j
    refine Fin.addCases (fun b=>?_) (fun b=>?_) j
    · intro he
      simp only [slots,Fin.addCases_left,Fin.addCases_right] at he
      exact False.elim (hd b he.symm)
    · intro _he
      exact congrArg (Fin.natAdd B) (Subsingleton.elim a b)

theorem run_at {t B s : Nat} (p : Machine B s) (body : Fin B→Fin t) (driver : Fin t)
    (hi : Function.Injective body) (hd : ∀i,body i≠driver) (N cost : Nat)
    (H : Nat→Fin B→Nat) (A : Nat→Fin B→List Bool)
    (hin : Fin t→Nat) (tin : Fin t→List Bool)
    (hhead : ∀i,hin (body i)=H 0 i) (htape : ∀i,tin (body i)=A 0 i)
    (hdriver : hin driver=1) (hword : tin driver=UnaryTemplate.tape N)
    (hround : ∀j<N,Step p cost (H j) (A j) (H (j+1)) (A (j+1))) :
    Step (RecoveryFocus.machine (slots body driver) (RepeatMachine.machine p (fun _ _=>true)))
      (N*(cost+3)+3) hin tin
      (dockH (slots body driver) hin (Fin.addCases (H N) (fun _ : Fin 1=>1)))
      (install (slots body driver) tin (Fin.addCases (A N) (fun _ : Fin 1=>UnaryTemplate.tape N))) := by
  apply (template_run p N cost H A hround).dock (slots body driver) (slots_injective body driver hi hd)
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [slots,Fin.addCases_left] using hhead j
    · simpa only [slots,Fin.addCases_right] using hdriver
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [slots,Fin.addCases_left] using htape j
    · simpa only [slots,Fin.addCases_right] using hword

/-- Apply the actual initialized entry to the original clause Repeat. The
round supplier is the remaining exact machine obligation; no blank parser
ports or shortened driver word are assumed by this application. -/
theorem after_ready (sources : EightSources) {gamma : Real} (par : Parameters sources gamma)
    (k r extra : Nat) (hspace : size sources k r par.clauseDegree+96≤extra)
    {B sc : Nat} (clause : Machine B sc)
    (body : Fin B→Fin (WorkspaceSelectedAdmission.originalTapes sources par k+1+1+extra))
    (hi : Function.Injective body)
    (hd : ∀i,body i≠WorkspaceSelectedEntryReady.driver sources par k r extra hspace)
    (N cost entryFuel : Nat) (H : Nat→Fin B→Nat) (A : Nat→Fin B→List Bool)
    (tin middle : Fin (WorkspaceSelectedAdmission.originalTapes sources par k+1+1+extra)→List Bool)
    (hentry : Step (WorkspaceSelectedEntryReady.program sources par k r extra hspace).2 entryFuel
      (fun _=>0) tin (WorkspaceSelectedEntryReady.finalHeads sources par k r extra hspace) middle)
    (hhead : ∀i,WorkspaceSelectedEntryReady.finalHeads sources par k r extra hspace (body i)=H 0 i)
    (htape : ∀i,middle (body i)=A 0 i)
    (hword : middle (WorkspaceSelectedEntryReady.driver sources par k r extra hspace)=UnaryTemplate.tape N)
    (hround : ∀j<N,Step clause cost (H j) (A j) (H (j+1)) (A (j+1))) :
    let port:=slots body (WorkspaceSelectedEntryReady.driver sources par k r extra hspace)
    Step (Composition.machine (WorkspaceSelectedEntryReady.program sources par k r extra hspace).2
      (RecoveryFocus.machine port (RepeatMachine.machine clause (fun _ _=>true))))
      (entryFuel+1+(N*(cost+3)+3)) (fun _=>0) tin
      (dockH port (WorkspaceSelectedEntryReady.finalHeads sources par k r extra hspace)
        (Fin.addCases (H N) (fun _ : Fin 1=>1)))
      (install port middle (Fin.addCases (A N) (fun _ : Fin 1=>UnaryTemplate.tape N))) := by
  exact hentry.seq (run_at clause body _ hi hd N cost H A _ middle hhead htape
    (WorkspaceSelectedEntryReady.driver_head sources par k r extra hspace) hword hround)

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryRepeat
