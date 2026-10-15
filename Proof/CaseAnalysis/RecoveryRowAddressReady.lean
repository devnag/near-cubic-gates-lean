import Proof.CaseAnalysis.RecoveryRowAddressMeaning

/-! Start the existing raw-address copy from the projector's zero-head
driver boundary and pay one complete rewind, including that driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddress
open LocalBitMultitape RecoveryExecution Composition
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def position : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun i=>if i=2 then .right else .stay⟩ else none
noncomputable def prepared:=Composition.machine position machine
noncomputable def readyMachine:=Rewind.machine prepared
def readyBudget (fields : List (List Bool)):=2*(budget fields+2)+2
def rawInput (fields : List (List Bool)) (tail : List Bool) : Fin 3→List Bool:=
  ![FieldList.stream fields++tail,[],CompareMachine.word fields.length]
def rawOutput (fields : List (List Bool)) (tail : List Bool) : Fin 3→List Bool:=
  ![FieldList.stream fields++tail,fields.flatten,CompareMachine.word fields.length]

theorem position_run (A : Fin 3→List Bool) :
    ∃ r,run position 1 A=some r ∧ r.steps=1 ∧ r.final.heads=![0,0,1] ∧ r.final.tapes=A := by
  have step : LocalBitMultitape.step position ⟨0,fun _=>0,A⟩=some ⟨1,![0,0,1],A⟩ := by
    change some (applyAction (⟨0,fun _=>0,A⟩ : Configuration 3 2)
      ⟨1,fun _=>none,fun i=>if i=2 then .right else .stay⟩)=_
    congr 1
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  obtain ⟨r,rr,rf,rs⟩:=(Timed.single (by rfl) step).run (by rfl)
  exact ⟨r,rr,rs,congrArg Configuration.heads rf,congrArg Configuration.tapes rf⟩

theorem prepared_run (fields : List (List Bool)) (tail : List Bool) :
    ∃ r,run prepared (budget fields+2) (rawInput fields tail)=some r ∧
      r.final.tapes=rawOutput fields tail ∧ r.steps=budget fields+2 := by
  obtain ⟨p,pr,ps,ph,pt⟩:=position_run (rawInput fields tail)
  obtain ⟨q,qr,qf,qs⟩:=copy_run [] fields tail []
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at qr qf
  have qr' : runFrom machine (budget fields) (restart p.final machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    have hi : (⟨machine.start,![0,0,1],rawInput fields tail⟩ : Configuration 3 _)=
        cfg 0 (FieldList.stream fields++tail) 0 [] fields.length 1 := by
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> rfl
    rw [hi]
    exact qr
  have whole:=Composition.run_join position machine _ _ _ p q pr qr'
  have hb : 1+1+budget fields=budget fields+2:=by omega
  rw [hb] at whole
  refine ⟨joinedReceipt p q,whole,?_,?_⟩
  · change q.final.tapes=_
    rw [qf]
    funext i;fin_cases i <;> rfl
  · change p.steps+1+q.steps=_
    omega

theorem address_ready (fields : List (List Bool)) (tail : List Bool) (B : ℕ)
    (hB : budget fields+2≤B) :
    ClockJoin.ReadyRun readyMachine (readyBudget fields)
      (Fin.addCases (m:=3) (n:=1) (rawInput fields tail) (fun _=>List.replicate B false))
      (Fin.addCases (m:=3) (n:=1) (rawOutput fields tail) (fun _=>List.replicate B false)) := by
  obtain ⟨p,pr,pt,ps⟩:=prepared_run fields tail
  obtain ⟨r,rr,rt,rc,rh,rs,_⟩:=Rewind.Workspace.reset_workspace prepared _ _ p pr B
  rw [ps] at rr
  refine ⟨r,rr,?_,rh,?_⟩
  · funext i
    refine Fin.addCases (m:=3) (n:=1) (fun j=>?_) (fun j=>?_) i
    · rw [rt j,pt]
      simp only [Fin.addCases_left]
    · fin_cases j
      simp only [Fin.addCases_right]
      change r.final.tapes 3=_
      change r.final.tapes 3=List.replicate (max B p.steps) false at rc
      rw [rc,ps,max_eq_left hB]
  · rw [rs,ps]
    exact Nat.le_refl _

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddress
