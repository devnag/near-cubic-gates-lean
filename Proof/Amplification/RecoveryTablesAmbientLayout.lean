import Proof.Amplification.RecoveryTablesDrivers

/-! The fresh table workspace shares only the scanner source and two
already produced scalar drivers. Its four false cells and two head moves
are initialized by one actual transition. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTablesAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailHeads : Fin 9→Nat := ![1,0,0,0,1,0,0,0,0]
def tailTapes : Fin 9→List Bool := ![[false],[],[],[false],[false],[],[],[false],[]]
def heads (h : Fin 270→Nat) : Fin 279→Nat :=
  Fin.addCases (m:=270) (n:=9) (motive:=fun _=>Nat) h tailHeads
def tapes (a : Fin 270→List Bool) : Fin 279→List Bool :=
  Fin.addCases (m:=270) (n:=9) (motive:=fun _=>List Bool) a tailTapes
def coldHeads (h : Fin 270→Nat) : Fin 279→Nat :=
  Fin.addCases (m:=270) (n:=9) (motive:=fun _=>Nat) h (fun _=>0)
def coldTapes (a : Fin 270→List Bool) : Fin 279→List Bool :=
  Fin.addCases (m:=270) (n:=9) (motive:=fun _=>List Bool) a (fun _=>[])
def slots : Fin 12→Fin 279 := ![193,270,96,271,272,273,62,274,275,276,277,278]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def program := RecoveryFocus.machine slots RecoveryColdTables.resetProgram

structure Sources (word : List Bool) (k width cap : Nat) (h : Fin 270→Nat) (a : Fin 270→List Bool) : Prop where
  sourceHead : h 193=2*k
  sourceTape : a 193=frame word
  widthHead : h 62=1
  widthTape : a 62=CompareMachine.word (2*width)
  capHead : h 96=1
  capTape : a 96=CompareMachine.word cap

def bootProgram : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    (fun i=>if i.val=0 ∨ i.val=3 ∨ i.val=4 ∨ i.val=7 then some false else none),
    (fun i=>if i.val=0 ∨ i.val=4 then .right else .stay)⟩ else none

theorem boot_run : ∃ r,run bootProgram 1 (fun _=>[])=some r ∧
    r.final.heads=tailHeads ∧ r.final.tapes=tailTapes ∧ r.steps=1 := by
  have h : step bootProgram (initialConfiguration bootProgram (fun _=>[]))=
      some (⟨1,tailHeads,tailTapes⟩ : Configuration 9 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],hs⟩

noncomputable def ambientBoot := RecoveryBankPair.rightMachine (t:=270) bootProgram
theorem boot_ambient (h : Fin 270→Nat) (a : Fin 270→List Bool) :
    ∃ r,runFrom ambientBoot 1 ⟨ambientBoot.start,coldHeads h,coldTapes a⟩=some r ∧
      r.final.heads=heads h ∧ r.final.tapes=tapes a ∧ r.steps=1 := by
  obtain ⟨base,hr,hh,ht,hs⟩ := boot_run
  obtain ⟨r,h,he,hf⟩ := RecoveryBankPair.right_run bootProgram 1 _ base hr h a
  refine ⟨r,h,?_,?_,he.trans hs⟩
  · rw [hf]
    change Fin.addCases (m:=270) (n:=9) (motive:=fun _=>Nat) _ base.final.heads=_
    rw [hh]
    rfl
  · rw [hf]
    change Fin.addCases (m:=270) (n:=9) (motive:=fun _=>List Bool) _ base.final.tapes=_
    rw [ht]
    rfl

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem input_layout (word : List Bool) (k width cap : Nat) (h : Fin 270→Nat) (a : Fin 270→List Bool)
    (ha : Sources word k width cap h a) :
    RecoveryFocus.config slots (heads h) (tapes a)
      (Rewind.recording (RecoveryColdTables.initial RecoveryColdTables.machine.start word k width cap) 0)=
      (⟨program.start,heads h,tapes a⟩ : Configuration 279 _) := by
  apply focus_configuration slots slots_injective
  · rfl
  · intro j; fin_cases j <;> first | exact ha.sourceHead.symm | exact ha.capHead.symm | exact ha.widthHead.symm | rfl
  · intro j; fin_cases j <;> first | exact ha.sourceTape.symm | exact ha.capTape.symm | exact ha.widthTape.symm | rfl
  · intro i _; rfl
  · intro i _; rfl

end NearCubicWires.RepairOrdinary.RecoveryColdTablesAmbient
