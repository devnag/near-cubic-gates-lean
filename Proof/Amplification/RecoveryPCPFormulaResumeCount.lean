import Proof.Amplification.RecoveryProjectionDimensionUnary
import Proof.PCP.VerifierDecodingUnaryFrame

/-! Physically derive the exponential randomness-loop count from the actual
retained unary width. The existing frame writer and binary-to-unary parser
produce exactly Compare.word (2^R-1); no count field is assumed. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCount
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def frameSlots : Fin 2→Fin 6 := ![0,1]
def parseSlots (i : Fin 5) : Fin 6 := ⟨i.val+1,by have hi:=i.isLt; omega⟩
theorem frame_injective : Function.Injective frameSlots := by decide
theorem parse_injective : Function.Injective parseSlots := by
  intro i j h; apply Fin.ext; have hv:=congrArg Fin.val h
  dsimp only [parseSlots] at hv; omega
noncomputable def frameMachine := RecoveryFocus.machine frameSlots UnaryFrameMachine.machine
noncomputable def parseMachine := RecoveryFocus.machine parseSlots RecoveryProjectionDimension.parsedMachine
noncomputable def machine := Composition.machine frameMachine parseMachine

def heads : Fin 6→Nat := ![1,0,0,0,0,0]
def input (R : Nat) : Fin 6→List Bool := ![CompareMachine.word R,[],[],[],[],[]]
def framed (R : Nat) : Fin 6→List Bool :=
  ![CompareMachine.word R,RepairOrdinary.frame (List.replicate R true),[],[],[],[]]
def budget (R : Nat) := 24*2^R*(R+1)+4*R+5

theorem count_run (R : Nat) : ∃ r,
    runFrom machine (budget R) ⟨machine.start,heads,input R⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes 0=CompareMachine.word R ∧
      r.final.tapes 4=CompareMachine.word (2^R-1) ∧ r.steps≤budget R := by
  obtain ⟨raw,hRaw,rf,rs,_rp⟩ := UnaryFrameMachine.unary_frame_run R
  obtain ⟨first,hFirst,_fc,fs,fh,ft,fo⟩ := RecoveryFocus.dock frameSlots frame_injective
    UnaryFrameMachine.machine (4*R+2) heads (input R) _
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) raw hRaw
  have hheads : first.final.heads=heads := by
    funext i; fin_cases i
    · change first.final.heads (frameSlots 0)=_; rw [fh,rf]; rfl
    · change first.final.heads (frameSlots 1)=_; rw [fh,rf]; rfl
    all_goals rw [(fo _ (by intro j; fin_cases j <;> decide)).1]
  have htapes : first.final.tapes=framed R := by
    funext i; fin_cases i
    · change first.final.tapes (frameSlots 0)=_; rw [ft,rf]; rfl
    · change first.final.tapes (frameSlots 1)=_; rw [ft,rf]; rfl
    all_goals rw [(fo _ (by intro j; fin_cases j <;> decide)).2]; rfl
  obtain ⟨parsed,hParsed,hCount⟩ := RecoveryProjectionDimension.parsed_ready (List.replicate R true)
  obtain ⟨base,hBase,bt,bh,bs⟩ := hParsed
  obtain ⟨last,hLast,_lc,ls,lh,lt,lo⟩ := RecoveryFocus.dock parseSlots parse_injective
    RecoveryProjectionDimension.parsedMachine _ first.final.heads first.final.tapes _
    (by intro i; rw [hheads]; fin_cases i <;> rfl)
    (by intro i; rw [htapes]; fin_cases i <;> rfl) base hBase
  have hall:=Composition.run_join frameMachine parseMachine _ _ _ first last hFirst hLast
  have htime : (4*R+2)+1+(Unary.budget (List.replicate R true)+2)=budget R := by
    unfold Unary.budget budget
    rw [List.length_replicate,BoundedCounter.true_value]
    ring
  rw [htime] at hall
  refine ⟨_,hall,?_,?_,?_,?_⟩
  · funext i; fin_cases i
    · change last.final.heads 0=_
      rw [(lo 0 (by intro j h; have hv:=congrArg Fin.val h; dsimp [parseSlots] at hv; omega)).1,hheads]
      rfl
    all_goals
      first
      | (change last.final.heads (parseSlots 0)=_; rw [lh,bh]; rfl)
      | (change last.final.heads (parseSlots 1)=_; rw [lh,bh]; rfl)
      | (change last.final.heads (parseSlots 2)=_; rw [lh,bh]; rfl)
      | (change last.final.heads (parseSlots 3)=_; rw [lh,bh]; rfl)
      | (change last.final.heads (parseSlots 4)=_; rw [lh,bh]; rfl)
  · change last.final.tapes 0=_
    rw [(lo 0 (by intro j h; have hv:=congrArg Fin.val h; dsimp [parseSlots] at hv; omega)).2,htapes]
    rfl
  · change last.final.tapes (parseSlots 3)=_
    rw [lt,bt,hCount]
    congr 1
    have hv:=BoundedCounter.true_value R
    omega
  · change first.steps+1+last.steps≤_
    rw [←htime]
    omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCount
