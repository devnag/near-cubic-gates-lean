import Proof.Rows.CapLoop

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace CapWidthReader
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound RadixSemantics

def fieldSlots (i : Fin 6) : Fin 11 := i.castAdd 5
def seekSlots : Fin 4 → Fin 11 := ![6,7,4,3]
def loopSlots : Fin 7 → Fin 11 := ![6,7,4,3,8,9,10]
theorem field_injective : Function.Injective fieldSlots := by decide
theorem seek_injective : Function.Injective seekSlots := by decide
theorem loop_injective : Function.Injective loopSlots := by decide

theorem field_pick (i : Fin 11) : RecoveryFocus.pick fieldSlots i=
    (![some 0,some 1,some 2,some 3,some 4,some 5,none,none,none,none,none] :
      Fin 11 → Option (Fin 6)) i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot _ field_injective 0
  · exact RecoveryFocus.pick_slot _ field_injective 1
  · exact RecoveryFocus.pick_slot _ field_injective 2
  · exact RecoveryFocus.pick_slot _ field_injective 3
  · exact RecoveryFocus.pick_slot _ field_injective 4
  · exact RecoveryFocus.pick_slot _ field_injective 5
  all_goals decide
theorem seek_pick (i : Fin 11) : RecoveryFocus.pick seekSlots i=
    (![none,none,none,some 3,some 2,none,some 0,some 1,none,none,none] :
      Fin 11 → Option (Fin 4)) i := by
  fin_cases i
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot _ seek_injective 3
  · exact RecoveryFocus.pick_slot _ seek_injective 2
  · decide
  · exact RecoveryFocus.pick_slot _ seek_injective 0
  · exact RecoveryFocus.pick_slot _ seek_injective 1
  all_goals decide

noncomputable def field := RecoveryFocus.machine fieldSlots MatrixDimensionField.machine
noncomputable def seek := RecoveryFocus.machine seekSlots CapSentinelInput.seek
noncomputable def loop := RecoveryFocus.machine loopSlots CapDoublingBodies.machine
noncomputable def machine := Composition.machine (Composition.machine field seek) loop

def initialHeads (pos : Nat) : Fin 11 → Nat := ![pos,0,0,0,0,0,0,0,0,0,0]
def initialBank (source : List Bool) : Fin 11 → List Bool := ![source,[],[],[],[],[],[],[],[],[],[]]
def parsedHeads (pos : Nat) : Fin 11 → Nat := ![pos,0,0,1,0,0,0,0,0,0,0]
def parsedBank (source bits : List Bool) : Fin 11 → List Bool :=
  ![source,List.replicate bits.length true,List.replicate bits.length true,
    UnaryTemplate.tape bits.length,frame bits,List.replicate (2*bits.length+1) false,
    [],[],[],[],[]]
def readyHeads (pos w : Nat) : Fin 11 → Nat := ![pos,0,0,w,2*w-1,0,1,1,0,0,0]
def readyBank (source bits : List Bool) : Fin 11 → List Bool :=
  ![source,List.replicate bits.length true,List.replicate bits.length true,
    UnaryTemplate.tape bits.length,frame bits,List.replicate (2*bits.length+1) false,
    CapDoublingPass.word 0,CapDoublingPass.word 0,[],[],[]]

def outputs (source : List Bool) (pos n : Nat) (H : Fin 11 → Nat)
    (A : Fin 11 → List Bool) : Prop :=
  A 0=source ∧ H 0=pos ∧ A 8=List.replicate n true ∧ H 8=0 ∧
  A 9=List.replicate n true ∧ H 9=0 ∧ A 10=UnaryTemplate.tape n ∧ H 10=1

theorem field_run (pre bits suffix : List Bool) :
    let source := pre++List.replicate bits.length true++false::(bits++suffix)
    Step field (6*bits.length+7) (initialHeads pre.length) (initialBank source)
      (parsedHeads (pre.length+2*bits.length+1)) (parsedBank source bits) := by
  dsimp only
  let source := pre++List.replicate bits.length true++false::(bits++suffix)
  obtain ⟨r,hr,hf,_⟩ := MatrixDimensionField.field_run pre bits suffix
  have base := Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have h := base.dock fieldSlots field_injective (initialHeads pre.length) (initialBank source)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  apply h.congr
  · funext i;fin_cases i <;> simp [dockH,field_pick,parsedHeads,initialHeads,MatrixDimensionField.output]
  · funext i;fin_cases i <;> simp [install,field_pick,parsedBank,initialBank,MatrixDimensionField.output,source]

theorem seek_run (source bits : List Bool) (pos : Nat) :
    Step seek (2*bits.length+2) (parsedHeads pos) (parsedBank source bits)
      (readyHeads pos bits.length) (readyBank source bits) := by
  have h := (CapSentinelInput.seek_run bits.length bits).dock
    seekSlots seek_injective (parsedHeads pos) (parsedBank source bits)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  apply h.congr
  · funext i;fin_cases i <;> simp [dockH,seek_pick,readyHeads,parsedHeads]
  · funext i;fin_cases i <;> simp [install,seek_pick,readyBank,parsedBank,
      CapSentinelInput.seekData,CapSentinelInput.word]

theorem loop_run (source bits : List Bool) (pos : Nat) (hne : bits≠[]) :
    ∃ H A, Step loop (8*value bits+12*bits.length+6)
      (readyHeads pos bits.length) (readyBank source bits) H A ∧
      outputs source pos (value bits) H A := by
  obtain ⟨H,A,base,h8,hh8,h9,hh9,h10,hh10⟩ :=
    CapDoublingBodies.loop_run bits hne
  have h := base.dock loopSlots loop_injective
    (readyHeads pos bits.length) (readyBank source bits)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  have hn : RecoveryFocus.pick loopSlots (0 : Fin 11)=none := by decide
  refine ⟨_,_,h,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [install,hn,readyBank,Matrix.cons_val_zero]
  · simp only [dockH,hn,readyHeads,Matrix.cons_val_zero]
  · change install loopSlots (readyBank source bits) A (loopSlots 4)=_
    simpa only [install,RecoveryFocus.pick_slot _ loop_injective] using h8
  · change dockH loopSlots (readyHeads pos bits.length) H (loopSlots 4)=_
    simpa only [dockH_slot _ loop_injective] using hh8
  · change install loopSlots (readyBank source bits) A (loopSlots 5)=_
    simpa only [install,RecoveryFocus.pick_slot _ loop_injective] using h9
  · change dockH loopSlots (readyHeads pos bits.length) H (loopSlots 5)=_
    simpa only [dockH_slot _ loop_injective] using hh9
  · change install loopSlots (readyBank source bits) A (loopSlots 6)=_
    simpa only [install,RecoveryFocus.pick_slot _ loop_injective] using h10
  · change dockH loopSlots (readyHeads pos bits.length) H (loopSlots 6)=_
    simpa only [dockH_slot _ loop_injective] using hh10

/-- Width parsing, one paid end scan and the reverse doubling loop. The
original metadata cursor is retained at the next field. -/
theorem run (pre bits suffix : List Bool) (hne : bits≠[]) :
    let source := pre++List.replicate bits.length true++false::(bits++suffix)
    ∃ H A, Step machine (8*value bits+20*bits.length+17)
      (initialHeads pre.length) (initialBank source) H A ∧
      outputs source (pre.length+2*bits.length+1) (value bits) H A := by
  dsimp only
  let source := pre++List.replicate bits.length true++false::(bits++suffix)
  obtain ⟨H,A,third,fields⟩ := loop_run source bits (pre.length+2*bits.length+1) hne
  have joined := ((field_run pre bits suffix).seq
    (seek_run source bits (pre.length+2*bits.length+1))).seq third
  exact ⟨H,A,joined.enlarge (by omega),fields⟩

theorem natural_run (pre suffix : List Bool) (n : Nat) :
    ∃ H A, Step machine (8*n+20*natBitLength n+17)
      (initialHeads pre.length) (initialBank (pre++RepairRepresentation.natWord n++suffix)) H A ∧
      outputs (pre++RepairRepresentation.natWord n++suffix)
        (pre.length+2*natBitLength n+1) n H A := by
  let bits := SignedSortKey.binary (natBitLength n) n
  have hv : value bits=n := SignedSortKey.binary_value _ _
    (Nat.lt_pow_succ_log_self (by decide) n)
  have hl : bits.length=natBitLength n := SignedSortKey.binary_length _ _
  have hne : bits≠[] := by
    intro he
    have hz := congrArg List.length he
    simp only [hl,List.length_nil] at hz
    unfold natBitLength at hz
    omega
  have source : pre++List.replicate bits.length true++false::(bits++suffix)=
      pre++RepairRepresentation.natWord n++suffix := by
    rw [hl]
    dsimp only [bits]
    simp only [WilliamsInputHeader.natWord_eq,List.append_assoc,List.cons_append]
  obtain ⟨H,A,h,fields⟩ := run pre bits suffix hne
  rw [source,hv,hl] at h fields
  exact ⟨H,A,h,fields⟩

end CapWidthReader
