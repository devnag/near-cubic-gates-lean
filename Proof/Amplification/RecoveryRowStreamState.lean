import Proof.Amplification.RecoveryRowLeaf

/-! Shared51-tape certificate-row state. The streamed row reader writes its
payload directly onto the clause-input tape; all other arithmetic workspace
and the retained valuation source survive the paid read. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RecoveryClauseEvaluation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def replaceState (s : State) (bits : List Bool) : State := {s with bits:=bits}

theorem replace_other (s : State) (e : Extra) (bits : List Bool)
    (hw : bits.length=s.bits.length) (i : Fin 42) (hi : i≠0) :
    RecoveryClauseEvaluation.tapes (replaceState s bits) e i=RecoveryClauseEvaluation.tapes s e i := by
  refine Fin.addCases (m:=28) (n:=14) (motive:=fun j=>j≠0 →
    RecoveryClauseEvaluation.tapes (replaceState s bits) e j=RecoveryClauseEvaluation.tapes s e j) ?_ ?_ i hi
  · intro j hj
    rw [tapes_left,tapes_left]
    fin_cases j <;> first
      | exact False.elim (hj rfl)
      | simp [State.tapes,State.core,replaceState,RecoveryRawListStep.input,RecoveryRawListStep.tapes,
          RecoveryReusableUnpair.input,RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw,Fin.addCases]
  · intro j _
    rw [tapes_right,tapes_right]
    simp [Extra.tapes,replaceState,RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw]

theorem replace_valid (s : State) (e : Extra) (word bits : List Bool)
    (hs : s.Valid) (he : e.Valid s word) (hw : bits.length=s.bits.length) :
    (replaceState s bits).Valid ∧ e.Valid (replaceState s bits) word := by
  have hc : RecoveryReusableUnpair.capacity bits=RecoveryReusableUnpair.capacity s.bits := by
    simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw]
  constructor
  · simpa only [State.Valid,replaceState,hc,hw] using hs
  · refine ⟨he.source,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [replaceState,hw] using he.row
    · simpa only [replaceState,hc] using he.counter
    · simpa only [replaceState,hw] using he.count
    · simpa only [replaceState,hw] using he.committed
    · simpa only [replaceState,hw] using he.cap
    · simpa only [replaceState,hw] using he.prefixBound
    · simpa only [replaceState,hc] using he.reset

structure Data where
  state : State
  extra : Extra
  kind : List Bool
  code : List Bool
  count : List Bool
  flags : Fin 3→Bool
  source : List Bool
  pos : Nat
  valid : Bool

def Data.left (d : Data) : Fin 46→List Bool :=
  RecoveryRowLeaf.tapes (RecoveryClauseEvaluation.tapes d.state d.extra) d.kind d.flags
def Data.right (d : Data) : Fin 5→List Bool :=
  ![frame d.code,frame d.count,d.source,CompareMachine.word d.state.bits.length,[d.valid]]
def Data.rightHeads (d : Data) : Fin 5→Nat := ![0,0,d.pos,1,0]
def Data.cfg {s : Nat} (d : Data) (q : Fin s) : Configuration 51 s :=
  ⟨q,Fin.addCases (m:=46) (n:=5) (motive:=fun _=>Nat) (fun _=>0) d.rightHeads,
    Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) d.left d.right⟩
def Data.reader (d : Data) : RecoveryRowFields.Data :=
  ⟨d.source,d.pos,d.state.bits.length,![frame d.kind,frame d.code,frame d.count,frame d.state.bits],d.valid⟩
def rowSlots : Fin 7→Fin 51 := ![48,42,46,47,0,49,50]
theorem rowSlots_injective : Function.Injective rowSlots := by decide
noncomputable def readMachine := RecoveryFocus.machine rowSlots RecoveryRowFields.machine
noncomputable def leafMachine := TapeEmbedding.machine 5 RecoveryRowLeaf.machine

def Data.Valid (d : Data) (word : List Bool) : Prop :=
  d.state.Valid ∧ d.extra.Valid d.state word ∧
    d.kind.length ≤ d.state.bits.length ∧ d.code.length ≤ d.state.bits.length ∧ d.count.length ≤ d.state.bits.length

theorem reader_valid (d : Data) (word : List Bool) (h : d.Valid word) : d.reader.Valid := by
  intro i
  rcases h with ⟨_,_,hk,hc,hn⟩
  fin_cases i <;> simp [Data.reader] <;> omega

def Data.afterRead (d : Data) (bits : List Bool) : Data :=
  {d with
    state:=replaceState d.state (RecoveryRowFields.words d.state.bits.length bits 3)
    kind:=RecoveryRowFields.words d.state.bits.length bits 0
    code:=RecoveryRowFields.words d.state.bits.length bits 1
    count:=RecoveryRowFields.words d.state.bits.length bits 2
    pos:=d.pos+8*d.state.bits.length
    valid:=true}

theorem words_length (width : Nat) (bits : List Bool) (i : Fin 4)
    (h : 4*width ≤ bits.length) : (RecoveryRowFields.words width bits i).length=width := by
  unfold RecoveryRowFields.words
  rw [List.length_take,List.length_drop]
  apply Nat.min_eq_left
  have hi := i.isLt
  have hm := Nat.mul_le_mul_right width (show i.val+1 ≤ 4 by omega)
  rw [Nat.succ_mul] at hm
  omega

theorem afterRead_width (d : Data) (bits : List Bool) (h : 4*d.state.bits.length ≤ bits.length) :
    (d.afterRead bits).state.bits.length=d.state.bits.length := words_length _ _ 3 h

theorem afterRead_valid (d : Data) (word bits : List Bool) (hd : d.Valid word)
    (h : 4*d.state.bits.length ≤ bits.length) : (d.afterRead bits).Valid word := by
  have hw := afterRead_width d bits h
  obtain ⟨hs,he⟩ := replace_valid d.state d.extra word _ hd.1 hd.2.1 hw
  refine ⟨hs,he,?_,?_,?_⟩
  all_goals change (RecoveryRowFields.words d.state.bits.length bits _).length ≤ (d.afterRead bits).state.bits.length
  all_goals rw [hw,words_length _ _ _ h]

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem read_input (d : Data) :
    RecoveryFocus.config rowSlots (d.cfg readMachine.start).heads (d.cfg readMachine.start).tapes
      (d.reader.cfg RecoveryRowFields.machine.start)=d.cfg readMachine.start := by
  apply focus_configuration rowSlots rowSlots_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i _; rfl
  · intro i _; rfl

end NearCubicWires.RepairOrdinary.RecoveryRowStream
