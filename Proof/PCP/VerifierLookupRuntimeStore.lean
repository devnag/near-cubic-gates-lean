import Proof.PCP.VerifierLookupFieldReaders

/-! The complete lookup's fixed 21-tape boundary. Dimensions and reset
capacity are actual retained tapes. Only immutable input data is mathematical
configuration notation; all changed buffers are outputs of executed calls. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  code : List Bool
  codePos : ℕ
  t : ℕ
  s : ℕ
  j : ℕ
  state : List Bool
  scans : List Bool
  scanPos : ℕ
  halt : Bool
  accept : Bool
  present : Bool
  nextState : List Bool
  tags : List Bool
  flag : Bool
  flagQuery : List Bool
  flagCounter : List Bool
  query : List Bool
  counter : List Bool
  scanCopy : List Bool
  cap : ℕ

def cfg {n : ℕ} (q : Fin n) (d : Store) : Configuration 21 n :=
  ⟨q,fun i=>match i.val with
    | 0=>d.codePos | 1=>1 | 2=>1 | 3=>1 | 5=>1 | 7=>d.scanPos | 20=>1 | _=>0,
    fun i=>match i.val with
    | 0=>frame d.code
    | 1=>CapMachine.counter d.code.length d.t
    | 2=>CapMachine.counter d.code.length d.s
    | 3=>CapMachine.counter d.code.length d.code.length
    | 4=>frame (binary d.j d.s)
    | 5=>CompareMachine.word d.j
    | 6=>frame d.state
    | 7=>d.scans
    | 8=>[d.halt]
    | 9=>[d.accept]
    | 10=>[d.present]
    | 11=>d.nextState
    | 12=>d.tags
    | 13=>[d.flag]
    | 14=>d.flagQuery
    | 15=>d.flagCounter
    | 16=>d.query
    | 17=>d.counter
    | 18=>d.scanCopy
    | 19=>List.replicate d.cap false
    | _=>CompareMachine.word (4*d.t)⟩

def clearSlots : Fin 1 → Fin 21 := ![13]
def flagsQuerySlots : Fin 5 → Fin 21 := ![13,6,14,15,19]
def tableQuerySlots : Fin 5 → Fin 21 := ![18,6,16,17,19]
def navigationSlots : Fin 5 → Fin 21 := ![0,1,2,3,5]
def flagsSelectSlots : Fin 7 → Fin 21 := ![0,14,15,13,19,5,1]
def tableSelectSlots : Fin 7 → Fin 21 := ![0,16,17,13,19,5,1]
def haltSlots : Fin 2 → Fin 21 := ![0,8]
def acceptSlots : Fin 2 → Fin 21 := ![0,9]
def presenceSlots : Fin 2 → Fin 21 := ![0,10]
def claimedSlots : Fin 3 → Fin 21 := ![7,18,1]
def nextSlots : Fin 3 → Fin 21 := ![0,11,5]
def tagsSlots : Fin 3 → Fin 21 := ![0,12,20]

noncomputable def clearProgram := RecoveryFocus.machine clearSlots LookupReadBit.clear
noncomputable def flagsQueryProgram := RecoveryFocus.machine flagsQuerySlots LookupQuery.machine
noncomputable def tableQueryProgram := RecoveryFocus.machine tableQuerySlots LookupQuery.machine
noncomputable def flagsNavigationProgram := RecoveryFocus.machine navigationSlots (LookupNavigation.machine false)
noncomputable def tableNavigationProgram := RecoveryFocus.machine navigationSlots (LookupNavigation.machine true)
noncomputable def flagsSelectProgram := RecoveryFocus.machine flagsSelectSlots LookupPosition.flagsMachine
noncomputable def tableSelectProgram := RecoveryFocus.machine tableSelectSlots LookupPosition.tableMachine
noncomputable def haltProgram := RecoveryFocus.machine haltSlots LookupReadBit.machine
noncomputable def acceptProgram := RecoveryFocus.machine acceptSlots LookupReadBit.machine
noncomputable def presenceProgram := RecoveryFocus.machine presenceSlots LookupReadBit.machine
noncomputable def claimedProgram := RecoveryFocus.machine claimedSlots LookupRetainField.machine
noncomputable def nextProgram := RecoveryFocus.machine nextSlots FieldMachine.machine
noncomputable def tagsProgram := RecoveryFocus.machine tagsSlots FieldMachine.machine

def navigation (d : Store) : LookupNavigation.Store :=
  ⟨frame d.code,d.codePos,d.code.length,d.t,d.s,d.j⟩
def positioned (d : Store) (pos : ℕ) : Store := {d with codePos:=pos}
def cleared (d : Store) : Store := {d with flag:=false}
def flagsInitialized (d : Store) : Store :=
  {d with flagQuery:=frame d.state,flagCounter:=frame (List.replicate d.state.length false)}
def claimed (d : Store) (bits : List Bool) : Store := {d with scanCopy:=frame bits}
def tableInitialized (d : Store) (bits : List Bool) : Store :=
  {d with query:=frame (bits++d.state),counter:=frame (List.replicate (bits.length+d.state.length) false)}
def readHalt (d : Store) (bit : Bool) : Store := {d with halt:=bit,codePos:=d.codePos+2}
def readAccept (d : Store) (bit : Bool) : Store := {d with accept:=bit,codePos:=d.codePos+2}
def readPresence (d : Store) (bit : Bool) : Store := {d with present:=bit,codePos:=d.codePos+2}
def readNext (d : Store) (bits : List Bool) : Store := {d with nextState:=frame bits,codePos:=d.codePos+2*bits.length}
def readTags (d : Store) (bits : List Bool) : Store := {d with tags:=frame bits,codePos:=d.codePos+2*bits.length}

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
