import Proof.Amplification.RecoveryCaseOneBitInput
import Proof.Amplification.RecoveryCaseOneEntry

/-! A single framed external word supplies all data ports of the actual
Case-1 bit program. The entry parser and the bit program share only the
physically reconstructed hierarchy word and the retained address. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneOrdinary
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)

def base (k : Nat) := RecoveryCaseOneBit.tapes source amp k
def tapes (k : Nat) := 14+base source amp k
def entrySlots (k : Nat) (i : Fin 14) : Fin (tapes source amp k) := i.castAdd (base source amp k)
def bitSlots (k : Nat) (i : Fin (base source amp k)) : Fin (tapes source amp k) :=
  if i.val=0 then (10 : Fin 14).castAdd (base source amp k) else
  if i.val=RecoveryCaseOneBit.base source amp k then (7 : Fin 14).castAdd (base source amp k) else i.natAdd 14

theorem entry_injective (k : Nat) : Function.Injective (entrySlots source amp k) := by
  intro i j h; exact Fin.ext (congrArg (fun z : Fin (tapes source amp k)=>z.val) h)
theorem bit_injective (k : Nat) : Function.Injective (bitSlots source amp k) := by
  intro i j h
  have hv:=congrArg (fun z : Fin (tapes source amp k)=>z.val) h
  apply Fin.ext
  dsimp only [bitSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega

theorem bit_positive (k : Nat) (i : Fin (base source amp k)) : (bitSlots source amp k i).val≠0 := by
  dsimp only [bitSlots]
  split_ifs <;> simp only [Fin.val_castAdd,Fin.val_natAdd] <;> omega

def ports (k : Nat) : Ports (tapes source amp k) :=
  ⟨by dsimp [tapes]; omega,
    bitSlots source amp k (RecoveryCaseOneBit.ports source amp k).outputTape,
    bit_positive source amp k _,
    bitSlots source amp k (RecoveryCaseOneBit.ports source amp k).queryTape,
    bit_positive source amp k _⟩
def first (k : Nat) := RecoveryFocus.machine (entrySlots source amp k) RecoveryCaseOneEntry.machine
def pieces (k CH Cpad : Nat) (code : List Bool) : Fin 2→Piece (tapes source amp k) :=
  ![ordinary (first source amp k),
    focused (RecoveryCaseOneBit.program source amp k CH Cpad code) (bitSlots source amp k)]
def next (k CH Cpad : Nat) (code : List Bool) (j : Fin 2)
    (_ : Fin (pieces source amp k CH Cpad code j).states) (_ : Fin (tapes source amp k)→Bool) : Option (Fin 2) :=
  if j=0 then some 1 else none
def program (k CH Cpad : Nat) (code : List Bool) :=
  (ports source amp k).program (graph (pieces source amp k CH Cpad code) 0 (next source amp k CH Cpad code))
def input (k : Nat) (raw : List Bool) : Fin (tapes source amp k)→List Bool :=
  Fin.addCases (m:=14) (n:=base source amp k) (motive:=fun _=>List Bool)
    (RecoveryCaseOneEntry.input raw) (fun _=>[])

theorem entry_input (k : Nat) (raw : List Bool) (i : Fin 14) :
    input source amp k raw (entrySlots source amp k i)=RecoveryCaseOneEntry.input raw i := by
  simp only [input,entrySlots,Fin.addCases_left]

end
end NearCubicWires.RepairSource.RecoveryCaseOneOrdinary
