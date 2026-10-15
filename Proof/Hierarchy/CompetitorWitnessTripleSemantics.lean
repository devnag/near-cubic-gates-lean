import Proof.Hierarchy.CompetitorWitnessTriple

/-! Exact connection of the physically extracted words to the existing
canonical typed recovery-witness header, including both family tags. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessTriple
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CanonicalBinary CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def node (bits : List Bool) (k : ℕ) := value (word bits k)
def field (bits : List Bool) (k : ℕ) := value (RecoveryFixedUnpair.leftWord (word bits k))
def nodeCode (code : ℕ) : ℕ → ℕ
  | 0 => code
  | k+1 => (Nat.unpair (nodeCode code k)).2

theorem node_eq (bits : List Bool) (k : ℕ) : node bits k=nodeCode (value bits) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (RecoveryFixedUnpair.word_values (word bits k)).2.trans (congrArg (fun n => (Nat.unpair n).2) ih)
theorem field_eq (bits : List Bool) (k : ℕ) : field bits k=(Nat.unpair (nodeCode (value bits) k)).1 := by
  exact (RecoveryFixedUnpair.word_values (word bits k)).1.trans (congrArg (fun n => (Nat.unpair n).1) (node_eq bits k))
theorem pair_node (bits : List Bool) (k : ℕ) : Nat.pair (field bits k) (node bits (k+1))=node bits k := by
  rw [field_eq,node_eq,nodeCode,node_eq]
  exact Nat.pair_unpair _

def structural (bits : List Bool) : Prop :=
  field bits 0=1 ∧ field bits 2=1 ∧ field bits 4=1 ∧ node bits 6=0

theorem extracted_values (bits : List Bool) (mode oracle sum : ℕ)
    (h : value bits=encodeTaggedList [mode,oracle,sum]) :
    structural bits ∧ field bits 1=mode ∧ field bits 3=oracle ∧ field bits 5=sum := by
  simp only [structural,field_eq,node_eq,h,nodeCode,encodeTaggedList,Nat.unpair_pair]
  trivial

theorem structural_iff (bits : List Bool) : structural bits ↔
    value bits=encodeTaggedList [field bits 1,field bits 3,field bits 5] := by
  constructor
  · rintro ⟨h0,h2,h4,h6⟩
    change node bits 0=_
    rw [←pair_node bits 0,←pair_node bits 1,←pair_node bits 2,←pair_node bits 3,
      ←pair_node bits 4,←pair_node bits 5,h0,h2,h4,h6]
    rfl
  · intro h
    exact (extracted_values bits _ _ _ h).1

theorem encoded_modes : encodeNat 0=0 ∧ encodeNat 1=3 := by
  norm_num [encodeNat,encodeBits,encodeBoolList,Nat.zero_bits,Nat.one_bits,encodeBalancedList,boolCode,Nat.pair]

def headerValid (bits : List Bool) : Prop := structural bits ∧ (field bits 1=0 ∨ field bits 1=3)

theorem checked_header {limits : RecoveryWitnessLimits} (w : CheckedRecoveryWitness limits)
    (bits : List Bool) (h : value bits=w.code) : headerValid bits := by
  cases w with
  | symmetric oracle hs sum =>
    obtain ⟨hstruct,hmode,_,_⟩ := extracted_values bits _ _ _ h
    exact ⟨hstruct,Or.inl (hmode.trans encoded_modes.1)⟩
  | threshold oracle hs sum =>
    obtain ⟨hstruct,hmode,_,_⟩ := extracted_values bits _ _ _ h
    exact ⟨hstruct,Or.inr (hmode.trans encoded_modes.2)⟩

end NearCubicWires.RepairOrdinary.CompetitorWitnessTriple
