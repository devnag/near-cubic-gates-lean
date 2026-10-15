import Proof.Amplification.RecoveryMarkerMetadata

/-! Accepted marker atoms yield their actual natural-tag shape and saved
field. Only the committed atom reuses its clause-code tail. Empty tests
may wrap a zero word; no later semantic claim interprets that discarded
wrapped value. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
open LocalBitMultitape RecoveryMarkerClause RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputCode (x : State) := value x.inner.data.bits
def literalTag (x : State) := (Nat.unpair (Nat.unpair (inputCode x-1)).1).1
def literalValue (x : State) := (Nat.unpair (Nat.unpair (inputCode x-1)).1).2
def literalTail (x : State) := (Nat.unpair (inputCode x-1)).2

theorem accepted_shape (which : Fin 3) (x : State) (ha : answer which x=true) :
    inputCode x≠0 ∧ literalTag x≤1 ∧ tagOK which (decide (literalTag x≠0))=true ∧
      (which.val≠1 → literalTail x=0) := by
  rw [answer_eq_codeCheck,codeCheck] at ha
  simp only [Bool.and_eq_true,decide_eq_true_eq] at ha
  refine ⟨ha.1.1.1,ha.1.1.2,ha.1.2,?_⟩
  intro hm
  have h := ha.2
  rw [if_neg hm,decide_eq_true_eq] at h
  exact h

theorem code_rebuild (x : State) (hz : inputCode x≠0) :
    Nat.pair (Nat.pair (literalTag x) (literalValue x)) (literalTail x)+1=inputCode x := by
  unfold literalTag literalValue literalTail
  rw [Nat.pair_unpair,Nat.pair_unpair]
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)

theorem output_outer_bits (which : Fin 3) (x : State) : (output which x).outer.bits=x.outer.bits := by
  dsimp only [output]
  split
  · unfold final tested
    split
    · unfold saved RecoveryMarkerSave.saved RecoveryMarkerSave.stored
      split <;> unfold withSign <;> split <;> rfl
    · unfold emptyStep saved RecoveryMarkerSave.saved RecoveryMarkerSave.stored
      split <;> unfold withSign <;> split <;> rfl
  · rfl

theorem committed_tail (x : State) (ha : answer 1 x=true) : inputCode (output 1 x)=literalTail x := by
  have hz := (accepted_shape 1 x ha).1
  have hg : good 1 (literalStep x)=true := by
    rw [answer,Bool.and_eq_true] at ha
    exact ha.1
  have ho : output 1 x=final 1 (withSign 1 (literalStep x)) := by
    dsimp only [output]
    exact if_pos hg
  rw [ho]
  change value (saved 1 (literalStep x)).inner.data.bits=literalTail x
  rw [saved_bits]
  exact RecoveryRawLiteral.output_tail x.inner hz

theorem accepted_metadata (which : Fin 3) (x : State) (ha : answer which x=true) :
    RecoveryMarkerMetadata.read (output which x)=
      RecoveryMarkerMetadata.store which
        (if which.val=0 then {RecoveryMarkerMetadata.read x with flat:=decide (literalTag x≠0)}
          else RecoveryMarkerMetadata.read x)
        (frame (variableWord x)) := by
  have hz := (accepted_shape which x ha).1
  rw [RecoveryMarkerMetadata.atom_read which x ha]
  congr 1
  unfold withSign
  split
  · rw [RecoveryMarkerMetadata.read_flat,RecoveryMarkerMetadata.read_literal,decoded_sign x hz]
    rfl
  · exact RecoveryMarkerMetadata.read_literal x

theorem accepted_variable (which : Fin 3) (x : State) (ha : answer which x=true) :
    value (variableWord x)=literalValue x := variable_value x (accepted_shape which x ha).1

end NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
