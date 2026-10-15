import Proof.MachineModel.UWitnessBootstrap

/-! The m field consists of exactly w witness bits, with no inner delimiter.
The physical outer marker is checked for every bit, and no bit beyond this
fixed prefix is inspected. -/
namespace NearCubicWires.RepairOrdinary.UWitnessField
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w : ℕ) (witness : List Bool) : Configuration 3 6 :=
  ⟨FieldMachine.machine.start,![0,0,1],![frame witness,[],CompareMachine.word w]⟩
def accepted (w : ℕ) (witness : List Bool) : Configuration 3 6 :=
  FieldMachine.finished (frame witness) (frame (witness.take w)) (2*w) w
def rejected (w : ℕ) (witness : List Bool) : Configuration 3 6 :=
  FieldMachine.scan 5 (frame witness) (2*witness.length) w witness.length
    (Streaming.marks witness) []

theorem frame_split (word : List Bool) (n : ℕ) :
    frame word=Streaming.marks (word.take n)++frame (word.drop n) := by
  rw [←Streaming.frame_append,List.take_append_drop]

theorem read_run (w : ℕ) (witness : List Bool) :
    ∃ r,runFrom FieldMachine.machine (4*w+2) (input w witness)=some r ∧
      r.final=(if w ≤ witness.length then accepted w witness else rejected w witness) ∧
      r.steps ≤ 4*w+2 := by
  by_cases hlen : w ≤ witness.length
  · obtain ⟨r,hr,hf,hs,_⟩ := FieldMachine.field_run [] (witness.take w) (frame (witness.drop w)) [] (by simp)
    have he : (witness.take w).length=w := by simp [List.length_take,Nat.min_eq_left hlen]
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at hr hf
    rw [he,←frame_split] at hr hf
    rw [he] at hs
    have hi : FieldMachine.scan 0 (frame witness) 0 w 0 [] []=input w witness := by
      apply configuration_ext
      · rfl
      · rfl
      · funext i; fin_cases i <;> rfl
    rw [hi] at hr
    exact ⟨r,hr,by simpa [hlen,accepted] using hf,by omega⟩
  · have hshort : witness.length < w := by omega
    obtain ⟨r,hr,hf,hs,_⟩ := FieldMachine.field_reject_run [] witness [] w hshort (by simp)
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at hr hf
    have hi : FieldMachine.scan 0 (frame witness) 0 w 0 [] []=input w witness := by
      apply configuration_ext
      · rfl
      · rfl
      · funext i; fin_cases i <;> rfl
    rw [hi] at hr
    have ht : 2*witness.length+1 ≤ 4*w+2 := by omega
    have hm := runFrom_moreFuel FieldMachine.machine (2*witness.length+1)
      (4*w+2-(2*witness.length+1)) _ r hr
    rw [Nat.add_sub_of_le ht] at hm
    exact ⟨r,hm,by simpa [hlen,rejected] using hf,by omega⟩

end NearCubicWires.RepairOrdinary.UWitnessField
