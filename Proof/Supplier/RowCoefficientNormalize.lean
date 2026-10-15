import Proof.Supplier.RowCachedEquationMeaning

/-! Normalize a completed P/N coefficient once. One fixed ordinary controller
compares its two framed words, subtracts in the physically selected order,
and retains the sign flag and absolute magnitude with all heads restored. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientNormalize
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compareSlots : Fin 4 → Fin 5 := ![1,0,2,4]
def positiveSlots : Fin 4 → Fin 5 := ![0,1,3,4]
def negativeSlots : Fin 4 → Fin 5 := ![1,0,3,4]
noncomputable def compare := RecoveryFocus.machine compareSlots compareMachine
noncomputable def positive := RecoveryFocus.machine positiveSlots subtractMachine
noncomputable def negative := RecoveryFocus.machine negativeSlots subtractMachine
def sizes : Fin 3 → ℕ := fun _=>7
noncomputable def programs (j : Fin 3) : Machine 5 (sizes j) :=
  if j=0 then compare else if j=1 then positive else negative
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 5 → Bool) : Option (Fin 3) :=
  if j=0 then if bits 2 then some 1 else some 2 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def data (w p n cap : ℕ) (flag magnitude : List Bool) : Fin 5 → List Bool :=
  ![frame (binary w p),frame (binary w n),flag,magnitude,List.replicate cap false]
def input (w p n cap : ℕ) := data w p n cap [false] []
def middle (w p n cap : ℕ) := data w p n (max cap (2*w+1)) [decide (n≤p)] []
def magnitude (p n : ℕ) := if n≤p then p-n else n-p
def output (w p n cap : ℕ) := data w p n (max cap (2*w+1))
  [decide (n≤p)] (frame (binary w (magnitude p n)))

theorem compare_ready (w p n cap : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ReadyRun compare (4*w+4) (input w p n cap) (middle w p n cap) := by
  have h := RecoveryRootRound.compare_ready (binary w n) (binary w p) cap (by simp)
  simp only [binary_length,binary_value w p hp,binary_value w n hn] at h
  have focused := h.focus compareSlots (by decide) (input w p n cap)
    (by intro i; fin_cases i <;> rfl)
  have he : install compareSlots (input w p n cap)
      ![frame (binary w n),frame (binary w p),[decide (n≤p)],List.replicate (max cap (2*w+1)) false]=
      middle w p n cap := by
    funext i
    fin_cases i
    · exact install_slot compareSlots (by decide) _ _ 1
    · exact install_slot compareSlots (by decide) _ _ 0
    · exact install_slot compareSlots (by decide) _ _ 2
    · exact install_other compareSlots _ _ _ (by decide)
    · exact install_slot compareSlots (by decide) _ _ 3
  exact he ▸ focused

theorem positive_ready (w p n cap : ℕ) (hp : p<2^w) (hle : n≤p) :
    ReadyRun positive (4*w+4) (middle w p n cap) (output w p n cap) := by
  have h := subtract_ready w p n [] (max cap (2*w+1)) hle hp (by simp)
  simp only [max_eq_left (Nat.le_max_right cap (2*w+1))] at h
  have focused := h.focus positiveSlots (by decide) (middle w p n cap)
    (by intro i; fin_cases i <;> rfl)
  have he : install positiveSlots (middle w p n cap)
      ![frame (binary w p),frame (binary w n),frame (binary w (p-n)),List.replicate (max cap (2*w+1)) false]=
      output w p n cap := by
    unfold output magnitude
    rw [if_pos hle]
    funext i
    fin_cases i
    · exact install_slot positiveSlots (by decide) _ _ 0
    · exact install_slot positiveSlots (by decide) _ _ 1
    · exact install_other positiveSlots _ _ _ (by decide)
    · exact install_slot positiveSlots (by decide) _ _ 2
    · exact install_slot positiveSlots (by decide) _ _ 3
  exact he ▸ focused

theorem negative_ready (w p n cap : ℕ) (hn : n<2^w) (hlt : p<n) :
    ReadyRun negative (4*w+4) (middle w p n cap) (output w p n cap) := by
  have h := subtract_ready w n p [] (max cap (2*w+1)) hlt.le hn (by simp)
  simp only [max_eq_left (Nat.le_max_right cap (2*w+1))] at h
  have focused := h.focus negativeSlots (by decide) (middle w p n cap)
    (by intro i; fin_cases i <;> rfl)
  have he : install negativeSlots (middle w p n cap)
      ![frame (binary w n),frame (binary w p),frame (binary w (n-p)),List.replicate (max cap (2*w+1)) false]=
      output w p n cap := by
    unfold output magnitude
    rw [if_neg (by omega : ¬n≤p)]
    funext i
    fin_cases i
    · exact install_slot negativeSlots (by decide) _ _ 1
    · exact install_slot negativeSlots (by decide) _ _ 0
    · exact install_other negativeSlots _ _ _ (by decide)
    · exact install_slot negativeSlots (by decide) _ _ 2
    · exact install_slot negativeSlots (by decide) _ _ 3
  exact he ▸ focused

theorem normalize_run (w p n cap : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ReadyRun machine (8*w+10) (input w p n cap) (output w p n cap) := by
  have first : ReadyRun (programs 0) (4*w+4) (input w p n cap) (middle w p n cap) :=
    compare_ready w p n cap hp hn
  have whole : Timed machine (8*w+10) (initialConfiguration machine (input w p n cap))
      (RecoveryCalls.stopped sizes (fun _=>0) (output w p n cap)) := by
    by_cases hle : n≤p
    · have firstCall := first.call sizes programs 0 next 0 1 (by
        intro q
        simp [next,middle,data,readTapeBit,hle])
      have last : ReadyRun (programs 1) (4*w+4) (middle w p n cap) (output w p n cap) :=
        positive_ready w p n cap hp hle
      have lastCall := last.stop sizes programs 0 next 1 (by intro q; rfl)
      have h := firstCall.trans lastCall
      have ht : 4*w+4+1+(4*w+4+1)=8*w+10 := by omega
      rw [ht] at h
      exact h
    · have firstCall := first.call sizes programs 0 next 0 2 (by
        intro q
        simp [next,middle,data,readTapeBit,hle])
      have last : ReadyRun (programs 2) (4*w+4) (middle w p n cap) (output w p n cap) :=
        negative_ready w p n cap hn (by omega)
      have lastCall := last.stop sizes programs 0 next 2 (by intro q; rfl)
      have h := firstCall.trans lastCall
      have ht : 4*w+4+1+(4*w+4+1)=8*w+10 := by omega
      rw [ht] at h
      exact h
  obtain ⟨r,hr,rf,rs⟩ := whole.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by rw [rf]; rfl,by intro i; rw [rf]; rfl,rs⟩

theorem magnitude_eq (p n : ℕ) : magnitude p n=((p : ℤ)-n).natAbs := by
  by_cases hle : n≤p
  · have hz : (p : ℤ)-n=(p-n : ℕ) := by omega
    rw [magnitude,if_pos hle,hz]
    simp
  · have hz : (p : ℤ)-n=-((n-p : ℕ) : ℤ) := by omega
    rw [magnitude,if_neg hle,hz]
    simp

theorem sign_eq (p n : ℕ) : (!decide (n≤p))=decide ((p : ℤ)-n<0) := by
  apply Bool.eq_iff_iff.mpr
  simp

end NearCubicWires.RepairOrdinary.RowCoefficientNormalize
