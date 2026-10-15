import Proof.Amplification.RecoveryTseitinNativeReuseLayout

/-! The all-scratch erase is an actual paid pass and returns the same exact
state required by the next original native-node iteration. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def retained (i : Fin 1338) : Prop := i=0 ∨ i=1 ∨ i=1062 ∨ i=1333
theorem erase_away (i : Fin 1338) (hi : retained i) : ∀ j,eraseSlots j≠i := by
  intro j
  refine Fin.addCases (m:=1332) (n:=2) (fun k=>?_) (fun k=>?_) j
  · intro he
    have hv:=congrArg Fin.val he
    simp only [eraseSlots,Fin.addCases_left] at hv
    have hs:=scratch_range k
    rcases hi with rfl|rfl|rfl|rfl <;> dsimp at hv <;> omega
  · fin_cases k <;> rcases hi with rfl|rfl|rfl|rfl <;> decide
theorem coverage (i : Fin 1338) : retained i ∨ ∃ j,eraseSlots j=i := by
  by_cases hp : retained i
  · exact Or.inl hp
  right
  have hi:=i.isLt
  by_cases h36 : i=1336
  · exact ⟨(0 : Fin 2).natAdd 1332,h36.symm⟩
  by_cases h37 : i=1337
  · exact ⟨(1 : Fin 2).natAdd 1332,h37.symm⟩
  have h0 : i.val≠0:=fun he=>hp (Or.inl (Fin.ext he))
  have h1 : i.val≠1:=fun he=>hp (Or.inr (Or.inl (Fin.ext he)))
  have h62 : i.val≠1062:=fun he=>hp (Or.inr (Or.inr (Or.inl (Fin.ext he))))
  have h33 : i.val≠1333:=fun he=>hp (Or.inr (Or.inr (Or.inr (Fin.ext he))))
  have h36v : i.val≠1336:=fun he=>h36 (Fin.ext he)
  have h37v : i.val≠1337:=fun he=>h37 (Fin.ext he)
  by_cases hlow : i.val<1062
  · refine ⟨(⟨i.val-2,by omega⟩ : Fin 1332).castAdd 2,?_⟩
    apply Fin.ext
    simp only [eraseSlots,Fin.addCases_left,scratch]
    split_ifs <;> dsimp <;> omega
  by_cases hmid : i.val<1333
  · refine ⟨(⟨i.val-3,by omega⟩ : Fin 1332).castAdd 2,?_⟩
    apply Fin.ext
    simp only [eraseSlots,Fin.addCases_left,scratch]
    split_ifs <;> dsimp <;> omega
  · refine ⟨(⟨i.val-4,by omega⟩ : Fin 1332).castAdd 2,?_⟩
    apply Fin.ext
    simp only [eraseSlots,Fin.addCases_left,scratch]
    split_ifs <;> dsimp <;> omega
theorem data_scratch (n index : Nat) (word out : List Bool) (cap : Nat) (j : Fin 1332) :
    data n index word out cap ((scratch j).castAdd 2)=List.replicate cap false := by
  have hr:=scratch_range j
  have hi:=(scratch j).isLt
  unfold data
  repeat rw [if_neg (by intro he; have hv:=congrArg Fin.val he; dsimp at hv; omega)]
theorem heads_scratch (pos cursor : Nat) (j : Fin 1332) : heads pos cursor ((scratch j).castAdd 2)=0 := by
  have hr:=scratch_range j
  unfold heads
  repeat rw [if_neg (by intro he; have hv:=congrArg Fin.val he; dsimp at hv; omega)]

theorem erase_run {z : Nat} (n index pos : Nat) (word out : List Bool) (cap : Nat)
    (ambient : Configuration 1338 z) (hh : ambient.heads=heads pos out.length)
    (ht : ∀ i,retained i → ambient.tapes i=data n index word out cap i)
    (hd : ambient.tapes 1336=List.replicate cap true)
    (hl : ambient.tapes 1337=List.replicate (cap+1) false)
    (hb : ∀ j,(ambient.tapes ((scratch j).castAdd 2)).length ≤ cap) :
    ∃ r,runFrom eraseMachine (2*cap+4) (Composition.restart ambient eraseMachine.start)=some r ∧
      r.final.heads=heads pos out.length ∧ r.final.tapes=data n index word out cap ∧ r.steps ≤ 2*cap+4 := by
  let backing : Fin 1332→List Bool:=fun j=>ambient.tapes ((scratch j).castAdd 2)
  have hin (j : Fin 1334) : ambient.tapes (eraseSlots j)=
      (Fin.addCases (m:=1333) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=1332) (n:=1) (motive:=fun _=>List Bool) backing (fun _=>List.replicate cap true))
        (fun _=>List.replicate (cap+1) false)) j := by
    refine Fin.addCases (m:=1332) (n:=2) (fun k=>?_) (fun k=>?_) j
    · simp only [eraseSlots,Fin.addCases_left]
      have he : k.castAdd 2=(k.castAdd 1).castAdd 1 := Fin.ext rfl
      rw [he]
      simp only [Fin.addCases_left,backing]
    · fin_cases k
      · exact hd
      · exact hl
  have hhead (j : Fin 1334) : ambient.heads (eraseSlots j)=0 := by
    rw [hh]
    refine Fin.addCases (m:=1332) (n:=2) (fun k=>?_) (fun k=>?_) j
    · simpa only [eraseSlots,Fin.addCases_left] using heads_scratch pos out.length k
    · fin_cases k <;> rfl
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryScratchErase.erase_ready cap (cap+1) backing hb).focus_at
    eraseSlots erase_injective ambient.heads ambient.tapes hin hhead
  refine ⟨r,hr,rh.trans hh,?_,rs.le⟩
  rw [rt]
  funext i
  rcases coverage i with hi|⟨j,rfl⟩
  · rw [install_other eraseSlots _ _ _ (erase_away i hi)]
    exact ht i hi
  · rw [install_slot eraseSlots erase_injective]
    refine Fin.addCases (m:=1332) (n:=2) (fun k=>?_) (fun k=>?_) j
    · simp only [eraseSlots,Fin.addCases_left]
      have he : k.castAdd 2=(k.castAdd 1).castAdd 1 := Fin.ext rfl
      rw [he]
      simp only [Fin.addCases_left]
      exact (data_scratch n index word out cap k).symm
    · fin_cases k
      · rfl
      · simp only [max_self]; rfl

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
