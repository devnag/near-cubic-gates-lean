import Proof.CaseAnalysis.RowsSupportCircuitPadding
import Proof.CaseAnalysis.WitnessTermRound

/-! The strengthened term controller adds one public support tape. Every
original term, coefficient, native, reset-driver and log port keeps its index. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape CloseoutWitness RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 1704) : Fin 2533:=
  if h:i.val<1703 then (TermCircuitDock.slots ⟨i.val,h⟩).castAdd 1 else 2532

theorem slots_old (i : Fin 1703) : slots (i.castAdd 1)=(TermCircuitDock.slots i).castAdd 1:=by
  simp only [slots,Fin.val_castAdd,Fin.isLt,↓reduceDIte]

theorem slots_last : slots 1703=2532:=rfl

theorem slots_injective : Function.Injective slots:=by
  intro i j he
  by_cases hi:i.val<1703
  · by_cases hj:j.val<1703
    · rw [slots,dif_pos hi,slots,dif_pos hj] at he
      have same:TermCircuitDock.slots ⟨i.val,hi⟩=TermCircuitDock.slots ⟨j.val,hj⟩:=
        Fin.ext (congrArg (fun z : Fin 2533=>z.val) he)
      exact Fin.ext (congrArg (fun z : Fin 1703=>z.val) (TermCircuitDock.slots_injective same))
    · rw [slots,dif_pos hi,slots,dif_neg hj] at he
      have hv:=(congrArg (fun z : Fin 2533=>z.val) he)
      have bound:=(TermCircuitDock.slots ⟨i.val,hi⟩).isLt
      change (TermCircuitDock.slots ⟨i.val,hi⟩).val=2532 at hv
      omega
  · by_cases hj:j.val<1703
    · rw [slots,dif_neg hi,slots,dif_pos hj] at he
      have hv:=(congrArg (fun z : Fin 2533=>z.val) he)
      have bound:=(TermCircuitDock.slots ⟨j.val,hj⟩).isLt
      change 2532=(TermCircuitDock.slots ⟨j.val,hj⟩).val at hv
      omega
    · apply Fin.ext
      omega

def lift {α : Type} (old : Fin 2532 → α) (last : α) : Fin 2533 → α:=
  Fin.addCases (m:=2532) (n:=1) old (fun _=>last)

theorem old_away (i : Fin 2532) (hi : ∀ j,TermCircuitDock.slots j≠i) :
    ∀ j,slots j≠i.castAdd 1:=by
  intro j he
  by_cases h:j.val<1703
  · have eq:(TermCircuitDock.slots ⟨j.val,h⟩).castAdd 1=i.castAdd 1:=by
      simpa only [slots,h,↓reduceDIte] using he
    exact hi ⟨j.val,h⟩ (Fin.ext (congrArg (fun z : Fin 2533=>z.val) eq))
  · rw [slots,dif_neg h] at he
    have hv:=congrArg (fun z : Fin 2533=>z.val) he
    change 2532=i.val at hv
    omega

noncomputable def sizes (s : ℕ):=TermRound.sizes s
noncomputable def programs {s : ℕ} (circuit : Machine 1704 s) : (j : Fin 5) → Machine 2533 (sizes s j)
  | 0=>TapeEmbedding.machine 1 TermRound.begin
  | 1=>RecoveryFocus.machine slots circuit
  | 2=>TapeEmbedding.machine 1 TermRound.foldFlag
  | 3=>TapeEmbedding.machine 1 TermRound.ending
  | 4=>TapeEmbedding.machine 1 TermCircuitReset.machine

def next {s : ℕ} (j : Fin 5) (state : Fin (sizes s j)) (bits : Fin 2533 → Bool) : Option (Fin 5):=
  TermRound.next j state (fun i=>bits (i.castAdd 1))
noncomputable def machine {s : ℕ} (circuit : Machine 1704 s):=
  RecoveryCalls.machine (sizes s) (programs circuit) 0 next

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
