import Proof.CaseAnalysis.WitnessInput

/-! A cold family directly aliases the bounded header's three payload
ports and one fresh shared verdict. Its remaining tapes occupy its own
fresh segment, so the two mode branches require no input copying. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.HeaderDock
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (m : ℕ):=150+(m+1)
def input (m : ℕ) (data : Fin 150→List Bool) : Fin (tapes m)→List Bool:=
  Fin.addCases (m:=150) (n:=m+1) (motive:=fun _=>List Bool) data (fun _=>[])
def old (m : ℕ) (i : Fin 150) : Fin (tapes m):=i.castAdd (m+1)
def flag (m : ℕ) : Fin (tapes m):=(0 : Fin (m+1)).natAdd 150

def slots {t : ℕ} (m offset O F V : ℕ) (h:offset+t ≤ m) (i : Fin t) : Fin (tapes m):=
  if i.val=F then old m 118 else if i.val=O then old m 78
  else if i.val=2 then old m 0 else if i.val=V then flag m
  else (⟨1+offset+i.val,by have hi:=i.isLt;omega⟩ : Fin (m+1)).natAdd 150

theorem slots_injective {t : ℕ} (m offset O F V : ℕ) (h:offset+t ≤ m)
    : Function.Injective (slots (t:=t) m offset O F V h):=by
  intro i j he
  have hv:=congrArg Fin.val he
  dsimp only [slots,old,flag] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega

theorem input_local {t : ℕ} (m offset O F V : ℕ) (h:offset+t ≤ m)
    (x raw bits : List Bool)
    (data : Fin 150→List Bool) (hx:data 0=frame x) (ho:data 78=frame raw) (hf:data 118=frame bits)
    (i : Fin t) :
    input m data (slots m offset O F V h i)=
      if i.val=F then frame bits else if i.val=O then frame raw else if i.val=2 then frame x else []:=by
  by_cases hfi:i.val=F
  · rw [slots,if_pos hfi,input,old,Fin.addCases_left,if_pos hfi];exact hf
  by_cases hoi:i.val=O
  · rw [slots,if_neg hfi,if_pos hoi,input,old,Fin.addCases_left,if_neg hfi,if_pos hoi];exact ho
  by_cases hxi:i.val=2
  · rw [slots,if_neg hfi,if_neg hoi,if_pos hxi,input,old,Fin.addCases_left,
      if_neg hfi,if_neg hoi,if_pos hxi];exact hx
  rw [slots,if_neg hfi,if_neg hoi,if_neg hxi]
  split_ifs <;> simp only [input,flag,Fin.addCases_right]

theorem flag_slot {t : ℕ} (m offset O F V : ℕ) (h:offset+t ≤ m)
    (hO:2<O) (hF:O<F) (hV:F<V) (v : Fin t) (hv:v.val=V) :
    slots m offset O F V h v=flag m:=by
  rw [slots,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos hv]

theorem untouched_header {t : ℕ} (m offset O F V : ℕ) (h:offset+t ≤ m)
    (i : Fin 150) (hi:i≠0 ∧ i≠78 ∧ i≠118) :
    ∀j,slots (t:=t) m offset O F V h j≠old m i:=by
  intro j he
  have hv:=congrArg Fin.val he
  have bound:=i.isLt
  have hn:i.val≠0 ∧ i.val≠78 ∧ i.val≠118:=
    ⟨fun z=>hi.1 (Fin.ext z),fun z=>hi.2.1 (Fin.ext z),fun z=>hi.2.2 (Fin.ext z)⟩
  dsimp only [slots,old,flag] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.HeaderDock
