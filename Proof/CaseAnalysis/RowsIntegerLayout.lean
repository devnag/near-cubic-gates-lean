import Proof.CaseAnalysis.RowsIntegerBank

/-! Direct aliases from the canonical list's physical stream/count/flag to
the native integer loop. The input-power bank shares only the raw input and
its actual capacity driver; no stream serialization is repeated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loopSlots (i : Fin 221) : Fin 459:=i.castAdd 238
def bankSlots (i : Fin 220) : Fin 459:=i.castAdd 239
def canonSlots (i : Fin 174) : Fin 459:=
  if i.val=0 then 221 else if i.val=30 then 217 else if i.val=41 then 220
    else if i.val=172 then 219 else ⟨222+i.val,by omega⟩
def powerSlots (i : Fin 63) : Fin 459:=
  if i.val=0 then 221 else if i.val=60 then 215 else ⟨396+i.val,by omega⟩
theorem canon_val (i : Fin 174) : (canonSlots i).val=
    if i.val=0 then 221 else if i.val=30 then 217 else if i.val=41 then 220
      else if i.val=172 then 219 else 222+i.val:=by
  unfold canonSlots
  split_ifs <;> rfl
theorem power_val (i : Fin 63) : (powerSlots i).val=
    if i.val=0 then 221 else if i.val=60 then 215 else 396+i.val:=by
  unfold powerSlots
  split_ifs <;> rfl
theorem loop_injective : Function.Injective loopSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 459=>k.val) h)
theorem bank_injective : Function.Injective bankSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 459=>k.val) h)
theorem canon_injective : Function.Injective canonSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [canon_val,canon_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem power_injective : Function.Injective powerSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [power_val,power_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem power_canon (i : Fin 174) (hi : i.val≠0) : ∀ j,powerSlots j≠canonSlots i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [power_val,canon_val] at hv
  split_ifs at hv <;> omega
theorem power_core (i : Fin 220) (hi : i.val≠215) : ∀ j,powerSlots j≠bankSlots i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [power_val] at hv
  change (if j.val=0 then 221 else if j.val=60 then 215 else 396+j.val)=i.val at hv
  split_ifs at hv <;> omega
theorem canon_core (i : Fin 220) (hs : i.val≠217) (hf : i.val≠219) :
    ∀ j,canonSlots j≠bankSlots i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [canon_val] at hv
  change (if j.val=0 then 221 else if j.val=30 then 217 else if j.val=41 then 220
      else if j.val=172 then 219 else 222+j.val)=i.val at hv
  split_ifs at hv <;> omega

def input (bits : List Bool) (i : Fin 459):=if i=221 then frame bits else []
noncomputable def powered (bits : List Bool) (out : Fin 63→List Bool):=install powerSlots (input bits) out
noncomputable def parsed (bits : List Bool) (powOut : Fin 63→List Bool) (canOut : Fin 174→List Bool):=
  install canonSlots (powered bits powOut) canOut
theorem powered_canon (bits : List Bool) (out : Fin 63→List Bool) (hraw : out 0=frame bits) :
    ∀ i,powered bits out (canonSlots i)=CloseoutWitness.CanonicalTest.input bits i:=by
  intro i
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    change install powerSlots _ out (powerSlots 0)=_
    rw [install_slot _ power_injective,hraw]
    rfl
  · rw [powered,install_other _ _ _ _ (power_canon i hi)]
    have hn:canonSlots i≠221:=by
      intro h
      have hv:=congrArg Fin.val h
      rw [canon_val] at hv
      split_ifs at hv <;> omega
    simp only [input,if_neg hn]
    change []=(if i.val=0 then frame bits else [])
    rw [if_neg hi]

theorem parsed_bank (bits : List Bool) (powOut : Fin 63→List Bool) (canOut : Fin 174→List Bool)
    (cap : ℕ) (source : List Bool) (flag : Bool)
    (hp : powOut 60=List.replicate cap true) (hs : canOut 30=source) (hf : canOut 172=[flag]) :
    ∀ i,parsed bits powOut canOut (bankSlots i)=CloseoutRowsIntegerBank.input cap [] source flag i:=by
  intro i
  by_cases hsource:i.val=217
  · have he:i=217:=Fin.ext hsource
    subst i
    change install canonSlots _ canOut (canonSlots 30)=_
    rw [install_slot _ canon_injective,hs]
    rfl
  by_cases hflag:i.val=219
  · have he:i=219:=Fin.ext hflag
    subst i
    change install canonSlots _ canOut (canonSlots 172)=_
    rw [install_slot _ canon_injective,hf]
    rfl
  rw [parsed,install_other _ _ _ _ (canon_core i hsource hflag)]
  by_cases hdriver:i.val=215
  · have he:i=215:=Fin.ext hdriver
    subst i
    change install powerSlots _ powOut (powerSlots 60)=_
    rw [install_slot _ power_injective,hp]
    rfl
  rw [powered,install_other _ _ _ _ (power_core i hdriver)]
  have hn:bankSlots i≠221:=by
    intro h
    have hv:=congrArg Fin.val h
    change i.val=221 at hv
    omega
  have hs':i≠217:=fun h=>hsource (congrArg Fin.val h)
  have hf':i≠219:=fun h=>hflag (congrArg Fin.val h)
  have hd':i≠215:=fun h=>hdriver (congrArg Fin.val h)
  simp only [input,if_neg hn,CloseoutRowsIntegerBank.input,if_neg hs',if_neg hf',if_neg hd']
  split_ifs <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
