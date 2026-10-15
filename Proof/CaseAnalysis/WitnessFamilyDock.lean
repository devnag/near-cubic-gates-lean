import Proof.CaseAnalysis.WitnessFamilyFields
import Proof.CaseAnalysis.WitnessFamilyPadding

/-! The canonical exact-V header shares the actual family source,
repeat driver and verdict with the complete family loop. Its fixed
private bank is retained outside that loop without a second traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyDock
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 177) : Fin 3241 :=
  ⟨if i.val=30 then 3061 else if i.val=41 then 3063 else if i.val=172 then 724 else 3064+i.val,
    by split_ifs <;> omega⟩
noncomputable def reader:=RecoveryFocus.machine slots FamilyCount.machine

def coreHeads (base : Fin 3061 → ℕ) : Fin 3064 → ℕ:=
  Fin.addCases (m:=3063) (n:=1) (motive:=fun _=>ℕ) (FamilyLoad.heads 0 base) (fun _=>0)
def coreData (H : ℕ) (base : Fin 3061 → List Bool) (source driver : List Bool) : Fin 3064 → List Bool:=
  Fin.addCases (m:=3063) (n:=1) (motive:=fun _=>List Bool) (FamilyLoad.data H base source) (fun _=>driver)
def extra (H V : ℕ) (bits : List Bool) (i : Fin 177):=
  if i.val=0 then ZeroPadding.pad H (frame bits) else if i.val=174 then List.replicate V true else List.replicate H false
def heads (base : Fin 3061 → ℕ) : Fin 3241 → ℕ:=
  Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>ℕ) (coreHeads base) (fun _=>0)
def input (H V : ℕ) (bits : List Bool) (base : Fin 3061 → List Bool) : Fin 3241 → List Bool:=
  Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>List Bool)
    (coreData H base (List.replicate H false) (List.replicate H false)) (extra H V bits)

theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv:=congrArg (fun k : Fin 3241=>k.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem normal_slot (i : Fin 177) (h30 : i≠30) (h41 : i≠41) (h172 : i≠172) :
    slots i=i.natAdd 3064 := by
  have hn30:i.val≠30:=by intro h;exact h30 (Fin.ext h)
  have hn41:i.val≠41:=by intro h;exact h41 (Fin.ext h)
  have hn172:i.val≠172:=by intro h;exact h172 (Fin.ext h)
  simp only [slots,if_neg hn30,if_neg hn41,if_neg hn172]
  rfl

theorem core_outside (i : Fin 3064) (h3061 : i≠3061) (h3063 : i≠3063) (h724 : i≠724) :
    ∀ j,slots j≠i.castAdd 177 := by
  intro j h
  have hv:=congrArg (fun k : Fin 3241=>k.val) h
  dsimp only [slots,Fin.val_castAdd] at hv
  split_ifs at hv
  · exact h3061 (Fin.ext hv.symm)
  · exact h3063 (Fin.ext hv.symm)
  · exact h724 (Fin.ext hv.symm)
  · omega

theorem heads_reader (base : Fin 3061 → ℕ) (h724 : base 724=0) (i : Fin 177) : heads base (slots i)=0 := by
  by_cases h30:i=30
  · subst i;rfl
  by_cases h41:i=41
  · subst i;rfl
  by_cases h172:i=172
  · subst i;exact h724
  rw [normal_slot i h30 h41 h172,heads,Fin.addCases_right]

theorem input_reader (H V : ℕ) (bits : List Bool) (base : Fin 3061 → List Bool)
    (h724 : base 724=[false]) (i : Fin 177) : input H V bits base (slots i)=FamilyFields.input H V bits i := by
  by_cases h30:i=30
  · subst i;rfl
  by_cases h41:i=41
  · subst i;rfl
  by_cases h172:i=172
  · subst i;exact h724
  rw [normal_slot i h30 h41 h172,input,Fin.addCases_right]
  by_cases h0:i=0
  · subst i;rfl
  by_cases h174:i=174
  · subst i;exact (ZeroPadding.pad_zero (List.replicate V true)).symm
  have hn0:i.val≠0:=by intro h;exact h0 (Fin.ext h)
  have hn172:i.val≠172:=by intro h;exact h172 (Fin.ext h)
  have hn174:i.val≠174:=by intro h;exact h174 (Fin.ext h)
  simp only [extra,if_neg hn0,if_neg hn174,FamilyFields.input,FamilyFields.capacity,if_neg hn172,
    FamilyCount.input,ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyDock
