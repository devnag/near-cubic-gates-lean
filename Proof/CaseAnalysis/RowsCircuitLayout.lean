import Proof.CaseAnalysis.RowsCircuitTopPublish

/-! Frozen full circuit ABI. The original bottom field stream is aliased
directly; the already produced top-domain template later drives the bottom
loop. Retained requests and metadata stay outside reusable gate scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuit
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prefixSlots (i : Fin 639) : Fin 1703:=i.castAdd 1064
def gateSlots (i : Fin 1049) : Fin 1703:=if i.val=1035 then 624 else ⟨639+i.val,by omega⟩
def bottomSlots (i : Fin 1060) : Fin 1703:=
  if i.val=1052 then 297 else if i.val=1059 then 624 else ⟨639+i.val,by omega⟩
def topLoadSlots : Fin 4→Fin 1703:=![158,640,1694,1695]
def topPublishSlots : Fin 12→Fin 1703:=![1672,1633,1680,1684,1686,1694,1695,1701,1692,1702,1689,1696]
def heads (i : Fin 1703):=if i.val=1674 then 1 else 0
def input (cap core W L : ℕ) (bits : List Bool) (i : Fin 1703) : List Bool:=
  if i.val=1 then frame bits else if i.val=1674 then UnaryTemplate.tape core else
    if i.val=1694 then List.replicate cap true else
      if i.val=1698 then List.replicate W true else if i.val=1699 then List.replicate L true else []

theorem prefix_injective : Function.Injective prefixSlots:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 1703=>k.val) h)
theorem gate_val (i : Fin 1049) : (gateSlots i).val=if i.val=1035 then 624 else 639+i.val:=by
  unfold gateSlots;split_ifs <;> rfl
theorem gate_injective : Function.Injective gateSlots:=by
  intro i j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
  rw [gate_val,gate_val] at hv
  apply Fin.ext;split_ifs at hv <;> omega
theorem bottom_val (i : Fin 1060) : (bottomSlots i).val=
    if i.val=1052 then 297 else if i.val=1059 then 624 else 639+i.val:=by
  unfold bottomSlots;split_ifs <;> rfl
theorem bottom_injective : Function.Injective bottomSlots:=by
  intro i j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
  rw [bottom_val,bottom_val] at hv
  apply Fin.ext;split_ifs at hv <;> omega
theorem topPublish_injective : Function.Injective topPublishSlots:=by decide

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuit
