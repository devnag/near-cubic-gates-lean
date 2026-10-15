import Proof.PCP.PCPPNativeNodeRead

/-! Physically dispatch one of the five native node tags from the actual
sentinel word returned by the native field reader. Values beyond four do
not receive a successful classification; typed callers use the five tags. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeTag
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 10 where
  descriptionBits := 0
  start := 0
  halted := fun q => decide (5 ≤ q.val)
  rule := fun q bs => if hq : q.val < 5 then
    if bs 0 then
      if h : q.val < 4 then some ⟨⟨q.val+1,by omega⟩,fun _ => none,fun _ => .right⟩
      else none
    else some ⟨⟨q.val+5,by omega⟩,fun _ => none,fun _ => .stay⟩
    else none
def entry (tag : Fin 5) : Configuration 1 10 :=
  ⟨0,fun _ => 1,fun _ => UnaryTemplate.tape tag.val⟩
def receipt (tag : Fin 5) : ExecutionReceipt 1 10 :=
  ⟨⟨⟨tag.val+5,by omega⟩,fun _ => tag.val+1,fun _ => UnaryTemplate.tape tag.val⟩,
    tag.val+1,tag.val+2⟩

theorem tag_run (tag : Fin 5) : runFrom machine (tag.val+1) (entry tag)=some (receipt tag) := by
  fin_cases tag <;> rfl

end NearCubicWires.RepairOrdinary.PCPPNativeTag
