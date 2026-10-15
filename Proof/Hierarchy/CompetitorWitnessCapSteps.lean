import Proof.Hierarchy.CompetitorWitnessHeaderTyped

/-! The whole witness cap is checked before decoding. Each witness bit costs
sixteen input bits; an overlong witness is rejected without scanning its
unbounded suffix. These are literal steps of the fixed ordinary machine. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 34) (dx dw : HeadMove) (flag : Option Bool := none) : Action 3 34 :=
  ⟨q,![none,none,flag],![dx,dw,.stay]⟩
def machine : Machine 3 34 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==33
  rule := fun q cells=>
    if h0 : q.val=0 then
      some (if cells 1 then action 1 .stay .right else action 33 .stay .stay (some true))
    else if h1 : q.val≤16 then
      some (if cells 0 then action ⟨q.val+16,by omega⟩ .right .stay
        else action 33 .stay .stay (some false))
    else if h2 : q.val≤32 then
      some (if q.val=32 then action 0 .right .right
        else action ⟨q.val-15,by omega⟩ .right .stay)
    else none
def cfg (q : Fin 34) (x w : List Bool) (px pw : ℕ) (flag : List Bool := []) : Configuration 3 34 :=
  ⟨q,![px,pw,0],![x,w,flag]⟩
def marker (k : ℕ) (hk : k<16) : Fin 34 := ⟨k+1,by omega⟩
def payload (k : ℕ) (hk : k<16) : Fin 34 := ⟨k+17,by omega⟩

theorem witness_step (x pre tail : List Bool) (px : ℕ) :
    step machine (cfg 0 x (pre++true::tail) px pre.length)=
      some (cfg 1 x (pre++true::tail) px (pre.length+1)) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem accept_step (x pre : List Bool) (px : ℕ) :
    step machine (cfg 0 x (pre++[false]) px pre.length)=
      some (cfg 33 x (pre++[false]) px pre.length [true]) := by
  have hr := Streaming.read_append pre [] false
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem input_step (k : ℕ) (hk : k<16) (pre tail w : List Bool) (pw : ℕ) :
    step machine (cfg (marker k hk) (pre++true::tail) w pre.length pw)=
      some (cfg (payload k hk) (pre++true::tail) w (pre.length+1) pw) := by
  have h1 : k+1≤16 := by omega
  simp [step,machine,cfg,marker,Configuration.scanned,Streaming.read_append,h1]
  apply configuration_ext
  · apply Fin.ext; simp [applyAction,action,payload]
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem reject_step (k : ℕ) (hk : k<16) (pre w : List Bool) (pw : ℕ) :
    step machine (cfg (marker k hk) (pre++[false]) w pre.length pw)=
      some (cfg 33 (pre++[false]) w pre.length pw [false]) := by
  have h1 : k+1≤16 := by omega
  have hr := Streaming.read_append pre [] false
  simp [step,machine,cfg,marker,Configuration.scanned,hr,h1]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem payload_step (k : ℕ) (hk : k<15) (x w : List Bool) (px pw : ℕ) :
    step machine (cfg (payload k (by omega)) x w px pw)=
      some (cfg (marker (k+1) (by omega)) x w (px+1) pw) := by
  have h1 : ¬k+17≤16 := by omega
  have h2 : k+17≤32 := by omega
  have h3 : k+17≠32 := by omega
  simp [step,machine,cfg,payload,h1,h2,h3]
  apply configuration_ext
  · apply Fin.ext; simp [applyAction,action,marker]
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem payload_last (x w : List Bool) (px pw : ℕ) :
    step machine (cfg (payload 15 (by decide)) x w px pw)=
      some (cfg 0 x w (px+1) (pw+1)) := by
  simp [step,machine,cfg,payload]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CompetitorWitnessCap
