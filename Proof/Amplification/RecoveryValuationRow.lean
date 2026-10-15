import Proof.Amplification.RecoveryCheckedLiteral

/-! Actual first-match valuation-row lookup. The query and retained row are
compared bit by bit; the row's final physical bit is used only for the first
matching key. The fixed finite control preserves a previous match. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationRow
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eqNext (a b old : Bool) := old && (a==b)
def equalBits : List Bool→List Bool→Bool→Bool
  | [],_,old => old
  | a::left,b::right,old => equalBits left right (eqNext a b old)
  | _::_,[],_ => false

theorem equalBits_value (left right : List Bool) (old : Bool) (hw : left.length=right.length) :
    equalBits left right old=(old && decide (value left=value right)) := by
  induction left generalizing right old with
  | nil => cases right <;> simp_all [equalBits,value]
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length=right.length := by simpa using hw
      rw [equalBits,ih _ _ hlen]
      cases a <;> cases b <;> cases old <;> apply Bool.eq_iff_iff.mpr <;>
        simp [eqNext,value] <;> omega

def matched (found eq : Bool) := found || eq
def selected (found eq bit old : Bool) := if found then old else if eq then bit else old

def scanState (eq : Bool) : Fin 7 := if eq then 1 else 0
def bitState (eq : Bool) : Fin 7 := if eq then 3 else 2
def rowState (eq : Bool) : Fin 7 := if eq then 5 else 4

def scanAction (q : Fin 7) : Action 4 7 :=
  ⟨q,fun _ => none,![.right,.right,.stay,.stay]⟩
def rowAction (q : Fin 7) : Action 4 7 :=
  ⟨q,fun _ => none,![.stay,.right,.stay,.stay]⟩
def finishAction (eq : Bool) (scanned : Fin 4→Bool) : Action 4 7 :=
  ⟨6,![none,none,some (matched (scanned 2) eq),some (selected (scanned 2) eq (scanned 1) (scanned 3))],
    fun _ => .stay⟩
def rawMachine : Machine 4 7 where
  descriptionBits := 0
  start := scanState true
  halted := fun q => q.val==6
  rule := fun q scanned =>
    if q.val<2 then
      if scanned 0 then some (scanAction (bitState (q.val==1)))
      else some (rowAction (rowState (q.val==1)))
    else if q.val<4 then some (scanAction (scanState (eqNext (scanned 0) (scanned 1) (q.val==3))))
    else if q.val<6 then some (finishAction (q.val==5) scanned)
    else none

def cfg (q : Fin 7) (left right : List Bool) (lp rp : Nat) (found old : Bool) : Configuration 4 7 :=
  ⟨q,![lp,rp,0,0],![left,right,[found],[old]]⟩

theorem marker_step (left right : List Bool) (lp rp : Nat) (found old eq : Bool)
    (hr : readTapeBit left lp=true) :
    step rawMachine (cfg (scanState eq) left right lp rp found old)=
      some (cfg (bitState eq) left right (lp+1) (rp+1) found old) := by
  cases eq <;> simp [step,rawMachine,scanState,bitState,cfg,Configuration.scanned,hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem bit_step (left right : List Bool) (lp rp : Nat) (found old eq a b : Bool)
    (hl : readTapeBit left lp=a) (hr : readTapeBit right rp=b) :
    step rawMachine (cfg (bitState eq) left right lp rp found old)=
      some (cfg (scanState (eqNext a b eq)) left right (lp+1) (rp+1) found old) := by
  cases eq <;> simp [step,rawMachine,bitState,cfg,Configuration.scanned,hl,hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem row_step (left right : List Bool) (lp rp : Nat) (found old eq : Bool)
    (hr : readTapeBit left lp=false) :
    step rawMachine (cfg (scanState eq) left right lp rp found old)=
      some (cfg (rowState eq) left right lp (rp+1) found old) := by
  cases eq <;> simp [step,rawMachine,scanState,rowState,cfg,Configuration.scanned,hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem finish_step (left right : List Bool) (lp rp : Nat) (found old eq bit : Bool)
    (hr : readTapeBit right rp=bit) :
    step rawMachine (cfg (rowState eq) left right lp rp found old)=
      some (cfg 6 left right lp rp (matched found eq) (selected found eq bit old)) := by
  cases eq <;> simp [step,rawMachine,rowState,cfg] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> first | rfl |
    (simp [applyAction,finishAction,Configuration.scanned,hr,writeTapeBit]; rfl))

theorem scan_prefix (preLeft preRight left right : List Bool) (found old eq bit : Bool)
    (hw : left.length=right.length) :
    Timed rawMachine (2*left.length+2)
      (cfg (scanState eq) (preLeft++frame left) (preRight++frame (right++[bit]))
        preLeft.length preRight.length found old)
      (cfg 6 (preLeft++frame left) (preRight++frame (right++[bit]))
        (preLeft.length+2*left.length) (preRight.length+2*right.length+1)
        (matched found (equalBits left right eq)) (selected found (equalBits left right eq) bit old)) := by
  induction left generalizing preLeft preRight right eq with
  | nil =>
    have he : right=[] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    have hl : readTapeBit (preLeft++frame []) preLeft.length=false := by
      simpa [frame] using Streaming.read_append preLeft [] false
    have hr : readTapeBit (preRight++frame ([]++[bit])) (preRight.length+1)=bit := by
      simpa [frame,List.append_assoc] using Streaming.read_append (preRight++[true]) [false] bit
    have h := (Timed.single (by cases eq <;> rfl) (row_step _ _ _ _ found old eq hl)).trans
      (Timed.single (by cases eq <;> rfl) (finish_step _ _ _ _ found old eq bit hr))
    simpa [equalBits] using h
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length=right.length := by simpa using hw
      have ht := ih (preLeft++[true,a]) (preRight++[true,b]) right (eqNext a b eq) hlen
      have hl : readTapeBit (preLeft++frame (a::left)) preLeft.length=true := by
        simpa [frame] using Streaming.read_append preLeft (a::frame left) true
      have hla : readTapeBit (preLeft++frame (a::left)) (preLeft.length+1)=a := by
        simpa [frame,List.append_assoc] using Streaming.read_append (preLeft++[true]) (frame left) a
      have hrb : readTapeBit (preRight++frame ((b::right)++[bit])) (preRight.length+1)=b := by
        simpa [frame,List.append_assoc] using Streaming.read_append (preRight++[true]) (frame (right++[bit])) b
      have hbit := bit_step _ _ _ _ found old eq a b hla hrb
      have hm := marker_step (preLeft++frame (a::left)) (preRight++frame ((b::right)++[bit]))
        preLeft.length preRight.length found old eq hl
      have tail : Timed rawMachine (2*left.length+2)
          (cfg (scanState (eqNext a b eq)) (preLeft++frame (a::left))
            (preRight++frame ((b::right)++[bit])) (preLeft.length+2) (preRight.length+2) found old)
          (cfg 6 (preLeft++frame (a::left)) (preRight++frame ((b::right)++[bit]))
            (preLeft.length+2*(a::left).length) (preRight.length+2*(b::right).length+1)
            (matched found (equalBits (a::left) (b::right) eq))
            (selected found (equalBits (a::left) (b::right) eq) bit old)) := by
        convert ht using 1 <;> simp [frame,equalBits,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      have h := Timed.step (by cases eq <;> rfl) hm (Timed.step (by cases eq <;> rfl) hbit tail)
      convert h using 1
      simp
      omega

def machine := Rewind.machine rawMachine

theorem row_ready (left right : List Bool) (found old bit : Bool) (capacity : Nat)
    (hw : left.length=right.length) :
    ReadyRun machine (4*left.length+6)
      ![frame left,frame (right++[bit]),[found],[old],List.replicate capacity false]
      ![frame left,frame (right++[bit]),[matched found (decide (value left=value right))],
        [selected found (decide (value left=value right)) bit old],
        List.replicate (max capacity (2*left.length+2)) false] := by
  obtain ⟨base,hr,hf,hs⟩ := (scan_prefix [] [] left right found old true bit hw).run (by rfl)
  have hi : cfg (scanState true) ([]++frame left) ([]++frame (right++[bit])) 0 0 found old=
      initialConfiguration rawMachine ![frame left,frame (right++[bit]),[found],[old]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  simp only [List.length_nil] at hr
  rw [hi] at hr
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace rawMachine _ _ base hr capacity
  have he : 2*base.steps+2=4*left.length+6 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [hf,cfg] using ht 0
    · simpa [hf,cfg] using ht 1
    · simpa [hf,cfg,equalBits_value left right true hw] using ht 2
    · simpa [hf,cfg,equalBits_value left right true hw] using ht 3
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryValuationRow
