import Proof.Hierarchy.HierarchyWidth

/-! A fixed finite ordinary program rounds a paid unary allocation A to
p*(A/p+1)+q. Its p residue states read A once; a fixed finishing chain writes
the exact remaining p+q-(A%p) symbols. -/
namespace NearCubicWires.RepairOrdinary.HierarchySlice
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states (p q : ℕ) := 2*p+q+1
def loopState (p q : ℕ) (hp : 0<p) (i : ℕ) : Fin (states p q) :=
  ⟨i%p,by have := Nat.mod_lt i hp; dsimp [states]; omega⟩
def finishState (p q r : ℕ) (hr : r≤p+q) : Fin (states p q) :=
  ⟨p+r,by dsimp [states]; omega⟩
def raw (p q : ℕ) (hp : 0<p) : Machine 2 (states p q) where
  descriptionBits := 0
  start := loopState p q hp 0
  halted := fun s => s.val==2*p+q
  rule := fun s scan => if hs : s.val<p then
      some (if scan 0 then ⟨loopState p q hp (s.val+1),![none,some true],fun _ => .right⟩
        else ⟨finishState p q s.val (by omega),fun _ => none,fun _ => .stay⟩)
    else if ht : s.val<2*p+q then
      some ⟨⟨s.val+1,by dsimp [states]; omega⟩,![none,some true],![.stay,.right]⟩
    else none
def config {s : ℕ} (state : Fin s) (A pos out : ℕ) : Configuration 2 s :=
  ⟨state,![pos,out],![List.replicate A true,List.replicate out true]⟩
theorem append_one (out : ℕ) : List.replicate out true++[true]=List.replicate (out+1) true := by
  simpa using (List.replicate_add out 1 true).symm

theorem loop_step (p q : ℕ) (hp : 0<p) (A i : ℕ) (hi : i<A) :
    step (raw p q hp) (config (loopState p q hp i) A i i)=
      some (config (loopState p q hp (i+1)) A (i+1) (i+1)) := by
  have hm := Nat.mod_lt i hp
  have hr : readTapeBit (List.replicate A true) i=true := by rw [ClockUnaryProduct.read_unary]; simp [hi]
  have hw := Streaming.write_append (List.replicate i true) true
  simp only [List.length_replicate] at hw
  simp [step,raw,config,loopState,hm,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j
    · rfl
    · simpa [applyAction,hw] using append_one i

theorem loop_stop (p q : ℕ) (hp : 0<p) (A : ℕ) :
    step (raw p q hp) (config (loopState p q hp A) A A A)=
      some (config (finishState p q (A%p) (by have := Nat.mod_lt A hp; omega)) A A A) := by
  have hm := Nat.mod_lt A hp
  have hr : readTapeBit (List.replicate A true) A=false := by rw [ClockUnaryProduct.read_unary]; simp
  simp [step,raw,config,loopState,hm,Configuration.scanned,hr]
  rfl

theorem finish_step (p q : ℕ) (hp : 0<p) (r : ℕ) (hr : r<p+q) (A out : ℕ) :
    step (raw p q hp) (config (finishState p q r (by omega)) A A out)=
      some (config (finishState p q (r+1) (by omega)) A A (out+1)) := by
  have hw := Streaming.write_append (List.replicate out true) true
  simp only [List.length_replicate] at hw
  have hge : ¬p+r<p := by omega
  have hlt : p+r<2*p+q := by omega
  simp [step,raw,config,finishState,hge,hlt]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j
    · rfl
    · simpa [applyAction,hw] using append_one out

end NearCubicWires.RepairOrdinary.HierarchySlice
