import Proof.PCP.PCPPNativeCanonicalWalkPop
import Proof.Amplification.RecoveryCursorCalls

/-! One fixed ordinary DFS controller. Every branch test reads the actual
decoded tag or stack return control, and every call transition is charged. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev coreStates := Fintype.card (RecoveryCalls.Control PCPPNativeCanonicalTree.stepSizes)
def sizes : Fin 7→ℕ := ![coreStates,4,2,5,2,4,6]
noncomputable def programs : (j : Fin 7)→Machine 29 (sizes j)
  | ⟨0,_⟩=>coreMachine
  | ⟨1,_⟩=>pushMachine
  | ⟨2,_⟩=>markMachine
  | ⟨3,_⟩=>copyMachine
  | ⟨4,_⟩=>countMachine
  | ⟨5,_⟩=>peekMachine
  | ⟨6,_⟩=>popMachine
  | ⟨n+7,h⟩=>False.elim (by omega)
def next (j : Fin 7) (q : Fin (sizes j)) (scanned : Fin 29→Bool) : Option (Fin 7) :=
  if j.val=0 then if scanned 25 then some 1 else if scanned 24 then some 3 else some 5
  else if j.val=1 then some 2
  else if j.val=2 then some 0
  else if j.val=3 then some 4
  else if j.val=4 then some 5
  else if j.val=5 then if q.val=2 then some 6 else none
  else some 0
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def atCall (j : Fin 7) (x : State) :=
  controlConfig (RecoveryCalls.code sizes j) (x.cfg (programs j).start)
def Path (j k : Fin 7) (fuel : ℕ) (x y : State) : Prop :=
  ∃ n≤fuel,Timed machine n (atCall j x) (atCall k y)

theorem Path.trans {j k l : Fin 7} {a b : ℕ} {x y z : State}
    (h:Path j k a x y) (g:Path k l b y z) : Path j l (a+b) x z := by
  obtain ⟨n,hn,hp⟩:=h
  obtain ⟨m,hm,gp⟩:=g
  exact ⟨n+m,by omega,hp.trans gp⟩
theorem Path.mono {j k : Fin 7} {a b : ℕ} {x y : State}
    (h:Path j k a x y) (hab:a≤b) : Path j k b x y := by
  obtain ⟨n,hn,hp⟩:=h
  exact ⟨n,hn.trans hab,hp⟩

theorem path_of_run (j k : Fin 7) (fuel : ℕ) (x y : State)
    (r : ExecutionReceipt 29 (sizes j))
    (hr:runFrom (programs j) fuel (x.cfg (programs j).start)=some r)
    (hf:r.final=y.cfg r.final.control)
    (hn:next j r.final.control (y.cfg r.final.control).scanned=some k) :
    Path j k (fuel+1) x y := by
  obtain ⟨n,hbound,hpath⟩:=call_receipt sizes programs 0 next j k fuel _ r hr (by rw [hf];exact hn)
  rw [hf] at hpath
  exact ⟨n,hbound,hpath⟩

def afterCore (x : State) := x.withCore (PCPPNativeCanonicalTree.stepped x.core)
theorem afterCore_flags (x : State) {s : ℕ} (q : Fin s) :
    ((afterCore x).cfg q).scanned 24=decide ((Nat.unpair (value x.core.bits)).1=1) ∧
    ((afterCore x).cfg q).scanned 25=decide ((Nat.unpair (value x.core.bits)).1=2) := by
  constructor
  · change readTapeBit [(PCPPNativeCanonicalTree.stepped x.core).flags 1] 0=_
    rw [PCPPNativeCanonicalTree.stepped_flags,PCPPNativeCanonicalTree.classified_flag]
    rfl
  · change readTapeBit [(PCPPNativeCanonicalTree.stepped x.core).flags 2] 0=_
    rw [PCPPNativeCanonicalTree.stepped_flags,PCPPNativeCanonicalTree.classified_flag]
    rfl

theorem core_branch (x : State) (hx:x.core.Valid)
    (hb:(Nat.unpair (value x.core.bits)).1=2) :
    Path 0 1 (PCPPNativeCanonicalTree.stepTime x.core+1) x (afterCore x) := by
  obtain ⟨r,hr,hf,_⟩:=core_run x hx
  exact path_of_run 0 1 _ x _ r hr hf (by
    simp only [next,Fin.val_zero,↓reduceIte,(afterCore_flags x _).2,hb,decide_true])

theorem core_leaf (x : State) (hx:x.core.Valid)
    (hb:(Nat.unpair (value x.core.bits)).1=1) :
    Path 0 3 (PCPPNativeCanonicalTree.stepTime x.core+1) x (afterCore x) := by
  obtain ⟨r,hr,hf,_⟩:=core_run x hx
  exact path_of_run 0 3 _ x _ r hr hf (by
    simp only [next,Fin.val_zero,↓reduceIte,(afterCore_flags x _).1,(afterCore_flags x _).2,hb,decide_true]
    rfl)

theorem core_empty (x : State) (hx:x.core.Valid)
    (h1:(Nat.unpair (value x.core.bits)).1≠1) (h2:(Nat.unpair (value x.core.bits)).1≠2) :
    Path 0 5 (PCPPNativeCanonicalTree.stepTime x.core+1) x (afterCore x) := by
  obtain ⟨r,hr,hf,_⟩:=core_run x hx
  exact path_of_run 0 5 _ x _ r hr hf (by
    simp only [next,Fin.val_zero,↓reduceIte,(afterCore_flags x _).1,(afterCore_flags x _).2,
      h1,h2,decide_false]
    rfl)

theorem push_path (x : State) (bits : List Bool) (hx:x.Valid)
    (hw:bits.length=x.core.bits.length)
    (hsrc:x.core.tapes 18=ZeroPadding.pad x.capacity (frame bits)) :
    Path 1 2 (4*bits.length+4) x (pushed x bits) := by
  obtain ⟨r,hr,hf,_⟩:=push_run x bits hx hw hsrc
  exact path_of_run 1 2 _ x _ r hr hf (by rfl)

theorem mark_path (x : State) : Path 2 0 2 x (marked x) := by
  obtain ⟨r,hr,hf,_⟩:=mark_run x
  exact path_of_run 2 0 1 x _ r hr (by rw [hf];rfl) (by rfl)

theorem copy_path (x : State) (hx:x.Valid) : Path 3 4 (4*x.core.bits.length+5) x (leaf x) := by
  obtain ⟨r,hr,hf,_⟩:=leaf_copy x hx
  exact path_of_run 3 4 _ x _ r hr hf (by rfl)

theorem count_path (x : State) : Path 4 5 2 x (counted x) := by
  obtain ⟨r,hr,hf,_⟩:=count_run x
  exact path_of_run 4 5 1 x _ r hr (by rw [hf];rfl) (by rfl)

theorem peek_path (x : State) (pre : List Bool) (hstack:x.stack=pre++[true])
    (hC:x.stack.length≤x.capacity) : Path 5 6 3 x (restacked x pre) := by
  obtain ⟨r,hr,hf,_⟩:=peek_some x pre hstack hC
  exact path_of_run 5 6 2 x _ r hr (by rw [hf];rfl) (by rw [hf];rfl)

theorem pop_path (x : State) (bits pre : List Bool) (hx:x.Valid)
    (hw:bits.length=x.core.bits.length) (hstack:x.stack=pre++(frame bits).reverse) :
    Path 6 0 (4*bits.length+7) x (restored x bits pre) := by
  obtain ⟨r,hr,hf,_⟩:=pop_run x bits pre hx hw hstack
  exact path_of_run 6 0 _ x _ r hr hf (by rfl)

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
