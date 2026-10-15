import Proof.PCP.PCPPNativeCanonicalTreeMeaning

/-! The ordinary pending-stack marker is a real cell above each reversed
field. The false bottom distinguishes an empty stack even for empty words.
Both commands preserve the active stack boundary and finite zero backing. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalStack
open LocalBitMultitape RecoveryExecution
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oneCfg {s : ℕ} (q : Fin s) (stack : List Bool) (pos : ℕ) : Configuration 1 s :=
  ⟨q,fun _=>pos,fun _=>stack⟩
def mark : Machine 1 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>some true,fun _=>.right⟩ else none

theorem mark_run (pre : List Bool) (C : ℕ) :
    ∃ r,runFrom mark 1 (oneCfg 0 (ZeroPadding.pad C pre) pre.length)=some r ∧
      r.final=oneCfg 1 (ZeroPadding.pad C (pre++[true])) (pre.length+1) ∧ r.steps=1 := by
  have h:step mark (oneCfg 0 (ZeroPadding.pad C pre) pre.length)=
      some (oneCfg 1 (ZeroPadding.pad C (pre++[true])) (pre.length+1)):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      change writeTapeBit (ZeroPadding.pad C pre) pre.length true=_
      rw [ZeroPadding.write_pad,Streaming.write_append]
      rfl
  exact (Timed.single (by rfl) h).run (by rfl)

def peek : Machine 1 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (2≤q.val)
  rule:=fun q scanned=>if q.val=0 then some ⟨1,fun _=>none,fun _=>.left⟩
    else if q.val=1 then
      if scanned 0 then some ⟨2,fun _=>some false,fun _=>.stay⟩
      else some ⟨3,fun _=>none,fun _=>.right⟩
    else none

theorem pad_false (pre : List Bool) (C : ℕ) (hC:pre.length+1≤C) :
    ZeroPadding.pad C (pre++[false])=ZeroPadding.pad C pre := by
  unfold ZeroPadding.pad
  simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append]
  rw [←List.replicate_succ]
  congr 2
  omega

theorem peek_start (stack : List Bool) (pos : ℕ) :
    step peek (oneCfg 0 stack pos)=some (oneCfg 1 stack (pos-1)) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · rfl

theorem peek_some (pre : List Bool) (C : ℕ) (hC:pre.length+1≤C) :
    ∃ r,runFrom peek 2 (oneCfg 0 (ZeroPadding.pad C (pre++[true])) (pre.length+1))=some r ∧
      r.final=oneCfg 2 (ZeroPadding.pad C pre) pre.length ∧ r.steps=2 := by
  have h0:=peek_start (ZeroPadding.pad C (pre++[true])) (pre.length+1)
  rw [Nat.add_sub_cancel] at h0
  have h1:step peek (oneCfg 1 (ZeroPadding.pad C (pre++[true])) pre.length)=
      some (oneCfg 2 (ZeroPadding.pad C pre) pre.length):=by
    have hb:readTapeBit (ZeroPadding.pad C (pre++[true])) pre.length=true:=by
      rw [ZeroPadding.read_pad]
      exact Streaming.read_append pre [] true
    simp only [step,peek,oneCfg,Configuration.scanned,hb,↓reduceIte]
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      change writeTapeBit (ZeroPadding.pad C (pre++[true])) pre.length false=_
      rw [ZeroPadding.write_pad,DimensionTrim.write_at pre [] true false]
      exact pad_false pre C hC
  exact ((Timed.single (by rfl : peek.halted (0 : Fin 4)=false) h0).trans
    (Timed.single (by rfl : peek.halted (1 : Fin 4)=false) h1)).run (by rfl)

theorem peek_empty (C : ℕ) :
    ∃ r,runFrom peek 2 (oneCfg 0 (ZeroPadding.pad C [false]) 1)=some r ∧
      r.final=oneCfg 3 (ZeroPadding.pad C [false]) 1 ∧ r.steps=2 := by
  have h0:=peek_start (ZeroPadding.pad C [false]) 1
  have h1:step peek (oneCfg 1 (ZeroPadding.pad C [false]) 0)=
      some (oneCfg 3 (ZeroPadding.pad C [false]) 1):=by
    have hb:readTapeBit (ZeroPadding.pad C [false]) 0=false:=by rw [ZeroPadding.read_pad];rfl
    simp only [step,peek,oneCfg,Configuration.scanned,hb]
    rfl
  exact ((Timed.single (by rfl : peek.halted (0 : Fin 4)=false) h0).trans
    (Timed.single (by rfl : peek.halted (1 : Fin 4)=false) h1)).run (by rfl)

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalStack
