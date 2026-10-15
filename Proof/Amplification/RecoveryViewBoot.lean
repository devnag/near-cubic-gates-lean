import Proof.Amplification.RecoveryViewNative

/-! One physical transition initializes the raw-view flags and count
sentinels and positions the already produced unary drivers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def falseFlag (i : Fin 100) : Prop :=
  i.val=55 ∨ i.val=59 ∨ i.val=60 ∨ i.val=64 ∨ i.val=67 ∨ i.val=91 ∨ i.val=95 ∨ i.val=97
def trueFlag (i : Fin 100) : Prop := i.val=65 ∨ i.val=66
def bootFlag (i : Fin 100) : Prop := falseFlag i ∨ trueFlag i
def bootMove (i : Fin 100) : Prop := i.val=62 ∨ i.val=67 ∨ i.val=96 ∨ i.val=97
instance (i : Fin 100) : Decidable (falseFlag i) := inferInstanceAs (Decidable (_∨_∨_∨_∨_∨_∨_∨_))
instance (i : Fin 100) : Decidable (trueFlag i) := inferInstanceAs (Decidable (_∨_))
instance (i : Fin 100) : Decidable (bootFlag i) := inferInstanceAs (Decidable (_∨_))
instance (i : Fin 100) : Decidable (bootMove i) := inferInstanceAs (Decidable (_∨_∨_∨_))
def bootHeads (pos : Nat) (i : Fin 100) := if bootMove i then 1 else bankHeads pos i
def bootTapes (bits : List Bool) (a : Fin 100→List Bool) (i : Fin 100) :=
  if bootFlag i then [decide (trueFlag i)] else stage7 bits a i
def bootProgram : Machine 100 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    (fun i=>if bootFlag i then some (decide (trueFlag i)) else none),
    (fun i=>if bootMove i then .right else .stay)⟩ else none

theorem flag_geometry : ∀ (i : Fin 100), bootFlag i →
    (32 : Nat) ≤ i.val ∧ i≠23 ∧ i≠32 ∧ i≠63 ∧ i≠68 ∧ i≠62 ∧ i≠96 ∧ i≠53 ∧ i≠89 ∧ i≠98 := by decide
theorem move_geometry : ∀ (i : Fin 100), bootMove i → i≠23 := by decide

theorem flag_blank (bits : List Bool) (a : Fin 100→List Bool) (ha : Sources bits a)
    (i : Fin 100) (hi : bootFlag i) : stage7 bits a i=[] := by
  obtain ⟨h32,_,h0,h1,h2,h3,h4,h5,h6,hr⟩ := flag_geometry i hi
  simpa [stage7,stage6,stage5,stage4,stage3,stage2,stage1,put,
    h0,h1,h2,h3,h4,h5,h6,hr] using ha.empty i h32

theorem boot_step (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    step bootProgram ⟨0,bankHeads pos,stage7 bits a⟩=
      some ⟨1,bootHeads pos,bootTapes bits a⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hm : bootMove i
    · have hn := move_geometry i hm
      simp [applyAction,bootHeads,bankHeads,hm,hn,HeadMove.apply]
    · simp [applyAction,bootHeads,hm,HeadMove.apply]
  · funext i
    by_cases hf : bootFlag i
    · have hn := (flag_geometry i hf).2.1
      have hz := flag_blank bits a ha i hf
      simp [applyAction,bootTapes,bankHeads,hf,hn,hz,writeTapeBit]
    · simp [applyAction,bootTapes,hf]

theorem boot_run (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    ∃ r,runFrom bootProgram 1 ⟨bootProgram.start,bankHeads pos,stage7 bits a⟩=some r ∧
      r.final.heads=bootHeads pos ∧ r.final.tapes=bootTapes bits a := by
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) (boot_step bits pos a ha)).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf]⟩

end NearCubicWires.RepairOrdinary.RecoveryColdView
