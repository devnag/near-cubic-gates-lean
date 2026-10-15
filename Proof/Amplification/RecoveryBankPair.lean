import Proof.Amplification.RecoveryOuterRootWhole

/-! Two disjoint fixed tape banks. Running one leaves every tape and head
of the other untouched, including retained input and append cursors. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBankPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {t u s : Nat} (lh : Fin t → Nat) (lt : Fin t → List Bool)
    (rh : Fin u → Nat) (rt : Fin u → List Bool) (q : Fin s) : Configuration (t+u) s :=
  ⟨q,Fin.addCases lh rh,Fin.addCases lt rt⟩

def leftMachine {t u s : Nat} (p : Machine t s) := TapeEmbedding.machine u p
def rightMachine {t u s : Nat} (p : Machine u s) :=
  TapeRenaming.machine (finAddFlip : Fin (u+t)≃Fin (t+u)) (TapeEmbedding.machine t p)

theorem flip_cfg {t u s : Nat} (lh : Fin t → Nat) (lt : Fin t → List Bool)
    (rh : Fin u → Nat) (rt : Fin u → List Bool) (q : Fin s) :
    TapeRenaming.config finAddFlip (cfg rh rt lh lt q)=cfg lh lt rh rt q := by
  apply configuration_ext
  · rfl
  · funext i
    obtain ⟨j,rfl⟩ := (finAddFlip : Fin (u+t)≃Fin (t+u)).surjective i
    change (cfg rh rt lh lt q).heads (finAddFlip.symm (finAddFlip j))=(cfg lh lt rh rt q).heads (finAddFlip j)
    rw [Equiv.symm_apply_apply]
    refine Fin.addCases (m:=u) (n:=t) (fun k=>?_) (fun k=>?_) j
    · simp [cfg]
    · simp [cfg]
  · funext i
    obtain ⟨j,rfl⟩ := (finAddFlip : Fin (u+t)≃Fin (t+u)).surjective i
    change (cfg rh rt lh lt q).tapes (finAddFlip.symm (finAddFlip j))=(cfg lh lt rh rt q).tapes (finAddFlip j)
    rw [Equiv.symm_apply_apply]
    refine Fin.addCases (m:=u) (n:=t) (fun k=>?_) (fun k=>?_) j
    · simp [cfg]
    · simp [cfg]

theorem left_run {t u s : Nat} (p : Machine t s) (b : Nat) (source : Configuration t s)
    (base : ExecutionReceipt t s) (hr : runFrom p b source=some base)
    (rh : Fin u → Nat) (rt : Fin u → List Bool) :
    ∃ r,runFrom (leftMachine (u:=u) p) b (cfg source.heads source.tapes rh rt source.control)=some r ∧
      r.steps=base.steps ∧ r.final=cfg base.final.heads base.final.tapes rh rt base.final.control := by
  exact ⟨TapeEmbedding.receipt rh rt base,TapeEmbedding.run_embed p rh rt b source base hr,rfl,rfl⟩

theorem right_run {t u s : Nat} (p : Machine u s) (b : Nat) (source : Configuration u s)
    (base : ExecutionReceipt u s) (hr : runFrom p b source=some base)
    (lh : Fin t → Nat) (lt : Fin t → List Bool) :
    ∃ r,runFrom (rightMachine (t:=t) p) b (cfg lh lt source.heads source.tapes source.control)=some r ∧
      r.steps=base.steps ∧ r.final=cfg lh lt base.final.heads base.final.tapes base.final.control := by
  have he := TapeEmbedding.run_embed p lh lt b source base hr
  have h := TapeRenaming.run_rename (finAddFlip : Fin (u+t)≃Fin (t+u)) (TapeEmbedding.machine t p)
    b _ (TapeEmbedding.receipt lh lt base) he
  change runFrom (rightMachine (t:=t) p) b (TapeRenaming.config finAddFlip
    (cfg source.heads source.tapes lh lt source.control))=some _ at h
  rw [flip_cfg] at h
  refine ⟨TapeRenaming.receipt finAddFlip (TapeEmbedding.receipt lh lt base),h,rfl,?_⟩
  exact flip_cfg lh lt base.final.heads base.final.tapes base.final.control

end NearCubicWires.RepairOrdinary.RecoveryBankPair
