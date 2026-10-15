import Proof.CaseAnalysis.CommonProgramRecoveryRetained

/-! Every later private bank is still physically empty after recovery.
The original address is retained and the shared result remains empty. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem above_bound {t u : ℕ} (embed : Fin t→Fin u)
    (hv : ∀ j,(embed j).val=j.val) (i : Fin u) (hi : t ≤ i.val) : ∀ j,embed j≠i:=by
  intro j he
  have hj:=j.isLt
  have hh:=(hv j).symm.trans (congrArg Fin.val he)
  omega

theorem after_prefix_blank (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (i : Fin (tapes p))
    (hi : (prefixProgram p).base.tapeCount ≤ i.val) : afterPrefix p bits out i=[]:=by
  have away : ∀ j,prefixSlot p j≠i:=by
    intro j he
    have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
    have hj:=j.isLt
    change j.val=i.val at hv
    omega
  have hpos:=(prefixProgram p).base.twoTapes
  change install _ _ _ _=[]
  rw [install_other _ _ _ _ away]
  exact if_neg (by omega)

theorem recovered_fresh (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config) (i : Fin (tapes p)) (hi : n1 p ≤ i.val) :
    (recovered p bits out padding final).heads i=0 ∧
      (recovered p bits out padding final).tapes i=[]:=by
  have hl : ∀ z : Fin (n1 p),(lift1 p z).val=z.val:=by
    intro z
    simp only [lift1,Fin.val_castAdd]
  have away : ∀ j,recoverySlot p j≠i:=
    fun j=>above_bound (t:=n1 p) (u:=tapes p) (lift1 p) hl i hi (recoveryBank p j)
  have h:=recovered_outside p bits out padding final i away
  refine ⟨h.1,h.2.trans (after_prefix_blank p bits out i ?_)⟩
  unfold n1 n0 at hi
  omega

theorem recovered_output (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config) :
    (recovered p bits out padding final).heads (ports p).outputTape=0 ∧
      (recovered p bits out padding final).tapes (ports p).outputTape=[]:=by
  have h:=recovered_outside p bits out padding final _ (recovery_output_outside p)
  exact ⟨h.1,h.2.trans (after_prefix_blank p bits out _ (Nat.le_refl _))⟩

theorem recovered_address (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config)
    (ha : out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits) :
    (recovered p bits out padding final).heads (lift0 p (address0 p))=0 ∧
      (recovered p bits out padding final).tapes (lift0 p (address0 p))=frame bits:=by
  have h:=recovered_outside p bits out padding final _ (recovery_address_outside p)
  refine ⟨h.1,h.2.trans ?_⟩
  exact (install_slot _ (prefix_injective p) _ _
    ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩).trans ha

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
