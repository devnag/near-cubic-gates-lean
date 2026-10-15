import Proof.CaseAnalysis.CommonProgramRecoveryRun

/-! The real recovery run leaves the final address and output outside its
selected bank. Selected words and heads come from that same recovery trace. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem recovery_outside (p : Parameters) (i : Fin (n0 p))
    (hi : ∀ j,recoveryShared p j≠i) (j : Fin (rn p)) : recoverySlot p j≠lift0 p i:=by
  intro he
  have hbank : recoveryBank p j=i.castAdd (rn p):=lift1_injective p he
  exact CloseoutCommonPortBank.outside _ _ i hi j hbank

theorem recovery_address_outside (p : Parameters) :
    ∀ j,recoverySlot p j≠lift0 p (address0 p):=by
  apply recovery_outside
  intro j he
  fin_cases j
  · exact (by decide : (3 : Fin 5)≠0) (header_injective p he)
  · exact (by decide : (2 : Fin 5)≠0) (header_injective p he)
  · exact (by decide : (1 : Fin 5)≠0) (header_injective p he)

theorem recovery_output_outside (p : Parameters) :
    ∀ j,recoverySlot p j≠(ports p).outputTape:=by
  apply recovery_outside
  intro j he
  fin_cases j
  · exact (by decide : (3 : Fin 5)≠4) (header_injective p he)
  · exact (by decide : (2 : Fin 5)≠4) (header_injective p he)
  · exact (by decide : (1 : Fin 5)≠4) (header_injective p he)

theorem recovered_outside (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config) (i : Fin (tapes p)) (hi : ∀ j,recoverySlot p j≠i) :
    (recovered p bits out padding final).heads i=0 ∧
      (recovered p bits out padding final).tapes i=afterPrefix p bits out i:=by
  have hn : ¬∃ j,recoverySlot p j=i:=by rintro ⟨j,hj⟩;exact hi j hj
  simp only [recovered,RecoveryFocus.config,RecoveryFocus.pick,dif_neg hn,and_self]

theorem recovered_heads (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config) (j : Fin (rn p)) :
    (recovered p bits out padding final).heads (recoverySlot p j)=final.heads j:=by
  simp only [recovered,RecoveryFocus.config,RecoveryFocus.pick_slot _ (recovery_injective p),ZeroPadding.config]

theorem recovered_word (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config) (j : Fin (rn p))
    (hj : j≠RecoveryBoundedCold.queryPort (source p) p.k p.degree) :
    (recovered p bits out padding final).tapes (recoverySlot p j)=final.tapes j:=by
  simp only [recovered,RecoveryFocus.config,RecoveryFocus.pick_slot _ (recovery_injective p),
    ZeroPadding.config,RecoveryBoundedCold.queryCaps]
  exact (congrArg (fun c=>ZeroPadding.pad c (final.tapes j)) (if_neg hj)).trans
    (ZeroPadding.pad_zero _)

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
