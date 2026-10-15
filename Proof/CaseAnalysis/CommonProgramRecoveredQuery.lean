import Proof.CaseAnalysis.CommonProgramRecoveryRetained

/-! The literal shared query after recovery includes its earlier paid
prefix padding. Its maximum length is the reset-capacity consumer. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem recovered_query_length (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config) :
    ((recovered p bits out padding final).tapes (ports p).queryTape).length=
      max padding (final.tapes (RecoveryBoundedCold.queryPort (source p) p.k p.degree)).length:=by
  let q:=RecoveryBoundedCold.queryPort (source p) p.k p.degree
  have hslot : recoverySlot p q=(ports p).queryTape:=recovery_query p
  have ht : (recovered p bits out padding final).tapes (recoverySlot p q)=
      ZeroPadding.pad padding (final.tapes q):=by
    simp only [recovered,RecoveryFocus.config,RecoveryFocus.pick_slot _ (recovery_injective p),
      ZeroPadding.config,RecoveryBoundedCold.queryCaps,q,if_true]
  exact (congrArg List.length ((congrArg
    (recovered p bits out padding final).tapes hslot.symm).trans ht)).trans
      (ZeroPadding.pad_length _ _)

theorem recovered_query_head (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (padding : ℕ)
    (final : (recovery p).Config)
    (hh : final.heads (RecoveryBoundedCold.queryPort (source p) p.k p.degree)=0) :
    (recovered p bits out padding final).heads (ports p).queryTape=0:=
  (congrArg (recovered p bits out padding final).heads (recovery_query p).symm).trans
    ((recovered_heads p bits out padding final _).trans hh)

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
