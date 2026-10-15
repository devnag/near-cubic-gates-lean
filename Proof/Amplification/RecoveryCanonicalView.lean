import Proof.Amplification.RecoveryCanonicalPrefix

/-! The original canonical valuation prefix determines the exact native
raw-view cursor produced by the actual cold reader. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready_native {s : Nat} (code : Nat) (c : Certificate) (hc : Fits code c)
    (H : Fin 100→Nat) (A : Fin 100→List Bool)
    (hr : RecoveryColdView.Ready code.bits (TableFirst.pack (Serialization.width code) c) H A)
    (q : Fin s) :
    ZeroPadding.config (RecoveryColdView.nativeCaps code.bits)
      ⟨q,(fun j=>H (viewSlots j)),(fun j=>A (viewSlots j))⟩=
      RecoveryRawViewEnd.cfg
        (view code.bits (TableFirst.pack (Serialization.width code) c)
          (2*(valuationPrefix code c).length)) 0 q := by
  obtain ⟨table,tail,count,a,hparse,_,hd,ha,hs,_,hh,ht⟩ := hr
  have hp := ready_offset code c hc table tail count hparse hd
  rw [hh,ht,hp]
  have hn := boot_native_layout code.bits (TableFirst.pack (Serialization.width code) c)
    (2*(count*(RecoveryColdView.width code.bits+2)+1)) a ha hs q
  rw [hp] at hn
  exact hn

theorem raw_code (code : Nat) (word : List Bool) (pos : Nat) :
    RecoveryRawViewBody.code (view code.bits word pos)=code :=
  (RecoveryColdHeader.code_value code.bits).trans (RecoveryUnpair.bits_value code)

theorem raw_counts (code : Nat) (c : Certificate) (hc : Fits code c) :
    c.view.length≤RecoveryColdView.limit code.bits ∧
      ∀ clause∈c.view,clause.length≤RecoveryColdView.limit code.bits := by
  have h := RawSyntaxCertificate.view_bounds code c.view hc.1
  have hb := (TableFirst.counts_fit code).1
  rw [limit_code]
  exact ⟨h.1.trans hb,fun clause hm=>(h.2 clause hm).1.trans hb⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
