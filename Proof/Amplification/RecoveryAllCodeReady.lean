import Proof.Amplification.RecoveryAllCodeLayout

/-! Discharge the whole all-code entry from the actual successful cold
endpoint. The code, valuation word and table buffers are the originals. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready_native {s : Nat} (code : Nat) (word : List Bool)
    (H : Fin 493→Nat) (A : Fin 493→List Bool)
    (hr : RecoveryColdCompact.Ready code.bits word H A) (q : Fin s) :
    ∃ count n ib m ob,
      RecoveryAllCode.Prepared (state code.bits word
        (RecoveryColdCompact.buffer ib word) (RecoveryColdCompact.buffer ob word) count n m)
        (limit code.bits) word (count*(width code.bits+2)+1)
        (RecoveryColdCompact.buffer ib word) (RecoveryColdCompact.buffer ob word) [] [] ∧
      ZeroPadding.config (caps code.bits word)
        ⟨q,(fun j=>H (slots j)),(fun j=>A (slots j))⟩=
        RecoveryAllCode.cfg (state code.bits word
          (RecoveryColdCompact.buffer ib word) (RecoveryColdCompact.buffer ob word) count n m) q := by
  have hsat := ready_sat code.bits word H A hr
  have hview := RecoveryColdSAT.ready_view code.bits word _ _ hsat
  have hp : ∃ table rest,readList (limit code.bits) (readEntry (width code.bits)) word=some (table,rest) := by
    obtain ⟨table,rest,count,a,hp,_⟩ := hview
    exact ⟨table,rest,hp⟩
  obtain ⟨count,_,_,_,hv⟩ := RecoveryColdView.ready_native code.bits word _ _ hview q
  have hs := RecoveryColdSAT.ready_sat code.bits word _ _ hsat q
  have hm := ready_marker code.bits word H A hr q
  obtain ⟨n,ib,m,ob,hn,hmb,hc⟩ := ready_compact code.bits word H A hr q
  refine ⟨count,n,ib,m,ob,prepared code word _ _ count n m hn hmb hp,?_⟩
  exact native_layout code.bits word _ _ count n m H A q hv hs hm hc

end NearCubicWires.RepairOrdinary.RecoveryColdAllCode
