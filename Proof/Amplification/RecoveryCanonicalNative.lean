import Proof.Amplification.RecoveryCanonicalCompact

/-! The actual positive cold run docks at one explicit canonical348-tape
checker state, with the same valuation and zero-padded row suffixes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def witness (code : Nat) (c : Certificate) := TableFirst.pack (Serialization.width code) c
def innerBuffer (code : Nat) (c : Certificate) := RecoveryColdCompact.buffer (innerBits code c) (witness code c)
def outerBuffer (code : Nat) (c : Certificate) := RecoveryColdCompact.buffer (outerBits code c) (witness code c)
def canonicalState (code : Nat) (c : Certificate) :=
  RecoveryColdAllCode.state code.bits (witness code c) (innerBuffer code c) (outerBuffer code c)
    c.table.length c.inner.length c.outer.length

theorem canonical_prepared (code : Nat) (c : Certificate) (hc : Fits code c) :
    RecoveryAllCode.Prepared (canonicalState code c) (RecoveryColdView.limit code.bits)
      (witness code c) (c.table.length*(RecoveryColdView.width code.bits+2)+1)
      (innerBuffer code c) (outerBuffer code c) [] [] := by
  apply RecoveryColdAllCode.prepared
  · rw [limit_code]
    exact hc.2.2.2.1.trans (TableFirst.counts_fit code).2.1
  · rw [limit_code]
    exact hc.2.2.2.2.1.trans (TableFirst.counts_fit code).2.2
  · exact ⟨c.table,suffix code c,valuation_parse code c hc⟩

theorem compact_native {s : Nat} (code : Nat) (c : Certificate)
    (H : Fin 493→Nat) (A : Fin 493→List Bool) (hr : CompactReady code c H A) (q : Fin s) :
    ZeroPadding.config (RecoveryColdCompact.caps code.bits (witness code c))
      ⟨q,(fun j=>H (RecoveryColdCompact.bankSlots j)),(fun j=>A (RecoveryColdCompact.bankSlots j))⟩=
      (RecoveryColdCompact.state code.bits (witness code c) (innerBuffer code c) (outerBuffer code c)
        c.inner.length c.outer.length).cfg q := by
  obtain ⟨h,a,_,_,hh,ht⟩ := hr
  rw [hh,ht]
  apply RecoveryColdCompact.bank_native code.bits (witness code c) (innerBits code c) (outerBits code c)
    c.inner.length c.outer.length (RecoveryColdCompact.bankHeads h) (RecoveryColdCompact.bankInput a) q
  · intro i hi
    have hn : ¬(i=(270 : Fin 493) ∨ i=(274 : Fin 493)) := by
      simp only [Fin.ext_iff]
      omega
    simp only [RecoveryColdCompact.bankHeads,if_neg hn,RecoveryColdCompact.liftedHeads]
    simp [Fin.addCases,Nat.not_lt.mpr hi]
  · intro i hi
    simp [RecoveryColdCompact.bankInput,Fin.addCases,Nat.not_lt.mpr hi]

theorem canonical_native {s : Nat} (code : Nat) (c : Certificate) (hc : Fits code c)
    (H : Fin 493→Nat) (A : Fin 493→List Bool) (hr : CompactReady code c H A) (q : Fin s) :
    ZeroPadding.config (RecoveryColdAllCode.caps code.bits (witness code c))
      ⟨q,(fun j=>H (RecoveryColdAllCode.slots j)),(fun j=>A (RecoveryColdAllCode.slots j))⟩=
      RecoveryAllCode.cfg (canonicalState code c) q := by
  have hready := compact_ready code c hc H A hr
  have hsat := RecoveryColdAllCode.ready_sat code.bits (witness code c) H A hready
  have hview := RecoveryColdSAT.ready_view code.bits (witness code c) _ _ hsat
  have hv := ready_native code c hc _ _ hview q
  have hpos : (valuationPrefix code c).length=c.table.length*(RecoveryColdView.width code.bits+2)+1 := by
    rw [prefix_length,width_code]
  rw [hpos] at hv
  have hs := RecoveryColdSAT.ready_sat code.bits (witness code c) _ _ hsat q
  have hm := RecoveryColdAllCode.ready_marker code.bits (witness code c) H A hready q
  have hcp := compact_native code c H A hr q
  exact RecoveryColdAllCode.native_layout code.bits (witness code c) (innerBuffer code c) (outerBuffer code c)
    c.table.length c.inner.length c.outer.length H A q hv hs hm hcp

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
