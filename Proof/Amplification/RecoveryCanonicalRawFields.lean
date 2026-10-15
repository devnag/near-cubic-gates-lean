import Proof.Amplification.RecoveryCanonicalCompactAccept

/-! Canonical raw-view cursor, code and bounds at the same checker state.
These use the retained whole-witness valuation layout. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_width (code : Nat) (c : Certificate) :
    (canonicalState code c).width=RecoveryColdView.width code.bits :=
  RecoveryColdAllCode.state_width _ _ _ _ _ _ _

theorem raw_word (code : Nat) (c : Certificate) :
    witness code c=valuationPrefix code c++
      (RawSyntaxCertificate.pack (canonicalState code c).width c.view++tableWords code c) := by
  rw [canonical_width,width_code]
  simp only [witness,TableFirst.pack,valuationPrefix,tableWords,List.append_assoc]

theorem raw_position (code : Nat) (c : Certificate) :
    (canonicalState code c).raw.view.inner.stream.pos=2*(valuationPrefix code c).length := by
  change 2*(c.table.length*(RecoveryColdView.width code.bits+2)+1)=_
  rw [prefix_length,width_code]

theorem raw_bounded (code : Nat) (c : Certificate)
    (h : wellSizedCNFEncoding code (RawSyntaxCertificate.project c.view)=true) :
    RecoveryRawViewLoop.boundedView (natBitLength code) c.view=true := by
  simp only [wellSizedCNFEncoding,Bool.and_eq_true] at h
  apply List.all_eq_true.mpr
  intro clause hm
  have hclause := List.all_eq_true.mp h.2 (RawSyntaxCertificate.projectClause clause)
    (List.mem_map.mpr ⟨clause,hm,rfl⟩)
  rw [Bool.and_eq_true] at hclause
  apply List.all_eq_true.mpr
  intro literal hl
  have hli := List.all_eq_true.mp hclause.2 (RawSyntaxCertificate.projectLiteral literal)
    (List.mem_map.mpr ⟨literal,hl,rfl⟩)
  exact hli

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
