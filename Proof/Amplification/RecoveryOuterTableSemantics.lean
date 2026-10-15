import Proof.Amplification.RecoveryOuterTableInvariant

/-! Outer-table recursive Boolean semantics use the existing balanced-row
parser and structural predicate, with the fixed retained inner membership. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure RecoveryOuterLeaf
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
open RecoveryRowTable (localAnswer tableCheck)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_advance (width : Nat) (innerRows : List Row) (n : Nat) (x : Cursor) (outerBits innerBits : List Bool)
    (hw : x.data.outer.base.state.bits.length=width)
    (h : localAnswer width (predicate innerRows) x.prior x.input=true) :
    tableCheck width (predicate innerRows) (n+1) x.prior x.input=
      tableCheck width (predicate innerRows) n (advance x outerBits innerBits).prior (advance x outerBits innerBits).input := by
  have hi : 4*width ≤ x.input.length := by
    have hs : (readRow width x.input).isSome=true := Option.isSome_iff_exists.mpr (by
      cases hp : readRow width x.input with
      | none=>simp [localAnswer,hp] at h
      | some pair=>exact ⟨pair,rfl⟩)
    simpa only [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] using hs
  have hp := RecoveryRowFields.readRow_full width x.input hi
  simp only [localAnswer,hp,Option.any_some] at h
  simp only [tableCheck,hp,h,Bool.true_and,advance,hw]

end NearCubicWires.RepairOrdinary.RecoveryOuterTable
