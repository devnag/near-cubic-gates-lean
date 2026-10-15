import Proof.MachineModel.Padded

/-! Exact existing native-bank projections consumed by the physical incidence
dock. These are field identities, not producers for the remaining metadata. -/
namespace NearCubicWires.ExtIncidence.BankFields
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem heads {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).heads=
      CloseoutRowsBankFields.heads out :=
  CloseoutRowsBankFields.polynomial_heads gs p F Q w C rows out

theorem table {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 36=
      ZeroPadding.pad C rows.flatten := by
  change ZeroPadding.pad C (ZeroPadding.pad 0 (ZeroPadding.pad 0 rows.flatten))=_
  rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]

theorem template {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 38=
      ZeroPadding.pad C (UnaryTemplate.tape gs.length) := by
  change ZeroPadding.pad C (ZeroPadding.pad 0 (ZeroPadding.pad 0 (UnaryTemplate.tape gs.length)))=_
  rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]

theorem driver {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 104=List.replicate C true := by
  change ZeroPadding.pad C (List.replicate C true)=_
  simp [ZeroPadding.pad]

theorem log {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 105=List.replicate (C+1) false := by
  change ZeroPadding.pad (C+1) (List.replicate (C+1) false)=_
  simp [ZeroPadding.pad]

theorem table_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w : ℕ)
    (ms : List (List (Fin gs.length))) (hM : ms.length ≤ 2^w) :
    (rawRows ms).flatten.length ≤ CloseoutRowsPreparationBounds.capacity n p F w gs.length Q := by
  have hc:=CloseoutRowsPreparationFits.cursor_fits n p F w gs.length Q ms.length 1 hM (by omega)
  rw [Padded.raw_rows_length]
  unfold RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget
    RowMaskLookupReusable.capacity RowMaskLookup.budget at hc
  nlinarith

end NearCubicWires.ExtIncidence.BankFields
