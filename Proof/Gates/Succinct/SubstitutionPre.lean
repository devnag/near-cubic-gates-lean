import Proof.Gates.Succinct.SubstitutionPhaseSpecs
import Proof.Gates.Succinct.SubstitutionEmissionStart

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct NearCubicGates.Close.Outer
open RepairRepresentation (natWord)

theorem preSpec : PreSpec := by
  intro o q B cap hcap
  have hcp := capH_ge o B
  have h4 := sq4 (sizeS o B)
  have hS : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨σ1, e1, hH⟩ := header_spec o B cap (by omega)
  obtain ⟨σ2, e2, hC⟩ := countPass_spec cap o B σ1 hH (by omega)
  obtain ⟨σ3, e3, hst, hsh, hv3, hc3⟩ := sizes_spec cap o B σ2 hC (by omega)
  obtain ⟨hs2, -, hcell2⟩ := hC
  have hs3 : StrAt σ3 o.word (PCPPNative.descriptor B) [] (ofl o.circuit) (natWord o.ell) (pC o) (pB B) 0 0 0 := by
    unfold StrAt at hs2 ⊢; rw [hst, hsh]; exact hs2
  obtain ⟨σ4, e4, hM⟩ := emStart_spec cap o B σ3 hs3 hv3 (by rw [hc3, hcell2]) hcap
  exact ⟨σ1, σ2, σ3, σ4, e1, e2, e3, e4, hM⟩

end NearCubicGates.Close.Succinct.SubstMachine
