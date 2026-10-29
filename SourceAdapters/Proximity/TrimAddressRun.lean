import SourceAdapters.Proximity.TrimAddressOutput
import Proof.Gates.CheckedPCPP.NodeEmit

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": exact address-schedule output from the prepared query table. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

theorem schedule_bounds {n : ℕ} (V : ThreeQueryVerifier n) :
    (trimSortedAddresses ⟨n, V⟩).length ≤ inputSize V ∧
    ∀ v ∈ trimSortedAddresses ⟨n, V⟩, natBitLength v ≤ inputSize V := by
  constructor
  · have hc := List.toFinset_card_le (proofValues V)
    rw [proofValues_toFinset] at hc
    have hp := proofValues_length_le V
    simp only [trimSortedAddresses, Finset.length_sort]
    omega
  · intro v hv
    have hp : v ∈ proofValues V := (proofValues_mem V v).mpr (by simpa [trimSortedAddresses] using hv)
    exact field_bits_le V (proofValue_mem_fields V hp)

theorem address_prepared {n : ℕ} (V : ThreeQueryVerifier n) (a b : DS VV MM)
    (hb : Prepared a b V) (hW : inputSize V + 4 ≤ C.Wd) :
    Hs C addressOutput b (200 * (inputSize V + 1) ^ 2)
      (fun d => d.out = b.out ++ trimAddressWord ⟨n, V⟩) := by
  let records := trimSortedAddresses ⟨n, V⟩
  obtain ⟨hN, hbits⟩ := schedule_bounds V
  change records.length ≤ inputSize V at hN
  have hlen : records.length = (usedProofAddresses V).card := by simp [records, trimSortedAddresses]
  have hsize : natBitLength records.length ≤ inputSize V + 1 :=
    (NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le _).trans (by omega)
  have hval : inputSize V + 1 + 2 < 2 ^ C.Wd :=
    lt_of_lt_of_le (by omega : inputSize V + 1 + 2 < C.Wd) (Nat.lt_two_pow_self).le
  have he := address_output (C := C) b hb.constants records (inputSize V + 1) hb.distinctRAM
    (hb.distinctCount.trans hlen.symm) (by rw [hb.distinctCursor, hlen])
    (lt_of_lt_of_le (by omega : records.length < C.Wd) (Nat.lt_two_pow_self).le)
    (by omega) hval hsize (fun v hv => (hbits v hv).trans (by omega))
  refine Hs.mono he ?_ ?_
  · have hm := Nat.mul_le_mul_right (40 * (inputSize V + 1) + 50) (Nat.add_le_add_right hN 1)
    change (records.length + 1) * (40 * (inputSize V + 1) + 50) + 10 ≤ _
    change (records.length + 1) * (40 * (inputSize V + 1) + 50) ≤ _ at hm
    nlinarith
  · intro d hd
    simpa only [trimAddressWord, records, hlen] using hd

def addressProgram : St VV MM := .seq prepareProgram addressOutput

theorem address_program {n : ℕ} (V : ThreeQueryVerifier n) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = trimRequestWord ⟨n, V⟩)
    (hq : a.ram sN = []) (hqrc : a.rc sN = 0)
    (hp : a.ram proofStore = []) (hprc : a.rc proofStore = 0)
    (hu : a.ram distinctStore = []) (hurc : a.rc distinctStore = 0)
    (hW : inputSize V + 4 ≤ C.Wd) :
    Hs C addressProgram a (1000 * (inputSize V + 1) ^ 2)
      (fun b => b.out = a.out ++ trimAddressWord ⟨n, V⟩) := by
  obtain ⟨b, nb, eb, hb, bp⟩ := prepare_program (C := C) V a hc hin hq hqrc hp hprc hu hurc (by omega)
  obtain ⟨d, nd, ed, hd, dout⟩ := address_prepared (C := C) V a b bp hW
  refine ⟨d, nb + nd + 1, Ex.seq eb ed, by nlinarith, ?_⟩
  change d.out = a.out ++ trimAddressWord ⟨n, V⟩
  rw [dout, bp.output]

end NearCubicGates.Adapters.Proximity.Trim
