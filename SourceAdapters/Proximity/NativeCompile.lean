import SourceAdapters.Proximity.NativePrint
import SourceAdapters.Proximity.PrefixSizes
import Proof.Gates.Cells.Prelude
import Proof.Gates.Succinct.Eval
import Proof.Gates.CounterMachine.PrefixFinal

/-! Q04: initialized ordinary compilation of the exact native descriptor to
CW19's independent source encoding. Widths use the paid logarithmic header. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

noncomputable def nativeCtx (S : SourceCircuit) : Ctx :=
  ctxOf noCallee ⟨16, 1, 0, 0, 0, 0⟩ (LengthPrefix.wrapped (PCPPNative.descriptor S.circuit))

def nativeCompiler : Script := .seq initP (.seq (setK threeReg 3) (.seq rdNatI nativeToSource))

theorem native_bounds (S : SourceCircuit) :
    let L := (PCPPNative.descriptor S.circuit).length
    S.circuit.nodes.length + 5 ≤ L ∧ natBitLength S.arity ≤ 8 * (L + 1) ∧
      natBitLength S.circuit.nodes.length ≤ 8 * (L + 1) ∧
      natBitLength S.circuit.output.val ≤ 8 * (L + 1) ∧
      ∀ x ∈ S.circuit.nodes.flatMap nodeFields, natBitLength x ≤ 8 * (L + 1) := by
  let L := (PCPPNative.descriptor S.circuit).length
  have hlen := NearCubicGates.Close.Succinct.descriptor_length_ge S.circuit
  have hn := S.inputs_le_size
  change S.arity ≤ S.circuit.nodes.length at hn
  have ho := S.circuit.output.isLt
  refine ⟨hlen, ?_, ?_, ?_, ?_⟩
  · have hb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le S.arity
    omega
  · have hb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le S.circuit.nodes.length
    omega
  · have hb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le S.circuit.output.val
    omega
  · intro x hx
    obtain ⟨node, hnode, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hnode
    have hfield : ∃ j : Fin 3, x = PCPPRequestNodeSchema.fields S.circuit.nodes[i] j := by
      simp only [nodeFields, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    obtain ⟨j, rfl⟩ := hfield
    have hb := PCPPRequestNodeSchema.field_bound S.circuit.nodes[i] i.val (S.circuit.wellFormed i) j
    have hi := i.isLt
    have hw := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le
      (PCPPRequestNodeSchema.fields S.circuit.nodes[i] j)
    omega

theorem native_width (S : SourceCircuit) :
    16 * ((PCPPNative.descriptor S.circuit).length + 1) ≤ (nativeCtx S).Wd := by
  have hp := LengthPrefix.allocation_covers_length (PCPPNative.descriptor S.circuit)
  simp only [nativeCtx, ctxOf, Sz.W, Nat.one_mul]
  omega

theorem native_compiler_runs (S : SourceCircuit) :
    ∃ b cost, Ex (nativeCtx S) nativeCompiler (a0 : State) b cost ∧
      b.out = sourceCircuitWord S ∧ cost ≤ 20000 * ((PCPPNative.descriptor S.circuit).length + 1) ^ 2 := by
  let C := nativeCtx S
  let word := PCPPNative.descriptor S.circuit
  let L := word.length
  have hsize := native_bounds S
  change S.circuit.nodes.length + 5 ≤ L ∧ _ at hsize
  obtain ⟨hmL, hn, hm, ho, hf⟩ := hsize
  have hwidth := native_width S
  change 16 * (L + 1) ≤ C.Wd at hwidth
  have hsmall : 4 ≤ 2 ^ C.Wd := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ C.Wd by omega)
    norm_num at hh
    exact hh
  have hN : 3 * S.circuit.nodes.length < 2 ^ C.Wd :=
    lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  have hbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le L
  obtain ⟨b, nb, eb, hb, cb, bram, brc, bip, bout, _, _, _, _⟩ :=
    initP_spec (C := C) (a0 : State) rfl rfl rfl (by omega)
  obtain ⟨d, nd, ed, hd, d3, dsh, df⟩ := setK_spec (C := C) threeReg (by decide) 3 b (by omega)
  have ds := Same.of_sh dsh
  have cd := Cst.of_fr cb df (by decide)
  have hdInput : C.inp.drop d.ip = natWord L ++ word := by
    rw [ds.ip, bip]
    rfl
  obtain ⟨e, ne, ee, he, _, _, eip, eo, ef⟩ := rdNatI_spec (C := C) d cd L word hdInput (by omega)
  have ce := cst_fr cd ef
  simp only [Prod.mk.injEq] at eo
  have heInput : C.inp.drop e.ip = word := by rw [eip, ← List.drop_drop, hdInput, List.drop_left]
  have he3 : e.env threeReg = 3 := (ef threeReg (by decide)).trans d3
  have heRam : e.ram sN = [] := by rw [eo.2.1, ds.ram, bram]; rfl
  have heRc : e.rc sN = 0 := by rw [eo.2.2.1, ds.rc, brc]; rfl
  obtain ⟨z, nz, ez, hz, zout⟩ := native_to_source S e ce he3 heRam heRc heInput
    (8 * (L + 1)) (by omega) hn hm ho hf hN hsmall
  refine ⟨z, _, Ex.seq eb (Ex.seq ed (Ex.seq ee ez)), ?_, ?_⟩
  · have heOut : e.out = [] := by rw [eo.1, ds.out, bout]; rfl
    simpa only [heOut, List.nil_append] using zout
  · have hc : 1000 * (S.circuit.nodes.length + 1) * (8 * (L + 1) + 1) ≤ 9000 * (L + 1) ^ 2 := by
      have hh := Nat.mul_le_mul (show S.circuit.nodes.length + 1 ≤ L + 1 by omega)
        (show 8 * (L + 1) + 1 ≤ 9 * (L + 1) by omega)
      nlinarith
    change _ ≤ 20000 * (L + 1) ^ 2
    nlinarith

noncomputable def nativeCompilerWordFunction : WordFunction SourceCircuit
    (fun S => LengthPrefix.wrapped (PCPPNative.descriptor S.circuit)) sourceCircuitWord
    (fun S => langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
      (LengthPrefix.wrapped (PCPPNative.descriptor S.circuit))
      (20000 * ((PCPPNative.descriptor S.circuit).length + 1) ^ 2)) :=
  wordFunction_of_lang (Req := SourceCircuit) (V := VV) (M := MM)
    (fun S => LengthPrefix.wrapped (PCPPNative.descriptor S.circuit)) sourceCircuitWord
    noCallee ⟨16, 1, 0, 0, 0, 0⟩ nativeCompiler
    (fun S => 20000 * ((PCPPNative.descriptor S.circuit).length + 1) ^ 2)
    (native_compiler_runs) (fun S => by
      have h := native_width S
      change 1 ≤ (nativeCtx S).Wd
      omega)

end NearCubicGates.Adapters.Proximity.SourcePrinting
