import SourceAdapters.Proximity.SourcePrinting
import SourceAdapters.Proximity.CircuitRepresentation
import Proof.PCP.PCPPRequestNodeSchema

/-! Q04: the exact source node writer from the native descriptor's three fields. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def tagReg : Fin VV := 30
def leftReg : Fin VV := 31
def rightReg : Fin VV := 32
def threeReg : Fin VV := 33

def writeConstant : Script := .seq (emitBits [false, false, false])
  (.ite (.eq leftReg vZ) (emitBits [false]) (emitBits [true]))

def writeInput : Script := .seq (emitBits [false, false, true]) (fieldFrom leftReg)
def writeNot : Script := .seq (emitBits [false, true, false]) (fieldFrom leftReg)
def writeAnd : Script := .seq (emitBits [false, true, true]) (.seq (fieldFrom leftReg) (fieldFrom rightReg))
def writeOr : Script := .seq (emitBits [true, false, false]) (.seq (fieldFrom leftReg) (fieldFrom rightReg))
def writeBinary : Script := .ite (.eq tagReg threeReg) writeAnd writeOr
def writeHigher : Script := .ite (.eq tagReg v2) writeNot writeBinary
def writeNonconstant : Script := .ite (.eq tagReg v1) writeInput writeHigher
def writeNode : Script := .ite (.eq tagReg vZ) writeConstant writeNonconstant

theorem write_constant (C : Ctx) (bit : Bool) (a : State) (hc : Cst a)
    (hv : a.env leftReg = bit.toNat) :
    Hs C writeConstant a 12 (fun b => Printed a b [false, false, false, bit]) := by
  refine Hs.mono (Hs.seq (t2 := 4) (emit_bits C [false, false, false] a) (fun b hb => ?_))
    (by norm_num) (fun _ h => h)
  have hL : b.env leftReg = bit.toNat := (hb.vars leftReg (by decide)).trans hv
  have hZ := (hb.constants hc).z
  have he : Hs C (.ite (.eq leftReg vZ) (emitBits [false]) (emitBits [true])) b 4
      (fun d => Printed b d [bit]) := by
    cases bit
    · exact Hs.iteT (by unfold Cnd.wf; decide) (by simp [Cnd.eval, hL, hZ]) (emit_bits C [false] b)
    · exact Hs.iteF (by unfold Cnd.wf; decide) (by simp [Cnd.eval, hL, hZ]) (emit_bits C [true] b)
  exact he.mono le_rfl (fun _ hd => hb.trans hd)

/-- Every branch, payload bit and marker has an actual charged language run. -/
theorem write_node (C : Ctx) {n : ℕ} (node : BooleanNode n) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd)
    (hT : a.env tagReg = PCPPRequestNodeSchema.fields node 0)
    (hL : a.env leftReg = PCPPRequestNodeSchema.fields node 1)
    (hR : a.env rightReg = PCPPRequestNodeSchema.fields node 2)
    (h3 : a.env threeReg = 3) :
    Hs C writeNode a
      (10 * (PCPPRequestNodeSchema.fields node 1).bits.length +
        10 * (PCPPRequestNodeSchema.fields node 2).bits.length + 40)
      (fun b => Printed a b (sourceNodeWord node)) := by
  have h0 := hc.z
  have h1 := hc.one
  have h2 := hc.two
  cases node with
  | const bit =>
    have he := Hs.iteT (c := .eq tagReg vZ) (s := writeConstant) (u := writeNonconstant) (by unfold Cnd.wf; decide)
      (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h0])
      (write_constant C bit a hc (by simpa [PCPPRequestNodeSchema.fields] using hL))
    exact he.mono (by omega) (fun _ h => h)
  | input i =>
    have e := prefix_field C [false, false, true] leftReg (by decide) a hc hW
    rw [hL] at e
    have he := Hs.iteF (c := .eq tagReg vZ) (s := writeConstant) (u := writeNonconstant) (by unfold Cnd.wf; decide)
      (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h0])
      (Hs.iteT (c := .eq tagReg v1) (s := writeInput) (u := writeHigher) (by unfold Cnd.wf; decide)
        (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h1]) e)
    exact he.mono (by simp [PCPPRequestNodeSchema.fields]; omega) (fun _ h => h)
  | not j =>
    have e := prefix_field C [false, true, false] leftReg (by decide) a hc hW
    rw [hL] at e
    have he := Hs.iteF (c := .eq tagReg vZ) (s := writeConstant) (u := writeNonconstant) (by unfold Cnd.wf; decide)
      (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h0])
      (Hs.iteF (c := .eq tagReg v1) (s := writeInput) (u := writeHigher) (by unfold Cnd.wf; decide)
        (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h1])
        (Hs.iteT (c := .eq tagReg v2) (s := writeNot) (u := writeBinary) (by unfold Cnd.wf; decide)
          (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h2]) e))
    exact he.mono (by simp [PCPPRequestNodeSchema.fields]; omega) (fun _ h => h)
  | and j k =>
    have e := prefix_two_fields C [false, true, true] leftReg rightReg (by decide) (by decide) a hc hW
    rw [hL, hR] at e
    have he := Hs.iteF (c := .eq tagReg vZ) (s := writeConstant) (u := writeNonconstant) (by unfold Cnd.wf; decide)
      (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h0])
      (Hs.iteF (c := .eq tagReg v1) (s := writeInput) (u := writeHigher) (by unfold Cnd.wf; decide)
        (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h1])
        (Hs.iteF (c := .eq tagReg v2) (s := writeNot) (u := writeBinary) (by unfold Cnd.wf; decide)
          (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h2])
          (Hs.iteT (c := .eq tagReg threeReg) (s := writeAnd) (u := writeOr) (by unfold Cnd.wf; decide)
            (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h3]) e)))
    exact he.mono (by simp [PCPPRequestNodeSchema.fields]; omega) (fun _ h => h)
  | or j k =>
    have e := prefix_two_fields C [true, false, false] leftReg rightReg (by decide) (by decide) a hc hW
    rw [hL, hR] at e
    have he := Hs.iteF (c := .eq tagReg vZ) (s := writeConstant) (u := writeNonconstant) (by unfold Cnd.wf; decide)
      (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h0])
      (Hs.iteF (c := .eq tagReg v1) (s := writeInput) (u := writeHigher) (by unfold Cnd.wf; decide)
        (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h1])
        (Hs.iteF (c := .eq tagReg v2) (s := writeNot) (u := writeBinary) (by unfold Cnd.wf; decide)
          (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h2])
          (Hs.iteF (c := .eq tagReg threeReg) (s := writeAnd) (u := writeOr) (by unfold Cnd.wf; decide)
            (by simp [Cnd.eval, hT, PCPPRequestNodeSchema.fields, h3]) e)))
    exact he.mono (by simp [PCPPRequestNodeSchema.fields]; omega) (fun _ h => h)

end NearCubicGates.Adapters.Proximity.SourcePrinting
