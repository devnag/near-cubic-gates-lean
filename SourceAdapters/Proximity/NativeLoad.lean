import SourceAdapters.Proximity.NodeLoop
import Proof.PCP.PCPPNativeRequestSchema

/-! Q04: the actual native-descriptor header and counted node-list loader. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

variable {C : Ctx}

def arityReg : Fin VV := 36
def outputReg : Fin VV := 37
def totalReg : Fin VV := 38

def tripleCount : Script := .seq (.op (.copy totalReg nodeCountReg))
  (.seq (.op (.add totalReg nodeCountReg)) (.op (.add totalReg nodeCountReg)))

theorem triple_count (a : State) (hW : 3 * a.env nodeCountReg < 2 ^ C.Wd) :
    Ex C tripleCount a (a.set totalReg (3 * a.env nodeCountReg)) 5 := by
  change 3 * a.env 35 < 2 ^ C.Wd at hW
  have e1 := Ex.op (OpEx.copy (C := C) totalReg nodeCountReg a (by decide))
  let b := a.set totalReg (a.env nodeCountReg)
  have e2 := Ex.op (OpEx.add (C := C) totalReg nodeCountReg b (by decide)
    (by simp [b, DS.set, totalReg, nodeCountReg]; omega))
  let d := b.set totalReg (b.env totalReg + b.env nodeCountReg)
  have e3 := Ex.op (OpEx.add (C := C) totalReg nodeCountReg d (by decide)
    (by simp [d, b, DS.set, totalReg, nodeCountReg]; omega))
  have he := Ex.seq e1 (Ex.seq e2 e3)
  have hs : d.set totalReg (d.env totalReg + d.env nodeCountReg) =
      a.set totalReg (3 * a.env nodeCountReg) := by
    simp [d, b, DS.set, totalReg, nodeCountReg, Nat.succ_mul]
  rwa [hs] at he

def loadNative : Script := .seq (readInto arityReg)
  (.seq (readInto nodeCountReg) (.seq tripleCount (.seq (readF totalReg) (readInto outputReg))))

def loadScratch : List (Fin VV) := [arityReg, nodeCountReg, totalReg, outputReg] ++ readT

structure NativeLoaded (a b : State) {n : ℕ} (D : BooleanCircuit n) : Prop where
  arity : b.env arityReg = n
  count : b.env nodeCountReg = D.nodes.length
  output : b.env outputReg = D.output.val
  ram : b.ram = Function.update a.ram sN (a.ram sN ++ D.nodes.flatMap nodeFields)
  cursor : b.rc = Function.update a.rc sN ((a.ram sN).length + 3 * D.nodes.length)
  input : b.ip = a.ip + (PCPPNative.descriptor D).length
  other : (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc)
  vars : Fr a b loadScratch

theorem NativeLoaded.constants {a b : State} {n : ℕ} {D : BooleanCircuit n}
    (h : NativeLoaded a b D) (hc : Cst a) : Cst b := Cst.of_fr hc h.vars (by decide)

theorem load_native {n : ℕ} (D : BooleanCircuit n) (a : State) (hc : Cst a)
    (hin : C.inp.drop a.ip = PCPPNative.descriptor D)
    (hrc : a.rc sN = (a.ram sN).length)
    (Λ : ℕ) (hΛ : Λ + 2 ≤ C.Wd)
    (hn : natBitLength n ≤ Λ) (hm : natBitLength D.nodes.length ≤ Λ)
    (ho : natBitLength D.output.val ≤ Λ)
    (hf : ∀ x ∈ D.nodes.flatMap nodeFields, natBitLength x ≤ Λ)
    (hW : 3 * D.nodes.length < 2 ^ C.Wd) :
    Hs C loadNative a ((3 * D.nodes.length + 3) * (30 * Λ + 50) + 50)
      (fun b => NativeLoaded a b D) := by
  let fields := D.nodes.flatMap nodeFields
  have hinput : C.inp.drop a.ip = natWord n ++ (natWord D.nodes.length ++
      (fields.flatMap natWord ++ natWord D.output.val)) := by
    simpa only [PCPPNative.descriptor_eq, fields, nodes_fields_word, List.append_assoc] using hin
  obtain ⟨b, nb, eb, hb, rb⟩ := read_into arityReg (by decide) a hc n _ hinput (by omega)
  have htail1 := rb.tail _ hinput
  obtain ⟨d, nd, ed, hd, rd⟩ := read_into nodeCountReg (by decide) b (rb.constants hc (by decide))
    D.nodes.length _ htail1 (by omega)
  have htail2 := rd.tail _ htail1
  let f := d.set totalReg (3 * d.env nodeCountReg)
  have ef := triple_count d (by rw [rd.value]; exact hW)
  have hfc : Cst f := Cst.of_fr (rd.constants (rb.constants hc (by decide)) (by decide))
    (Fr.set d _ (show totalReg ∈ [totalReg] by simp)) (by decide)
  have hob := rb.other
  have hod := rd.other
  simp only [Prod.mk.injEq] at hob hod
  have hfrc : f.rc sN = (f.ram sN).length := by simpa [f, DS.set, hod.2.1, hod.2.2.1, hob.2.1, hob.2.2.1] using hrc
  obtain ⟨g, ng, eg, hg, lg, hgc, fg⟩ := readF_spec (C := C) totalReg (by decide) f hfc fields
    (natWord D.output.val) Λ htail2
    (by simp only [f, DS.set_env_self, rd.value, fields, nodeFields_length]) hf hΛ
    (by simpa only [fields, nodeFields_length] using hW) hfrc
  have htail3 : C.inp.drop g.ip = natWord D.output.val ++ [] := by
    rw [lg.2.2.1, ← List.drop_drop]
    change (C.inp.drop d.ip).drop _ = _
    rw [htail2, List.drop_left, List.append_nil]
  obtain ⟨z, nz, ez, hz, rz⟩ := read_into outputReg (by decide) g hgc D.output.val [] htail3 (by omega)
  have hoz := rz.other
  simp only [Prod.mk.injEq] at hoz
  refine ⟨z, _, Ex.seq eb (Ex.seq ed (Ex.seq ef (Ex.seq eg ez))), ?_, ?_⟩
  · simp only [fields, nodeFields_length] at hg
    nlinarith
  · refine ⟨?_, ?_, rz.value, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rz.vars arityReg (by decide), fg arityReg (by decide)]
      simpa [f, DS.set, arityReg, totalReg] using (rd.vars arityReg (by decide)).trans rb.value
    · rw [rz.vars nodeCountReg (by decide), fg nodeCountReg (by decide)]
      simpa [f, DS.set, nodeCountReg, totalReg] using rd.value
    · rw [hoz.2.1, lg.1]
      simp only [f, DS.set_ram, hod.2.1, hob.2.1, fields]
    · rw [hoz.2.2.1, lg.2.1]
      simp only [f, DS.set_ram, DS.set_rc, hod.2.1, hob.2.1, hod.2.2.1, hob.2.2.1,
        fields, nodeFields_length]
    · rw [rz.cursor, lg.2.2.1]
      change d.ip + (fields.flatMap natWord).length + (natWord D.output.val).length = _
      rw [rd.cursor, rb.cursor, PCPPNative.descriptor_eq]
      simp only [fields, nodes_fields_word, List.length_append]
      omega
    · rw [hoz.1, hoz.2.2.2.1, hoz.2.2.2.2.1, hoz.2.2.2.2.2,
        lg.2.2.2.1, lg.2.2.2.2.1, lg.2.2.2.2.2.1, lg.2.2.2.2.2.2]
      simpa only [f, DS.set_out, DS.set_kin, DS.set_kout, DS.set_kc] using
        (show (d.out, d.kin, d.kout, d.kc) = (a.out, a.kin, a.kout, a.kc) from by
          rw [hod.1, hod.2.2.2.1, hod.2.2.2.2.1, hod.2.2.2.2.2,
            hob.1, hob.2.2.2.1, hob.2.2.2.2.1, hob.2.2.2.2.2])
    · exact Fr.trans (rb.vars.weaken (by decide)) (Fr.trans (rd.vars.weaken (by decide))
        (Fr.trans (Fr.set d _ (show totalReg ∈ loadScratch by decide))
          (Fr.trans (fg.weaken (by decide)) (rz.vars.weaken (by decide)))))

end NearCubicGates.Adapters.Proximity.SourcePrinting
