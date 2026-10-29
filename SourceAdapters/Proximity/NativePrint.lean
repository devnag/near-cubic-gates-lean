import SourceAdapters.Proximity.NativeLoad

/-! Q04: the complete native-to-source descriptor transducer after initialization. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity

variable {C : Ctx}

/-- Uses the bitsLength_le_natBitLength in ValidatorCompositeLeafBounds. -/
theorem bits_le_field_width (v : ℕ) : v.bits.length ≤ natBitLength v := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) v)

def writeHeader : Script := .seq (fieldFrom arityReg) (.seq (fieldFrom nodeCountReg) (fieldFrom outputReg))

theorem write_header (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ C.Wd) :
    Hs C writeHeader a
      (10 * (a.env arityReg).bits.length + 10 * (a.env nodeCountReg).bits.length +
        10 * (a.env outputReg).bits.length + 20)
      (fun b => Printed a b (frame (a.env arityReg).bits ++ frame (a.env nodeCountReg).bits ++
        frame (a.env outputReg).bits)) := by
  refine Hs.mono (Hs.seq
    (t2 := 10 * (a.env nodeCountReg).bits.length + 10 * (a.env outputReg).bits.length + 13)
    (field_from C arityReg (by decide) a hc hW) (fun b hb => ?_)) (by omega) (fun _ h => h)
  have he := two_fields C nodeCountReg outputReg (by decide) (by decide) b (hb.constants hc) hW
  rw [hb.vars nodeCountReg (by decide), hb.vars outputReg (by decide)] at he
  exact he.mono le_rfl (fun _ hd => by simpa only [List.append_assoc] using hb.trans hd)

def nativeToSource : Script := .seq loadNative (.seq writeHeader (.seq (.op (.rwM sN)) writeStoredNodes))

theorem native_to_source (S : SourceCircuit) (a : State) (hc : Cst a)
    (h3 : a.env threeReg = 3) (hzero : a.ram sN = []) (hrc : a.rc sN = 0)
    (hin : C.inp.drop a.ip = PCPPNative.descriptor S.circuit)
    (Λ : ℕ) (hΛ : Λ + 2 ≤ C.Wd)
    (hn : natBitLength S.arity ≤ Λ) (hm : natBitLength S.circuit.nodes.length ≤ Λ)
    (ho : natBitLength S.circuit.output.val ≤ Λ)
    (hf : ∀ x ∈ S.circuit.nodes.flatMap nodeFields, natBitLength x ≤ Λ)
    (hNW : 3 * S.circuit.nodes.length < 2 ^ C.Wd) (hW : 4 ≤ 2 ^ C.Wd) :
    Hs C nativeToSource a (1000 * (S.circuit.nodes.length + 1) * (Λ + 1))
      (fun b => b.out = a.out ++ sourceCircuitWord S) := by
  obtain ⟨b, nb, eb, hb, lb⟩ := load_native S.circuit a hc hin (by rw [hzero, hrc]; rfl)
    Λ hΛ hn hm ho hf hNW
  obtain ⟨d, nd, ed, hd, pd⟩ := write_header b (lb.constants hc) hW
  have dr := pd.rest_eq
  simp only [rest, Prod.mk.injEq] at dr
  let e := d.rew sN
  have ee := Ex.op (OpEx.rwM (C := C) sN d)
  have h3e : e.env threeReg = 3 := by
    change d.env threeReg = 3
    rw [pd.vars threeReg (by decide), lb.vars threeReg (by decide), h3]
  have hNe : e.env nodeCountReg = S.circuit.nodes.length := by
    change d.env nodeCountReg = S.circuit.nodes.length
    rw [pd.vars nodeCountReg (by decide), lb.count]
  have hstore : (e.ram sN).drop (e.rc sN) = S.circuit.nodes.flatMap nodeFields ++ [] := by
    simp only [e, DS.rew]
    rw [Function.update_self, List.drop_zero, dr.2.1, lb.ram, Function.update_self, hzero]
    simp
  have hdC := pd.constants (lb.constants hc)
  have heC : Cst e := ⟨hdC.z, hdC.one, hdC.two⟩
  have hwidth : ∀ node ∈ S.circuit.nodes, ∀ i : Fin 3,
      (PCPPRequestNodeSchema.fields node i).bits.length ≤ Λ := by
    intro node hnode i
    apply (bits_le_field_width _).trans
    apply hf
    refine List.mem_flatMap.mpr ⟨node, hnode, ?_⟩
    fin_cases i <;> simp [nodeFields]
  obtain ⟨z, nz, ez, hz, pz⟩ := write_stored_nodes C S.circuit.nodes [] e heC hW h3e hstore hNe
    (by omega) Λ hwidth
  refine ⟨z, _, Ex.seq eb (Ex.seq ed (Ex.seq ee ez)), ?_, ?_⟩
  · have hn' := (bits_le_field_width S.arity).trans hn
    have hm' := (bits_le_field_width S.circuit.nodes.length).trans hm
    have ho' := (bits_le_field_width S.circuit.output.val).trans ho
    rw [lb.arity, lb.count, lb.output] at hd
    have hcurs : d.rc sN = 3 * S.circuit.nodes.length := by
      rw [dr.2.2.1, lb.cursor, Function.update_self, hzero]
      simp
    rw [hcurs]
    nlinarith
  · change z.out = a.out ++ sourceCircuitWord S
    rw [pz.out_eq]
    change d.out ++ S.circuit.nodes.flatMap sourceNodeWord = _
    rw [pd.out_eq, lb.arity, lb.count, lb.output]
    have hbout := congrArg Prod.fst lb.other
    change b.out = a.out at hbout
    rw [hbout]
    simp only [sourceCircuitWord, List.append_assoc]

end NearCubicGates.Adapters.Proximity.SourcePrinting
