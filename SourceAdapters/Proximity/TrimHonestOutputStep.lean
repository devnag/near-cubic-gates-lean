import SourceAdapters.Proximity.TrimHonestOutputFrame

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": read one retained original label, emit its canonical bit,
and advance the bounded schedule index. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def outputTemps : List (Fin VV) := scheduleIndex :: addressReg :: addressTemps
def outputStep : St VV MM := .seq (.op (.rdM scheduleStore addressReg))
  (.seq emitAddress (.op (.inc scheduleIndex)))

theorem output_step {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : BitInput N) (a : DS VV MM) (hc : Cst a)
    (ready : Ready C V input proof a) (address : ℕ) (tail : List ℕ)
    (hread : (a.ram scheduleStore).drop (a.rc scheduleStore) = address :: tail)
    (haddress : address < 2 ^ C.Wd) (hindex : a.env scheduleIndex + 1 < 2 ^ C.Wd) :
    Hs C outputStep a
      (6 * N + 16 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 36)
      (fun b => b.out = a.out ++ [canonicalClauseProof V input (finiteProofOracle proof) address] ∧
        b.rc scheduleStore = a.rc scheduleStore + 1 ∧ b.env scheduleIndex = a.env scheduleIndex + 1 ∧
        Ready C V input proof b ∧ OutputFrame outputTemps a b) := by
  have hl := congrArg List.length hread
  simp only [List.length_drop, List.length_cons] at hl
  have hv : (a.ram scheduleStore).getD (a.rc scheduleStore) 0 = address := fld_of_drop hread
  let b := (a.set addressReg address).adv scheduleStore
  have e1 : Ex C (.op (.rdM scheduleStore addressReg)) a b 1 := by
    simpa only [b, hv] using Ex.op (OpEx.rdM (C := C) scheduleStore addressReg a (by omega))
  have fb : OutputFrame outputTemps a b :=
    (OutputFrame.set outputTemps a addressReg address (by simp [outputTemps])).trans
      (OutputFrame.advance outputTemps _)
  have rb : Ready C V input proof b := (ready.set addressReg address (by decide) (by decide)).advance
  have ba : b.env addressReg = address := by simp [b, DS.adv]
  obtain ⟨d, cost, e2, hcost, dout, rd, fd⟩ :=
    emit_address V input proof b (fb.constants hc (by decide)) rb (by rw [ba]; exact haddress)
  have di : d.env scheduleIndex = a.env scheduleIndex := by
    rw [fd.env scheduleIndex (by decide)]
    simp [b, DS.adv, DS.set, scheduleIndex, addressReg]
  have e3 := Ex.op (OpEx.inc (C := C) scheduleIndex d (by rw [di]; exact hindex))
  let e := d.set scheduleIndex (d.env scheduleIndex + 1)
  refine ⟨e, 1 + (cost + 1 + 1) + 1, Ex.seq e1 (Ex.seq e2 e3), by omega, ?_⟩
  refine ⟨?_, ?_, by simp [e, di], rd.set scheduleIndex _ (by decide) (by decide), ?_⟩
  · change d.out = _
    have bo : b.out = a.out := rfl
    simpa only [ba, bo] using dout
  · change d.rc scheduleStore = _
    rw [fd.cursor scheduleStore (by decide)]
    simp [b, DS.adv]
  · exact fb.trans (((OutputFrame.of_lookup fd).weaken
      (fun _ hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))).trans
      (OutputFrame.set outputTemps d scheduleIndex _ (by simp [outputTemps])))

end NearCubicGates.Adapters.Proximity.TrimHonest
