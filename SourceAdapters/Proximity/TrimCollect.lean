import SourceAdapters.Proximity.TrimCollectLoop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": full collector including paid rewind and initialization. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def collectSetup : St VV MM := .seq (.op (.rwM sN))
  (.seq (.op (.zero c0)) (.op (.zero proofCountReg)))

def collectInitial (a : DS VV MM) : DS VV MM :=
  ((a.rew sN).set c0 0).set proofCountReg 0

def collectProgram : St VV MM := .seq collectSetup collectSweep

theorem collect_setup (a : DS VV MM) :
    Ex C collectSetup a (collectInitial a) (a.rc sN + 5) := by
  have he := Ex.seq (Ex.op (OpEx.rwM (C := C) sN a))
    (Ex.seq (Ex.op (OpEx.zero c0 (a.rew sN)))
      (Ex.op (OpEx.zero proofCountReg ((a.rew sN).set c0 0))))
  simpa only [collectSetup, collectInitial, Nat.add_assoc] using he

theorem collect_initial_frame (a : DS VV MM) : CollectFrame a (collectInitial a) := by
  have hf : CollectFrame a (a.rew sN) := by
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
    intro m hs _
    simp [DS.rew, hs]
  exact hf.trans ((DistinctRecords.Frame.set collectRegisters sN proofStore _ c0 0 (by decide)).trans
    (DistinctRecords.Frame.set collectRegisters sN proofStore _ proofCountReg 0 (by decide)))

theorem collect_program {n : ℕ} (qs : List (SignedQuery n)) (a : DS VV MM) (hc : Cst a)
    (hsource : a.ram sN = qs.flatMap trimQueryFields)
    (hempty : a.ram proofStore = []) (hcursor : a.rc proofStore = 0)
    (hN : a.env fieldsReg = (qs.flatMap trimQueryFields).length)
    (hwidth : (qs.flatMap trimQueryFields).length < 2 ^ C.Wd) :
    Hs C collectProgram a (a.rc sN + 16 * qs.length + 8)
      (CollectLoopPost a (qs.flatMap queryProofValues) (3 * qs.length)) := by
  let b := collectInitial a
  have hf : CollectFrame a b := collect_initial_frame a
  have hbs : b.ram sN = [] ++ qs.flatMap trimQueryFields := by
    simpa [b, collectInitial, DS.rew] using hsource
  have hbc : b.rc sN = ([] : List ℕ).length := by simp [b, collectInitial, DS.rew]
  have hbi : b.env c0 = ([] : List ℕ).length := by vsimp [b, collectInitial, DS.rew]
  have hbl : b.env fieldsReg = ([] : List ℕ).length + 3 * qs.length := by
    rw [hf.env fieldsReg (by decide), hN, flatFields_length]
    simp
  have hbm : b.ram proofStore = [] := hempty
  have hbr : b.rc proofStore = ([] : List ℕ).length := by
    simpa [b, collectInitial, DS.rew, proofStore, sN] using hcursor
  have hbn : b.env proofCountReg = ([] : List ℕ).length := by simp [b, collectInitial]
  obtain ⟨d, nd, ed, hd, dm, drc, dn, ds, di, df⟩ :=
    collect_sweep (C := C) qs b [] [] (hf.cst collectRegisters_valid hc)
      hbs hbc hbi hbl hbm hbr hbn (by simp)
      (by simpa only [List.length_nil, Nat.zero_add, flatFields_length] using hwidth)
  refine ⟨d, a.rc sN + 5 + nd + 1, Ex.seq (collect_setup a) ed, by omega, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hf.trans df⟩
  · simpa using dm
  · simpa using drc
  · simpa using dn
  · simpa using ds
  · simpa using di

end NearCubicGates.Adapters.Proximity.Trim
