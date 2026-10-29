import SourceAdapters.Proximity.TrimCollectRead

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": retain precisely the proof-address fields, with paid writes.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
variable {C : Ctx}

def retainAddress : St VV MM :=
  .seq (.op (.wrM proofStore addressReg)) (.op (.inc proofCountReg))

def chooseAddress : St VV MM := .ite (.eq tagReg v1) retainAddress skipS

def KeepPost (a : DS VV MM) (output : List ℕ) (b : DS VV MM) : Prop :=
  b.ram proofStore = output ∧ b.rc proofStore = output.length ∧
  b.env proofCountReg = output.length ∧ b.rc sN = a.rc sN ∧
  b.env c0 = a.env c0 ∧ CollectFrame a b

theorem retain_address (a : DS VV MM) (output : List ℕ) (value : ℕ)
    (hm : a.ram proofStore = output) (hrc : a.rc proofStore = output.length)
    (hn : a.env proofCountReg = output.length) (hv : a.env addressReg = value)
    (hW : output.length + 1 < 2 ^ C.Wd) :
    Hs C retainAddress a 3 (KeepPost a (output ++ [value])) := by
  refine Hs.seq (t2 := 1) (hs_wrM C proofStore addressReg a (by rw [hrc, hm])) (fun b hb => ?_)
  subst b
  have hcount : (a.put proofStore (a.env addressReg)).env proofCountReg = output.length := hn
  refine Hs.mono (hs_inc C proofCountReg _ (by rw [hcount]; exact hW)) le_rfl ?_
  rintro b rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [DS.put, hm, hrc, hv, putAt]
  · simp [DS.put, hrc]
  · simp [hcount]
  · simp [DS.put, sN, proofStore]
  · vsimp [DS.put]
  · exact (DistinctRecords.Frame.put collectRegisters sN proofStore (by decide) a _).trans
      (DistinctRecords.Frame.set collectRegisters sN proofStore _ proofCountReg _ (by decide))

theorem choose_address (a : DS VV MM) (hc : Cst a) (output : List ℕ) (value : ℕ)
    (flag : Bool) (htag : a.env tagReg = flag.toNat)
    (hm : a.ram proofStore = output) (hrc : a.rc proofStore = output.length)
    (hn : a.env proofCountReg = output.length) (hv : a.env addressReg = value)
    (hW : output.length + 1 < 2 ^ C.Wd) :
    Hs C chooseAddress a 4 (KeepPost a (output ++ if flag then [value] else [])) := by
  cases flag with
  | false =>
    change Hs C chooseAddress a 4 (KeepPost a (output ++ []))
    rw [List.append_nil]
    refine Hs.mono (Hs.iteF (c := Cnd.eq tagReg v1) (show tagReg ≠ v1 by decide)
      (by simp [Cnd.eval, htag, hc.one]) (skip_spec (C := C) a)) (by decide) ?_
    rintro b rfl
    refine ⟨hm, hrc, ?_, rfl, ?_, ?_⟩
    · vsimp [hn]
    · vsimp []
    · exact DistinctRecords.Frame.set collectRegisters sN proofStore a vJ 0 (by decide)
  | true =>
    exact Hs.iteT (c := Cnd.eq tagReg v1) (show tagReg ≠ v1 by decide)
      (by simp [Cnd.eval, htag, hc.one]) (retain_address a output value hm hrc hn hv hW)

end NearCubicGates.Adapters.Proximity.Trim
