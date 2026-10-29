import SourceAdapters.Code.DistinctRecordsChoice

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": one paid read/compare/retain iteration. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.DistinctRecords
open NearCubicGates.Close.Cells

def step (r : Registers) (source destination : Fin MM) : St VV MM :=
  .seq (.op (.rdM source r.current)) (.seq (choose r destination) (.op (.inc c0)))

def StepPost (r : Registers) (source destination : Fin MM) (a : DS VV MM)
    (output : List ℕ) (value : ℕ) (b : DS VV MM) : Prop :=
  b.ram destination = output ∧ b.rc destination = output.length ∧ b.env r.count = output.length ∧
  b.env r.previous = value ∧ b.env r.started = 1 ∧ b.rc source = a.rc source + 1 ∧
  b.env c0 = a.env c0 + 1 ∧ Frame r source destination a b

theorem step_spec (C : Ctx) (r : Registers) (hv : r.Valid)
    (source destination : Fin MM) (hsd : source ≠ destination) (a : DS VV MM) (hc : Cst a)
    (output : List ℕ) (value : ℕ) (previous : Option ℕ)
    (hm : a.ram destination = output) (hrc : a.rc destination = output.length)
    (hn : a.env r.count = output.length) (hh : History r a previous)
    (hread : a.rc source < (a.ram source).length)
    (hvalue : (a.ram source).getD (a.rc source) 0 = value)
    (hw : output.length + 1 < 2 ^ C.Wd) (hiw : a.env c0 + 1 < 2 ^ C.Wd) :
    Hs C (step r source destination) a 13
      (StepPost r source destination a (output ++ emitted previous value) value) := by
  obtain ⟨h0, _, hcp, hcs, hcn, _, _, _⟩ := r.separations hv
  have h0c : c0 ≠ r.current := by intro he; apply h0; simp [he]
  have h0p : c0 ≠ r.previous := by intro he; apply h0; simp [he]
  have h0s : c0 ≠ r.started := by intro he; apply h0; simp [he]
  have h0n : c0 ≠ r.count := by intro he; apply h0; simp [he]
  let a1 := (a.set r.current value).adv source
  have er : Hs C (.op (.rdM source r.current)) a 1 (· = a1) := by
    have e := hs_rdM C source r.current a hread
    simpa only [hvalue] using e
  have hf : Frame r source destination a a1 :=
    (Frame.set r source destination a r.current value (by simp [scratch])).trans
      (Frame.advance r source destination _)
  have hhs : History r a1 previous := by
    simpa only [History, a1, DS.adv, DS.set, Function.update_of_ne (Ne.symm hcs),
      Function.update_of_ne (Ne.symm hcp)] using hh
  have hchoose := choose_spec C r hv source destination hsd a1 (hf.cst hv hc) output value previous
    hm (by simpa [a1, DS.adv, Ne.symm hsd] using hrc)
    (by simpa [a1, DS.adv, Ne.symm hcn] using hn)
    (by simp [a1, DS.adv]) hhs hw
  have hindex : a1.env c0 = a.env c0 := by simp [a1, DS.adv, h0c]
  refine Hs.seq (t2 := 11) er (fun d hd => ?_)
  subst d
  refine Hs.seq (t2 := 1) hchoose (fun b hb => ?_)
  obtain ⟨bm, brc, bn, bp, bs, bsrc, bi, bf⟩ := hb
  have hinc := hs_inc C c0 b (by rw [bi, hindex]; exact hiw)
  refine Hs.mono hinc le_rfl ?_
  rintro d rfl
  refine ⟨bm, brc, ?_, ?_, ?_, ?_, ?_,
    hf.trans (bf.trans (Frame.set r source destination b c0 _ (by simp [scratch])))⟩
  · simpa [Ne.symm h0n] using bn
  · simpa [Ne.symm h0p] using bp
  · simpa [Ne.symm h0s] using bs
  · simpa [a1, DS.adv] using bsrc
  · simp [bi, hindex]

end NearCubicGates.Adapters.Code.DistinctRecords
