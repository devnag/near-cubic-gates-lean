import SourceAdapters.Code.DistinctRecordsAppend
import SourceAdapters.Code.DistinctRecordsData

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": first-record and equal-record branches of the paid scan. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.DistinctRecords
open NearCubicGates.Close.Cells

def History (r : Registers) (a : DS VV MM) (previous : Option ℕ) : Prop :=
  a.env r.started = previous.isSome.toNat ∧ ∀ value, previous = some value → a.env r.previous = value

def ChoicePost (r : Registers) (source destination : Fin MM) (a : DS VV MM)
    (output : List ℕ) (value : ℕ) (b : DS VV MM) : Prop :=
  b.ram destination = output ∧ b.rc destination = output.length ∧ b.env r.count = output.length ∧
  b.env r.previous = value ∧ b.env r.started = 1 ∧ b.rc source = a.rc source ∧
  b.env c0 = a.env c0 ∧ Frame r source destination a b

def choose (r : Registers) (destination : Fin MM) : St VV MM :=
  .ite (.eq r.started vZ) (keep r destination)
    (.ite (.eq r.current r.previous) skipS (keep r destination))

theorem keep_spec (C : Ctx) (r : Registers) (hv : r.Valid)
    (source destination : Fin MM) (hsd : source ≠ destination) (a : DS VV MM) (hc : Cst a)
    (output : List ℕ) (value : ℕ) (hm : a.ram destination = output)
    (hrc : a.rc destination = output.length) (hn : a.env r.count = output.length)
    (hvalue : a.env r.current = value) (hw : output.length + 1 < 2 ^ C.Wd) :
    Hs C (keep r destination) a 7 (ChoicePost r source destination a (output ++ [value]) value) := by
  obtain ⟨h0, _, _, _, _, hps, hpn, hsn⟩ := r.separations hv
  have h0p : c0 ≠ r.previous := by intro he; apply h0; simp [he]
  have h0s : c0 ≠ r.started := by intro he; apply h0; simp [he]
  have h0n : c0 ≠ r.count := by intro he; apply h0; simp [he]
  refine ⟨_, _, keep_runs C r hv destination a hc (by rw [hrc, hm]) (by rw [hn]; exact hw), le_rfl, ?_⟩
  have hf := keep_frame r source destination hsd a
  simpa [ChoicePost, kept, DS.put, DS.set, putAt, hm, hrc, hn, hvalue,
    hps, hpn, Ne.symm hsn, h0p, h0s, h0n, hsd] using hf

theorem choose_spec (C : Ctx) (r : Registers) (hv : r.Valid)
    (source destination : Fin MM) (hsd : source ≠ destination) (a : DS VV MM) (hc : Cst a)
    (output : List ℕ) (value : ℕ) (previous : Option ℕ)
    (hm : a.ram destination = output) (hrc : a.rc destination = output.length)
    (hn : a.env r.count = output.length) (hvalue : a.env r.current = value)
    (hh : History r a previous) (hw : output.length + 1 < 2 ^ C.Wd) :
    Hs C (choose r destination) a 9
      (ChoicePost r source destination a (output ++ emitted previous value) value) := by
  obtain ⟨_, hj, hcp, _, _, _, _, _⟩ := r.separations hv
  have hsz : r.started ≠ vZ := by intro he; apply hv.2.1; simp [scratch, he]
  have hk := keep_spec C r hv source destination hsd a hc output value hm hrc hn hvalue hw
  cases previous with
  | none =>
    have hs : a.env r.started = 0 := hh.1
    have he := Hs.iteT (c := .eq r.started vZ)
      (u := .ite (.eq r.current r.previous) skipS (keep r destination)) hsz
      (by simp [Cnd.eval, hs, hc.z]) hk
    simpa [choose, emitted] using he.mono (by omega : 7 + 1 ≤ 9) (fun _ h => h)
  | some previous =>
    have hs : a.env r.started = 1 := hh.1
    have hp : a.env r.previous = previous := hh.2 previous rfl
    have hfalse : (Cnd.eq r.started vZ).eval a = false := by simp [Cnd.eval, hs, hc.z]
    by_cases heq : previous = value
    · have hpv : a.env r.previous = value := hp.trans heq
      have hjp : r.previous ≠ vJ := by intro he; apply hj; simp [he]
      have hjs : r.started ≠ vJ := by intro he; apply hj; simp [he]
      have hjn : r.count ≠ vJ := by intro he; apply hj; simp [he]
      have hpost : ChoicePost r source destination a output value (a.set vJ 0) := by
        have hf := Frame.set r source destination a vJ 0 (by simp [scratch])
        simpa [ChoicePost, DS.set, hm, hrc, hn, hpv, hs, hjp, hjs, hjn,
          (by decide : c0 ≠ vJ)] using hf
      have hz := Hs.op (OpEx.zero (C := C) vJ a) hpost
      have hi := Hs.iteT (c := .eq r.current r.previous) (u := keep r destination)
        hcp (by simp [Cnd.eval, hvalue, hpv]) hz
      have ho := Hs.iteF (c := .eq r.started vZ) (s := keep r destination) hsz hfalse hi
      simpa [choose, skipS, emitted, heq] using ho.mono (by omega : 1 + 1 + 1 ≤ 9) (fun _ h => h)
    · have hi := Hs.iteF (c := .eq r.current r.previous) (s := skipS)
        hcp (by simp [Cnd.eval, hvalue, hp, Ne.symm heq]) hk
      have ho := Hs.iteF (c := .eq r.started vZ) (s := keep r destination) hsz hfalse hi
      simpa [choose, emitted, heq] using ho

end NearCubicGates.Adapters.Code.DistinctRecords
