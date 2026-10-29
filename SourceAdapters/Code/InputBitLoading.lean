import SourceAdapters.Code.CountedParsing
import Proof.Gates.Cells.Mac

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": framed input fields at arbitrary prefixes are loaded into a bit
store with a paid linear scan, retaining their full length and trailing zeros. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.InputBitLoading

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing

def body (m : Fin MM) (len : Fin VV) : St VV MM :=
  .seq (.op (.rdI vJ)) (.seq (.op (.wrM m vJ))
    (.seq (.op (.inc len)) (.op (.rdI vJ))))

def script (m : Fin MM) (len : Fin VV) : St VV MM :=
  .seq (.op (.zero len)) (.seq (.op (.rdI vJ)) (.loop (.lt vZ vJ) (body m len)))

/-- The exact state after loading the listed bits. -/
def loaded (m : Fin MM) (len : Fin VV) (a : DS VV MM) (pos flag : ℕ)
    (bits : List Bool) : DS VV MM :=
  {a with ip := pos
          env := fun i => if i = vJ then flag else if i = len then bits.length else a.env i
          ram := Function.update a.ram m (bits.map Bool.toNat)
          rc := Function.update a.rc m bits.length}

private theorem loop_runs (C : Ctx) (m : Fin MM) (len : Fin VV)
    (hlj : len ≠ vJ) (hlz : len ≠ vZ) (a : DS VV MM) (hz : a.env vZ = 0) :
    ∀ (bits pre suffix done : List Bool), C.inp = pre ++ frame bits ++ suffix →
      done.length + bits.length < 2 ^ C.Wd →
      Ex C (.loop (.lt vZ vJ) (body m len))
        (loaded m len a (pre.length + 1) (!bits.isEmpty).toNat done)
        (loaded m len a (pre.length + 2 * bits.length + 1) 0 (done ++ bits))
        (9 * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre suffix done _ _
    have h := Ex.loopF (C := C) (c := Cnd.lt vZ vJ) (s := body m len)
      (a := loaded m len a (pre.length + 1) 0 done) (by decide : vZ ≠ vJ)
      (by simp [Cnd.eval, loaded, Ne.symm hlz, (by decide : vZ ≠ vJ), hz])
    simpa using h
  | cons bit bits ih =>
    intro pre suffix done hin hcap
    let a0 := loaded m len a (pre.length + 1) 1 done
    have ht : (Cnd.lt vZ vJ).eval a0 = true := by
      simp [Cnd.eval, a0, loaded, Ne.symm hlz, (by decide : vZ ≠ vJ), hz]
    have hin0 : C.inp = (pre ++ [true]) ++ bit :: (frame bits ++ suffix) := by
      simpa [frame, List.append_assoc] using hin
    have e1 := CountedParsing.read_at_prefix C vJ a0 (pre ++ [true]) bit
      (frame bits ++ suffix) hin0 (by simp [a0, loaded])
    let a1 := CountedParsing.readState vJ a0 bit
    have e2 : Ex C (.op (.wrM m vJ)) a1 (a1.put m bit.toNat) 1 := by
      have e := OpEx.wrM (C := C) m vJ a1 (by simp [a1, CountedParsing.readState, a0, loaded])
      simpa [a1, CountedParsing.readState] using Ex.op e
    let a2 := a1.put m bit.toNat
    have hlen2 : a2.env len = done.length := by
      simp [a2, a1, CountedParsing.readState, a0, loaded, DS.put, DS.set, hlj]
    have e3 := Ex.op (OpEx.inc (C := C) len a2 (by rw [hlen2]; simp only [List.length_cons] at hcap; omega))
    rw [hlen2] at e3
    let a3 := a2.set len (done.length + 1)
    have hin1 : C.inp = (pre ++ [true, bit]) ++ frame bits ++ suffix := by
      simpa [frame, List.append_assoc] using hin
    have hpos : a3.ip = (pre ++ [true, bit]).length := by
      simp [a3, a2, a1, CountedParsing.readState, a0, loaded, DS.put]
    have e4 : Ex C (.op (.rdI vJ)) a3 (CountedParsing.readState vJ a3 (!bits.isEmpty)) 1 := by
      apply CountedParsing.read_bit C vJ a3 (!bits.isEmpty)
      · rw [hpos, hin1]
        have hp := Parsing.frame_nonempty bits
        simp only [List.length_append]
        omega
      · rw [hpos, hin1, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
        simpa using Parsing.frame_first bits suffix
    have hnext : CountedParsing.readState vJ a3 (!bits.isEmpty) =
        loaded m len a ((pre ++ [true, bit]).length + 1) (!bits.isEmpty).toNat (done ++ [bit]) := by
      apply state_ext
      · funext i
        by_cases hj : i = vJ
        · subst i; simp [CountedParsing.readState, loaded, DS.set]
        · by_cases hl : i = len
          · subst i
            simp [CountedParsing.readState, a3, a2, a1, a0, loaded, DS.set, DS.put, hlj]
          · simp [CountedParsing.readState, a3, a2, a1, a0, loaded, DS.set, DS.put, hj, hl]
      · simp [CountedParsing.readState, a3, a2, a1, a0, loaded, DS.put]
      · rfl
      · funext q
        by_cases hq : q = m
        · subst q
          simp [CountedParsing.readState, a3, a2, a1, a0, loaded, DS.put, putAt]
        · simp [CountedParsing.readState, a3, a2, a1, a0, loaded, DS.put, hq]
      · funext q
        by_cases hq : q = m
        · subst q
          simp [CountedParsing.readState, a3, a2, a1, a0, loaded, DS.put]
        · simp [CountedParsing.readState, a3, a2, a1, a0, loaded, DS.put, hq]
      · rfl
      · rfl
      · rfl
    have ebody := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))
    rw [hnext] at ebody
    have ei := ih (pre ++ [true, bit]) suffix (done ++ [bit]) hin1
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hcap ⊢; omega)
    have e := Ex.loopT (c := Cnd.lt vZ vJ) (by decide : vZ ≠ vJ) ht ebody ei
    have hfinal : loaded m len a ((pre ++ [true, bit]).length + 2 * bits.length + 1) 0
        ((done ++ [bit]) ++ bits) =
        loaded m len a (pre.length + 2 * (bit :: bits).length + 1) 0 (done ++ bit :: bits) := by
      congr 1
      · simp; omega
      · simp [List.append_assoc]
    rw [hfinal] at e
    convert e using 1 <;> simp [body, a0]
    omega

/-- Exact loading of an input field, including empty words and trailing zeros. -/
theorem runs (C : Ctx) (m : Fin MM) (len : Fin VV)
    (hlj : len ≠ vJ) (hlz : len ≠ vZ) (a : DS VV MM) (hz : a.env vZ = 0)
    (bits pre suffix : List Bool) (hin : C.inp = pre ++ frame bits ++ suffix)
    (hip : a.ip = pre.length) (hempty : a.ram m = []) (hcursor : a.rc m = 0)
    (hwidth : bits.length < 2 ^ C.Wd) :
    Ex C (script m len) a (loaded m len a (pre.length + (frame bits).length) 0 bits)
      (9 * bits.length + 6) := by
  have e0 := Ex.op (OpEx.zero (C := C) len a)
  let a0 := a.set len 0
  have e1 : Ex C (.op (.rdI vJ)) a0 (CountedParsing.readState vJ a0 (!bits.isEmpty)) 1 := by
    apply CountedParsing.read_bit C vJ a0 (!bits.isEmpty)
    · change a.ip < C.inp.length
      rw [hip, hin]
      simp only [List.length_append]
      have hp := Parsing.frame_nonempty bits
      omega
    · change C.inp.getD a.ip false = _
      rw [hip, hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      simpa using Parsing.frame_first bits suffix
  have hstart : CountedParsing.readState vJ a0 (!bits.isEmpty) =
      loaded m len a (pre.length + 1) (!bits.isEmpty).toNat [] := by
    apply state_ext
    · funext i
      by_cases hj : i = vJ
      · subst i; simp [CountedParsing.readState, loaded, DS.set]
      · by_cases hl : i = len
        · subst i; simp [CountedParsing.readState, a0, loaded, DS.set, hlj]
        · simp [CountedParsing.readState, a0, loaded, DS.set, hj, hl]
    · simp [CountedParsing.readState, a0, loaded, hip]
    · rfl
    · funext q
      by_cases hq : q = m
      · subst q; simp [CountedParsing.readState, a0, loaded, hempty]
      · simp [CountedParsing.readState, a0, loaded, hq]
    · funext q
      by_cases hq : q = m
      · subst q; simp [CountedParsing.readState, a0, loaded, hcursor]
      · simp [CountedParsing.readState, a0, loaded, hq]
    · rfl
    · rfl
    · rfl
  rw [hstart] at e1
  have el := loop_runs C m len hlj hlz a hz bits pre suffix [] hin (by simpa using hwidth)
  have he := Ex.seq e0 (Ex.seq e1 el)
  have hcost : 1 + (1 + (9 * bits.length + 2) + 1) + 1 = 9 * bits.length + 6 := by omega
  rw [hcost] at he
  simpa [script, frame_length, Nat.add_assoc] using he

/-- Preservation interface for a caller that later reads the stored bits. -/
theorem spec (C : Ctx) (m : Fin MM) (len : Fin VV)
    (hlj : len ≠ vJ) (hlc : len ∉ [vZ, v1, v2])
    (a : DS VV MM) (hc : Cst a) (bits pre suffix : List Bool)
    (hin : C.inp = pre ++ frame bits ++ suffix) (hip : a.ip = pre.length)
    (hempty : a.ram m = []) (hcursor : a.rc m = 0) (hwidth : bits.length < 2 ^ C.Wd) :
    Hs C (script m len) a (9 * bits.length + 6) (fun b =>
      b.ram m = bits.map Bool.toNat ∧ b.env len = bits.length ∧ b.rc m = bits.length ∧
      b.ip = pre.length + (frame bits).length ∧ Cst b ∧ b.out = a.out ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ q, q ≠ m → b.ram q = a.ram q ∧ b.rc q = a.rc q) ∧ Fr a b [vJ, len]) := by
  have hlz : len ≠ vZ := by intro he; apply hlc; simp [he]
  have hfr : Fr a (loaded m len a (pre.length + (frame bits).length) 0 bits) [vJ, len] := by
    intro i hi
    have hij : i ≠ vJ := by intro he; apply hi; simp [he]
    have hil : i ≠ len := by intro he; apply hi; simp [he]
    simp [loaded, hij, hil]
  refine ⟨_, _, runs C m len hlj hlz a hc.z bits pre suffix hin hip hempty hcursor hwidth, le_rfl,
    ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, hfr⟩
  · simp [loaded]
  · simp [loaded, hlj]
  · simp [loaded]
  · apply Cst.of_fr hc hfr
    refine ⟨?_, ?_, ?_⟩
    · simp [Ne.symm hlz, (by decide : vZ ≠ vJ)]
    · have h1 : v1 ≠ len := by intro he; apply hlc; simp [← he]
      simp [h1, (by decide : v1 ≠ vJ)]
    · have h2 : v2 ≠ len := by intro he; apply hlc; simp [← he]
      simp [h2, (by decide : v2 ≠ vJ)]
  · intro q hq
    simp [loaded, hq]

end NearCubicGates.Adapters.Code.InputBitLoading

