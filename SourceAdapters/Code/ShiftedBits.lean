import SourceAdapters.Code.ShiftedBitsStep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid shifted bit-word preparation. A distinct outer index
survives every guarded lookup, whose internal scan uses c0. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.ShiftedBits

open NearCubicGates.Close.Cells

def shifted (bits : List Bool) (offset count : ℕ) : List Bool :=
  (List.range count).map (fun i => bits.getD (offset + i) false)

@[simp] theorem shifted_length (bits : List Bool) (offset count : ℕ) :
    (shifted bits offset count).length = count := by simp [shifted]

theorem shifted_succ (bits : List Bool) (offset count : ℕ) :
    shifted bits offset (count + 1) = shifted bits offset count ++ [bits.getD (offset + count) false] := by
  simp [shifted, List.range_succ]

def script (source destination : Fin MM) (len offset count index address result : Fin VV) : St VV MM :=
  forS index count (step source destination len offset index address result)

/-- Append an exact shifted word, defaulting false beyond the source length.
The offset never controls an iteration count or a cursor movement. -/
theorem runs (C : Ctx) (source destination : Fin MM) (hsd : source ≠ destination)
    (len offset count index address result : Fin VV)
    (hl : len ∉ [index, c0, vJ, address, result])
    (ho : offset ∉ [index, c0, vJ, address, result])
    (hn : count ∉ [index, c0, vJ, address, result])
    (hi : index ∉ [c0, vJ, address, result]) (ha : address ∉ [c0, vJ, result])
    (hcst : vZ ∉ [index, c0, vJ, address, result] ∧ v1 ∉ [index, c0, vJ, address, result] ∧
      v2 ∉ [index, c0, vJ, address, result])
    (a : DS VV MM) (hc : Cst a) (bits previous : List Bool)
    (hbits : a.ram source = bits.map Bool.toNat)
    (hprevious : a.ram destination = previous.map Bool.toNat)
    (hlen : a.env len = bits.length) (hsource : a.rc source ≤ bits.length)
    (hdestination : a.rc destination = previous.length)
    (hwidth : bits.length < 2 ^ C.Wd) (hcount : a.env count < 2 ^ C.Wd)
    (hadd : a.env offset + a.env count < 2 ^ C.Wd) :
    Hs C (script source destination len offset count index address result) a
      (a.env count * (6 * bits.length + 20) + 4) (fun b =>
      b.ram destination = (previous ++ shifted bits (a.env offset) (a.env count)).map Bool.toNat ∧
      b.rc destination = previous.length + a.env count ∧ b.rc source ≤ bits.length ∧
      (∀ q, q ≠ destination → b.ram q = a.ram q) ∧
      (∀ q, q ≠ source → q ≠ destination → b.rc q = a.rc q) ∧
      b.env len = bits.length ∧ b.env offset = a.env offset ∧ b.env count = a.env count ∧
      b.env index = a.env count ∧ Cst b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      Fr a b [index, c0, vJ, address, result]) := by
  have hni : count ≠ index := by intro h; apply hn; simp [h]
  have sub : [c0, vJ, address, result] ⊆ [index, c0, vJ, address, result] :=
    fun _ h => List.mem_cons_of_mem index h
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ram = Function.update a.ram destination ((previous ++ shifted bits (a.env offset) k).map Bool.toNat) ∧
    b.rc destination = previous.length + k ∧ b.rc source ≤ bits.length ∧
    (∀ q, q ≠ source → q ≠ destination → b.rc q = a.rc q) ∧
    b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
    Fr a b [index, c0, vJ, address, result]
  have initial : I 0 a := by
    refine ⟨?_, by simpa using hdestination, hsource, fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
    funext q
    by_cases hq : q = destination
    · subst q; simpa [shifted] using hprevious
    · simp [hq]
  have loopRun := forS_spec' (C := C) index count hni.symm
    (step source destination len offset index address result) a (a.env count) hcount I
    (6 * bits.length + 16)
    (fun k b v ⟨bm, bd, bs, br, bi, bo, bki, bko, bkc, bf⟩ =>
      ⟨bm, bd, bs, br, bi, bo, bki, bko, bkc, bf.trans (Fr.set b v (by simp))⟩)
    initial rfl ?_
  · refine Hs.mono loopRun (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _) ?_
    rintro b ⟨⟨bm, bd, bs, br, bi, bo, bki, bko, bkc, bf⟩, bindex, bcount⟩
    refine ⟨?_, bd, bs, ?_, br, (bf len hl).trans hlen, bf offset ho, bcount, bindex,
      Cst.of_fr hc bf hcst, bi, bo, bki, bko, bkc, bf⟩
    · rw [bm, Function.update_self]
    · intro q hq
      rw [bm, Function.update_of_ne hq]
  · intro k hk b ⟨bm, bd, bs, br, bi, bo, bki, bko, bkc, bf⟩ bindex bcount
    have bodyRun := step_runs C source destination hsd len offset index address result
      (fun h => hl (sub h)) (fun h => ho (sub h)) hi ha
      ⟨fun h => hcst.1 (sub h), fun h => hcst.2.1 (sub h), fun h => hcst.2.2 (sub h)⟩
      b (Cst.of_fr hc bf hcst) bits (previous ++ shifted bits (a.env offset) k)
      (by rw [bm, Function.update_of_ne hsd]; exact hbits)
      (by rw [bm, Function.update_self]) ((bf len hl).trans hlen) bs
      (by simpa using bd) hwidth (by rw [bf offset ho, bindex]; omega)
    refine Hs.mono bodyRun le_rfl ?_
    rintro d ⟨dm, dd, ds, dmr, dcr, di, dout, dki, dko, dkc, df⟩
    have af : Fr a d [index, c0, vJ, address, result] := bf.trans (df.weaken sub)
    refine ⟨⟨?_, ?_, ds, ?_, di.trans bi, dout.trans bo, dki.trans bki, dko.trans bko,
      dkc.trans bkc, af⟩, (df index hi).trans bindex, (df count (fun h => hn (sub h))).trans bcount⟩
    · funext q
      by_cases hq : q = destination
      · subst q
        rw [Function.update_self, dm, bf offset ho, bindex, shifted_succ]
        simp only [List.append_assoc]
      · rw [dmr q hq, bm, Function.update_of_ne hq, Function.update_of_ne hq]
    · simpa [Nat.add_assoc] using dd
    · intro q hqs hqd
      exact (dcr q hqs hqd).trans (br q hqs hqd)

end NearCubicGates.Adapters.Code.ShiftedBits
