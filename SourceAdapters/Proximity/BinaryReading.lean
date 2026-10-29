import SourceAdapters.Proximity.ReadChannels

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": actual low-bit-first framed natural parsing.
The loop works on arbitrary finite bit words, including empty and trailing-zero
words, and records both the exact value and the next binary weight. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.FrameReading

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CountedParsing (state_ext)
open RadixSemantics (value)
variable {V M : ℕ}

private theorem Rne (R : Fin 4 ↪ Fin V) {i j : Fin 4} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

def finish (call : Bool) (R : Fin 4 ↪ Fin V) (a : DS V M) (cursor v p : ℕ) : DS V M :=
  position call (((a.set (R 1) 0).set (R 2) v).set (R 3) p) cursor

def binaryStep (call : Bool) (R : Fin 4 ↪ Fin V) : St V M :=
  .seq (.op (readOp call (R 1)))
    (.seq (.ite (.eq (R 0) (R 1)) (.op (.zero (R 1))) (.op (.add (R 2) (R 3))))
      (.seq (.op (.shl (R 3))) (.op (readOp call (R 1)))))

def binaryLoop (call : Bool) (R : Fin 4 ↪ Fin V) : St V M :=
  .loop (.lt (R 0) (R 1)) (binaryStep call R)

theorem binary_loop (C : Ctx) (call : Bool) (R : Fin 4 ↪ Fin V) :
    ∀ (bits pre tail : List Bool) (a : DS V M) (v p : ℕ),
      word C call a = pre ++ frame bits ++ tail → pos call a = pre.length + 1 →
      a.env (R 0) = 0 → a.env (R 1) = (!bits.isEmpty).toNat → a.env (R 2) = v → a.env (R 3) = p →
      v + p * value bits < 2 ^ C.Wd → p * 2 ^ bits.length < 2 ^ C.Wd →
      Ex C (binaryLoop call R) a
        (finish call R a (pre.length + 2 * bits.length + 1)
          (v + p * value bits) (p * 2 ^ bits.length)) (10 * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre tail a v p _ hip hz hf hv hp _ _
    have hflag : a.env (R 1) = 0 := by simpa using hf
    have hfinal : finish call R a (pre.length + 1) v p = a := by
      cases call <;> apply state_ext
      all_goals try rfl
      all_goals try (simpa [finish, position, pos] using hip.symm)
      all_goals
        funext i
        by_cases h3 : i = R 3
        · subst i; simp [finish, position, DS.set, hp]
        · by_cases h2 : i = R 2
          · subst i; simp [finish, position, DS.set, hv]
          · by_cases h1 : i = R 1
            · subst i; simp [finish, position, DS.set, hflag]
            · simp [finish, position, DS.set, h1, h2, h3]
    simpa only [binaryLoop, List.length_nil, value, Nat.mul_zero, Nat.add_zero, pow_zero, Nat.mul_one, hfinal]
      using Ex.loopF (C := C) (c := Cnd.lt (R 0) (R 1)) (s := binaryStep call R) (a := a)
        (Rne R (by decide)) (by simp [Cnd.eval, hz, hflag])
  | cons bit bits ih =>
    intro pre tail a v p hin hip hz hf hv hp hvalue hpower
    have hflag : a.env (R 1) = 1 := by simpa using hf
    have hsum (hb : bit = true) : v + p < 2 ^ C.Wd := by
      subst bit
      simp only [value, Bool.toNat_true] at hvalue
      nlinarith
    have hin0 : word C call a = (pre ++ [true]) ++ bit :: (frame bits ++ tail) := by
      simpa [frame, List.append_assoc] using hin
    have e1 := read_prefix C call (R 1) a (pre ++ [true]) bit (frame bits ++ tail) hin0 (by simp; omega)
    let d := readState call (R 1) a bit
    have hd0 : d.env (R 0) = 0 := by simp [d, readState, DS.set, hz]
    have hd1 : d.env (R 1) = bit.toNat := by simp [d, readState]
    have hd2 : d.env (R 2) = v := by simp [d, readState, DS.set, hv]
    have hd3 : d.env (R 3) = p := by simp [d, readState, DS.set, hp]
    let e := d.set (R 2) (v + bit.toNat * p)
    have e2 : Ex C (.ite (.eq (R 0) (R 1)) (.op (.zero (R 1))) (.op (.add (R 2) (R 3)))) d e 2 := by
      cases bit
      · have he : d.set (R 1) 0 = e := by
          apply state_ext <;> try rfl
          funext i
          by_cases h1 : i = R 1
          · subst i; simp [e, DS.set, hd1]
          · by_cases h2 : i = R 2
            · subst i; simp [e, DS.set, hd2]
            · simp [e, DS.set, h1, h2]
        rw [← he]
        exact Ex.iteT (Rne R (by decide)) (by simp [Cnd.eval, hd0, hd1]) (Ex.op (OpEx.zero (R 1) d))
      · simpa only [e, Bool.toNat_true, Nat.one_mul, hd2, hd3] using
          Ex.iteF (c := Cnd.eq (R 0) (R 1)) (Rne R (by decide))
            (by simp [Cnd.eval, hd0, hd1])
            (Ex.op (OpEx.add (C := C) (R 2) (R 3) d (Rne R (by decide)) (by rw [hd2, hd3]; exact hsum rfl)))
    have hep : e.env (R 3) = p := by simp [e, DS.set, hd3]
    have hdouble : 2 * p < 2 ^ C.Wd := by
      simp only [List.length_cons, pow_succ] at hpower
      have hh := Nat.one_le_pow bits.length 2 (by decide)
      nlinarith
    have e3 := Ex.op (OpEx.shl (C := C) (R 3) e (by rw [hep]; exact hdouble))
    rw [hep] at e3
    let f := e.set (R 3) (2 * p)
    let pre' := pre ++ [true, bit]
    have hfin : word C call f = pre' ++ frame bits ++ tail := by
      simp only [f, e, d, readState, word_set, word_position]
      simpa [pre', frame, List.append_assoc] using hin
    have hfpos : pos call f = pre'.length := by simp [f, e, d, readState, pre', hip]
    have e4 := read_frame_flag C call (R 1) f pre' bits tail hfin hfpos
    let g := readState call (R 1) f (!bits.isEmpty)
    have hg0 : g.env (R 0) = 0 := by simp [g, f, e, d, readState, DS.set, hz]
    have hg1 : g.env (R 1) = (!bits.isEmpty).toNat := by simp [g, readState]
    have hg2 : g.env (R 2) = v + bit.toNat * p := by simp [g, f, e, readState, DS.set]
    have hg3 : g.env (R 3) = 2 * p := by simp [g, f, readState, DS.set]
    have ei := ih pre' tail g (v + bit.toNat * p) (2 * p)
      (by simpa [g, readState] using hfin) (by simp [g, readState, hfpos]) hg0 hg1 hg2 hg3
      (by simp only [value] at hvalue; nlinarith)
      (by simp only [List.length_cons, pow_succ] at hpower; nlinarith)
    have hfinal : finish call R g (pre'.length + 2 * bits.length + 1)
        (v + bit.toNat * p + 2 * p * value bits) (2 * p * 2 ^ bits.length) =
      finish call R a (pre.length + 2 * (bit :: bits).length + 1)
        (v + p * value (bit :: bits)) (p * 2 ^ (bit :: bits).length) := by
      cases call <;> apply state_ext
      all_goals simp [finish, g, f, e, d, readState, position, pos, DS.set, pre', value, pow_succ]
      all_goals try omega
      all_goals
        funext i
        simp only [Function.update_apply]
        split_ifs <;> ring
    rw [hfinal] at ei
    have eb := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))
    have er := Ex.loopT (c := Cnd.lt (R 0) (R 1)) (Rne R (by decide))
      (by simp [Cnd.eval, hz, hflag]) eb ei
    convert er using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

end NearCubicGates.Adapters.Proximity.FrameReading
