import SourceAdapters.Code.CellSending
import Proof.Gates.ENP.ListedFields

/-!
Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": actual ordinary cell program for the source's natural
fields, frame(Nat.bits). The zero natural has no payload bits. Each halving
iteration emits the exact marker/low-bit pair; cost is linear in bit length.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CellSending

variable {V M : ℕ}

def naturalFieldStep (R : Fin 5 ↪ Fin V) : St V M :=
  .seq (.op (.dm (R 2) (R 1) (R 3) (R 4)))
    (.seq (sendPayload (R 0) (R 4) false true) (.op (.half (R 2))))

def naturalFieldLoop (R : Fin 5 ↪ Fin V) : St V M :=
  .loop (.lt (R 0) (R 2)) (naturalFieldStep R)

def naturalField (R : Fin 5 ↪ Fin V) : St V M :=
  .seq (naturalFieldLoop R) (.op (.emit false))

def naturalFieldState (R : Fin 5 ↪ Fin V) (a : DS V M) (n : ℕ) : DS V M :=
  let b := if n = 0 then a else ((a.set (R 2) 0).set (R 3) 0).set (R 4) 1
  {b with out := a.out ++ Streaming.marks n.bits}

private theorem Rne (R : Fin 5 ↪ Fin V) {i j : Fin 5} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

theorem naturalFieldLoop_run (C : Ctx) (R : Fin 5 ↪ Fin V) (hW : 4 ≤ 2 ^ C.Wd) :
    ∀ (n : ℕ) (a : DS V M), a.env (R 0) = 0 → a.env (R 1) = 2 → a.env (R 2) = n →
      Ex C (naturalFieldLoop R) a (naturalFieldState R a n) (10 * n.bits.length + 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a hz ht hn
    by_cases hzero : n = 0
    · rw [hzero] at hn ⊢
      have h := Ex.loopF (C := C) (s := naturalFieldStep R)
        (c := Cnd.lt (R 0) (R 2)) (a := a) (Rne R (by decide))
        (by simp [Cnd.eval, hz, hn])
      simpa [naturalFieldLoop, naturalFieldState, Streaming.marks] using h
    · have hsmall : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by decide)
      let b := ((a.set (R 3) (n / 2)).set (R 4) (n % 2))
      have e1 : Ex C (.op (.dm (R 2) (R 1) (R 3) (R 4))) a b 1 := by
        simpa only [b, hn, ht] using Ex.op (OpEx.dm (R 2) (R 1) (R 3) (R 4) a
          (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide))
          (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (by omega) (by simpa [ht] using hW))
      have hb0 : b.env (R 0) = 0 := by simp [b, DS.set, Rne R, hz]
      have hbbit : b.env (R 4) = (decide (n % 2 = 1)).toNat := by
        simp only [b, DS.set_env_self]
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
      have e2 := send_payload C (R 0) (R 4) (Rne R (by decide)) false true b
        (decide (n % 2 = 1)) hb0 hbbit (by simp)
      let c := sent false b [true, decide (n % 2 = 1)]
      have hc2 : c.env (R 2) = n := by simp [c, b, DS.set, Rne R, hn]
      have e3 := Ex.op (OpEx.half (C := C) (R 2) c)
      rw [hc2] at e3
      let d := c.set (R 2) (n / 2)
      have ed : Ex C (naturalFieldStep R) a d 8 := by
        simpa only [naturalFieldStep, payload, payloadCost, ↓reduceIte] using Ex.seq e1 (Ex.seq e2 e3)
      have hd0 : d.env (R 0) = 0 := by simp [d, c, b, DS.set, Rne R, hz]
      have hd1 : d.env (R 1) = 2 := by simp [d, c, b, DS.set, Rne R, ht]
      have ei := ih (n / 2) hsmall d hd0 hd1 (by simp [d])
      have efinal : naturalFieldState R d (n / 2) = naturalFieldState R a n := by
        have hbits := NearCubicGates.Close.ENP.bits_eq_cons n hzero
        apply NearCubicGates.Adapters.Code.CountedParsing.state_ext
        · funext i
          by_cases hhalf : n / 2 = 0
          · have hn1 : n = 1 := by omega
            dsimp [naturalFieldState, d, c, b, sent, DS.set]
            norm_num [hn1]
            have h23 := Rne R (show (2 : Fin 5) ≠ 3 by decide)
            have h24 := Rne R (show (2 : Fin 5) ≠ 4 by decide)
            have h34 := Rne R (show (3 : Fin 5) ≠ 4 by decide)
            simp only [Function.update_apply]
            split_ifs <;> simp_all
          · simp [naturalFieldState, hhalf, hzero, d, c, b, sent, DS.set, Function.update_apply]
            split_ifs <;> simp_all [Rne R]
        · simp [naturalFieldState, hzero, d, c, b, sent, DS.set]
          split <;> rfl
        · simp [naturalFieldState, hzero, d, c, b, sent, Streaming.marks, hbits, List.append_assoc]
        · simp [naturalFieldState, hzero, d, c, b, sent, DS.set]
          split <;> rfl
        · simp [naturalFieldState, hzero, d, c, b, sent, DS.set]
          split <;> rfl
        · simp [naturalFieldState, hzero, d, c, b, sent, DS.set]
          split <;> rfl
        · simp [naturalFieldState, hzero, d, c, b, sent, DS.set]
          split <;> rfl
        · simp [naturalFieldState, hzero, d, c, b, sent, DS.set]
          split <;> rfl
      rw [efinal] at ei
      have hrun := Ex.loopT (c := Cnd.lt (R 0) (R 2)) (Rne R (by decide))
        (by simp [Cnd.eval, hz, hn, Nat.pos_of_ne_zero hzero]) ed ei
      have hlen : n.bits.length = (n / 2).bits.length + 1 := by
        rw [NearCubicGates.Close.ENP.bits_eq_cons n hzero, List.length_cons]
      convert hrun using 1 <;> first | rfl | omega

/-- Exact marked binary field, with every loop iteration charged. -/
theorem naturalField_run (C : Ctx) (R : Fin 5 ↪ Fin V) (hW : 4 ≤ 2 ^ C.Wd)
    (n : ℕ) (a : DS V M) (hz : a.env (R 0) = 0) (ht : a.env (R 1) = 2) (hn : a.env (R 2) = n) :
    Ex C (naturalField R) a
      {naturalFieldState R a n with out := a.out ++ frame n.bits} (10 * n.bits.length + 4) := by
  have e1 := naturalFieldLoop_run C R hW n a hz ht hn
  have e2 := Ex.op (OpEx.emit (C := C) false (naturalFieldState R a n))
  have hframe : Streaming.marks n.bits ++ [false] = frame n.bits := by
    simpa only [Streaming.frame_append, frame, List.append_nil] using (Streaming.frame_append n.bits []).symm
  simpa only [naturalField, naturalFieldState, List.append_assoc, hframe] using Ex.seq e1 e2

end NearCubicGates.Adapters.Proximity
