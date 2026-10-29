import SourceAdapters.Proximity.BinaryField

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": charged calls followed by exact output parsing.
The callee in the context carries its actual ordinary WordFunction. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.FrameReading

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
variable {V M : ℕ}

def callNatural (R : Fin 4 ↪ Fin V) : St V M :=
  .seq (.op .kcall) (readBinary true R)

theorem call_natural (C : Ctx) (R : Fin 4 ↪ Fin V) (a : DS V M) (request : C.K.Req) (n : ℕ)
    (hz : a.env (R 0) = 0) (hin : a.kin = C.K.inw request) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = frame n.bits) (hW : n.bits.length + 1 ≤ C.Wd) :
    Ex C (callNatural R) a
      (finish true R (a.called (frame n.bits)) (2 * n.bits.length + 1) n (2 ^ n.bits.length))
      (C.Lk + C.Bk + 10 * n.bits.length + 12) := by
  have e1 := Ex.op (OpEx.kcall request a hin hbudget)
  rw [hout] at e1
  have e2 := read_natural C true R (a.called (frame n.bits)) n [] []
    (by simpa [DS.called] using hz) (by simp [word, DS.called]) (by simp [pos, DS.called]) hW
  simp only [List.length_nil, Nat.zero_add] at e2
  convert Ex.seq e1 e2 using 1 <;> first | rfl | omega

def readTaggedNatural (call : Bool) (R : Fin 4 ↪ Fin V) (tag : Fin V) : St V M :=
  .seq (.op (readOp call tag)) (readBinary call R)

theorem read_tagged_natural (C : Ctx) (call : Bool) (R : Fin 4 ↪ Fin V) (tag : Fin V)
    (hne : R 0 ≠ tag) (a : DS V M) (b : Bool) (n : ℕ) (pre tail : List Bool)
    (hz : a.env (R 0) = 0) (hin : word C call a = pre ++ b :: (frame n.bits ++ tail))
    (hip : pos call a = pre.length) (hW : n.bits.length + 1 ≤ C.Wd) :
    Ex C (readTaggedNatural call R tag) a
      (finish call R (readState call tag a b) (pre.length + 2 * n.bits.length + 2) n (2 ^ n.bits.length))
      (10 * n.bits.length + 12) := by
  have e1 := read_prefix C call tag a pre b (frame n.bits ++ tail) hin hip
  have e2 := read_natural C call R (readState call tag a b) n (pre ++ [b]) tail
    (by simp [readState, DS.set, hne, hz])
    (by simpa [readState, List.append_assoc] using hin)
    (by simp [readState, hip]) hW
  have hcursor : (pre ++ [b]).length + 2 * n.bits.length + 1 = pre.length + 2 * n.bits.length + 2 := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [hcursor] at e2
  convert Ex.seq e1 e2 using 1 <;> first | rfl | omega

def callTaggedNatural (R : Fin 4 ↪ Fin V) (tag : Fin V) : St V M :=
  .seq (.op .kcall) (readTaggedNatural true R tag)

theorem call_tagged_natural (C : Ctx) (R : Fin 4 ↪ Fin V) (tag : Fin V)
    (hne : R 0 ≠ tag) (a : DS V M) (request : C.K.Req) (b : Bool) (n : ℕ)
    (hz : a.env (R 0) = 0) (hin : a.kin = C.K.inw request) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = b :: frame n.bits) (hW : n.bits.length + 1 ≤ C.Wd) :
    Ex C (callTaggedNatural R tag) a
      (finish true R (readState true tag (a.called (b :: frame n.bits)) b)
        (2 * n.bits.length + 2) n (2 ^ n.bits.length))
      (C.Lk + C.Bk + 10 * n.bits.length + 14) := by
  have e1 := Ex.op (OpEx.kcall request a hin hbudget)
  rw [hout] at e1
  have e2 := read_tagged_natural C true R tag hne (a.called (b :: frame n.bits)) b n [] []
    (by simpa [DS.called] using hz) (by simp [word, DS.called]) (by simp [pos, DS.called]) hW
  simp only [List.length_nil, Nat.zero_add] at e2
  convert Ex.seq e1 e2 using 1 <;> first | rfl | omega

def callBit (bit : Fin V) : St V M := .seq (.op .kcall) (.op (.rdK bit))

theorem call_bit (C : Ctx) (bit : Fin V) (a : DS V M) (request : C.K.Req) (b : Bool)
    (hin : a.kin = C.K.inw request) (hbudget : C.K.bud request ≤ C.Bk) (hout : C.K.outw request = [b]) :
    Ex C (callBit bit) a (readState true bit (a.called [b]) b) (C.Lk + C.Bk + 3) := by
  have e1 := Ex.op (OpEx.kcall request a hin hbudget)
  rw [hout] at e1
  have e2 := read_prefix C true bit (a.called [b]) [] b []
    (by simp [word, DS.called]) (by simp [pos, DS.called])
  convert Ex.seq e1 e2 using 1 <;> first | rfl | omega

end NearCubicGates.Adapters.Proximity.FrameReading
