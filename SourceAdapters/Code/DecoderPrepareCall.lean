import SourceAdapters.Code.DecoderRequest

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": one complete paid zero-message length query and source
decoder-request serialization, retaining the received input cursor. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderPrepareCall

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells

abbrev State := DS 12 0
abbrev Script := St 12 0

def script (size : Fin 12) : Script := .seq (LengthCall.script size) (DecoderRequest.script size)

def result (a : State) (output : List Bool) (pos n : ℕ) (bits : List Bool) : State :=
  DecoderRequest.result (LengthCall.result a output) pos n bits

theorem runs (C : Ctx) (size : Fin 12) (hs9 : size ≠ 9) (hs1 : size ≠ 1) (hs11 : size ≠ 11)
    (request : C.K.Req) (n : ℕ) (output bits pre tail suffix : List Bool) (a : State)
    (hz : a.env 0 = 0) (ho : a.env 10 = 1) (hlen : a.env size = n) (hki : a.kin = [])
    (hword : C.K.inw request = List.replicate n false) (hout : C.K.outw request = frame output)
    (hsize : output.length = bits.length) (hroom : n ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk)
    (hcap : output.length + 2 * n < 2 ^ C.Wd)
    (hin : C.inp = pre ++ frame (bits ++ tail) ++ suffix) (hip : a.ip = pre.length) :
    Ex C (script size) a (result a output (pre.length + 2 * bits.length) n bits)
      (22 * n + 21 * bits.length + C.Lk + C.Bk + 38) := by
  have e1 := LengthCall.runs C size hs9 request n output a hz ho hlen hki hword hout hroom hbudget (by omega)
  let b := LengthCall.result a output
  have e2 := DecoderRequest.runs C size hs9 n bits pre tail suffix b
    (by simp [b, LengthCall.result, DS.set, hz])
    (by simp [b, LengthCall.result, DS.set, ho])
    (by simp [b, LengthCall.result, DS.set])
    (by simp [b, LengthCall.result, DS.set, hs9, hs1, hs11, hlen])
    (by simp [b, LengthCall.result, DS.set, hsize]) hin
    (by simp [b, LengthCall.result, hip]) (by omega)
  exact (Ex.seq e1 e2).mono (by rw [hsize]; omega)

end NearCubicGates.Adapters.Code.DecoderPrepareCall
