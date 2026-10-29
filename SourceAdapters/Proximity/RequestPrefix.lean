import SourceAdapters.Proximity.RequestWriting

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact dispatcher tags and repeatable circuit prefixes,
and natural request arguments copied from retained loop registers. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.RequestWriting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CountedParsing NearCubicGates.Adapters.Code.CellSending
variable {V M : ℕ}

def prefixRequest (R : Fin 5 ↪ Fin V) (tag : List Bool) : St V M :=
  .seq (callLiteral (R 2) tag) (copySource R)

def prefixResult (R : Fin 5 ↪ Fin V) (a : DS V M) (tag source : List Bool) : DS V M :=
  sent true ((a.set (R 2) 0).set (R 3) 0) (tag ++ source)

theorem prefix_request (C : Ctx) (R : Fin 5 ↪ Fin V) (a : DS V M) (tag source pre tail : List Bool)
    (hz : a.env (R 0) = 0) (ho : a.env (R 1) = 1) (hl : a.env (R 4) = source.length)
    (hin : C.inp = pre ++ source ++ tail) (hip : a.ip = pre.length)
    (hroom : a.kin.length + tag.length + source.length ≤ C.Lk) :
    Ex C (prefixRequest R tag) a (prefixResult R a tag source)
      (2 * tag.length + 15 * source.length + 13) := by
  have e1 := call_literal C (R 2) tag a (by omega)
  let b := sent true (a.set (R 2) 0) tag
  have e2 := copy_source C R b source pre tail
    (by simp [b, DS.set, hz]) (by simp [b, DS.set, ho]) (by simp [b, DS.set, hl]) hin
    (by simpa [b] using hip) (by simpa [b, sent] using hroom)
  have hf : sent true ((b.set (R 2) 0).set (R 3) 0) source = prefixResult R a tag source := by
    simp [prefixResult, b, sent, DS.set, List.append_assoc]
  rw [hf] at e2
  convert Ex.seq e1 e2 using 1 <;> first | rfl | omega

def appendNatural (R : Fin 5 ↪ Fin V) (source : Fin V) : St V M :=
  .seq (.op (.copy (R 2) source)) (naturalCallField R)

def appendNaturalResult (R : Fin 5 ↪ Fin V) (a : DS V M) (n : ℕ) : DS V M :=
  {naturalCallFieldState R (a.set (R 2) n) n with kin := a.kin ++ frame n.bits}

theorem append_natural (C : Ctx) (R : Fin 5 ↪ Fin V) (source : Fin V) (hne : R 2 ≠ source)
    (a : DS V M) (n : ℕ) (hz : a.env (R 0) = 0) (ht : a.env (R 1) = 2)
    (hn : a.env source = n) (hW : 4 ≤ 2 ^ C.Wd) (hroom : a.kin.length + (frame n.bits).length ≤ C.Lk) :
    Ex C (appendNatural R source) a (appendNaturalResult R a n) (10 * n.bits.length + 6) := by
  have e1 := Ex.op (OpEx.copy (C := C) (R 2) source a hne)
  rw [hn] at e1
  have e2 := naturalCallField_run C R hW n (a.set (R 2) n)
    (by simp [DS.set, hz]) (by simp [DS.set, ht]) (by simp) (by simpa using hroom)
  convert Ex.seq e1 e2 using 1 <;> first | rfl | omega

@[simp] theorem appendNaturalResult_env (R : Fin 5 ↪ Fin V) (a : DS V M) (n : ℕ) (x : Fin V)
    (h2 : x ≠ R 2) (h3 : x ≠ R 3) (h4 : x ≠ R 4) :
    (appendNaturalResult R a n).env x = a.env x := by
  unfold appendNaturalResult naturalCallFieldState
  split <;> simp [DS.set, h2, h3, h4]

@[simp] theorem appendNaturalResult_kin (R : Fin 5 ↪ Fin V) (a : DS V M) (n : ℕ) :
    (appendNaturalResult R a n).kin = a.kin ++ frame n.bits := rfl

end NearCubicGates.Adapters.Proximity.RequestWriting
