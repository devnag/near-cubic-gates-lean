import SourceAdapters.Proximity.SourceRequests

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": a fixed q-bit assignment is restricted to the source's
actual query count by paid guarded emissions. No extra answer is supplied to
the source's dependent decision-request domain. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecisionSending

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CellSending
open NearCubicGates.Adapters.Code.CountedParsing (state_ext)
open SourceRequests (State Script)

def remaining : Fin VV := 30

def sendPrefix : List Bool → Script
  | [] => .op (.zero t0)
  | bit :: bits => .ite (.lt vZ remaining)
      (.seq (.op (.kem bit)) (.seq (.op (.sub remaining v1)) (sendPrefix bits))) (.op (.zero t0))

def sentPrefix (a : State) (bits : List Bool) (n : ℕ) : State :=
  sent true ((a.set remaining (n - bits.length)).set t0 0) (bits.take n)

theorem send_prefix (C : Ctx) : ∀ (bits : List Bool) (a : State) (n : ℕ),
    Cst a → a.env remaining = n → a.kin.length + (bits.take n).length ≤ C.Lk →
    Ex C (sendPrefix bits) a (sentPrefix a bits n) (6 * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro a n _ hn _
    have hs : sentPrefix a [] n = a.set t0 0 := by
      simp only [sentPrefix, List.length_nil, Nat.sub_zero, List.take_nil, sent, ↓reduceIte,
        List.append_nil, DS.set]
      rw [← hn, Function.update_eq_self]
    rw [hs]
    exact (Ex.op (OpEx.zero (C := C) t0 a)).mono (by simp)
  | cons bit bits ih =>
    intro a n hc hn hroom
    cases n with
    | zero =>
      have hs : sentPrefix a (bit :: bits) 0 = a.set t0 0 := by
        simp only [sentPrefix, Nat.zero_sub, List.take_zero, sent, ↓reduceIte, List.append_nil, DS.set]
        rw [← hn, Function.update_eq_self]
      rw [hs]
      have e := Ex.iteF (c := Cnd.lt vZ remaining) (s := .seq (.op (.kem bit))
          (.seq (.op (.sub remaining v1)) (sendPrefix bits))) (by decide : vZ ≠ remaining)
        (by simp [Cnd.eval, hc.z, hn]) (Ex.op (OpEx.zero (C := C) t0 a))
      exact e.mono (by omega)
    | succ n =>
      have e1 := Ex.op (OpEx.kem (C := C) bit a (by simp only [List.take_succ_cons, List.length_cons] at hroom; omega))
      let b := sent true a [bit]
      have hb1 : b.env v1 = 1 := hc.one
      have hbn : b.env remaining = n + 1 := hn
      have e2 := Ex.op (OpEx.sub (C := C) remaining v1 b (by decide) (by rw [hb1, hbn]; omega))
      rw [hb1, hbn, Nat.add_sub_cancel] at e2
      let d := b.set remaining n
      have hd : Cst d := by
        refine ⟨?_, ?_, ?_⟩
        · rw [DS.set_env_ne _ _ (by decide : vZ ≠ remaining)]; exact hc.z
        · rw [DS.set_env_ne _ _ (by decide : v1 ≠ remaining)]; exact hc.one
        · rw [DS.set_env_ne _ _ (by decide : v2 ≠ remaining)]; exact hc.two
      have e3 := ih d n hd (by simp [d]) (by
        simp only [d, DS.set_kin, b, sent_kin, List.length_append, List.length_singleton]
        simp only [List.take_succ_cons, List.length_cons] at hroom
        omega)
      have hs : sentPrefix d bits n = sentPrefix a (bit :: bits) (n + 1) := by
        simp [sentPrefix, d, b, sent, DS.set, List.take_succ_cons, List.append_assoc]
      rw [hs] at e3
      have e := Ex.iteT (c := Cnd.lt vZ remaining) (t := .op (.zero t0)) (by decide : vZ ≠ remaining)
        (by simp [Cnd.eval, hc.z, hn]) (Ex.seq e1 (Ex.seq e2 e3))
      exact e.mono (by simp; omega)

end NearCubicGates.Adapters.Proximity.DecisionSending
