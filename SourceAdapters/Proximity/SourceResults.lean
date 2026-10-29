import SourceAdapters.Proximity.SourceRequests
import SourceAdapters.Proximity.CallReading

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact source results in the constructor register bank.
Calls preserve the circuit cursor, record stores, accumulated output and loop
parameters outside the explicitly listed scratch registers. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceResults

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open FrameReading

def resultReg : Fin VV := 27
def powerReg : Fin VV := 28
def tagReg : Fin VV := 26
def readRegs : Fin 4 ↪ Fin VV := ⟨![vZ, t0, resultReg, powerReg], by decide⟩
def scratch : List (Fin VV) := SourceRequests.scratch ++ [resultReg, powerReg, tagReg]

def rest (a : State) := (a.ip, a.out, a.ram, a.rc)

structure Returned (a b : State) : Prop where
  rest_eq : rest b = rest a
  kin_nil : b.kin = []
  vars : Fr a b scratch

theorem Returned.constants {a b : State} (h : Returned a b) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

theorem Returned.after_request {a b c : State} {word : List Bool}
    (h : SourceRequests.Requested a b word) (h' : Returned b c) : Returned a c := by
  have hh := h.rest_eq
  simp only [SourceRequests.rest, Prod.mk.injEq] at hh
  exact ⟨h'.rest_eq.trans (by simp [rest, hh]), h'.kin_nil,
    Fr.trans (h.vars.weaken (fun _ hm => List.mem_append_left _ hm)) h'.vars⟩

def scalarCall : Script := callNatural readRegs

theorem scalar_call (C : Ctx) (request : C.K.Req) (n : ℕ) (a : State) (hc : Cst a)
    (hin : a.kin = C.K.inw request) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = frame n.bits) (hW : n.bits.length + 1 ≤ C.Wd) :
    Hs C scalarCall a (C.Lk + C.Bk + 10 * n.bits.length + 12)
      (fun b => Returned a b ∧ b.env resultReg = n) := by
  have e := call_natural C readRegs a request n hc.z hin hbudget hout hW
  refine ⟨_, _, e, le_rfl, ⟨⟨rfl, rfl, ?_⟩, by simp [finish, position, readRegs, resultReg, powerReg]⟩⟩
  intro x hx
  have h0 : x ≠ t0 := fun he => hx (by simp [scratch, SourceRequests.scratch, he])
  have hr : x ≠ resultReg := fun he => hx (by simp [scratch, he])
  have hp : x ≠ powerReg := fun he => hx (by simp [scratch, he])
  simp [finish, position, readRegs, DS.called, DS.set, h0, hr, hp]

def addressCall : Script := callTaggedNatural readRegs tagReg

theorem address_call (C : Ctx) (request : C.K.Req) (tag : Bool) (n : ℕ) (a : State) (hc : Cst a)
    (hin : a.kin = C.K.inw request) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = tag :: frame n.bits) (hW : n.bits.length + 1 ≤ C.Wd) :
    Hs C addressCall a (C.Lk + C.Bk + 10 * n.bits.length + 14)
      (fun b => Returned a b ∧ b.env resultReg = n ∧ b.env tagReg = tag.toNat) := by
  have e := call_tagged_natural C readRegs tagReg (by decide) a request tag n hc.z hin hbudget hout hW
  refine ⟨_, _, e, le_rfl, ⟨⟨rfl, rfl, ?_⟩, ?_, ?_⟩⟩
  · intro x hx
    have h0 : x ≠ t0 := fun he => hx (by simp [scratch, SourceRequests.scratch, he])
    have hr : x ≠ resultReg := fun he => hx (by simp [scratch, he])
    have hp : x ≠ powerReg := fun he => hx (by simp [scratch, he])
    have ht : x ≠ tagReg := fun he => hx (by simp [scratch, he])
    simp [finish, readState, position, readRegs, DS.called, DS.set, h0, hr, hp, ht]
  · simp [finish, position, readRegs, resultReg, powerReg]
  · change (((((a.called (tag :: frame n.bits)).set tagReg tag.toNat).set t0 0).set resultReg n).set
      powerReg (2 ^ n.bits.length)).env tagReg = tag.toNat
    rw [DS.set_env_ne _ _ (by decide : tagReg ≠ powerReg),
      DS.set_env_ne _ _ (by decide : tagReg ≠ resultReg),
      DS.set_env_ne _ _ (by decide : tagReg ≠ t0), DS.set_env_self]

def booleanCall : Script := callBit resultReg

theorem boolean_call (C : Ctx) (request : C.K.Req) (bit : Bool) (a : State)
    (hin : a.kin = C.K.inw request) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = [bit]) :
    Hs C booleanCall a (C.Lk + C.Bk + 3)
      (fun b => Returned a b ∧ b.env resultReg = bit.toNat) := by
  have e := call_bit C resultReg a request bit hin hbudget hout
  refine ⟨_, _, e, le_rfl, ⟨⟨rfl, rfl, ?_⟩, by simp [readState]⟩⟩
  intro x hx
  have hr : x ≠ resultReg := fun he => hx (by simp [scratch, he])
  simp [readState, position, DS.called, DS.set, hr]

end NearCubicGates.Adapters.Proximity.SourceResults
