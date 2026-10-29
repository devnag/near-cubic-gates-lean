import SourceAdapters.Proximity.DescriptorParsing
import Proof.Gates.Cells.Idx

/-! Q04: reading and printing one node from the paid native-field store. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def stored (a : State) (x : Fin VV) (v : ℕ) : State := (a.set x v).adv sN

theorem read_stored (C : Ctx) (x : Fin VV) (v : ℕ) (tail : List ℕ) (a : State)
    (hin : (a.ram sN).drop (a.rc sN) = v :: tail) :
    Ex C (.op (.rdM sN x)) a (stored a x v) 1 := by
  have hl := congrArg List.length hin
  simp only [List.length_drop, List.length_cons] at hl
  have hv := fld_of_drop hin
  unfold fld at hv
  have he := Ex.op (OpEx.rdM (C := C) sN x a (by omega))
  simpa only [hv, stored] using he

theorem stored_tail (a : State) (x : Fin VV) (v : ℕ) (tail : List ℕ)
    (hin : (a.ram sN).drop (a.rc sN) = v :: tail) :
    ((stored a x v).ram sN).drop ((stored a x v).rc sN) = tail := by
  simp only [stored, DS.adv, DS.set_ram, DS.set_rc, Function.update_self]
  rw [← List.drop_drop, hin]
  rfl

def readNode : Script := .seq (.op (.rdM sN tagReg))
  (.seq (.op (.rdM sN leftReg)) (.op (.rdM sN rightReg)))

def readNodeState (a : State) {n : ℕ} (node : BooleanNode n) : State :=
  stored (stored (stored a tagReg (PCPPRequestNodeSchema.fields node 0))
    leftReg (PCPPRequestNodeSchema.fields node 1)) rightReg (PCPPRequestNodeSchema.fields node 2)

theorem read_node (C : Ctx) {n : ℕ} (node : BooleanNode n) (tail : List ℕ) (a : State)
    (hin : (a.ram sN).drop (a.rc sN) = nodeFields node ++ tail) :
    Ex C readNode a (readNodeState a node) 5 := by
  have e1 := read_stored C tagReg _ _ a hin
  have h1 := stored_tail a tagReg _ _ hin
  have e2 := read_stored C leftReg _ _ _ h1
  have h2 := stored_tail _ leftReg _ _ h1
  have e3 := read_stored C rightReg _ _ _ h2
  exact Ex.seq e1 (Ex.seq e2 e3)

def writeStoredNode : Script := .seq readNode writeNode

def nodeScratch : List (Fin VV) := [tagReg, leftReg, rightReg] ++ scratch

structure StoredPrinted (a b : State) (word : List Bool) (count : ℕ) : Prop where
  other : (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc)
  cursor : b.rc = Function.update a.rc sN (a.rc sN + count)
  out_eq : b.out = a.out ++ word
  vars : Fr a b nodeScratch

theorem StoredPrinted.constants {a b : State} {word : List Bool} {count : ℕ}
    (h : StoredPrinted a b word count) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

theorem write_stored_node (C : Ctx) {n : ℕ} (node : BooleanNode n) (tail : List ℕ)
    (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ C.Wd) (h3 : a.env threeReg = 3)
    (hin : (a.ram sN).drop (a.rc sN) = nodeFields node ++ tail) :
    Hs C writeStoredNode a
      (10 * (PCPPRequestNodeSchema.fields node 1).bits.length +
        10 * (PCPPRequestNodeSchema.fields node 2).bits.length + 46)
      (fun b => StoredPrinted a b (sourceNodeWord node) 3) := by
  have er := read_node C node tail a hin
  let d := readNodeState a node
  have hd : Cst d := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [d, readNodeState, stored, DS.adv, DS.set, tagReg, leftReg, rightReg, vZ, v1, v2]
    · exact hc.z
    · exact hc.one
    · exact hc.two
  have hp := write_node C node d hd hW
    (by simp [d, readNodeState, stored, DS.adv, DS.set, tagReg, leftReg, rightReg])
    (by simp [d, readNodeState, stored, DS.adv, DS.set, leftReg, rightReg])
    (by simp [d, readNodeState, stored, DS.adv, DS.set])
    (by simpa [d, readNodeState, stored, DS.adv, DS.set, tagReg, leftReg, rightReg, threeReg] using h3)
  obtain ⟨b, cost, he, hcost, hb⟩ := hp
  refine ⟨b, 5 + cost + 1, Ex.seq er he, by omega, ?_⟩
  have hr := hb.rest_eq
  simp only [rest, Prod.mk.injEq] at hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
    rfl
  · rw [hr.2.2.1]
    simp [d, readNodeState, stored, DS.adv, DS.set, Function.update_idem, Nat.add_assoc]
  · simpa only [d, readNodeState, stored, DS.adv, DS.set_out] using hb.out_eq
  · have hdfr : Fr a d nodeScratch := by
      intro y hy
      simp only [nodeScratch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [d, readNodeState, stored, DS.adv, DS.set, hy.1.1, hy.1.2.1, hy.1.2.2]
    exact Fr.trans hdfr (hb.vars.weaken (fun y hy => List.mem_append_right _ hy))

end NearCubicGates.Adapters.Proximity.SourcePrinting
