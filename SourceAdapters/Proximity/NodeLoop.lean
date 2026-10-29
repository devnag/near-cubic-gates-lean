import SourceAdapters.Proximity.NodeStore

/-! Q04: a paid loop printing the complete native node store in source format. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def loopReg : Fin VV := 34
def nodeCountReg : Fin VV := 35

def loopScratch : List (Fin VV) := loopReg :: nodeScratch

def writeStoredNodes : Script := forS loopReg nodeCountReg writeStoredNode

structure NodesPrinted (a b : State) (word : List Bool) (count : ℕ) : Prop where
  other : (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc)
  cursor : b.rc = Function.update a.rc sN (a.rc sN + count)
  out_eq : b.out = a.out ++ word
  vars : Fr a b loopScratch

theorem NodesPrinted.set_counter {a b : State} {word : List Bool} {count : ℕ}
    (h : NodesPrinted a b word count) (v : ℕ) : NodesPrinted a (b.set loopReg v) word count :=
  ⟨h.other, h.cursor, h.out_eq, Fr.trans h.vars (Fr.set b v (List.mem_cons_self ..))⟩

theorem NodesPrinted.constants {a b : State} {word : List Bool} {count : ℕ}
    (h : NodesPrinted a b word count) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

theorem write_stored_nodes (C : Ctx) {n : ℕ} (nodes : List (BooleanNode n)) (tail : List ℕ)
    (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ C.Wd) (h3 : a.env threeReg = 3)
    (hin : (a.ram sN).drop (a.rc sN) = nodes.flatMap nodeFields ++ tail)
    (hN : a.env nodeCountReg = nodes.length) (hNW : nodes.length < 2 ^ C.Wd)
    (Λ : ℕ) (hΛ : ∀ node ∈ nodes, ∀ i : Fin 3, (PCPPRequestNodeSchema.fields node i).bits.length ≤ Λ) :
    Hs C writeStoredNodes a (nodes.length * (20 * Λ + 50) + 4)
      (fun b => NodesPrinted a b (nodes.flatMap sourceNodeWord) (3 * nodes.length)) := by
  let I : ℕ → State → Prop := fun k b =>
    NodesPrinted a b ((nodes.take k).flatMap sourceNodeWord) (3 * k)
  have he := forS_spec' (C := C) loopReg nodeCountReg (by decide) writeStoredNode
    a nodes.length hNW I (20 * Λ + 46)
    (fun _ _ v h => h.set_counter v)
    (by refine ⟨rfl, ?_, by simp, Fr.refl _ _⟩; simp)
    hN ?_
  · exact he.mono (by nlinarith) (fun b hb => by simpa [I] using hb.1)
  · intro k hk b hb hkreg hcount
    have hother := hb.other
    simp only [Prod.mk.injEq] at hother
    have hdrop : (b.ram sN).drop (b.rc sN) = nodeFields nodes[k] ++
        ((nodes.drop (k + 1)).flatMap nodeFields ++ tail) := by
      rw [hother.2.1, hb.cursor, Function.update_self, ← List.drop_drop, hin]
      have hh : nodes.flatMap nodeFields = (nodes.take k).flatMap nodeFields ++
          (nodes.drop k).flatMap nodeFields := by rw [← List.flatMap_append, List.take_append_drop]
      have hlen : ((nodes.take k).flatMap nodeFields).length = 3 * k := by
        rw [nodeFields_length, List.length_take, Nat.min_eq_left hk.le]
      rw [hh, List.append_assoc, ← hlen, List.drop_left, List.drop_eq_getElem_cons hk,
        List.flatMap_cons, List.append_assoc]
    have hprint := write_stored_node C nodes[k] _ b (hb.constants hc) hW
      ((hb.vars threeReg (by decide)).trans h3) hdrop
    have hcost : 10 * (PCPPRequestNodeSchema.fields nodes[k] 1).bits.length +
        10 * (PCPPRequestNodeSchema.fields nodes[k] 2).bits.length + 46 ≤ 20 * Λ + 46 := by
      have h1 := hΛ nodes[k] (List.getElem_mem hk) 1
      have h2 := hΛ nodes[k] (List.getElem_mem hk) 2
      omega
    refine hprint.mono hcost ?_
    intro d hd
    refine ⟨⟨?_, ?_, ?_, Fr.trans hb.vars (hd.vars.weaken (fun _ h => List.mem_cons_of_mem loopReg h))⟩,
      (hd.vars loopReg (by decide)).trans hkreg, (hd.vars nodeCountReg (by decide)).trans hcount⟩
    · exact hd.other.trans hb.other
    · rw [hd.cursor, hb.cursor]
      simp [Nat.mul_add, Nat.add_assoc]
    · rw [hd.out_eq, hb.out_eq]
      rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]
      simp only [List.flatMap_singleton, List.append_assoc]

end NearCubicGates.Adapters.Proximity.SourcePrinting
