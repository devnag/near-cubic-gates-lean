import SourceAdapters.Proximity.NodePrinting
import Proof.Gates.Cells.Load

/-! Q04: paid native natural-field parsing with explicit cursor/register effects. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourcePrinting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

variable {C : Ctx}

def readInto (x : Fin VV) : Script := .seq rdNatI (.op (.copy x t3))

structure ReadInto (a b : State) (x : Fin VV) (v : ℕ) : Prop where
  value : b.env x = v
  cursor : b.ip = a.ip + (natWord v).length
  other : (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
    (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)
  vars : Fr a b (x :: rdNatT)

theorem ReadInto.constants {a b : State} {x : Fin VV} {v : ℕ}
    (h : ReadInto a b x v) (hc : Cst a) (hx : x ∉ [vZ, v1, v2]) : Cst b := by
  apply Cst.of_fr hc h.vars
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or]
    exact ⟨Ne.symm hx.1, by decide⟩
  · simp only [List.mem_cons, not_or]
    exact ⟨Ne.symm hx.2.1, by decide⟩
  · simp only [List.mem_cons, not_or]
    exact ⟨Ne.symm hx.2.2, by decide⟩

theorem read_into (x : Fin VV) (hx : x ≠ t3) (a : State) (hc : Cst a)
    (v : ℕ) (tail : List Bool) (hin : C.inp.drop a.ip = natWord v ++ tail)
    (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C (readInto x) a (30 * natBitLength v + 32) (fun b => ReadInto a b x v) := by
  refine Hs.mono (Hs.seq (t2 := 1) (rdNatI_spec a hc v tail hin hW)
    (fun b ⟨hv, _, hp, ho, hf⟩ => ?_)) (by omega) (fun _ h => h)
  refine Hs.mono (hs_copy C x t3 b hx) le_rfl ?_
  intro d hd; subst d
  refine ⟨by simp [hv], hp, ho, ?_⟩
  exact Fr.trans (hf.weaken (fun _ h => List.mem_cons_of_mem x h))
    (Fr.set b (b.env t3) (List.mem_cons_self ..))

theorem ReadInto.tail {a b : State} {x : Fin VV} {v : ℕ} (h : ReadInto a b x v)
    (tail : List Bool) (hin : C.inp.drop a.ip = natWord v ++ tail) : C.inp.drop b.ip = tail := by
  rw [h.cursor, ← List.drop_drop, hin, List.drop_left]

/-- The exact flattened sequence consumed by the released counted list reader. -/
def nodeFields {n : ℕ} (node : BooleanNode n) : List ℕ :=
  [PCPPRequestNodeSchema.fields node 0, PCPPRequestNodeSchema.fields node 1,
    PCPPRequestNodeSchema.fields node 2]

theorem nodeFields_word {n : ℕ} (node : BooleanNode n) :
    (nodeFields node).flatMap natWord = PCPPRequestNodeSchema.native node := by
  simp [nodeFields, PCPPRequestNodeSchema.native, List.append_assoc]

theorem nodes_fields_word {n : ℕ} (nodes : List (BooleanNode n)) :
    (nodes.flatMap nodeFields).flatMap natWord = nodes.flatMap PCPPRequestNodeSchema.native := by
  simp [List.flatMap_assoc, nodeFields_word]

theorem nodeFields_length {n : ℕ} (nodes : List (BooleanNode n)) :
    (nodes.flatMap nodeFields).length = 3 * nodes.length := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simp [nodeFields, ih]; omega

end NearCubicGates.Adapters.Proximity.SourcePrinting
