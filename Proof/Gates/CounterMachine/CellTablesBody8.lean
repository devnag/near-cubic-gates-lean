import Proof.Gates.CounterMachine.CellTablesBody7

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

def momBody (tg jv : Fin VV) : St VV MM :=
  .seq (emV tg) (.seq (emV lR) (.seq (emV jv) (.seq (.op (.copy bKey tg)) (.seq (.op (.mul bKey kB2 bTmp))
  (.seq (.op (.copy bKey bTmp)) (.seq (.op (.add bKey lR)) (.seq (.op (.mul bKey kB2 bTmp))
  (.seq (.op (.copy bKey bTmp)) (.seq (.op (.add bKey jv)) (tailB kPAD vZ vZ))))))))))

def momB : Bool → St VV MM
  | false => momBody v1 lJ
  | true => momBody v2 vZ

/-- The moment request of a body. -/
def momId (phi : Bool) (ro j : ℕ) : ReqId := if phi then .phiMoment ro else .digitMoment ro j

theorem hfold_zeros (B k : ℕ) : ∀ n, hfold B k (List.replicate n 0) = k * B ^ n
  | 0 => by simp [hfold]
  | n + 1 => by
    rw [List.replicate_succ', hfold_snoc, hfold_zeros B k n]; ring

theorem momId_mem (c : Call) (p : Params) (phi : Bool) (ro j : ℕ) (hro : ro < roleCount c.kind)
    (hj : phi = false → j < p.J) : momId phi ro j ∈ reqIds c p := by
  unfold reqIds momId
  apply List.mem_append_right
  simp only [List.mem_flatMap, List.mem_range, List.mem_append, List.mem_map, List.mem_singleton]
  refine ⟨ro, hro, ?_⟩
  cases phi with
  | false => left; exact ⟨j, hj rfl, rfl⟩
  | true => right; rfl

theorem descN_mom (phi : Bool) (ro j : ℕ) :
    (descN (momId phi ro j)).flatMap natWord = natWord (if phi then 2 else 1) ++ natWord ro ++
      natWord (if phi then 0 else j) := by
  cases phi <;> simp [momId, descN]

theorem reqKey_mom (c : Call) (p : Params) (phi : Bool) (ro j : ℕ) :
    reqKey c p (momId phi ro j) = (((if phi then 2 else 1) * 2 ^ keyBits p + ro) * 2 ^ keyBits p +
      (if phi then 0 else j)) * (2 ^ keyBits p) ^ dOf c p := by
  have hl : keyLen c p - 3 = dOf c p := by unfold keyLen dOf; omega
  have e1 : ∀ (st n : ℕ), List.foldl (fun acc x => acc * 2 ^ keyBits p + x) st (List.replicate n 0) =
      st * (2 ^ keyBits p) ^ n := fun st n => hfold_zeros _ st n
  cases phi <;>
  · unfold reqKey radixKey momId
    simp only [keyFields, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil, List.cons_append,
      List.nil_append, List.foldl_cons, e1]
    rw [show 0 + 1 + 1 + 1 = 3 by rfl, hl]
    ring

end NearCubicGates.Close.CounterMachine.CellTablesProg
