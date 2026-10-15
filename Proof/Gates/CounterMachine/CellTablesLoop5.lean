import Proof.Gates.CounterMachine.CellTablesLoop4

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN gKd gJ gRC)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem momL_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) (inp : List Bool)
    (a : DS VV MM) (hF : Fit RK r Wd Lk Bk wb) (hP : Pre (ctxK RK Wd inp Lk Bk) r a) (hJ : a.env gJ = r.p.J)
    (hRC : a.env gRC = roleCount r.c.kind) :
    Hs (ctxK RK Wd inp Lk Bk) momL a (roleCount r.c.kind * (r.p.J * (bodyCost Lk Bk wb r + 4) +
        bodyCost Lk Bk wb r + 5 + 4) + 4) (fun e => Pre (ctxK RK Wd inp Lk Bk) r e ∧
      e.ram sREC = a.ram sREC ++ ((List.range (roleCount r.c.kind)).flatMap (momIds r.p.J)).flatMap
        (recsOf r.c r.p r.wt) ∧ Keep a e [lR, lJ]) := by
  set C := ctxK RK Wd inp Lk Bk with hC
  have hRW : roleCount r.c.kind < 2 ^ C.Wd := by rw [← hRC]; exact hP.valid.env_lt gRC
  let I : ℕ → DS VV MM → Prop := fun k d => Pre C r d ∧
    d.ram sREC = a.ram sREC ++ ((List.range k).flatMap (momIds r.p.J)).flatMap (recsOf r.c r.p r.wt) ∧
    Keep a d [lR, lJ]
  refine Hs.mono (PrefixProg.forS_specV (C := C) lR gRC (by decide) momR a _ hRW I _
    (fun k d v hv ⟨i1, i2, i3⟩ => ⟨i1.set lR v (by decide) (by decide) (by decide) (by omega), i2,
      i3.trans (Keep.set _ _ _ _ (by simp))⟩) ⟨hP, by simp, Keep.refl _ _⟩ hRC ?_) le_rfl (fun e ⟨h, _, _⟩ => h)
  intro k hk d ⟨i1, i2, i3⟩ hdk hdm
  refine Hs.mono (momR_spec RK r Wd Lk Bk wb inp d k hk hF i1 hdk
    (by rw [i3.env gJ (not_bodyVar (by decide)) (by decide)]; exact hJ)) le_rfl ?_
  rintro e ⟨p1, r1, k1⟩
  refine ⟨⟨p1, ?_, i3.trans (k1.weaken (by simp))⟩, by rw [k1.env lR (not_bodyVar (by decide)) (by decide)]; exact hdk,
    by rw [k1.env gRC (not_bodyVar (by decide)) (by decide)]; exact hdm⟩
  rw [r1, i2, List.range_succ, List.flatMap_append, List.flatMap_append, List.append_assoc]
  simp

/-! ## The enumeration -/

theorem length_of_mem_vecs (q : ℕ) : ∀ (n : ℕ) (v : List ℕ), v ∈ vecs q n → v.length = n
  | 0, v, h => by simp [vecs] at h; simp [h]
  | n + 1, v, h => by
    simp only [vecs, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨a, _, w, hw, rfl⟩ := h
    simp [length_of_mem_vecs q n w hw]

theorem vecs_add (q : ℕ) : ∀ a b : ℕ, vecs q (a + b) = (vecs q a).flatMap fun κ => (vecs q b).map (κ ++ ·)
  | 0, b => by simp [vecs]
  | a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [vecs, vecs_add q a b, List.map_flatMap, List.flatMap_assoc, List.flatMap_map, List.map_map]
    apply List.flatMap_congr; intro x _
    apply List.flatMap_congr; intro κ _
    rfl

theorem range_resId (c : Call) (p : Params) (part : Option Bool) (q : ℕ) :
    (List.range (q ^ dOf c p)).map (resId c p part q) = (vecs q (roleCount c.kind * p.J)).flatMap fun κ =>
      (vecs q (roleCount c.kind)).map fun σ => ReqId.residue part q κ σ := by
  have hD : dOf c p = roleCount c.kind * p.J + roleCount c.kind := by unfold dOf; ring
  have h1 : (List.range (q ^ dOf c p)).map (Cells.digitsM (List.replicate (dOf c p) q)) = vecs q (dOf c p) := by
    rw [Cells.vecs_eq_vecsM, Cells.vecsM_eq, List.prod_replicate]
  have h2 : (List.range (q ^ dOf c p)).map (resId c p part q) = (vecs q (dOf c p)).map fun v =>
      ReqId.residue part q (v.take (roleCount c.kind * p.J)) (v.drop (roleCount c.kind * p.J)) := by
    rw [← h1, List.map_map]; rfl
  rw [h2, hD, vecs_add, List.map_flatMap]
  apply List.flatMap_congr
  intro κ hκ
  rw [List.map_map]
  apply List.map_congr_left
  intro σ _
  have hl := length_of_mem_vecs q _ κ hκ
  simp only [Function.comp_apply]
  rw [List.take_left' hl, List.drop_left' hl]

/-- **The loops visit exactly `reqIds`.** -/
theorem enum_eq (c : Call) (p : Params) :
    (parts c).flatMap (fun part => (p.primes.sort (· ≤ ·)).flatMap fun q =>
      (List.range (q ^ dOf c p)).map (resId c p part q)) ++
      (List.range (roleCount c.kind)).flatMap (momIds p.J) = reqIds c p := by
  unfold reqIds momIds
  congr 1
  apply List.flatMap_congr; intro part _
  apply List.flatMap_congr; intro q _
  exact range_resId c p part q

end NearCubicGates.Close.CounterMachine.CellTablesProg
