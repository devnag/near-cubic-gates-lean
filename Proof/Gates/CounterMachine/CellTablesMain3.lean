import Proof.Gates.CounterMachine.CellTablesMain2
import Proof.Gates.CounterMachine.CellTablesFin

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN gKd gJ gRC)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame finP)

def mainK : St VV MM := .seq startP (.seq resL (.seq momL finP))

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

def mainCost (Lk Bk wb : ℕ) (r : CellReq B1 B2 cT) : ℕ :=
  startCost r + (2 * partCost Lk Bk wb r + 3) + (roleCount r.c.kind * (r.p.J * (bodyCost Lk Bk wb r + 4) +
    bodyCost Lk Bk wb r + 5 + 4) + 4) +
    100 * ((reqIds r.c r.p).length * 2 ^ (r.c.n - r.p.k) + 1) * (recWidth r.c r.p r.wt + 10) + 3

theorem recs_lt (r : CellReq B1 B2 cT) (v : ℕ) (hv : v ∈ (reqIds r.c r.p).flatMap (recsOf r.c r.p r.wt)) :
    v < 2 ^ recWidth r.c r.p r.wt := by
  have hspec := cellReq_spec r
  obtain ⟨w0, hw0⟩ := r.hw
  simp only [List.mem_flatMap, recsOf, List.mem_map] at hv
  obtain ⟨id, hid, i, hi, rfl⟩ := hv
  have hi' := (CellTablesValue.printerOrder_mem' _ i).mp hi
  have hb := (Cells.cellRec_bounds r.c r.p r.wt hspec w0 hw0 i id hid).2
  have hcb : cellBits r.wt.I = r.c.n - r.p.k := outerCoords_length r.wt.I (cellReq_hk r)
  unfold recWidth; rw [hcb]
  calc _ < (i + 1) * 2 ^ (Cells.keyW r.c r.p + valueWidth r.c r.p) := hb
    _ ≤ 2 ^ (r.c.n - r.p.k) * 2 ^ (Cells.keyW r.c r.p + valueWidth r.c r.p) := Nat.mul_le_mul_right _ hi'
    _ = _ := by rw [← pow_add]; congr 1; unfold Cells.keyW; omega

theorem recs_length (r : CellReq B1 B2 cT) :
    ((reqIds r.c r.p).flatMap (recsOf r.c r.p r.wt)).length = (reqIds r.c r.p).length * 2 ^ (r.c.n - r.p.k) := by
  rw [List.length_flatMap]
  simp [recsOf, CellTables.printerOrder_length]

theorem main_run (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ)
    (hF : Fit RK r Wd Lk Bk wb) (hW : wdNeed r ≤ Wd) :
    ∃ b n, Ex (ctxK RK Wd (cellInput r) Lk Bk) mainK (a0 : DS VV MM) b n ∧ b.out = cellWord r.c r.p r.wt ∧
      n ≤ mainCost Lk Bk wb r := by
  set C := ctxK RK Wd (cellInput r) Lk Bk with hC
  have hWd : wdNeed r ≤ C.Wd := hW
  unfold wdNeed lamW at hWd
  have hcb : cellBits r.wt.I = r.c.n - r.p.k := outerCoords_length r.wt.I (cellReq_hk r)
  have hRW : recWidth r.c r.p r.wt = r.c.n - r.p.k + keyBits r.p * keyLen r.c r.p + valueWidth r.c r.p := by
    unfold recWidth; rw [hcb]
  have hVW1 : 1 ≤ valueWidth r.c r.p := by unfold valueWidth; omega
  have hm : ∃ b n, Ex C mainK (a0 : DS VV MM) b n ∧ (b.out = cellWord r.c r.p r.wt ∧ n ≤ mainCost Lk Bk wb r) := by
    unfold mainK
    show Hx C _ _ (fun b n => b.out = cellWord r.c r.p r.wt ∧ n ≤ mainCost Lk Bk wb r)
    refine Hs.then (start_spec RK r Wd Lk Bk hW) (fun e1 st n1 hn1 => ?_)
    refine Hs.then (resL_spec RK r Wd Lk Bk wb (cellInput r) e1 hF st.pre st.ramQ (le_of_eq st.rcQ) st.np st.ee st.kd)
      (fun e2 ⟨p2, r2, k2⟩ n2 hn2 => ?_)
    refine Hs.then (momL_spec RK r Wd Lk Bk wb (cellInput r) e2 hF p2
      (by rw [k2.env gJ (not_bodyVar (by decide)) (by decide)]; exact st.j)
      (by rw [k2.env gRC (not_bodyVar (by decide)) (by decide)]; exact st.rc)) (fun e3 ⟨p3, r3, k3⟩ n3 hn3 => ?_)
    have hrecs : e3.ram sREC = (reqIds r.c r.p).flatMap (recsOf r.c r.p r.wt) := by
      rw [r3, r2, st.recs, List.nil_append, ← enum_eq, List.flatMap_append]
      simp only [List.flatMap_assoc]
      rfl
    have e3RW : e3.env vRW = recWidth r.c r.p r.wt := by
      rw [k3.env vRW (not_bodyVar (by decide)) (by decide), k2.env vRW (not_bodyVar (by decide)) (by decide), st.rw,
        hRW]
    refine Hs.last (CellTables.finP_spec C e3 (recWidth r.c r.p r.wt) _ p3.valid p3.cst e3RW (by rw [hRW]; omega)
      (by rw [hRW]; omega) hrecs (by rw [p3.rcR, hrecs])
      (fun v hv => recs_lt r v hv)) (fun e4 ⟨o4, _, _⟩ n4 hn4 => ?_)
    refine ⟨?_, ?_⟩
    · rw [o4, k3.out, k2.out, st.out, List.nil_append]
      exact CellTablesValue.recs_cellWord r (reqIds r.c r.p) (List.Perm.refl _)
    · rw [recs_length] at hn4
      unfold mainCost
      omega
  obtain ⟨b, n, he, ho, hn⟩ := hm
  exact ⟨b, n, he, ho, hn⟩

end NearCubicGates.Close.CounterMachine.CellTablesProg
