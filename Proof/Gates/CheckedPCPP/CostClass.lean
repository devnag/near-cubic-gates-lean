import Proof.Gates.CheckedPCPP.CompBounds

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP.CostClass

open NearCubicWires NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.CheckedPCPP.NodeEmit

variable {ι : Type*} {S : ι → ℕ}

open PolyB in
theorem fieldCost_pb {a : ι → ℕ} (ha : PolyB S a) (k : ℕ) : PolyB S (fun i => fieldCost (a i) k) :=
  (add (add (add (mul (const 25) ha) (const (4 * k))) (const 4))
    (mul (add (add ha (const 1)) (const 10)) (add (mul (const 100) ha) (const 200)))).mono (fun i => by
      unfold fieldCost; have := natBitLength_le (a i)
      have h := Nat.mul_le_mul_right (100 * a i + 200) (show natBitLength (a i) + 10 ≤ a i + 1 + 10 by omega)
      omega)

open PolyB in
theorem nodeCost_pb {a : ι → ℕ} (ha : PolyB S a) : PolyB S (fun i => nodeCost (a i)) :=
  (add (mul (const 3) (fieldCost_pb ha 3)) (const 2)).mono (fun _ => le_of_eq rfl)

open PolyB in
theorem descCost_pb {q L V : ι → ℕ} (hq : PolyB S q) (hL : PolyB S L) (hV : PolyB S V) :
    PolyB S (fun i => DescW.descCost (q i) (L i) (V i)) := by
  have hn := nodeCost_pb hV
  have he : PolyB S (fun i => ChecksW.elemCost (V i)) :=
    (add (add (mul (const 5) (add hn (const 1))) (mul (const 21) hV)) (const 50)).mono (fun _ => le_of_eq rfl)
  have hc : PolyB S (fun i => ChecksW.colCost (V i)) := (add he (const 8)).mono (fun _ => le_of_eq rfl)
  have hh : PolyB S (fun i => ChecksW.headCost (V i)) :=
    (add (add (add hn (mul (const 3) hV)) (mul (const 18) hV)) (const 20)).mono (fun _ => le_of_eq rfl)
  have ht : PolyB S (fun i => ChecksW.tailCost (V i)) :=
    (add (add (mul (const 7) (add hn (const 1))) (mul (const 21) hV)) (const 70)).mono (fun _ => le_of_eq rfl)
  have hr : PolyB S (fun i => ChecksW.rowCost (q i) (V i)) :=
    (add (add (add (add hh (add (add (mul hq (add hc (const 8))) (mul (const 7) hq)) (const 3))) ht)
      (mul (const 3) hq)) (const 12)).mono (fun _ => le_of_eq rfl)
  have hk : PolyB S (fun i => ChecksW.checksCost (q i) (L i) (V i)) :=
    (add (add (mul hL (add hr (const 8))) (mul (const 7) hL)) (const 3)).mono (fun _ => le_of_eq rfl)
  have hrd : PolyB S (fun i => DescW.readCost (V i)) :=
    (mul (add hV (const 3)) (add (mul (const 80) hV) (const 120))).mono (fun _ => le_of_eq rfl)
  have hf : PolyB S (fun i => DescW.frontCost (V i)) :=
    (add (add (add (add (add (mul (const 3) hrd) (mul (const 21) hV)) (const 7))
      (add (mul (const 246) hV) (const 1))) (add (mul (const 10) hV) (const 1))) (const 5)).mono
      (fun _ => le_of_eq rfl)
  have hb : PolyB S (fun i => DescW.backCost (V i)) :=
    (add (add (add (mul (const 16) (mul hV (add (mul (const 12) hV) (const 18)))) (mul (const 3) (fieldCost_pb hV 3)))
      (mul (const 22) hV)) (const 20)).mono (fun _ => le_of_eq rfl)
  exact (add (add (add (add hf (const 1)) hk) (const 1)) hb).mono (fun _ => le_of_eq rfl)

open PolyB in
theorem encColsCost_pb {q L B : ι → ℕ} (hq : PolyB S q) (hL : PolyB S L) (hB : PolyB S B) (t : ℕ) :
    PolyB S (fun i => encColsCost (q i) (L i) (B i) t) := by
  have hm : PolyB S (fun i => msgCost (q i)) :=
    (mul (const 10) (pow (add hq (const 7)) 2)).mono (fun _ => le_of_eq rfl)
  have hr : PolyB S (fun i => rdCost (q i) (L i) (B i)) :=
    (add (add (mul (add hL (const 2)) (add (mul (const 70) hq) (const 50))) (mul (const 25) hB)) (const 60)).mono
      (fun _ => le_of_eq rfl)
  have hc : PolyB S (fun i => colCost (q i) (L i) (B i) t) :=
    (add (add (add (add hm hr) (mul (const (t + 2)) (add (mul (const 18) hB) (const 4)))) (mul (const 3) hL))
      (const 20)).mono (fun _ => le_of_eq rfl)
  exact (add (add (mul hq (add hc (const 4))) (mul (const 18) hq)) (const 5)).mono (fun _ => le_of_eq rfl)

open PolyB in
theorem supCost_pb {q L : ι → ℕ} (hq : PolyB S q) (hL : PolyB S L) : PolyB S (fun i => SupW.supCost (q i) (L i)) := by
  have hf := fieldCost_pb hq 3
  have hrow : PolyB S (fun i => SupW.rowCostS (q i)) :=
    (mul (const 100) (mul (add hq (const 1)) (add hf (const 50)))).mono (fun i => by
      unfold SupW.rowCostS; nlinarith)
  exact (add (add (add (add (mul hL (add hrow (const 8))) (mul (const 7) hL)) (const 3)) (const 1)) (const 7)).mono
    (fun _ => le_of_eq rfl)

open PolyB in
theorem costA_pb (Cb eb te : ℕ) {hl dl f2 wl q L B : ι → ℕ} (hhl : PolyB S hl) (hdl : PolyB S dl) (hf2 : PolyB S f2)
    (hwl : PolyB S wl) (hq : PolyB S q) (hL : PolyB S L) (hB : PolyB S B) :
    PolyB S (fun i => Comp.costA Cb eb (hl i) (dl i) (f2 i) (wl i) (q i) (L i) (B i) te) := by
  have hT : PolyB S (fun i => hl i + dl i + wl i + q i + B i + 11) :=
    add (add (add (add (add hhl hdl) hwl) hq) hB) (const 11)
  refine (add (add (add (add (mul (const 2000) (pow hT 2)) (mul (const eb) (add (add (mul (mul (const 40) hB) hB)
    (mul (const 40) hB)) (const 20)))) (encColsCost_pb hq hL hB te)) hf2) (const (100 * Cb + 1000))).mono
    (fun i => ?_)
  unfold Comp.costA FrameIn.frameInCost FrameIn.copyDescCost Glue.readQCost DescW.readCost EncSetup.powCost
  set T := hl i + dl i + wl i + q i + B i + 11 with hTd
  have h1 : (dl i + 11) * (dl i + 11) ≤ T ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h2 : (wl i + 3) * (80 * wl i + 120) ≤ 80 * T ^ 2 := by
    rw [sq]; nlinarith
  have h3 : 11 ≤ T := by omega
  have h4 : T ≤ T ^ 2 := by rw [sq]; nlinarith
  nlinarith

open PolyB in
theorem costB_pb {q L V f4 cwl f5 pbl rbl : ι → ℕ} (hq : PolyB S q) (hL : PolyB S L) (hV : PolyB S V)
    (hf4 : PolyB S f4) (hcw : PolyB S cwl) (hf5 : PolyB S f5) (hpb : PolyB S pbl) (hrb : PolyB S rbl) :
    PolyB S (fun i => Comp.costB (q i) (L i) (V i) (f4 i) (cwl i) (f5 i) (pbl i) (rbl i)) := by
  have h1 := descCost_pb hq hL hV
  have h2 : PolyB S (fun i => V i * (12 * V i + 18) + 14 * V i + 20) :=
    add (add (mul hV (add (mul (const 12) hV) (const 18))) (mul (const 14) hV)) (const 20)
  have h3 : PolyB S (fun i => 22 * cwl i + 5 * (2 * cwl i + 1)) :=
    add (mul (const 22) hcw) (mul (const 5) (add (mul (const 2) hcw) (const 1)))
  have h4 : PolyB S (fun i => 22 * pbl i + 22 * rbl i) := add (mul (const 22) hpb) (mul (const 22) hrb)
  have h := add (add (add (add (add h1 (mul (const 5) h2)) hf4) h3) hf5) (add h4 (const 100))
  exact h.mono (fun i => by unfold Comp.costB; omega)

open PolyB in
theorem costC_pb {q L : ι → ℕ} (hq : PolyB S q) (hL : PolyB S L) :
    PolyB S (fun i => Comp.costC (q i) (L i)) := by
  have h1 : PolyB S (fun i => q i * (18 * L i + 3 + 8)) := mul hq (add (add (mul (const 18) hL) (const 3)) (const 8))
  have h2 : PolyB S (fun i => 5 * (q i * L i)) := mul (const 5) (mul hq hL)
  have h3 : PolyB S (fun i => 25 * q i + 18 * L i + 100) :=
    add (add (mul (const 25) hq) (mul (const 18) hL)) (const 100)
  have h := add (add (add h1 h2) h3) (supCost_pb hq hL)
  exact h.mono (fun i => by unfold Comp.costC; omega)

end NearCubicGates.Close.CheckedPCPP.CostClass
