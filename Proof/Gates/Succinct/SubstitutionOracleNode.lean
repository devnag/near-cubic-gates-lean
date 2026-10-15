import Proof.Gates.Succinct.SubstitutionPlainNode

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct NearCubicGates.Close.Outer
open RepairRepresentation (natWord)

variable {q : ℕ}

/-- The cost class of an oracle gate. -/
def oIter (S : ℕ) : ℕ := (S + 1) * (cpIter S + 4) + 1000000 * (S + 2) ^ 2

theorem oCost (S nb l nl lb : ℕ) (hnb : nb ≤ S) (hl : l ≤ S) (hnl : nl ≤ 2 * S + 3) (hlb : lb ≤ S) :
    readCost l + 5 * nl + 2 + 1 + (18 * nb + 3 + 1 + (nb * (cpIter S + 4) + 1 + 1 + (5 * lb + 1 + 1 +
      (18 * l + 3 + 1 + (l * (1000 * (S + 1 + 3) + 4) + 1 + 1 + (3 * l + 1 + 1 + (18 * nb + 3))))))) ≤ oIter S := by
  unfold oIter
  have h1 := readCost_le l S hl
  have h2 : nb * (cpIter S + 4) ≤ S * (cpIter S + 4) := Nat.mul_le_mul_right _ hnb
  have h3 : l * (1000 * (S + 1 + 3) + 4) ≤ S * (1000 * (S + 4) + 4) := Nat.mul_le_mul hl (by omega)
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 : S * (1000 * (S + 4) + 4) ≤ 1004 * (S + 2) ^ 2 := by nlinarith
  rw [Nat.add_mul, Nat.one_mul]
  generalize cpIter S + 4 = CP at *
  generalize readCost l = R at *
  generalize (S + 2) ^ 2 = X at *
  generalize S * CP = SC at *
  omega

set_option maxHeartbeats 3200000 in
/-- **An oracle gate of `C`** (paper §11.4): its image is `B`'s nodes copied at offset `cur` (`cpNode`). -/
theorem nC5_spec (cap : ℕ) (B : BooleanCircuit q) (σ : WState 4 nrH) (hz : CBZ σ)
    (htagB : σ.val (regH .tagB) = 0) (htC : σ.val (regH .tC) = 0) (hcdB : σ.val (regH .cdB) = 0)
    (hL0 : σ.val (regH .L) = 0) (hcdL : σ.val (regH .cdL) = 0)
    (hD : σ.st sD = PCPPNative.descriptor B) (hDh : σ.sh sD = pB B)
    (ℓ : ℕ) (hLs : σ.st sL = natWord ℓ) (hLh : σ.sh sL = 0)
    (preW restW : List Bool) (args : List ℕ) (hlen : args.length = ℓ)
    (hW : σ.st sW = preW ++ args.flatMap natWord ++ restW) (hWh : σ.sh sW = preW.length)
    (fl : List Bool) (hF : σ.st sF = fl) (hFh : σ.sh sF = 0)
    (hnB : σ.val (regH .nB) = B.nodes.length) (hn1 : σ.val (regH .nB1) = B.nodes.length - 1)
    (hob : σ.val (regH .oB) = B.output.val) (S : ℕ)
    (hnBS : B.nodes.length ≤ S) (hq : q ≤ S) (hAS : ∀ x ∈ args, x ≤ S) (hwS : (args.flatMap natWord).length ≤ S)
    (hDS : (PCPPNative.descriptor B).length ≤ S)
    (hcur : σ.val (regH .cur) ≤ (S + 2) ^ 2) (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : σ.val (regH .cdW) + (PCPPNative.descriptor B).length + 2 * out.length +
      2 * (S * (12 * (S + 2) ^ 2 + 40)) + 2000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ, WExec cap nC5 σ τ (oIter S) ∧
      OutOK τ (out ++ (B.nodes.map (cpNode fl args (B.nodes.length - 1) B.output.val (σ.val (regH .cur)))).flatMap
        PCPPRequestNodeSchema.native) ∧
      τ.sh sW = preW.length + (args.flatMap natWord).length ∧
      τ.val (regH .cdW) = σ.val (regH .cdW) + (args.flatMap natWord).length ∧
      τ.val (regH .cur) = σ.val (regH .cur) + B.nodes.length ∧
      WClean τ ∧ CBZ τ ∧ Fr σ τ [sW, sO] [.cdW, .w 7, .cur] ∧ τ.st sW = σ.st sW := by
  have hsq : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hlS : args.length ≤ S := by
    have := flatMap_natWord_len args; omega
  have hnl := natWord_length ℓ
  have hbl := nbl_le ℓ
  -- 1. `L := ℓ`
  have e1 := getL_spec cap σ ℓ hLs hLh (fun r => hz.f r) (hz.z _ (by simp [zl])) (hz.z _ (by simp [zl])) hL0 hcdL
    (by omega)
  set σ1 := σ.setv (regH .L) ℓ with hσ1
  have f1 : Fr σ σ1 [] [.L] := fr_setv σ .L ℓ
  -- 2. `tC := n_B`
  obtain ⟨τ2, e2, v2, f2⟩ := add_fr cap .nB .tC (by simp) (by simp) (by simp) σ1
    (by rw [f1.v (by simp)]; exact hz.z _ (by simp [zl])) (by rw [f1.v (by simp), f1.v (by simp), htC, hnB]; omega)
  have g2 : ∀ u, u ∉ [HReg.L, .tC] → τ2.val (regH u) = σ.val (regH u) := fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rw [f2.v (by simp [hu.2]), f1.v (by simp [hu.1])]
  have s2 : ∀ i, τ2.st i = σ.st i ∧ τ2.sh i = σ.sh i := fun i => by
    rw [(f2.s (by simp)).1, (f2.s (by simp)).2]; simp [σ1]
  have hz2 : CBZ τ2 := ⟨fun r => by rw [g2 _ (by simp)]; exact hz.f r,
    fun u hu => by rw [g2 u (by intro m; simp at m; rcases m with rfl | rfl <;> simp [zl] at hu)]; exact hz.z u hu⟩
  -- 3. the copy loop
  obtain ⟨τ3, e3, o3, w3, z3, tg3, tc3, sh3, cd3, f3, st3⟩ := copyLoop_spec cap B τ2 hz2
    (by rw [g2 _ (by simp)]; exact htagB) (by rw [(s2 sD).1, hD]) (by rw [(s2 sD).2, hDh])
    (by rw [g2 _ (by simp)]; exact hcdB) (by rw [v2, f1.v (by simp), f1.v (by simp), htC, hnB]; simp)
    preW restW args (by rw [(s2 sW).1, hW]) (by rw [(s2 sW).2, hWh])
    (by rw [f2.v (by simp), hσ1]; simp [hlen]) fl (by rw [(s2 sF).1, hF]) (by rw [(s2 sF).2, hFh])
    (by rw [g2 _ (by simp), hn1]) (by rw [g2 _ (by simp), hob]) S hnBS hq hlS hAS hwS
    (by rw [g2 _ (by simp)]; exact hcur) out
    ⟨by rw [(s2 sO).1]; exact hout.1, by rw [(s2 sO).2]; exact hout.2.1, by rw [g2 _ (by simp)]; exact hout.2.2⟩
    ⟨fun i hi => by rw [g2 _ (by simp)]; exact hcl.1 i hi, by rw [g2 _ (by simp)]; exact hcl.2⟩
    (by omega)
  rw [g2 _ (by simp)] at o3
  have g3 : ∀ u, u ∉ [HReg.L, .tC, .cdB, .w 7] → τ3.val (regH u) = σ.val (regH u) := fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rw [f3.v (by simp [hu.2.1, hu.2.2.1, hu.2.2.2]), g2 u (by simp [hu.1, hu.2.1])]
  have hL3 : τ3.val (regH .L) = ℓ := by rw [f3.v (by simp), f2.v (by simp)]; simp [σ1]
  have hlB := lenB B B.nodes.length
  have hlenB : lenB B B.nodes.length ≤ (PCPPNative.descriptor B).length := by
    unfold lenB; rw [List.take_length, PCPPNative.descriptor_eq]; simp only [List.length_append]; omega
  -- 4. back to `B`'s nodes
  have e4 := wrewind_spec cap sD (regH .cdB) (lenB B B.nodes.length) τ3 cd3 (by rw [cd3]; omega)
  set τ4 := (τ3.setv (regH .cdB) 0).seth sD (τ3.sh sD - lenB B B.nodes.length) with hτ4
  have f4 : Fr τ3 τ4 [sD] [.cdB] := ((fr_setv τ3 .cdB 0).trans' (fr_seth _ sD _)).mono (by simp) (by simp)
  have hDh4 : τ4.sh sD = pB B := by simp only [τ4, WState.seth_sh, Function.update_self]; rw [sh3]; omega
  -- 5. skip the arguments
  obtain ⟨τ5, e5, v5, f5⟩ := add_fr cap .L .sk (by simp) (by simp) (by simp) τ4
    (by rw [f4.v (by simp)]; exact z3.z _ (by simp [zl]))
    (by rw [f4.v (by simp), f4.v (by simp), z3.z _ (by simp [zl]), hL3]; omega)
  have hsk5 : τ5.val (regH .sk) = args.length := by
    rw [v5, f4.v (by simp), f4.v (by simp), z3.z _ (by simp [zl]), hL3, hlen]; simp
  have hW5 : τ5.st sW = preW ++ args.flatMap natWord ++ restW := by
    rw [(f5.s (by simp)).1, (f4.s (by simp)).1, (f3.s (by simp)).1, (s2 sW).1, hW]
  have hWh5 : τ5.sh sW = preW.length := by
    rw [(f5.s (by simp)).2, (f4.s (by simp)).2, (f3.s (by simp)).2, (s2 sW).2, hWh]
  have g5 : ∀ u, u ∉ [HReg.L, .tC, .cdB, .w 7, .sk] → τ5.val (regH u) = σ.val (regH u) := fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rw [f5.v (by simp [hu.2.2.2.2]), f4.v (by simp [hu.2.2.1]), g3 u (by simp [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1])]
  have e6 := skipN_spec cap sW RW (fam_inj _ (by simp)) (regH .z) (regH .jk) (regH .sk)
    (famNe _ _ (by simp) (by simp)) (famNe _ _ (by simp) (by simp)) (famNe _ _ (by simp) (by simp)) (by simp)
    (by simp) τ5 preW restW args (S + 1)
    (fun x hx => (nbl_le x).trans (by have := hAS x hx; omega)) hW5 hWh5
    (famZero _ _ (fun r => by rw [g5 _ (by simp)]; exact hz.f r))
    (by rw [g5 _ (by simp)]; exact hz.z _ (by simp [zl])) (by rw [g5 _ (by simp)]; exact hz.z _ (by simp [zl]))
    hsk5 (by simp only [RW, fam_cd]; rw [g5 _ (by simp)]; omega) (by omega)
  set τ6 := ((τ5.seth sW (preW.length + (args.flatMap natWord).length)).setv (RW .cd)
    (τ5.val (RW .cd) + (args.flatMap natWord).length)).setv (regH .sk) 0 with hτ6
  have f6 : Fr τ5 τ6 [sW] [.cdW, .sk] := by
    refine ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; simp [τ6, Function.update_apply, hy]
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [τ6, RW, Function.update_apply, hr.1, hr.2]
  -- 6. `L := 0`, `cur += n_B`
  obtain ⟨τ7, e7, z7, f7⟩ := clr_fr cap .L τ6 (by rw [f6.v (by simp), f5.v (by simp), f4.v (by simp), hL3]; omega)
  obtain ⟨τ8, e8, v8, f8⟩ := add_fr cap .nB .cur (by simp) (by simp) (by simp) τ7
    (by rw [f7.v (by simp), f6.v (by simp), g5 _ (by simp)]; exact hz.z _ (by simp [zl]))
    (by rw [f7.v (by simp), f6.v (by simp), g5 _ (by simp), f7.v (by simp), f6.v (by simp), g5 _ (by simp), hnB]
        omega)
  have g8 : ∀ u, u ∉ [HReg.L, .tC, .cdB, .w 7, .sk, .cdW, .cur] → τ8.val (regH u) = σ.val (regH u) := fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rw [f8.v (by simp [hu.2.2.2.2.2.2]), f7.v (by simp [hu.1]), f6.v (by simp [hu.2.2.2.2.1, hu.2.2.2.2.2.1]),
      g5 u (by simp [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1])]
  have hs8 : ∀ i, i ≠ sW → i ≠ sD → τ8.st i = τ3.st i ∧ τ8.sh i = τ3.sh i := fun i h1 h2 => by
    rw [(f8.s (by simp)).1, (f8.s (by simp)).2, (f7.s (by simp)).1, (f7.s (by simp)).2, (f6.s (by simp [h1])).1,
      (f6.s (by simp [h1])).2, (f5.s (by simp)).1, (f5.s (by simp)).2, (f4.s (by simp [h2])).1,
      (f4.s (by simp [h2])).2]; exact ⟨rfl, rfl⟩
  have hc5 : τ5.val (RW .cd) = σ.val (regH .cdW) := by simp only [RW, fam_cd]; rw [g5 _ (by simp)]
  refine ⟨τ8, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : σ1.val (regH .nB) = B.nodes.length := by simp [σ1, hnB]
    have c4 : τ4.val (regH .L) = ℓ := by rw [f4.v (by simp), hL3]
    have c6 : τ6.val (regH .L) = ℓ := by rw [f6.v (by simp), f5.v (by simp), c4]
    have c7 : τ7.val (regH .nB) = B.nodes.length := by rw [f7.v (by simp), f6.v (by simp), g5 _ (by simp), hnB]
    rw [c1, c4, c6, c7]
    have hlS' : ℓ ≤ S := hlen ▸ hlS
    have hnS : (natWord ℓ).length ≤ 2 * S + 3 := by rw [natWord_length]; have := nbl_le ℓ; omega
    rw [hlen]
    exact oCost S B.nodes.length ℓ (natWord ℓ).length (lenB B B.nodes.length) hnBS hlS' hnS (hlenB.trans hDS)
  · exact ⟨by rw [(hs8 sO (by simp) (by simp)).1]; exact o3.1, by rw [(hs8 sO (by simp) (by simp)).2]; exact o3.2.1,
      by rw [f8.v (by simp), f7.v (by simp), f6.v (by simp), f5.v (by simp), f4.v (by simp)]; exact o3.2.2⟩
  · rw [(f8.s (by simp)).2, (f7.s (by simp)).2]; simp [τ6]
  · have hc5' : τ5.val (regH .cdW) = σ.val (regH .cdW) := g5 _ (by simp)
    rw [f8.v (by simp), f7.v (by simp)]; simp [τ6, RW, hc5']
  · rw [v8, f7.v (by simp), f6.v (by simp), g5 _ (by simp), f7.v (by simp), f6.v (by simp), g5 _ (by simp), hnB]
  · have hw8 : ∀ u, (u = .wt ∨ ∃ i : Fin 8, i ≠ 7 ∧ u = .w i) → τ8.val (regH u) = τ3.val (regH u) := by
      intro u hu
      have h1 : u ≠ .cur := by rcases hu with rfl | ⟨i, -, rfl⟩ <;> simp
      have h2 : u ≠ .L := by rcases hu with rfl | ⟨i, -, rfl⟩ <;> simp
      have h3 : u ≠ .cdW := by rcases hu with rfl | ⟨i, -, rfl⟩ <;> simp
      have h4 : u ≠ .sk := by rcases hu with rfl | ⟨i, -, rfl⟩ <;> simp
      have h5 : u ≠ .cdB := by rcases hu with rfl | ⟨i, -, rfl⟩ <;> simp
      rw [f8.v (by simp [h1]), f7.v (by simp [h2]), f6.v (by simp [h3, h4]), f5.v (by simp [h4]),
        f4.v (by simp [h5])]
    exact ⟨fun i hi => by rw [hw8 (.w i) (Or.inr ⟨i, hi, rfl⟩)]; exact w3.1 i hi,
      by rw [hw8 .wt (Or.inl rfl)]; exact w3.2⟩
  · refine ⟨fun r => by rw [g8 _ (by simp)]; exact hz.f r, fun u hu => ?_⟩
    by_cases hs : u = .sk
    · subst hs; rw [f8.v (by simp), f7.v (by simp)]; simp [τ6]
    · rw [g8 u (by simp [hs]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; simp [zl] at hu))]; exact hz.z u hu
  · refine ⟨fun y hy => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      by_cases hD' : y = sD
      · subst hD'
        rw [(f8.s (by simp)).1, (f8.s (by simp)).2, (f7.s (by simp)).1, (f7.s (by simp)).2,
          (f6.s (by simp)).1, (f6.s (by simp)).2, (f5.s (by simp)).1, (f5.s (by simp)).2]
        refine ⟨?_, ?_⟩
        · simp only [τ4, WState.seth_st, WState.setv_st]; rw [st3, (s2 sD).1]
        · rw [hDh4, hDh]
      · rw [(hs8 y hy.1 hD').1, (hs8 y hy.1 hD').2, (f3.s (by simp [hD', hy.2])).1, (f3.s (by simp [hD', hy.2])).2]
        exact s2 y
    · obtain ⟨u, rfl⟩ := regH_surj r
      have hu : u ∉ [HReg.cdW, .w 7, .cur] := fun m => hr (List.mem_map_of_mem m)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
      by_cases h1 : u = .L
      · subst h1; rw [f8.v (by simp), z7, hL0]
      · by_cases h2 : u = .tC
        · subst h2; rw [f8.v (by simp), f7.v (by simp), f6.v (by simp), f5.v (by simp), f4.v (by simp), tc3, htC]
        · by_cases h3 : u = .cdB
          · subst h3; rw [f8.v (by simp), f7.v (by simp), f6.v (by simp), f5.v (by simp)]; simp [τ4, hcdB]
          · by_cases h4 : u = .sk
            · subst h4; rw [f8.v (by simp), f7.v (by simp)]; simp [τ6]; exact (hz.z _ (by simp [zl])).symm
            · exact g8 u (by simp [h1, h2, h3, h4, hu.1, hu.2.1, hu.2.2])
    · rw [f8.2.2, f7.2.2, f6.2.2, f5.2.2, f4.2.2, f3.2.2, f2.2.2]; simp [σ1]
  · rw [(f8.s (by simp)).1, (f7.s (by simp)).1]; simp only [τ6, WState.setv_st, WState.seth_st]
    rw [(f5.s (by simp)).1, (f4.s (by simp)).1, (f3.s (by simp)).1, (s2 sW).1]

end NearCubicGates.Close.Succinct.SubstMachine
