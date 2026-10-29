import Proof.Gates.Succinct.SubstitutionCopyLoop

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

theorem cp_len_le (fl : List Bool) (args : List ℕ) (n1 ob off S : ℕ) (B : BooleanCircuit q) (t : ℕ)
    (htn : t ≤ B.nodes.length) (hnB : B.nodes.length ≤ S) (hargs : ∀ x ∈ args, x ≤ S) (hn1 : n1 ≤ S)
    (hob : ob ≤ S) (hoff : off ≤ (S + 2) ^ 2) :
    (((B.nodes.take t).map (cpNode fl args n1 ob off)).flatMap PCPPRequestNodeSchema.native).length ≤
      t * (12 * (S + 2) ^ 2 + 40) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, List.map_append,
      List.flatMap_append, List.length_append]
    have hw := B.wellFormed ⟨t, by omega⟩
    simp only [List.get_eq_getElem] at hw
    have := native_len_le (cpNode fl args n1 ob off B.nodes[t]) (2 * (S + 2) ^ 2 + 4)
      (cpNode_fields_le fl args n1 ob off S B.nodes[t] t hw (by omega) hargs hn1 hob hoff)
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have := ih (by omega)
    rw [Nat.succ_mul]; omega

set_option maxHeartbeats 1600000 in
/-- **The copy of `B`** (`sec:gadget-machine`, an oracle gate's image). -/
theorem copyLoop_spec (cap : ℕ) (B : BooleanCircuit q) (σ : WState 4 nrH) (hz : CBZ σ)
    (htag : σ.val (regH .tagB) = 0) (hD : σ.st sD = PCPPNative.descriptor B) (hDh : σ.sh sD = pB B)
    (hcd : σ.val (regH .cdB) = 0) (htC : σ.val (regH .tC) = B.nodes.length)
    (preA restA : List Bool) (args : List ℕ)
    (hA : σ.st sW = preA ++ args.flatMap natWord ++ restA) (hAh : σ.sh sW = preA.length)
    (hL : σ.val (regH .L) = args.length) (fl : List Bool) (hF : σ.st sF = fl) (hFh : σ.sh sF = 0)
    (hn1 : σ.val (regH .nB1) = B.nodes.length - 1) (hob : σ.val (regH .oB) = B.output.val) (S : ℕ)
    (hnB : B.nodes.length ≤ S) (hq : q ≤ S) (hlS : args.length ≤ S) (hAS : ∀ x ∈ args, x ≤ S)
    (hwS : (args.flatMap natWord).length ≤ S) (hcur : σ.val (regH .cur) ≤ (S + 2) ^ 2)
    (out : List Bool) (hout : OutOK σ out) (hcl : WClean σ)
    (hcap : (PCPPNative.descriptor B).length + 2 * out.length + 2 * (S * (12 * (S + 2) ^ 2 + 40)) +
      2000 * (S + 2) ^ 2 ≤ cap) :
    ∃ τ, WExec cap (.whr (regH .tC) (.seq (.dec (regH .tC)) copyBody)) σ τ (B.nodes.length * (cpIter S + 4) + 1) ∧
      OutOK τ (out ++ (B.nodes.map (cpNode fl args (B.nodes.length - 1) B.output.val (σ.val (regH .cur)))).flatMap
        PCPPRequestNodeSchema.native) ∧
      WClean τ ∧ CBZ τ ∧ τ.val (regH .tagB) = 0 ∧ τ.val (regH .tC) = 0 ∧
      τ.sh sD = pB B + lenB B B.nodes.length ∧ τ.val (regH .cdB) = lenB B B.nodes.length ∧
      Fr σ τ [sD, sO] [.cdB, .w 7, .tC] ∧ τ.st sD = σ.st sD := by
  set cp := cpNode fl args (B.nodes.length - 1) B.output.val (σ.val (regH .cur)) with hcp
  have hlenB : ∀ t, lenB B t ≤ (PCPPNative.descriptor B).length := by
    intro t
    unfold lenB
    rw [PCPPNative.descriptor_eq]
    simp only [List.length_append]
    have : ((B.nodes.take t).flatMap PCPPRequestNodeSchema.native).length ≤
        (B.nodes.flatMap PCPPRequestNodeSchema.native).length := by
      conv_rhs => rw [← List.take_append_drop t B.nodes]
      rw [List.flatMap_append, List.length_append]; omega
    omega
  let Inv : ℕ → WState 4 nrH → Prop := fun t τ =>
    CBZ τ ∧ τ.val (regH .tagB) = 0 ∧ τ.st sD = PCPPNative.descriptor B ∧ τ.sh sD = pB B + lenB B t ∧
      τ.val (regH .cdB) = lenB B t ∧
      OutOK τ (out ++ ((B.nodes.take t).map cp).flatMap PCPPRequestNodeSchema.native) ∧ WClean τ ∧
      Fr σ τ [sD, sO] [.cdB, .w 7, .tC]
  have hI0 : Inv 0 σ := ⟨hz, htag, hD, by simp [hDh, lenB], by simp [hcd, lenB], by simpa using hout, hcl,
    fr_refl _ _ _⟩
  obtain ⟨τ, e, hI, hτ⟩ := UnionMachine.Round.wloopE cap (regH .tC) copyBody (cpIter S) B.nodes.length Inv
    (by have : B.nodes.length ≤ S * (12 * (S + 2) ^ 2 + 40) := by nlinarith
        omega)
    (fun t ht τ hτI hτC => by
      obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := hτI
      set τ' := τ.setv (regH .tC) (B.nodes.length - t - 1) with hτ'
      have g' : ∀ u, u ∉ [HReg.cdB, .w 7, .tC] → τ'.val (regH u) = σ.val (regH u) := fun u hu => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
        simp only [τ', WState.setv_val, Function.update_apply, regH_eq_iff, hu.2.2, if_false]
        exact z8.v (by simp [hu.1, hu.2.1, hu.2.2])
      have s' : ∀ i, i ≠ sD → i ≠ sO → τ'.st i = σ.st i ∧ τ'.sh i = σ.sh i := fun i h1 h2 => by
        simp only [τ', WState.setv_st, WState.setv_sh]; exact z8.s (by simp [h1, h2])
      have hlo := cp_len_le fl args (B.nodes.length - 1) B.output.val (σ.val (regH .cur)) S B t (by omega) hnB hAS
        (by omega) (by have := B.output.isLt; omega) hcur
      have htS : t * (12 * (S + 2) ^ 2 + 40) ≤ S * (12 * (S + 2) ^ 2 + 40) := Nat.mul_le_mul_right _ (by omega)
      obtain ⟨τ'', e', o'', w'', zz'', sh'', cd'', f'', st''⟩ := copyStep cap B t ht τ'
        ⟨fun r => by simp [τ', z1.f r], fun u hu => by
          simp only [τ', WState.setv_val, Function.update_apply, regH_eq_iff]
          split_ifs with h; · subst h; simp [zl] at hu
          exact z1.z u hu⟩
        (by simp [τ', z2]) (by simp [τ', z3]) (by simp [τ', z4])
        preA restA args (by rw [(s' sW (by simp) (by simp)).1, hA]) (by rw [(s' sW (by simp) (by simp)).2, hAh])
        (by rw [g' _ (by simp), hL]) fl (by rw [(s' sF (by simp) (by simp)).1, hF])
        (by rw [(s' sF (by simp) (by simp)).2, hFh]) (by rw [g' _ (by simp), hn1]) (by rw [g' _ (by simp), hob]) S hnB
        hq hlS hAS hwS (by rw [g' _ (by simp)]; exact hcur)
        (out ++ ((B.nodes.take t).map cp).flatMap PCPPRequestNodeSchema.native)
        ⟨by simp [τ', z6.1], by simp [τ', z6.2.1], by simp [τ', z6.2.2]⟩
        ⟨fun i hi => by simp [τ', z7.1 i hi], by simp [τ', z7.2]⟩
        (by simp only [τ', WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]
            rw [z5]; have := hlenB t; simp only [List.length_append]; rw [← hcp] at hlo; omega)
      refine ⟨τ'', e', ⟨zz'', ?_, ?_, ?_, ?_, ?_, w'', ?_⟩, ?_⟩
      · rw [f''.v (by simp)]; simp [τ', z2]
      · rw [st'']; simp [τ', z3]
      · rw [sh'']
      · rw [cd'']; simp only [τ', WState.setv_val, Function.update_apply, regH_eq_iff, reduceCtorEq, if_false]
        rw [z5, lenB_succ B t ht]
      · rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.map_append,
          List.flatMap_append, ← List.append_assoc]
        rw [g' _ (by simp)] at o''
        simpa [cp] using o''
      · have := z8.trans' ((fr_setv τ .tC _).trans' f'')
        exact this.mono (by intro x hx; simp at hx ⊢; tauto) (by intro u hu; simp at hu ⊢; tauto)
      · rw [f''.v (by simp)]; simp [τ'])
    σ hI0 htC
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := hI
  refine ⟨τ, e, by simpa using z6, z7, z1, z2, hτ, z4, z5, z8, ?_⟩
  rw [z3, hD]

end NearCubicGates.Close.Succinct.SubstMachine
