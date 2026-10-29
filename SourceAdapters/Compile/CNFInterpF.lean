import SourceAdapters.Compile.CNFInterpE

/-!
# Token interpreter, part F: the swap token

`swapTokP` copies the next wire map (`sNW`, `iNc` entries) into the current wire map (`sWM`), sets `iWl := iNc`
and empties the next wire map: `RS.step` on `.swap`.
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

/-- Copy the next wire map into the current one and empty it. -/
def copyLoopP : St VV MM :=
  .loop (.lt iS iNc) (.seq (.op (.rdM sNW iX)) (.seq (.op (.wrM sWM iX)) (.op (.inc iS))))

def swapTokP : St VV MM :=
  .seq (.op (.rwM sNW)) (.seq (.op (.rwM sWM)) (.seq (.op (.zero iS)) (.seq copyLoopP
    (.seq (.op (.copy iWl iNc)) (.seq (.op (.rwM sNW)) (.op (.zero iNc)))))))

/-- One pass of the copy loop. -/
theorem copyBody_spec (a b : DS VV MM) (N i : ℕ) (hi : i < N) (hN : N ≤ (a.ram sNW).length)
    (b1 : b.env iS = i) (b2 : b.rc sNW = i) (b3 : b.rc sWM = i) (b4 : b.ram sNW = a.ram sNW)
    (b5 : (b.ram sWM).take i = (a.ram sNW).take i) (b6 : i ≤ (b.ram sWM).length) (hW : i + 1 < 2 ^ C.Wd) :
    Hs C (.seq (.op (.rdM sNW iX)) (.seq (.op (.wrM sWM iX)) (.op (.inc iS)))) b 5 (fun d =>
      d.env iS = i + 1 ∧ d.rc sNW = i + 1 ∧ d.rc sWM = i + 1 ∧ d.ram sNW = a.ram sNW ∧
      (d.ram sWM).take (i + 1) = (a.ram sNW).take (i + 1) ∧ i + 1 ≤ (d.ram sWM).length ∧
      (d.ram sWM).length ≤ max (b.ram sWM).length (i + 1) ∧ (∀ m, m ≠ sWM → d.ram m = b.ram m) ∧
      (∀ m, m ≠ sWM → m ≠ sNW → d.rc m = b.rc m) ∧ d.ip = b.ip ∧ d.out = b.out ∧ Fr b d [iS, iX]) := by
  set v := (a.ram sNW).getD i 0 with hv
  refine Hs.seqc (t1 := 1) (t2 := 3) (hs_rdM C sNW iX b (by rw [b2, b4]; omega)) (fun d1 e1 => ?_) (by omega)
  subst e1
  have d1v : ((b.set iX ((b.ram sNW).getD (b.rc sNW) 0)).adv sNW).env iX = v := by
    simp [DS.adv, DS.set, b2, b4, hv]
  have d1w : ((b.set iX ((b.ram sNW).getD (b.rc sNW) 0)).adv sNW).rc sWM = i := by
    simp [DS.adv, Function.update_of_ne (show sWM ≠ sNW by decide), b3]
  have d1r : ((b.set iX ((b.ram sNW).getD (b.rc sNW) 0)).adv sNW).ram = b.ram := by simp [DS.adv]
  have d1s : ((b.set iX ((b.ram sNW).getD (b.rc sNW) 0)).adv sNW).env iS = i := by
    simp [DS.adv, DS.set, Function.update_of_ne (show iS ≠ iX by decide), b1]
  set d1 := (b.set iX ((b.ram sNW).getD (b.rc sNW) 0)).adv sNW with hd1
  refine Hs.seqc (t1 := 1) (t2 := 1) (hs_wrM C sWM iX d1 (by rw [d1w, d1r]; exact b6)) (fun d2 e2 => ?_) (by omega)
  subst e2
  have d2s : (d1.put sWM (d1.env iX)).env iS = i := by simp [DS.put, d1s]
  refine Hs.op (OpEx.inc iS _ (by rw [d2s]; omega)) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [DS.set_env_self, d2s]
  · simp [DS.put, hd1, DS.adv, b2, Function.update_of_ne (show sNW ≠ sWM by decide)]
  · simp [DS.put, d1w]
  · simp [DS.put, Function.update_of_ne (show sNW ≠ sWM by decide), d1r, b4]
  · simp only [DS.set_ram, DS.put, Function.update_self, d1w, d1r, d1v]
    rw [take_putAt _ _ _ b6, b5, List.take_add_one]
    congr 1
    have hlt : i < (a.ram sNW).length := by omega
    simp [hv, List.getD_eq_getElem?_getD, hlt]
  · simp only [DS.set_ram, DS.put, Function.update_self, d1w, d1r]; rw [putAt_length _ _ _ b6]; omega
  · simp only [DS.set_ram, DS.put, Function.update_self, d1w, d1r]; rw [putAt_length _ _ _ b6]
  · intro m hm; simp [DS.put, Function.update_of_ne hm, d1r]
  · intro m h1 h2; simp [DS.put, hd1, DS.adv, Function.update_of_ne h1, Function.update_of_ne h2]
  · simp [DS.put, hd1, DS.adv]
  · simp [DS.put, hd1, DS.adv]
  · intro y hy
    have hy' : y ≠ iS ∧ y ≠ iX := by simpa using hy
    simp [DS.set, DS.put, hd1, DS.adv, Function.update_apply, hy'.1, hy'.2]

theorem swapTokP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd) :
    Hs C swapTokP a (a.rc sWM + 10 * k + 20) (fun d => IR n (k + 1) (S.step .swap) d ∧
      (∀ m, m ≠ sWM → m ≠ sNW → d.ram m = a.ram m ∧ d.rc m = a.rc m) ∧ d.ip = a.ip ∧ d.out = a.out ∧
      Fr a d irT) := by
  have hk := h.kc
  have hnk : S.next.length ≤ k := by have := h.nlen; have := h.bnw; omega
  have hNl := h.nlen
  let I : ℕ → DS VV MM → Prop := fun i b => b.env iS = i ∧ b.rc sNW = i ∧ b.rc sWM = i ∧ b.ram sNW = a.ram sNW ∧
    (b.ram sWM).take i = (a.ram sNW).take i ∧ i ≤ (b.ram sWM).length ∧
    (b.ram sWM).length ≤ max (a.ram sWM).length i ∧ (∀ m, m ≠ sWM → b.ram m = a.ram m) ∧
    (∀ m, m ≠ sWM → m ≠ sNW → b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [iS, iX]
  have hloop := Hs.loopN (C := C) (c := .lt iS iNc)
    (s := .seq (.op (.rdM sNW iX)) (.seq (.op (.wrM sWM iX)) (.op (.inc iS)))) (show iS ≠ iNc by decide) I
    S.next.length 5
    (fun i hi b hb => by
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hb
      have bnc : b.env iNc = S.next.length := by rw [b12 iNc (by decide), h.nc]
      refine ⟨by simp [Cnd.eval, b1, bnc, hi], ?_⟩
      refine Hs.mono (copyBody_spec a b S.next.length i hi hNl b1 b2 b3 b4 b5 b6 (by omega)) le_rfl ?_
      rintro d ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩
      refine ⟨d1, d2, d3, d4, d5, d6, by omega, fun m hm => by rw [d8 m hm, b8 m hm],
        fun m h1 h2 => by rw [d9 m h1 h2, b9 m h1 h2], by rw [d10, b10], by rw [d11, b11], b12.trans d12⟩)
    (fun b hb => by
      obtain ⟨b1, _, _, _, _, _, _, _, _, _, _, b12⟩ := hb
      simp [Cnd.eval, b1, b12 iNc (by decide), h.nc])
  refine Hs.seqc (t1 := S.next.length + 1) (t2 := a.rc sWM + 8 * S.next.length + 12)
    (Hs.mono (hs_rwM C sNW a) (by rw [h.rcnw]) (fun b hb => hb)) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.seqc (t1 := a.rc sWM + 1) (t2 := 8 * S.next.length + 10)
    (Hs.mono (hs_rwM C sWM _) (by simp [DS.rew, Function.update_of_ne (show sWM ≠ sNW by decide)])
      (fun b hb => hb)) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.seqc (t1 := 1) (t2 := 8 * S.next.length + 8) (hs_zero C iS _) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.seqc (t1 := S.next.length * (5 + 2) + 2) (t2 := S.next.length + 5) (hloop _ ⟨by simp,
    by simp [DS.rew, Function.update_of_ne (show sNW ≠ sWM by decide)],
    by simp [DS.rew], by simp [DS.rew], by simp, by simp, by simp [DS.rew],
    fun m hm => by simp [DS.rew], fun m h1 h2 => by simp [DS.rew, Function.update_of_ne h1, Function.update_of_ne h2],
    by simp [DS.rew], by simp [DS.rew], fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [DS.set, DS.rew, Function.update_apply, hy]⟩) (fun b hb => ?_) (by omega)
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hb
  have bnc : b.env iNc = S.next.length := by rw [b12 iNc (by decide), h.nc]
  refine Hs.seqc (t1 := 1) (t2 := S.next.length + 3) (hs_copy C iWl iNc b (by decide)) (fun d hd => ?_) (by omega)
  subst hd
  refine Hs.seqc (t1 := S.next.length + 1) (t2 := 1) (Hs.mono (hs_rwM C sNW _) (by simp [b2]) (fun d hd => hd))
    (fun d hd => ?_) (by omega)
  subst hd
  refine Hs.op (OpEx.zero iNc _) ?_
  have fz : ∀ y, y ∉ [iS, iX, iWl, iNc] → (((b.set iWl (b.env iNc)).rew sNW).set iNc 0).env y = a.env y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [DS.set, DS.rew, Function.update_apply, hy, b12 y (by simp [hy.1, hy.2.1])]
  have hkc : KC (((b.set iWl (b.env iNc)).rew sNW).set iNc 0) :=
    ⟨by rw [fz vZ (by decide), hk.z], by rw [fz v1 (by decide), hk.one], by rw [fz v2 (by decide), hk.two],
      by rw [fz kc3 (by decide), hk.k3], by rw [fz kc4 (by decide), hk.k4], by rw [fz kc5 (by decide), hk.k5],
      by rw [fz kc6 (by decide), hk.k6], by rw [fz kc7 (by decide), hk.k7], by rw [fz kc8 (by decide), hk.k8]⟩
  have hR : (((b.set iWl (b.env iNc)).rew sNW).set iNc 0).ram = b.ram := rfl
  have hRC : ∀ m, m ≠ sNW → (((b.set iWl (b.env iNc)).rew sNW).set iNc 0).rc m = b.rc m := fun m hm => by
    simp [DS.set, DS.rew, Function.update_of_ne hm]
  refine ⟨⟨hkc, ?_, ?_, h.nodes, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [fz dN (by decide), h.dn]
  · rw [fz iIdx (by decide), h.idx]; rfl
  · rw [fz iSp (by decide)]; exact h.stk.sp
  · rw [hR, b8 sSK (by decide)]; exact h.stk.take
  · rw [hR, b8 sSK (by decide)]; exact h.stk.len
  · simp [DS.set, DS.rew, bnc, RS.step, Function.update_of_ne (show iWl ≠ iNc by decide)]
  · show List.take S.next.length ((((b.set iWl (b.env iNc)).rew sNW).set iNc 0).ram sWM) = S.next
    rw [hR, b5, h.next]
  · show S.next.length ≤ ((((b.set iWl (b.env iNc)).rew sNW).set iNc 0).ram sWM).length
    rw [hR]; exact b6
  · simp [RS.step]
  · simp [RS.step]
  · simp [RS.step]
  · simp [DS.set, DS.rew, RS.step]
  · rw [hR, b8 sCL (by decide)]; exact h.cl
  · rw [hR, hRC sCL (by decide), b8 sCL (by decide), b9 sCL (by decide) (by decide)]; exact h.rccl
  · rw [hR, b8 sSK (by decide)]; have := h.bsk; omega
  · rw [hR, hRC sSK (by decide), b8 sSK (by decide), b9 sSK (by decide) (by decide)]; exact h.rsk
  · rw [hR]; have := h.bwm; omega
  · rw [hR, hRC sWM (by decide), b3]; exact b6
  · rw [hR, b4]; have := h.bnw; omega
  · show S.idx ≤ k + 1; have := h.bidx; omega
  · intro x hx; have := h.vstk x hx; omega
  · intro x hx; have := h.vnext x hx; omega
  · intro x hx; simp [RS.step] at hx
  · intro m h1 h2
    exact ⟨by rw [hR, b8 m h1], by rw [hRC m h2, b9 m h1 h2]⟩
  · simp [DS.set, DS.rew, b10]
  · simp [DS.set, DS.rew, b11]
  · intro y hy
    simp only [irT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    exact fz y (by simp; tauto)

end NearCubicGates.Adapters.Compile
