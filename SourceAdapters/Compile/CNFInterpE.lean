import SourceAdapters.Compile.CNFInterpD

/-!
# Token interpreter, part E: wire references and saves

`wirTokP` pushes entry `k` of the current wire map (`0` past its end), `saveTokP` moves the top of the stack to
the next wire map; they realize `RS.step` on `.wir k` and `.save` (`wirTokP_spec`, `saveTokP_spec`).
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

/-- `IR` after a change of the stack only (plus the cursor of the wire map). -/
theorem IR.stkOnly {n k : ℕ} {S : RS} {a b : DS VV MM} (h : IR n k S a) (st : List ℕ) (hst : StkRel b st)
    (hvst : ∀ x ∈ st, x ≤ k + 1) (hSK : (b.ram sSK).length ≤ k + 1) (hrsk : b.rc sSK ≤ (b.ram sSK).length)
    (hram : ∀ m, m ≠ sSK → b.ram m = a.ram m) (hrc : ∀ m, m ≠ sSK → m ≠ sWM → b.rc m = a.rc m)
    (hrwm : b.rc sWM ≤ (b.ram sWM).length) (hkc : KC b)
    (hregs : ∀ y ∈ [dN, iIdx, iWl, iNc], b.env y = a.env y) :
    IR n (k + 1) { S with stk := st } b := by
  have e : ∀ y ∈ [dN, iIdx, iWl, iNc], b.env y = a.env y := hregs
  refine ⟨hkc, ?_, ?_, h.nodes, hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hSK, hrsk, ?_, hrwm, ?_, ?_, hvst, ?_, ?_⟩
  · rw [e dN (by simp), h.dn]
  · rw [e iIdx (by simp), h.idx]
  · rw [e iWl (by simp), h.wl]
  · rw [hram sWM (by decide)]; exact h.wires
  · rw [hram sWM (by decide)]; exact h.wlen
  · rw [e iNc (by simp), h.nc]
  · rw [hram sNW (by decide)]; exact h.next
  · rw [hram sNW (by decide)]; exact h.nlen
  · rw [hrc sNW (by decide) (by decide)]; exact h.rcnw
  · rw [hram sCL (by decide)]; exact h.cl
  · rw [hram sCL (by decide), hrc sCL (by decide) (by decide)]; exact h.rccl
  · rw [hram sWM (by decide)]; have := h.bwm; omega
  · rw [hram sNW (by decide)]; have := h.bnw; omega
  · show S.idx ≤ k + 1; have := h.bidx; omega
  · intro x hx; have := h.vwires x hx; omega
  · intro x hx; have := h.vnext x hx; omega

/-- Push wire `iPl` (or `0` past the end of the wire map). -/
def wirTokP : St VV MM :=
  .seq (.ite (.lt iPl iWl) (.seq (seekP sWM iPl) (.op (.rdM sWM iX))) (.op (.zero iX))) (pushP iX)

theorem wirTokP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (j : ℕ) (hp : a.env iPl = j) (hj : j ≤ k) :
    Hs C wirTokP a (a.rc sWM + a.rc sSK + 11 * k + 30) (fun d => IR n (k + 1) (S.step (.wir j)) d ∧
      (∀ m, m ≠ sSK → m ≠ sWM → d.ram m = a.ram m ∧ d.rc m = a.rc m) ∧ d.ram sWM = a.ram sWM ∧ d.ip = a.ip ∧
      d.out = a.out ∧ Fr a d irT) := by
  have hk := h.kc
  have hstkk : S.stk.length ≤ k := by have := h.stk.len; have := h.bsk; omega
  have hwlk : S.wires.length ≤ k := by have := h.wlen; have := h.bwm; omega
  have hrsk : a.rc sSK ≤ k := le_trans h.rsk h.bsk
  have hval : S.wires.getD j 0 ≤ k := by
    rw [List.getD_eq_getElem?_getD]
    cases e : S.wires[j]? with
    | none => simp
    | some v => have := h.vwires v (List.mem_of_getElem? e); simpa using this
  -- the looked-up value
  have hlook : Hs C (.ite (.lt iPl iWl) (.seq (seekP sWM iPl) (.op (.rdM sWM iX))) (.op (.zero iX))) a
      (a.rc sWM + 5 * k + 9) (fun b => b.env iX = S.wires.getD j 0 ∧ b.ram = a.ram ∧ b.rc sWM ≤ (b.ram sWM).length ∧
        (∀ m, m ≠ sWM → b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [iS, iJ, iX]) := by
    refine Hs.ite (show iPl ≠ iWl by decide) (fun hc => ?_) (fun hc => ?_)
    · have hlt : j < S.wires.length := by simpa [Cnd.eval, hp, h.wl] using hc
      refine Hs.seqc (t1 := a.rc sWM + 5 * a.env iPl + 6) (t2 := 1) (seekP_spec (C := C) sWM iPl (by decide) a
        (by rw [hp]; have := h.wlen; omega) (by rw [hp]; omega)) (fun b hb => ?_) (by rw [hp]; omega)
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
      rw [hp] at b1
      refine Hs.op (OpEx.rdM sWM iX b (by rw [b1, b2]; have := h.wlen; omega)) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [DS.adv, DS.set_env_self, b1, b2]
        rw [← h.wires, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hlt]
      · simp [DS.adv, b2]
      · simp only [DS.adv, DS.set_ram, DS.set_rc, Function.update_self, b1, b2]; have := h.wlen; omega
      · intro m hm; simp only [DS.adv, DS.set_rc, Function.update_of_ne hm]; exact b3 m hm
      · simp [DS.adv, b4]
      · simp [DS.adv, b5]
      · intro y hy
        have hy' : y ≠ iS ∧ y ≠ iJ ∧ y ≠ iX := by simpa using hy
        simp only [DS.adv, DS.set]
        rw [Function.update_of_ne hy'.2.2, b6 y (by simp [hy'.1, hy'.2.1])]
    · have hge : S.wires.length ≤ j := by simpa [Cnd.eval, hp, h.wl] using hc
      refine Hs.mono (hs_zero C iX a) (by omega) ?_
      rintro b rfl
      refine ⟨?_, rfl, by simpa using h.rwm, fun _ _ => rfl, rfl, rfl, by fr_tac⟩
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
  refine Hs.seqc (t1 := a.rc sWM + 5 * k + 9) (t2 := a.rc sSK + 5 * k + 10) hlook (fun b hb => ?_) (by omega)
  obtain ⟨e1, r1, w1, c1', i1, o1, f1⟩ := hb
  have hst1 : StkRel b S.stk := ⟨by rw [f1 iSp (by decide)]; exact h.stk.sp, by rw [r1]; exact h.stk.take,
    by rw [r1]; exact h.stk.len⟩
  refine Hs.mono (pushP_spec (C := C) iX (by decide) b S.stk hst1 (by omega)) (by rw [c1' sSK (by decide)]; omega) ?_
  rintro d ⟨s2, l2, c2', u2, i2, o2, f2⟩
  rw [e1] at s2
  have hram : ∀ m, m ≠ sSK → d.ram m = a.ram m := fun m hm => by rw [(u2 m hm).1, r1]
  refine ⟨h.stkOnly _ s2 ?_ ?_ ?_ hram ?_ ?_ ((hk.of_fr f1 (by decide)).of_fr f2 (by decide)) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · omega
    · have := h.vstk x hx; omega
  · rw [r1] at l2; have := h.bsk; omega
  · rw [c2']; have := s2.len; simpa using this
  · intro m h1 h2; rw [(u2 m h1).2, c1' m h2]
  · rw [(u2 sWM (by decide)).2, hram sWM (by decide)]; rw [r1] at w1; exact w1
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;>
      · rw [f2 _ (by decide), f1 _ (by decide)]
  · intro m h1 h2; exact ⟨hram m h1, by rw [(u2 m h1).2, c1' m h2]⟩
  · exact hram sWM (by decide)
  · rw [i2, i1]
  · rw [o2, o1]
  · intro y hy
    simp only [irT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f2 y (by simp; tauto), f1 y (by simp; tauto)]

/-- Move the top of the stack to the next wire map. -/
def saveTokP : St VV MM := .seq (popP iX) (.seq (.op (.wrM sNW iX)) (.op (.inc iNc)))

theorem saveTokP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd) :
    Hs C saveTokP a (a.rc sSK + 5 * k + 14) (fun d => IR n (k + 1) (S.step .save) d ∧
      (∀ m, m ≠ sSK → m ≠ sNW → d.ram m = a.ram m ∧ d.rc m = a.rc m) ∧ d.ip = a.ip ∧ d.out = a.out ∧
      Fr a d irT) := by
  have hk := h.kc
  have hstkk : S.stk.length ≤ k := by have := h.stk.len; have := h.bsk; omega
  have hnk : S.next.length ≤ k := by have := h.nlen; have := h.bnw; omega
  have hxk : (popS S.stk).1 ≤ k := popS_le _ _ h.vstk
  refine Hs.seqc (t1 := a.rc sSK + 5 * S.stk.length + 10) (t2 := 3)
    (popP_spec (C := C) iX (by decide) a S.stk h.stk hk.z hk.one (by omega)) (fun b hb => ?_) (by omega)
  obtain ⟨e1, s1, r1, q1, c1', i1, o1, f1⟩ := hb
  have hnc : b.rc sNW = S.next.length := by rw [c1' sNW (by decide), h.rcnw]
  have hnl : S.next.length ≤ (b.ram sNW).length := by rw [r1]; exact h.nlen
  refine Hs.seqc (t1 := 1) (t2 := 1) (hs_wrM C sNW iX b (by rw [hnc]; exact hnl)) (fun d hd => ?_) (by omega)
  subst hd
  have bnc : (b.put sNW (b.env iX)).env iNc = S.next.length := by
    simp only [DS.put]; rw [f1 iNc (by decide), h.nc]
  refine Hs.op (OpEx.inc iNc _ (by rw [bnc]; omega)) ?_
  have k1 : KC b := hk.of_fr f1 (by decide)
  have hput : ((b.put sNW (b.env iX)).set iNc ((b.put sNW (b.env iX)).env iNc + 1)).ram sNW =
      putAt (a.ram sNW) S.next.length (popS S.stk).1 := by
    simp only [DS.set_ram, DS.put, Function.update_self]; rw [hnc, r1, e1]
  have hram : ∀ m, m ≠ sNW → ((b.put sNW (b.env iX)).set iNc ((b.put sNW (b.env iX)).env iNc + 1)).ram m =
      a.ram m := fun m hm => by simp only [DS.set_ram, DS.put, Function.update_of_ne hm]; rw [r1]
  have kfin : KC ((b.put sNW (b.env iX)).set iNc ((b.put sNW (b.env iX)).env iNc + 1)) := by
    refine k1.of_fr (T := [iNc]) ?_ (by decide)
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [DS.set, DS.put, Function.update_apply, hy]
  refine ⟨⟨kfin, ?_, ?_, h.nodes, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [DS.set, DS.put]; rw [Function.update_of_ne (by decide), f1 dN (by decide), h.dn]
  · simp only [DS.set, DS.put]; rw [Function.update_of_ne (by decide), f1 iIdx (by decide), h.idx]; rfl
  · simp only [DS.set, DS.put]; rw [Function.update_of_ne (by decide)]; exact s1.sp
  · rw [hram sSK (by decide), ← r1]; exact s1.take
  · rw [hram sSK (by decide), ← r1]; exact s1.len
  · simp only [DS.set, DS.put]; rw [Function.update_of_ne (by decide), f1 iWl (by decide), h.wl]; rfl
  · rw [hram sWM (by decide)]; exact h.wires
  · rw [hram sWM (by decide)]; exact h.wlen
  · rw [DS.set_env_self, bnc]; simp [RS.step]
  · simp only [RS.step, List.length_append, List.length_singleton]
    rw [hput, take_putAt _ _ _ h.nlen, h.next]
  · simp only [RS.step, List.length_append, List.length_singleton]
    rw [hput, putAt_length _ _ _ h.nlen]; omega
  · simp only [DS.set_rc, DS.put, Function.update_self, RS.step, List.length_append, List.length_singleton]
    rw [hnc]
  · rw [hram sCL (by decide)]; exact h.cl
  · rw [hram sCL (by decide)]; simp only [DS.set_rc, DS.put, Function.update_of_ne (show sCL ≠ sNW by decide)]
    rw [c1' sCL (by decide)]; exact h.rccl
  · rw [hram sSK (by decide)]; have := h.bsk; omega
  · rw [hram sSK (by decide)]; simp only [DS.set_rc, DS.put, Function.update_of_ne (show sSK ≠ sNW by decide)]
    have := s1.len; rw [r1] at this
    have := h.rsk; have := h.stk.len; have := popS_len S.stk; omega
  · rw [hram sWM (by decide)]; have := h.bwm; omega
  · rw [hram sWM (by decide)]; simp only [DS.set_rc, DS.put, Function.update_of_ne (show sWM ≠ sNW by decide)]
    rw [c1' sWM (by decide)]; exact h.rwm
  · rw [hput, putAt_length _ _ _ h.nlen]; have := h.bnw; omega
  · show S.idx ≤ k + 1; have := h.bidx; omega
  · intro x hx; have := h.vstk x (popS_mem _ _ hx); omega
  · intro x hx; have := h.vwires x hx; omega
  · intro x hx
    simp only [RS.step, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have := h.vnext x hx; omega
    · omega
  · intro m h1 h2
    refine ⟨hram m h2, ?_⟩
    simp only [DS.set_rc, DS.put, Function.update_of_ne h2]; exact c1' m h1
  · simp [DS.put, i1]
  · simp [DS.put, o1]
  · intro y hy
    simp only [irT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [DS.set, DS.put]
    rw [Function.update_of_ne hy.2.2.2.1, f1 y (by simp; tauto)]

end NearCubicGates.Adapters.Compile
