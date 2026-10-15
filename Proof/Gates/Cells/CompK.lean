import Proof.Gates.Cells.CompBase

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces.Formats

variable {V M : ℕ}

/-! ## Reading a frame -/

theorem frame_len (u : List Bool) : (frame u).length = 2 * u.length + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [frame, ih]; ring

theorem frame_read (w : List Bool) (q : ℕ) :
    readTapeBit (frame w) q = if q % 2 = 0 then decide (q / 2 < w.length) else w.getD (q / 2) false := by
  induction w generalizing q with
  | nil =>
    unfold readTapeBit; rcases q with _ | q
    · simp [frame]
    · simp [frame, List.getD_eq_getElem?_getD]
  | cons b w ih =>
    unfold readTapeBit
    rcases q with _ | _ | q
    · simp [frame]
    · simp [frame]
    · have := ih q
      unfold readTapeBit at this
      simp only [frame, List.getD_cons_succ, List.length_cons] at this ⊢
      rw [this]
      have h1 : (q + 2) % 2 = q % 2 := by omega
      have h2 : (q + 2) / 2 = q / 2 + 1 := by omega
      rw [h1, h2]
      split_ifs <;> simp

/-- Appending one framed bit: three writes at the final marker. -/
theorem rdEq_frame_snoc {l w : List Bool} (h : RdEq l (frame w)) (b : Bool) :
    RdEq (writeTapeBit (writeTapeBit (writeTapeBit l (2 * w.length) true) (2 * w.length + 1) b)
      (2 * w.length + 2) false) (frame (w ++ [b])) := by
  intro q
  rw [readTapeBit_write, readTapeBit_write, readTapeBit_write, h q, frame_read, frame_read]
  simp only [List.length_append, List.length_singleton]
  by_cases h2 : q = 2 * w.length + 2
  · subst h2; simp
  by_cases h1 : q = 2 * w.length + 1
  · subst h1
    have e1 : (2 * w.length + 1) % 2 = 1 := by omega
    have e2 : (2 * w.length + 1) / 2 = w.length := by omega
    simp [e1, e2, List.getD_eq_getElem?_getD]
  by_cases h0 : q = 2 * w.length
  · subst h0; simp
  rw [if_neg h2, if_neg h1, if_neg h0]
  split_ifs with hq
  · simp only [decide_eq_decide]; omega
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    by_cases hlt : q / 2 < w.length
    · rw [List.getElem?_append_left hlt]
    · have : w.length < q / 2 := by omega
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

section Map
variable {t : ℕ}

def kmap (o : Fin t) (j : Fin t) : Fin (NS M t V + 1) :=
  if j.val = 0 then sKI else if j = o then sKO else sT j

theorem kmap_inj (o : Fin t) : Function.Injective (kmap (M := M) (V := V) o) := by
  intro i j hij
  unfold kmap at hij
  by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
  · exact Fin.ext (by omega)
  · rw [if_pos hi0, if_neg hj0] at hij
    split_ifs at hij <;> (have := congrArg Fin.val hij; simp at this; try omega)
  · rw [if_neg hi0, if_pos hj0] at hij
    split_ifs at hij <;> (have := congrArg Fin.val hij; simp at this; try omega)
  · rw [if_neg hi0, if_neg hj0] at hij
    by_cases hio : i = o <;> by_cases hjo : j = o
    · rw [hio, hjo]
    · rw [if_pos hio, if_neg hjo] at hij; have := congrArg Fin.val hij; simp at this; omega
    · rw [if_neg hio, if_pos hjo] at hij; have := congrArg Fin.val hij; simp at this; omega
    · rw [if_neg hio, if_neg hjo] at hij; have := congrArg Fin.val hij; simp at this; exact Fin.ext (by omega)

/-- Streams outside the image of `kmap`. -/
theorem kmap_ne (o : Fin t) (i : Fin (NS M t V + 1))
    (hi : i.val ≠ 3 ∧ i.val ≠ 4 ∧ (i.val < 8 + 2 * M ∨ 8 + 2 * M + t ≤ i.val)) :
    ∀ j, kmap (M := M) (V := V) o j ≠ i := by
  intro j e
  unfold kmap at e
  split_ifs at e <;> (subst e; simp at hi; try omega)

def kclear (o : Fin t) : List (Fin (NS M t V + 1)) :=
  sKI :: ((List.finRange t).filter fun j => j.val ≠ 0 ∧ j ≠ o).map sT

theorem kclear_nodup (o : Fin t) : (kclear (M := M) (V := V) o).Nodup := by
  unfold kclear
  refine List.nodup_cons.2 ⟨?_, ?_⟩
  · simp only [List.mem_map, List.mem_filter, not_exists, not_and]
    intro j _ e; have := congrArg Fin.val e; simp at this; omega
  · refine List.Nodup.map (fun i j e => ?_) ((List.nodup_finRange t).filter _)
    have := congrArg Fin.val e; simp at this; exact Fin.ext (by omega)

end Map

section Transport
variable {C : Ctx} {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)}

theorem Enc.setKI (h : Enc C a σ) (w l : List Bool) (hl : RdEq l (frame w)) :
    Enc C { a with kin := w } (((σ.sets sKI l).seth sKI (2 * w.length)).setv rKI (2 * w.length)) where
  inS := by keep h.inS
  inH := by keep h.inH
  inR := by keep h.inR
  outS := by keep h.outS
  outH := by keep h.outH
  outR := by keep h.outR
  zero := ⟨by keep h.zero.1, by keep h.zero.2⟩
  var := fun x => ⟨by keep (h.var x).1, by keep (h.var x).2⟩
  ramS := fun m => by keep h.ramS m
  ramH := fun m => by keep h.ramH m
  ramR := fun m => by keep h.ramR m
  shL := fun m => by keep h.shL m
  shH := fun m => by keep h.shH m
  tpS := by keep h.tpS
  tpH := by keep h.tpH
  kiS := by simpa using hl
  kiH := by simp
  kiR := by simp
  koS := by keep h.koS
  koH := by keep h.koH
  koR := by keep h.koR
  scS := fun j => by keep h.scS j
  scH := fun j => by keep h.scH j
  lgS := by keep h.lgS
  lgH := by keep h.lgH
  ruS := by keep h.ruS
  ruH := by keep h.ruH
  zF := by keep h.zF
  zR := by keep h.zR
  zG := by keep h.zG
  zK := by keep h.zK
  zT := by keep h.zT
  zC1 := by keep h.zC1
  zC2 := by keep h.zC2
  cell := by keep h.cell

theorem Enc.setKC (h : Enc C a σ) (c : ℕ) :
    Enc C { a with kc := c } ((σ.seth sKO c).setv rKO c) where
  inS := by keep h.inS
  inH := by keep h.inH
  inR := by keep h.inR
  outS := by keep h.outS
  outH := by keep h.outH
  outR := by keep h.outR
  zero := ⟨by keep h.zero.1, by keep h.zero.2⟩
  var := fun x => ⟨by keep (h.var x).1, by keep (h.var x).2⟩
  ramS := fun m => by keep h.ramS m
  ramH := fun m => by keep h.ramH m
  ramR := fun m => by keep h.ramR m
  shL := fun m => by keep h.shL m
  shH := fun m => by keep h.shH m
  tpS := by keep h.tpS
  tpH := by keep h.tpH
  kiS := by keep h.kiS
  kiH := by keep h.kiH
  kiR := by keep h.kiR
  koS := by simpa using h.koS
  koH := by simp
  koR := by simp
  scS := fun j => by keep h.scS j
  scH := fun j => by keep h.scH j
  lgS := by keep h.lgS
  lgH := by keep h.lgH
  ruS := by keep h.ruS
  ruH := by keep h.ruH
  zF := by keep h.zF
  zR := by keep h.zR
  zG := by keep h.zG
  zK := by keep h.zK
  zT := by keep h.zT
  zC1 := by keep h.zC1
  zC2 := by keep h.zC2
  cell := by keep h.cell

end Transport

/-! ## `kem` and `rdK` -/

section KOps
variable (C : Ctx) (cap : ℕ) {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)}

/-- The program of `kem b`. -/
def kemP (K : Callee) (b : Bool) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (WMX.wr sKI true) (.seq (WMX.fwd sKI) (.seq (WMX.wr sKI b) (.seq (WMX.fwd sKI)
    (.seq (WMX.wr sKI false) (.seq (WMX.inc rKI) (WMX.inc rKI))))))

theorem kem_ok (he : Enc C a σ) (b : Bool) (hk : a.kin.length < C.Lk) (hcapK : 2 * C.Lk + 2 ≤ cap) :
    ∃ τ, Enc C { a with kin := a.kin ++ [b] } τ ∧ WXExec cap (kemP C.K b) σ τ (1 * KC C) := by
  have hK := KC_ge C
  set p := 2 * a.kin.length with hp
  have hh := he.kiH
  have hr := he.kiR
  have s1 := WXExec.wr cap sKI true σ
  have s2 := WXExec.fwd cap sKI (σ.sets sKI (writeTapeBit (σ.st sKI) (σ.sh sKI) true))
  set σ2 := (σ.sets sKI (writeTapeBit (σ.st sKI) (σ.sh sKI) true)).seth sKI
    ((σ.sets sKI (writeTapeBit (σ.st sKI) (σ.sh sKI) true)).sh sKI + 1) with hσ2
  have s3 := WXExec.wr cap sKI b σ2
  have s4 := WXExec.fwd cap sKI (σ2.sets sKI (writeTapeBit (σ2.st sKI) (σ2.sh sKI) b))
  set σ4 := (σ2.sets sKI (writeTapeBit (σ2.st sKI) (σ2.sh sKI) b)).seth sKI
    ((σ2.sets sKI (writeTapeBit (σ2.st sKI) (σ2.sh sKI) b)).sh sKI + 1) with hσ4
  have s5 := WXExec.wr cap sKI false σ4
  set σ5 := σ4.sets sKI (writeTapeBit (σ4.st sKI) (σ4.sh sKI) false) with hσ5
  have s6 := WXExec.inc cap rKI σ5 (by simp [hσ5, hσ4, hσ2, hr]; omega)
  have s7 := WXExec.inc cap rKI (σ5.setv rKI (σ5.val rKI + 1)) (by simp [hσ5, hσ4, hσ2, hr]; omega)
  have hl := rdEq_frame_snoc he.kiS b
  have hfin := he.setKI (a.kin ++ [b]) _ hl
  refine ⟨_, hfin, WXExec.cast cap (WXExec.seq' cap s1 (WXExec.seq' cap s2 (WXExec.seq' cap s3
    (WXExec.seq' cap s4 (WXExec.seq' cap s5 (WXExec.seq' cap s6 s7 le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
    le_rfl) ?_ (by omega)⟩
  simp only [hσ5, hσ4, hσ2, List.length_append, List.length_singleton]
  wst_eq

/-- The program of `rdK x`. -/
def rdKP (K : Callee) (x : Fin V) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (.ifs sKO (cOne x) (cZero x)) (.seq (WMX.fwd sKO) (WMX.inc rKO))

theorem rdK_ok (he : Enc C a σ) (hW : 1 ≤ C.Wd) (hcap : 2 * C.Wd + 1 ≤ cap) (x : Fin V) (hk : a.kc < a.kout.length)
    (hcapK : a.kout.length + 1 ≤ cap) :
    ∃ τ, Enc C { a.set x (bitOf a.kout a.kc) with kc := a.kc + 1 } τ ∧ WXExec cap (rdKP C.K x) σ τ (1 * KC C) := by
  have hK := KC_ge C
  have hFR := fRne (M := M)
  have hbit : wbit σ sKO = a.kout.getD a.kc false := by
    simp only [wbit]; rw [he.koH, he.koS]; rfl
  set v := bitOf a.kout a.kc with hv
  have s1 : WXExec cap (.ifs sKO (cOne x) (cZero x)) σ (σ.sets (vs x) (frame (binary C.Wd v))) (41 * C.Wd + 8) := by
    cases hb : a.kout.getD a.kc false
    · have hv0 : v = 0 := by rw [hv, bitOf, hb]; rfl
      rw [hv0]
      exact WXExec.ifsF (by rw [hbit, hb]) (WXExec.mono (BinW.zero_spec cap C.Wd (vs_ne_Z x) hFR σ _ 0 (he.var x)
        he.zero he.zF he.zR hcap) (by omega))
    · have hv1 : v = 1 := by rw [hv, bitOf, hb]; rfl
      rw [hv1]
      exact WXExec.ifsT (by rw [hbit, hb]) (BinW.one_spec cap C.Wd (vs_ne_Z x) hFR σ _ 0 (he.var x) he.zero he.zF
        he.zR hW hcap)
  set σ1 := σ.sets (vs x) (frame (binary C.Wd v))
  have s2 := WXExec.fwd cap sKO σ1
  have s3 := WXExec.inc cap rKO (σ1.seth sKO (σ1.sh sKO + 1)) (by simp [σ1, he.koR]; omega)
  have hfin := (he.setVar x v).setKC (a.kc + 1)
  refine ⟨_, hfin, WXExec.cast cap (WXExec.seq' cap s1 (WXExec.seq' cap s2 s3 le_rfl) le_rfl) ?_ (by omega)⟩
  have h1 := he.koH
  have h2 := he.koR
  simp only [σ1]
  wst_eq

end KOps

/-! ## `kcall` -/

section KCall
variable (C : Ctx) (cap : ℕ) {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)}

/-- The program of `kcall`. -/
noncomputable def kcallP (K : Callee) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (.wm (WM.rewind sKI rKI)) (.seq (.wm (WM.rewind sKO rKO)) (.seq (clearOne sKO sRU rC2)
    (.seq (WMX.machZ K.wf.program.machine (kmap K.wf.program.outputTape) sLG)
      (clearAll sRU rC2 (kclear K.wf.program.outputTape)))))

theorem rdEq_nil_frame_nil {l : List Bool} (h : RdEq l []) : RdEq l (frame []) := by
  intro q; rw [h q]; unfold readTapeBit; cases q <;> simp [frame]

theorem blank_of_rdEq {l w : List Bool} (h : RdEq l w) (m : ℕ) (hm : w.length ≤ m) :
    ∀ q, m ≤ q → readTapeBit l q = false := by
  intro q hq; rw [h q]; unfold readTapeBit; exact List.getD_eq_default _ _ (by omega)

theorem out_ne_zero : (C.K.wf.program.outputTape).val ≠ 0 := C.K.wf.program.outputFresh

theorem kmap_zero (j : Fin (TS C)) (hj : j.val = 0) :
    kmap (M := M) (V := V) C.K.wf.program.outputTape j = sKI := by simp [kmap, hj]

theorem kmap_out : kmap (M := M) (V := V) C.K.wf.program.outputTape C.K.wf.program.outputTape = sKO := by
  simp [kmap, out_ne_zero C]

theorem kmap_other (j : Fin (TS C)) (h0 : j.val ≠ 0) (ho : j ≠ C.K.wf.program.outputTape) :
    kmap (M := M) (V := V) C.K.wf.program.outputTape j = sT j := by simp [kmap, h0, ho]

theorem kcall_ok (he : Enc C a σ) (ha : Valid C a) (s : C.K.Req) (hs : a.kin = C.K.inw s)
    (hb : C.K.bud s ≤ C.Bk) (hcapR : Rk C + 2 ≤ cap) :
    ∃ τ, Enc C (a.called (C.K.outw s)) τ ∧ WXExec cap (kcallP C.K) σ τ ((1 + C.Lk + C.Bk) * KC C) := by
  set o := C.K.wf.program.outputTape with ho
  have hK3 := KC_ge3 C
  have hkin := ha.kin_le
  have hkout := ha.kout_le
  have hkc := ha.kc_le
  -- 1. rewind KI
  have r1 := wrewind_spec cap sKI rKI (2 * a.kin.length) σ he.kiR (by rw [he.kiR]; unfold Rk at hcapR; omega)
  set σ1 := (σ.setv rKI 0).seth sKI (σ.sh sKI - 2 * a.kin.length) with hσ1
  -- 2. rewind KO
  have hKOv : σ1.val rKO = a.kc := by
    simp only [hσ1, WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne (show (rKO : Fin (NR M)) ≠ rKI by lay_ne), he.koR]
  have r2 := wrewind_spec cap sKO rKO a.kc σ1 hKOv (by rw [hKOv]; unfold Rk at hcapR; omega)
  set σ2 := (σ1.setv rKO 0).seth sKO (σ1.sh sKO - a.kc) with hσ2
  have e2sh : ∀ i, σ2.sh i = if i = sKO then 0 else if i = sKI then 0 else σ.sh i := by
    intro i; simp only [hσ2, hσ1, WState.seth_sh, WState.setv_sh, Function.update_apply]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [he.koH, he.kiH]
  have e2st : σ2.st = σ.st := rfl
  have e2val : ∀ r, σ2.val r = if r = rKO then 0 else if r = rKI then 0 else σ.val r := by
    intro r; simp only [hσ2, hσ1, WState.seth_val, WState.setv_val, Function.update_apply]
  -- 3. clear KO
  have r3 := clearOne_exec (cap := cap) sKO sRU rC2 (by lay_ne) (Rk C) (by omega) σ2 (by rw [e2st]; exact he.ruS)
    (by rw [e2sh]; simp [show (sRU : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne,
      show (sRU : Fin (NS M (TS C) V + 1)) ≠ sKI by lay_ne, he.ruH]) (by rw [e2sh]; simp)
    (by rw [e2val]; simp [show (rC2 : Fin (NR M)) ≠ rKO by lay_ne, show (rC2 : Fin (NR M)) ≠ rKI by lay_ne, he.zC2])
  set σ3 := σ2.sets sKO (clearPrefix (Rk C) (σ2.st sKO)) with hσ3

  have hinj := kmap_inj (M := M) (V := V) o
  have hL : ∀ j, kmap (M := M) (V := V) o j ≠ sLG := kmap_ne o sLG (by simp only [sLG_val]; omega)
  have hKOblank : RdEq (σ3.st sKO) [] := by
    simp only [hσ3, WState.sets_st, Function.update_self, e2st]
    exact clearPrefix_blank _ _ (blank_of_rdEq he.koS (Rk C) (by unfold Rk; omega))
  have h0 : ∀ j, σ3.sh (kmap o j) = 0 := by
    intro j
    simp only [hσ3, WState.sets_sh, e2sh]
    by_cases h1 : j.val = 0
    · rw [kmap_zero C j h1]; simp [show (sKI : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne]
    · by_cases h2 : j = o
      · rw [h2, kmap_out C]; simp
      · rw [kmap_other C j h1 h2, if_neg (by lay_ne), if_neg (by lay_ne)]; exact he.scH j
  have hin : ∀ j, RdEq (σ3.st (kmap o j)) (C.K.wf.program.inputTapes (C.K.inw s) j) := by
    intro j
    simp only [Program.inputTapes]
    by_cases h1 : j.val = 0
    · rw [kmap_zero C j h1, if_pos h1, ← hs]
      simp only [hσ3, WState.sets_st, Function.update_of_ne (show (sKI : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne),
        e2st]
      exact he.kiS
    · rw [if_neg h1]
      by_cases h2 : j = o
      · rw [h2, kmap_out C]; exact hKOblank
      · rw [kmap_other C j h1 h2]
        simp only [hσ3, WState.sets_st, Function.update_of_ne (show (sT j : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne),
          e2st]
        exact he.scS j
  have hLst : σ3.st sLG = List.replicate C.Bk false := by
    simp only [hσ3, WState.sets_st, Function.update_of_ne (show (sLG : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne), e2st]
    exact he.lgS
  have hLsh : σ3.sh sLG = 0 := by
    simp only [hσ3, WState.sets_sh, e2sh]
    simp [show (sLG : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne, show (sLG : Fin (NS M (TS C) V + 1)) ≠ sKI by lay_ne,
      he.lgH]
  obtain ⟨τ4, tout, r4, d4, o4, far4⟩ := wordFunction_machZ_far C.K.wf s (cap := cap) (kmap o) hinj sLG hL σ3 h0
    hin C.Bk hLst hLsh hb

  have hRU4 : τ4.st sRU = List.replicate (Rk C) true ∧ τ4.sh sRU = 0 := by
    have := d4.other sRU (kmap_ne o sRU (by simp only [sRU_val]; omega))
    rw [this.1, this.2]
    simp only [hσ3, WState.sets_st, WState.sets_sh,
      Function.update_of_ne (show (sRU : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne), e2st, e2sh]
    simp [show (sRU : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne, show (sRU : Fin (NS M (TS C) V + 1)) ≠ sKI by lay_ne,
      he.ruS, he.ruH]
  have hval4 : τ4.val = σ3.val := d4.val
  have hC24 : τ4.val rC2 = 0 := by
    rw [hval4]; simp only [hσ3, WState.sets_val, e2val]
    simp [show (rC2 : Fin (NR M)) ≠ rKO by lay_ne, show (rC2 : Fin (NR M)) ≠ rKI by lay_ne, he.zC2]
  have hnot : (sRU : Fin (NS M (TS C) V + 1)) ∉ kclear (M := M) (V := V) o := by
    simp only [kclear, List.mem_cons, List.mem_map, List.mem_filter, not_or, not_exists, not_and]
    exact ⟨by lay_ne, fun j _ e => by have := congrArg Fin.val e; simp at this; omega⟩
  have hheads : ∀ X ∈ kclear (M := M) (V := V) o, τ4.sh X = 0 := by
    intro X hX
    simp only [kclear, List.mem_cons, List.mem_map, List.mem_filter] at hX
    rcases hX with rfl | ⟨j, ⟨_, hj⟩, rfl⟩
    · rw [← kmap_zero C ⟨0, by have := C.K.wf.program.twoTapes; show 0 < C.K.wf.program.tapeCount; omega⟩ rfl]
      exact d4.sh _
    · simp only [decide_eq_true_eq] at hj
      rw [← kmap_other C j hj.1 hj.2]; exact d4.sh _
  obtain ⟨τ5, r5, c5in, c5out, c5sh, c5val, c5cell⟩ := clearAll_runs (cap := cap) sRU rC2 (Rk C) (by omega)
    (kclear (M := M) (V := V) o) τ4 (kclear_nodup o) hnot hRU4.1 hRU4.2 hC24 hheads
  have hj0 : kmap (M := M) (V := V) o ⟨0, by have := C.K.wf.program.twoTapes; omega⟩ = sKI :=
    kmap_zero C _ rfl

  have hmemK : ∀ i, (∀ j, kmap (M := M) (V := V) o j ≠ i) → i ∉ kclear (M := M) (V := V) o := by
    intro i hi hm
    simp only [kclear, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq] at hm
    rcases hm with rfl | ⟨j, ⟨_, hj⟩, rfl⟩
    · exact hi _ hj0
    · exact hi j (kmap_other C j hj.1 hj.2)
  have keepSt : ∀ i, (∀ j, kmap (M := M) (V := V) o j ≠ i) → τ5.st i = σ.st i := by
    intro i hi
    rw [c5out i (hmemK i hi), (d4.other i hi).1]
    simp only [hσ3, WState.sets_st, e2st]
    rw [Function.update_of_ne (fun e => hi o (by rw [e, kmap_out C]))]
  have keepSh : ∀ i, (∀ j, kmap (M := M) (V := V) o j ≠ i) → τ5.sh i = σ.sh i := by
    intro i hi
    rw [c5sh, (d4.other i hi).2]
    simp only [hσ3, WState.sets_sh, e2sh]
    rw [if_neg (fun e => hi o (by rw [e, kmap_out C])), if_neg (fun e => hi _ (by rw [e, hj0]))]
  have keepVal : ∀ r, r ≠ rKO → r ≠ rKI → τ5.val r = σ.val r := by
    intro r h1 h2
    rw [c5val, hval4]; simp only [hσ3, WState.sets_val, e2val, if_neg h1, if_neg h2]
  have nk : ∀ i : Fin (NS M (TS C) V + 1), i.val ≠ 3 → i.val ≠ 4 → (i.val < 8 + 2 * M ∨ 8 + 2 * M + TS C ≤ i.val) →
      ∀ j, kmap (M := M) (V := V) o j ≠ i := fun i h3 h4 h5 => kmap_ne o i ⟨h3, h4, h5⟩
  have nkT : ∀ j : Fin (TS C), ¬ (j.val ≠ 0 ∧ j ≠ o) → ∀ j', kmap (M := M) (V := V) o j' ≠ sT j := by
    intro j hj j' e
    unfold kmap at e
    split_ifs at e with h1 h2
    · have := congrArg Fin.val e; simp at this; omega
    · have := congrArg Fin.val e; simp at this; omega
    · have := congrArg Fin.val e; simp at this
      have hjj : j' = j := Fin.ext (by omega)
      subst hjj; exact hj ⟨h1, h2⟩
  have hKR : Rk C = 2 * C.Lk + C.Bk + 3 := rfl
  refine ⟨τ5, ?_, ?_⟩
  · refine
      { inS := by rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.inS
        inH := by rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.inH
        inR := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.inR
        outS := by rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.outS
        outH := by rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.outH
        outR := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.outR
        zero := ⟨by rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.zero.1,
          by rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.zero.2⟩
        var := fun x => ⟨by rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact (he.var x).1,
          by rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact (he.var x).2⟩
        ramS := fun m => by
          have := m.isLt
          rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.ramS m
        ramH := fun m => by
          have := m.isLt
          rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.ramH m
        ramR := fun m => by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.ramR m
        shL := fun m => by
          have := m.isLt
          rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)),
            keepSt _ (nk (sM m) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.shL m
        shH := fun m => by
          have := m.isLt
          rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.shH m
        tpS := by rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.tpS
        tpH := by rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.tpH
        kiS := ?_
        kiH := ?_
        kiR := ?_
        koS := ?_
        koH := ?_
        koR := ?_
        scS := ?_
        scH := ?_
        lgS := by rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.lgS
        lgH := by rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.lgH
        ruS := by rw [keepSt _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.ruS
        ruH := by rw [keepSh _ (nk _ (by simp <;> omega) (by simp <;> omega) (by simp <;> omega))]; exact he.ruH
        zF := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.zF
        zR := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.zR
        zG := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.zG
        zK := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.zK
        zT := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.zT
        zC1 := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.zC1
        zC2 := by rw [keepVal _ (by lay_ne) (by lay_ne)]; exact he.zC2
        cell := by rw [c5cell, d4.cell]; simp only [hσ3, hσ2, hσ1, WState.sets_cell, WState.seth_cell,
          WState.setv_cell]; exact he.cell }
    ·
      have hmem : (sKI : Fin (NS M (TS C) V + 1)) ∈ kclear (M := M) (V := V) o := by simp [kclear]
      rw [c5in _ hmem]
      apply rdEq_nil_frame_nil
      apply clearPrefix_blank
      intro q hq
      have := far4 ⟨0, by have := C.K.wf.program.twoTapes; omega⟩ q (by
        simp only [Program.inputTapes, if_true, frame_len, ← hs]; omega)
      rwa [hj0] at this
    · rw [c5sh]; have := d4.sh ⟨0, by have := C.K.wf.program.twoTapes; omega⟩; rw [hj0] at this
      simp [DS.called, this]
    · rw [c5val, hval4]; simp [hσ3, e2val, DS.called]
    · have hnm : (sKO : Fin (NS M (TS C) V + 1)) ∉ kclear (M := M) (V := V) o := by
        simp only [kclear, List.mem_cons, List.mem_map, not_or, not_exists, not_and]
        exact ⟨by lay_ne, fun j _ e => by have := congrArg Fin.val e; simp at this; omega⟩
      rw [c5out _ hnm]; have := o4; rw [kmap_out C] at this; exact this
    · rw [c5sh]; have := d4.sh o; rw [kmap_out C] at this; simp [DS.called, this]
    · rw [c5val, hval4]; simp [hσ3, e2val, DS.called]
    · intro j
      by_cases hj : j.val ≠ 0 ∧ j ≠ o
      · have hmem : (sT j : Fin (NS M (TS C) V + 1)) ∈ kclear (M := M) (V := V) o := by
          simp only [kclear, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq]
          exact Or.inr ⟨j, ⟨List.mem_finRange j, hj⟩, rfl⟩
        rw [c5in _ hmem]
        apply clearPrefix_blank
        intro q hq
        have := far4 j q (by simp only [Program.inputTapes, if_neg hj.1]; simp; omega)
        rwa [kmap_other C j hj.1 hj.2] at this
      · rw [keepSt _ (nkT j hj)]; exact he.scS j
    · intro j
      by_cases hj : j.val ≠ 0 ∧ j ≠ o
      · rw [c5sh]; have := d4.sh j; rwa [kmap_other C j hj.1 hj.2] at this
      · rw [keepSh _ (nkT j hj)]; exact he.scH j
  · have hlen : (kclear (M := M) (V := V) o).length ≤ TS C + 1 := by
      simp only [kclear, List.length_cons, List.length_map]
      exact Nat.succ_le_succ ((List.length_filter_le _ _).trans (by simp))
    refine WXExec.seq' cap (WXExec.wm r1) (WXExec.seq' cap (WXExec.wm r2) (WXExec.seq' cap r3
      (WXExec.seq' cap r4 r5 le_rfl) le_rfl) le_rfl) ?_
    rw [hKR]
    have h5 : (kclear (M := M) (V := V) o).length * (18 * (2 * C.Lk + C.Bk + 3) + 4) ≤
        (TS C + 1) * (18 * (2 * C.Lk + C.Bk + 3) + 4) := Nat.mul_le_mul_right _ hlen
    nlinarith
end KCall

end NearCubicGates.Close.Cells
