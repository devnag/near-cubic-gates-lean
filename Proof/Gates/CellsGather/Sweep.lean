import Proof.Gates.CellsGather.Prog

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-- The loop. -/
def swLoop : St VV MM := .loop (.lt gx gPad) (.seq swBody (.op (.rdM sG gx)))

/-- The variables of the sweep phase. -/
def swT2 : List (Fin VV) := [gx, gPZ, gPad, gQ, gR, gK, gF, gA, gLast, gNQ]

theorem lastV_lt (Z : ℕ) : ∀ (l : List ℕ) (l0 : ℕ), l0 < 2 ^ Z → lastV Z l l0 < 2 ^ Z
  | [], l0, h => h
  | x :: l, l0, h => by
    unfold lastV
    rw [List.foldl_cons]
    exact lastV_lt Z l _ (by split_ifs <;> [exact Nat.mod_lt _ (by positivity); exact h])

theorem lastV_snoc' (Z : ℕ) (A : List ℕ) (x l0 : ℕ) : lastV Z (A ++ [x]) l0 = lastV Z [x] (lastV Z A l0) := by
  simp [lastV, List.foldl_append]

/-- **The invariant** after `k` real records. -/
structure SwI (Z VW : ℕ) (R : List ℕ) (n pad : ℕ) (e : DS VV MM) (k : ℕ) (b : DS VV MM) : Prop where
  k_le : k ≤ R.length
  ramO : ∀ m, m ≠ sA → b.ram m = e.ram m
  rcG : b.rc sG = k + 1
  x : b.env gx = (R ++ List.replicate n pad).getD k 0
  ramA : b.ram sA = sweep Z VW (R.take k) 0 ++ (e.ram sA).drop (sweep Z VW (R.take k) 0).length
  rcA : b.rc sA = (sweep Z VW (R.take k) 0).length
  last : b.env gLast = lastV Z (R.take k) 0
  nq : b.env gNQ = (sweep Z VW (R.take k) 0).length
  pz : b.env gPZ = 2 ^ Z
  pd : b.env gPad = pad
  fr : Fr e b swT2
  ip : b.ip = e.ip
  out : b.out = e.out
  kin : b.kin = e.kin
  kout : b.kout = e.kout
  kc : b.kc = e.kc

/-- The hypotheses of the sweep. -/
structure SwH (C : Ctx) (Z VW : ℕ) (R : List ℕ) (n pad : ℕ) (e : DS VV MM) : Prop where
  cst : Cst e
  vw : e.env p2VW = 2 ^ VW
  G : e.ram sG = R ++ List.replicate n pad
  n1 : 1 ≤ n
  lt : ∀ x ∈ R, x < pad
  w1 : 2 * 2 ^ Z ≤ 2 ^ C.Wd
  w2 : 4 ≤ 2 ^ C.Wd
  w3 : 2 ^ Z * 2 ^ VW + 2 ^ Z ≤ 2 ^ C.Wd
  nq : (sweep Z VW R 0).length + 1 < 2 ^ C.Wd

variable {C : Ctx}

theorem SwI.k_lt {Z VW : ℕ} {R : List ℕ} {n pad : ℕ} {e : DS VV MM} {k : ℕ} {b : DS VV MM}
    (H : SwH C Z VW R n pad e) (h : SwI Z VW R n pad e k b) (hx : b.env gx < b.env gPad) : k < R.length := by
  rcases Nat.lt_or_ge k R.length with hk | hk
  · exact hk
  · have hkR : k = R.length := le_antisymm h.k_le hk
    rw [h.x, h.pd, hkR, List.getD_eq_getElem _ _ (by simp; have := H.n1; omega),
      List.getElem_append_right (by omega)] at hx
    simp at hx

theorem sweep_take_le (Z VW : ℕ) (R : List ℕ) (k : ℕ) :
    (sweep Z VW (R.take k) 0).length ≤ (sweep Z VW R 0).length := by
  conv_rhs => rw [← List.take_append_drop k R]
  rw [sweep_append, List.length_append]; omega

/-- **One pass of the loop.** -/
theorem swStep {Z VW : ℕ} {R : List ℕ} {n pad : ℕ} {e : DS VV MM} {k : ℕ} {b : DS VV MM}
    (H : SwH C Z VW R n pad e) (h : SwI Z VW R n pad e k b) (hx : b.env gx < b.env gPad) :
    Hs C (.seq swBody (.op (.rdM sG gx))) b 14 (fun d => SwI Z VW R n pad e (k + 1) d) := by
  have hk := h.k_lt H hx
  have hcb : Cst b := Cst.of_fr H.cst h.fr (by decide)
  have hxk : b.env gx = R[k] := by
    rw [h.x, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hk]
  have hvw : b.env p2VW = 2 ^ VW := by rw [h.fr.ev (by decide)]; exact H.vw
  have hl : b.env gLast < 2 ^ Z := by rw [h.last]; exact lastV_lt Z _ 0 (by positivity)
  have htk : R.take (k + 1) = R.take k ++ [R[k]] := by rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  have hsw1 : sweep Z VW (R.take (k + 1)) 0 = sweep Z VW (R.take k) 0 ++ sweep Z VW [R[k]] (lastV Z (R.take k) 0) := by
    rw [htk, sweep_append]
  have hq : b.env gNQ + 1 < 2 ^ C.Wd := by
    have := sweep_take_le Z VW R (k + 1)
    rw [hsw1, List.length_append] at this
    have h2 := H.nq
    rw [h.nq]
    by_cases hf : gFlag Z R[k] = 0
    · have := sweep_take_le Z VW R k; omega
    · rw [sweep_one_q Z VW _ _ hf] at this; simp at this; omega
  refine Hs.mono (Hs.seq (swBody_spec (C := C) b hcb Z VW h.pz hvw H.w1 H.w2 H.w3 hl hq
    (sweep Z VW (R.take k) 0) (e.ram sA) h.ramA h.rcA) (fun b1 hb1 => ?_)) (by norm_num : 12 + 1 + 1 ≤ 14)
    (fun _ h => h)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := hb1
  rw [hxk, h.last] at r1 r2 r4 r5
  have hG1 : b1.ram sG = R ++ List.replicate n pad := by rw [(r3 sG (by decide)).1, h.ramO sG (by decide), H.G]
  have hrc1 : b1.rc sG = k + 1 := by rw [(r3 sG (by decide)).2, h.rcG]
  have hlen : b1.rc sG < (b1.ram sG).length := by rw [hrc1, hG1]; simp; have := H.n1; omega
  refine Hs.mono (hs_rdM C sG gx b1 hlen) le_rfl ?_
  rintro d rfl
  refine ⟨by omega, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [DS.adv, DS.set]; rw [(r3 m hm).1, h.ramO m hm]
  · simp only [DS.adv, DS.set, Function.update_self]; rw [hrc1]
  · simp only [DS.adv, DS.set, DS.env_set, Function.update_self]; rw [hG1, hrc1]
  · simp only [DS.adv, DS.set]; rw [r1, hsw1]
  · simp only [DS.adv, DS.set]; rw [Function.update_of_ne (by decide), r2, hsw1]
  · simp only [DS.adv, DS.set, DS.env_set]; rw [Function.update_of_ne (by decide), r4, htk, lastV_snoc']
  · simp only [DS.adv, DS.set, DS.env_set]; rw [Function.update_of_ne (by decide), r5, h.nq, hsw1,
      List.length_append]
  · simp only [DS.adv, DS.set, DS.env_set]; rw [Function.update_of_ne (by decide), r6.ev (by decide), h.pz]
  · simp only [DS.adv, DS.set, DS.env_set]; rw [Function.update_of_ne (by decide), r6.ev (by decide), h.pd]
  · intro y hy
    have hsub : ∀ z ∈ swT, z ∈ swT2 := by decide
    have h1 : y ≠ gx := fun e' => hy (by rw [e']; decide)
    have h2 : y ∉ swT := fun h' => hy (hsub y h')
    simp only [DS.adv, DS.set, DS.env_set]
    rw [Function.update_of_ne h1, r6 y h2, h.fr y hy]
  · simp only [DS.adv, DS.set]; rw [r7, h.ip]
  · simp only [DS.adv, DS.set]; rw [r8, h.out]
  · simp only [DS.adv, DS.set]; rw [r9, h.kin]
  · simp only [DS.adv, DS.set]; rw [r10, h.kout]
  · simp only [DS.adv, DS.set]; rw [r11, h.kc]

/-- **The loop.** -/
theorem swLoop_spec {Z VW : ℕ} {R : List ℕ} {n pad : ℕ} {e : DS VV MM} {b : DS VV MM}
    (H : SwH C Z VW R n pad e) (h : SwI Z VW R n pad e 0 b) :
    Hs C swLoop b (R.length * 16 + 2) (fun d => SwI Z VW R n pad e R.length d) := by
  have hμ0 : R.length + 1 - b.rc sG = R.length := by rw [h.rcG]; omega
  refine Hs.mono (Hs.loopM (C := C) (c := .lt gx gPad) (show (Cnd.lt gx gPad).wf from (by decide : gx ≠ gPad))
    (fun d => ∃ k, SwI Z VW R n pad e k d) (fun d => R.length + 1 - d.rc sG) 14 ?_ b ⟨0, h⟩) ?_ ?_
  · rintro d ⟨k, hd⟩ hev
    have hx : d.env gx < d.env gPad := by simpa [Cnd.eval] using hev
    have hk := hd.k_lt H hx
    refine Hs.mono (swStep H hd hx) le_rfl (fun d' hd' => ⟨⟨k + 1, hd'⟩, ?_⟩)
    rw [hd'.rcG, hd.rcG]; omega
  · rw [hμ0]
  · rintro d ⟨⟨k, hd⟩, hev⟩
    have hx : ¬ d.env gx < d.env gPad := by simpa [Cnd.eval] using hev
    have hk : k = R.length := by
      by_contra hne
      have hk' : k < R.length := lt_of_le_of_ne hd.k_le hne
      apply hx
      rw [hd.x, hd.pd, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hk']
      exact H.lt _ (List.getElem_mem _)
    rw [← hk]; exact hd

end NearCubicGates.Close.Cells.GatherPhase
