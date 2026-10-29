import SourceAdapters.Compile.CNFBalancedB

/-!
# The balanced encoder, part C: the whole encoder

proof of `lem:multitape-refuter`: the program computes the native balanced code of the clause-code list held in `sCL` (the payload
`sourceSATCode` of the formula) in one register. `balP` appends a `0` sentinel (every clause code is positive),
counts the clauses, then runs the explicit-stack evaluation (`CNFBalancedA.brun`) pass by pass (`bodyB_spec`).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.CanonicalBinary
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- A run of cost `n` moves each cursor forward by at most `n`. -/
theorem ex_rc_le {C : Ctx} {s : St VV MM} {a b : DS VV MM} {n : ℕ} (h : Ex C s a b n) (m : Fin MM) :
    b.rc m ≤ a.rc m + n := by
  induction h with
  | op ho =>
      cases ho with
      | rdM m' x a h =>
          simp only [DS.adv, DS.set]
          by_cases hm : m = m'
          · subst hm; rw [Function.update_self]
          · rw [Function.update_of_ne hm]; omega
      | wrM m' x a h =>
          simp only [DS.put]
          by_cases hm : m = m'
          · subst hm; rw [Function.update_self]
          · rw [Function.update_of_ne hm]; omega
      | rwM m' a =>
          simp only [DS.rew]
          by_cases hm : m = m'
          · subst hm; rw [Function.update_self]; omega
          · rw [Function.update_of_ne hm]; omega
      | srtM m' a h0 => simp [DS.srt]
      | kcall s a h1 h2 => simp [DS.called]
      | _ => simp [DS.set]
  | seq _ _ ih1 ih2 => omega
  | iteT _ _ _ ih => omega
  | iteF _ _ _ ih => omega
  | loopF _ _ => omega
  | loopT _ _ _ _ ih1 ih2 => omega
  | mono _ hle ih => omega

theorem Hs.rcLe {C : Ctx} {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM → Prop} (h : Hs C s a t R)
    (m : Fin MM) : Hs C s a t (fun b => R b ∧ b.rc m ≤ a.rc m + t) := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  exact ⟨b, n, he, hn, hb, (ex_rc_le he m).trans (by omega)⟩

variable {C : Ctx}

/-! ## One pass -/

def bodyB : St VV MM :=
  .seq (popG sTK bT bX) (.ite (.eq bX vZ) combP (.ite (.eq bX v1) zeroP' (.ite (.eq bX v2) leafP splitP)))

theorem bodyB_spec (cl : List ℕ) (B Hb : ℕ) (hB : B < 2 ^ C.Wd) (hW : Hb + cl.length + 10 < 2 ^ C.Wd)
    (S : BS) (a : DS VV MM) (h : BR cl Hb S a) (hok : bok cl B S) (hg1 : hgt Hb S) (hg2 : hgt Hb (bstep cl S)) :
    Hs C bodyB a (30 * Hb + 100) (fun b => BR cl Hb (bstep cl S) b ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b balT) := by
  obtain ⟨tk, vs, p⟩ := S
  obtain ⟨hne, hok⟩ := hok
  obtain ⟨c, ts, rfl⟩ : ∃ c ts, tk = c :: ts := by
    cases tk with
    | nil => exact absurd rfl hne
    | cons c ts => exact ⟨c, ts, rfl⟩
  obtain ⟨hc, h0, h2⟩ := hok c ts rfl
  dsimp only at h0 h2
  unfold hgt at hg1 hg2
  simp only [List.length_cons] at hg1
  refine Hs.seqc (t1 := 6 * Hb + 11) (t2 := 24 * Hb + 73) (tpop_spec cl Hb (by omega) (c :: ts) vs p a h
    (by simp only [List.length_cons]; omega))
    (fun b1 ⟨e1, h1, i1, o1, f1⟩ => ?_) (by omega)
  simp only [popS] at e1 h1
  have hfin : ∀ (S' : BS) (b : DS VV MM), BR cl Hb S' b → b.ip = b1.ip → b.out = b1.out → Fr b1 b balT →
      bstep cl ⟨c :: ts, vs, p⟩ = S' → BR cl Hb (bstep cl ⟨c :: ts, vs, p⟩) b ∧ b.ip = a.ip ∧ b.out = a.out ∧
        Fr a b balT := by
    intro S' b hb hi ho hf hS
    rw [hS]
    exact ⟨hb, by rw [hi, i1], by rw [ho, o1], (Fr.weaken f1 (by simp [balT])).trans hf⟩
  refine Hs.ite (show bX ≠ vZ by decide) (fun hc0 => ?_) (fun hc0 => ?_)
  · have c0 : c = 0 := by simpa [Cnd.eval, e1, h1.kc.z] using hc0
    subst c0
    simp only [bstep, List.length_cons] at hg2
    have hp1 := Nat.right_le_pair 2 (Nat.pair (popS (popS vs).2).1 (popS vs).1)
    have hb0 := h0 rfl
    refine Hs.mono (combP_spec cl Hb (by omega) ts vs p b1 h1 (by omega) (by omega) (by omega)) (by omega) ?_
    rintro b ⟨hb, hi, ho, hf⟩
    exact hfin _ b hb hi ho hf rfl
  · have c0 : c ≠ 0 := by simpa [Cnd.eval, e1, h1.kc.z] using hc0
    refine Hs.mono (t := 24 * Hb + 72) (Hs.ite (show bX ≠ v1 by decide) (fun hc1 => ?_) (fun hc1 => ?_)) (by omega)
      (fun b h => h)
    · have c1 : c = 1 := by simpa [Cnd.eval, e1, h1.kc.one] using hc1
      subst c1
      simp only [bstep, List.length_cons] at hg2
      refine Hs.mono (zeroP'_spec cl Hb (by omega) ts vs p b1 h1 (by omega)) (by omega) ?_
      rintro b ⟨hb, hi, ho, hf⟩
      exact hfin _ b hb hi ho hf rfl
    · have c1 : c ≠ 1 := by simpa [Cnd.eval, e1, h1.kc.one] using hc1
      refine Hs.mono (t := 24 * Hb + 70) (Hs.ite (show bX ≠ v2 by decide) (fun hc2 => ?_) (fun hc2 => ?_))
        (by omega) (fun b h => h)
      · have c2 : c = 2 := by simpa [Cnd.eval, e1, h1.kc.two] using hc2
        subst c2
        simp only [bstep, List.length_cons] at hg2
        obtain ⟨hpl, hpb⟩ := h2 rfl
        refine Hs.mono (leafP_spec cl Hb (by omega) ts vs p b1 h1 (by omega) hpl (by omega)) (by omega) ?_
        rintro b ⟨hb, hi, ho, hf⟩
        exact hfin _ b hb hi ho hf rfl
      · have c2 : c ≠ 2 := by simpa [Cnd.eval, e1, h1.kc.two] using hc2
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 3 := ⟨c - 3, by omega⟩
        simp only [bstep, List.length_cons] at hg2
        refine Hs.mono (splitP_spec cl Hb (by omega) ts vs p c' b1 h1 e1 hc (by omega)) (by omega) ?_
        rintro b ⟨hb, hi, ho, hf⟩
        exact hfin _ b hb hi ho hf rfl

/-! ## The loop -/

def loopB : St VV MM := .loop (.lt vZ bT) bodyB

theorem loopB_spec (cl : List ℕ) (B Hb K : ℕ) (hB : B < 2 ^ C.Wd) (hW : Hb + cl.length + 10 < 2 ^ C.Wd) (S0 : BS)
    (hok : ∀ j < K, bok cl B ((bstep cl)^[j] S0)) (hg : ∀ j ≤ K, hgt Hb ((bstep cl)^[j] S0))
    (hend : ((bstep cl)^[K] S0).tk = []) (a : DS VV MM) (h : BR cl Hb S0 a) :
    Hs C loopB a (K * (30 * Hb + 102) + 2) (fun b => BR cl Hb ((bstep cl)^[K] S0) b ∧ b.ip = a.ip ∧
      b.out = a.out ∧ Fr a b balT) := by
  have hloop := Hs.loopN (C := C) (c := .lt vZ bT) (s := bodyB) (show vZ ≠ bT by decide)
    (fun k b => BR cl Hb ((bstep cl)^[k] S0) b ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b balT) K (30 * Hb + 100)
    (fun k hk b ⟨hb, hi, ho, hf⟩ => by
      refine ⟨?_, ?_⟩
      · have hne := (hok k hk).1
        have hsp := hb.tk.sp
        simp only [Cnd.eval, hb.kc.z, hsp, decide_eq_true_eq]
        exact List.length_pos_of_ne_nil hne
      · refine Hs.mono (bodyB_spec cl B Hb hB hW _ b hb (hok k hk) (hg k (by omega)) ?_) le_rfl ?_
        · have := hg (k + 1) (by omega); rwa [Function.iterate_succ_apply'] at this
        · rintro d ⟨hd, di, do', df⟩
          exact ⟨by rw [Function.iterate_succ_apply']; exact hd, by rw [di, hi], by rw [do', ho], hf.trans df⟩)
    (fun b ⟨hb, _, _, _⟩ => by
      have hsp := hb.tk.sp
      simp [Cnd.eval, hb.kc.z, hsp, hend])
  exact hloop a ⟨h, rfl, rfl, Fr.refl _ _⟩

/-! ## Counting the clauses (sentinel `0`) -/

def cntP : St VV MM :=
  .seq (.op (.rwM sCL)) (.seq (.op (.zero bN)) (.seq (.op (.rdM sCL bU))
    (.loop (.lt vZ bU) (.seq (.op (.inc bN)) (.op (.rdM sCL bU))))))

theorem cntP_spec (cl : List ℕ) (hpos : ∀ x ∈ cl, 0 < x) (hW : cl.length + 2 < 2 ^ C.Wd) (a : DS VV MM)
    (hkc : KC a) (hcl : a.ram sCL = cl ++ [0]) (hrc : a.rc sCL = cl.length + 1) :
    Hs C cntP a (6 * cl.length + 12) (fun b => b.env bN = cl.length ∧ b.ram = a.ram ∧ b.rc sCL = cl.length + 1 ∧
      (∀ m, m ≠ sCL → b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [bN, bU]) := by
  set L := cl.length with hL
  let I : ℕ → DS VV MM → Prop := fun k b => b.env bN = k ∧ b.rc sCL = k + 1 ∧ b.env bU = (cl ++ [0]).getD k 0 ∧
    b.ram = a.ram ∧ (∀ m, m ≠ sCL → b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [bN, bU]
  have hloop := Hs.loopN (C := C) (c := .lt vZ bU) (s := .seq (.op (.inc bN)) (.op (.rdM sCL bU)))
    (show vZ ≠ bU by decide) I L 3
    (fun k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => by
      have hz : b.env vZ = 0 := by rw [h8 vZ (by decide), hkc.z]
      have hcode : 0 < (cl ++ [0]).getD k 0 := by
        rw [List.getD_append _ _ _ _ hk, List.getD_eq_getElem _ _ hk]; exact hpos _ (List.getElem_mem hk)
      refine ⟨by simp only [Cnd.eval, hz, h3, decide_eq_true_eq]; exact hcode, ?_⟩
      refine Hs.seqc (t1 := 1) (t2 := 1) (hs_inc C bN b (by rw [h1]; omega)) (fun d hd => ?_) (by omega)
      subst hd
      refine Hs.op (OpEx.rdM sCL bU _ (by simp [h2, h4, hcl]; omega)) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · vsimp [DS.adv, h1]
      · simp [DS.adv, h2]
      · simp [DS.adv, h2, h4, hcl]
      · simp [DS.adv, h4]
      · intro m hm; simp [DS.adv, Function.update_of_ne hm, h5 m hm]
      · simp [DS.adv, h6]
      · simp [DS.adv, h7]
      · intro y hy
        have := h8 y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [DS.adv, DS.set, Function.update_apply, hy, this])
    (fun b ⟨h1, h2, h3, _, _, _, _, h8⟩ => by
      have hz : b.env vZ = 0 := by rw [h8 vZ (by decide), hkc.z]
      have h0 : (cl ++ [0]).getD L 0 = 0 := by rw [List.getD_append_right _ _ _ _ (le_of_eq rfl)]; simp
      simp only [Cnd.eval, hz, h3, h0]; rfl)
  refine Hs.seqc (t1 := L + 2) (t2 := 5 * L + 8) (Hs.mono (hs_rwM C sCL a) (by rw [hrc]) (fun b h => h))
    (fun b1 hb1 => ?_) (by omega)
  subst hb1
  refine Hs.seqc (t1 := 1) (t2 := 5 * L + 6) (hs_zero C bN _) (fun b2 hb2 => ?_) (by omega)
  subst hb2
  refine Hs.seqc (t1 := 1) (t2 := L * (3 + 2) + 2) (hs_rdM C sCL bU _ (by simp [DS.rew, hcl]))
    (fun b3 hb3 => ?_) (by omega)
  subst hb3
  refine Hs.mono (hloop _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl ?_
  · vsimp [DS.adv, DS.rew]
  · simp [DS.adv, DS.rew]
  · simp [DS.adv, DS.rew, hcl]
  · simp [DS.adv, DS.rew]
  · intro m hm; simp [DS.adv, DS.rew, Function.update_of_ne hm]
  · simp [DS.adv, DS.rew]
  · simp [DS.adv, DS.rew]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [DS.adv, DS.rew, DS.set, Function.update_apply, hy]
  · rintro b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h4, h2, h5, h6, h7, h8⟩

/-! ## The encoder -/

/-- Rewind the clause, task and value stores; empty stacks; `bX := count + 1` (the root task). -/
def prepB : St VV MM :=
  .seq (.op (.rwM sCL)) (.seq (.op (.rwM sTK)) (.seq (.op (.rwM sVS)) (.seq (.op (.zero bT)) (.seq (.op (.zero bV))
    (.seq (.op (.copy bX bN)) (.op (.inc bX)))))))

/-- **The balanced encoder**: `bY := encodeBalancedList` of the clause codes in `sCL`. -/
def balP : St VV MM :=
  .seq (.op (.wrM sCL vZ)) (.seq cntP (.seq prepB (.seq (pushG sTK bT bX) (.seq loopB (popG sVS bV bY)))))

def balCost (L R : ℕ) : ℕ := R + (3 * L + 1) * (90 * L + 132) + 10 * L + 70

theorem seg_all (cl : List ℕ) : seg cl 0 cl.length = cl := by simp [seg]

theorem balP_spec (cl : List ℕ) (R : ℕ) (hpos : ∀ x ∈ cl, 0 < x) (hB : encodeBalancedList cl < 2 ^ C.Wd)
    (hW : 4 * cl.length + 20 < 2 ^ C.Wd) (a : DS VV MM) (hk : KC a) (hcl : a.ram sCL = cl)
    (hrc : a.rc sCL = cl.length) (hR : a.rc sTK + a.rc sVS ≤ R) :
    Hs C balP a (balCost cl.length R) (fun b => b.env bY = encodeBalancedList cl ∧ KC b ∧ b.out = a.out ∧
      b.ip = a.ip) := by
  set L := cl.length with hL
  set Hb := 3 * L + 1 with hHb
  -- the sentinel
  refine Hs.seqc (t1 := 1) (t2 := balCost L R - 2) (hs_wrM C sCL vZ a (by rw [hrc, hcl])) (fun b1 hb1 => ?_)
    (by unfold balCost; omega)
  subst hb1
  set b1 := a.put sCL (a.env vZ) with hb1
  have h1cl : b1.ram sCL = cl ++ [0] := by simp [hb1, DS.put, putAt, hrc, hcl, hk.z, hL]
  have h1rc : b1.rc sCL = L + 1 := by simp [hb1, DS.put, hrc]
  have h1o : ∀ m, m ≠ sCL → b1.rc m = a.rc m := fun m hm => by simp [hb1, DS.put, Function.update_of_ne hm]
  have hk1 : KC b1 := hk.of_fr (b := b1) (T := []) (fun y _ => rfl) (by decide)
  -- the count
  refine Hs.seqc (t1 := 6 * L + 12) (t2 := balCost L R - 6 * L - 15) (cntP_spec cl hpos (by omega) b1 hk1 h1cl h1rc)
    (fun b2 ⟨n2, r2, c2, o2, i2, u2, f2⟩ => ?_) (by unfold balCost; omega)
  have hk2 : KC b2 := hk1.of_fr f2 (by decide)
  -- rewind and empty stacks
  have s3 : Hs C prepB b2 (L + R + 14) (fun b => b.env bT = 0 ∧ b.env bV = 0 ∧ b.env bX = L + 1 ∧
      b.ram = b2.ram ∧ b.rc sCL = 0 ∧ b.rc sTK = 0 ∧ b.rc sVS = 0 ∧ b.ip = b2.ip ∧ b.out = b2.out ∧
      Fr b2 b [bT, bV, bX]) := by
    apply hs_of_wpc
    simp only [prepB, wpc, opwp]
    vsimp [DS.rew, n2, c2, o2 sTK (by decide), o2 sVS (by decide), h1o sTK (by decide), h1o sVS (by decide)]
    and_split
    all_goals first | omega | rfl | fr_tac | skip
    all_goals (try simp [Function.update_apply])
  refine Hs.seqc (t1 := L + R + 14) (t2 := balCost L R - 7 * L - R - 30) s3
    (fun b3 ⟨t3, v3, x3, r3, c3, k3, s3', i3, u3, f3⟩ => ?_) (by unfold balCost; omega)
  have hk3 : KC b3 := hk2.of_fr f3 (by decide)
  have st0 : StkG sTK bT b3 [] := ⟨by rw [t3]; rfl, by simp, by simp⟩
  have sv0 : StkG sVS bV b3 [] := ⟨by rw [v3]; rfl, by simp, by simp⟩
  refine Hs.seqc (t1 := 10) (t2 := balCost L R - 7 * L - R - 41) (Hs.mono (pushG_spec sTK bT bX (by decide)
    (by decide) b3 [] st0 (by simp; omega)) (by rw [k3]; simp) (fun b h => h)) (fun b4 hb4 => ?_)
    (by unfold balCost; omega)
  obtain ⟨g1, -, g3, g4, g5, g6, g7⟩ := hb4
  rw [x3] at g1
  have hBR : BR cl Hb ⟨[L + 1], [], 0⟩ b4 :=
    { kc := hk3.of_fr g7 (by decide)
      tk := g1
      vs := sv0.congr (g4 sVS (by decide)).1 (g7 bV (by decide))
      cl := by rw [(g4 sCL (by decide)).1, r3, r2, h1cl]
      p := by rw [(g4 sCL (by decide)).2, c3]
      rtk := by rw [g3]; simp only [List.length_nil]; omega
      rvs := by rw [(g4 sVS (by decide)).2, s3']; omega }
  obtain ⟨hg, hok, hfin⟩ := brun cl (encodeBalancedList cl) Hb L [] [] 0 (by omega) (by rw [seg_all])
    (by simp only [List.length_nil]; omega)
  rw [seg_all] at hfin
  have hK := bcnt_le L
  refine Hs.seqc (t1 := bcnt L * (30 * Hb + 102) + 2) (t2 := 3 * L + 17)
    (loopB_spec cl (encodeBalancedList cl) Hb (bcnt L) hB (by omega) _ hok hg (by rw [hfin]) b4 hBR)
    (fun b5 ⟨h5, i5, u5, f5⟩ => ?_) (by
      have : bcnt L * (30 * Hb + 102) ≤ (3 * L + 1) * (90 * L + 132) := by
        rw [hHb]; apply Nat.mul_le_mul hK; omega
      unfold balCost; omega)
  rw [hfin] at h5
  refine Hs.mono (popG_spec sVS bV bY (by decide) (by decide) b5 _ h5.vs h5.kc.z h5.kc.one (by simp; omega))
    (by have := h5.rvs; simp; omega) ?_
  rintro b6 ⟨e6, -, -, -, -, i6, u6, f6⟩
  refine ⟨by rw [e6]; rfl, h5.kc.of_fr f6 (by decide), ?_, ?_⟩
  · rw [u6, u5, g6, u3, u2]; simp [hb1, DS.put]
  · rw [i6, i5, g5, i3, i2]; simp [hb1, DS.put]

end NearCubicGates.Adapters.Compile
