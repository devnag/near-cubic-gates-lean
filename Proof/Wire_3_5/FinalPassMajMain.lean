import Proof.Wire_3_5.FinalPassMajLoop

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Maj
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.ListEval NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierWalk NearCubicWires.WireExponent3_5.FinalPass.Flat

variable (cap : ℕ)

/-! ## Uniform lengths -/

/-- The table word's length for rows of length `L`. -/
def lwLen (M J : ℕ) (W : ℕ → ℕ) (L : ℕ) : ℕ := (levelWord M J W (fun _ => List.replicate L false)).length

theorem lw_len (M J : ℕ) (W : ℕ → ℕ) (L : ℕ) (row : ℕ → List Bool) (h : ∀ j ≤ J, (row j).length = L) :
    (levelWord M J W row).length = lwLen M J W L := by
  have hmem : ∀ j ∈ levels J, j ≤ J := by intro j hj; simp [levels] at hj; omega
  unfold lwLen
  simp only [levelWord, List.length_append, List.length_flatMap, record_len]
  congr 2
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  rw [h j (hmem j hj)]
  simp

theorem accR_le (P : FlatListParams) (e : P.FlatSeed) (Z : List Bool) (s : ℕ) : accR P e Z s ≤ s := by
  unfold accR
  have h := sum_ite_unique (majStateFast P e Z) (fun a b ha hb => majStateFast_unique P e Z ha hb)
    ((List.range s).map (· + 1)) ((List.nodup_range).map (fun a b h => by simpa using h))
  rw [List.map_map] at h
  rw [show ((List.range s).map fun i => if majStateFast P e Z (i + 1) = true then i + 1 else 0) =
    (List.range s).map ((fun x => if majStateFast P e Z x = true then x else 0) ∘ fun x => x + 1) from rfl, h]
  cases hf : ((List.range s).map (· + 1)).find? (majStateFast P e Z) with
  | none => simp
  | some v =>
    have hv := List.mem_of_find?_eq_some hf
    simp at hv
    simp only [Option.getD_some]
    omega

/-- The count over the whole table is the number of visits reporting the state. -/
theorem hits_count (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (Z : List Bool) (hZ : Z.length = L) (s : ℕ) :
    hitsOf P.M P.base.J P.base.W (visitRows P e L) Z s (List.finRange P.walkLen) = majCount P e Z s := by
  unfold hitsOf
  rw [majCount_eq_sum]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  rw [reportRef_visit P e L Z hZ]

theorem flatTable_visits (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) :
    flatTable P e L = [] ++ visitWords P.base.J (visitRows P e L) (List.finRange P.walkLen) ++ false :: [] := by
  simp [flatTable, visitWords, visitRows]

/-! ## One state -/

/-- **One state**: `unary s` extended, `S` counted, the visits, the check, the table rewound, `MC` counted down. -/
def sBody : MProg :=
  .seq extendU (.seq (.inc mS) (.seq visitsM (.seq checkM (.seq (WM.rewind sFT mFP) (.dec mMC)))))

/-- The capacities of the majority machine. -/
structure MajCap (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (cap : ℕ) : Prop where
  hlw : 4 * (lwLen P.M P.base.J P.base.W L + L + 1) ≤ cap
  hft : (flatTable P e L).length < cap
  ht : 2 * P.walkLen + 2 ≤ cap
  hM : 2 * P.M + 2 ≤ cap

/-- The cost bound of one visit. -/
def visitBound (P : FlatListParams) (L : ℕ) : ℕ :=
  visitCost P.M P.base.J P.base.W L (lwLen P.M P.base.J P.base.W L)
    (mainCost (4 * (lwLen P.M P.base.J P.base.W L + L + 1)))

/-- The cost bound of one state. -/
def sBodyBound (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) : ℕ :=
  (7 * P.M + 1 + 1 + (1 + 1 + (5 * P.M + 1))) + 1 + (3 + 1 + ((P.walkLen * (visitBound P L + 2) + 1) + 1 +
    (checkCost P.walkLen P.walkLen P.M + 1 + ((5 * (flatTable P e L).length + 1) + 1 + 1))))

theorem visitsCost_eq (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (Z : List Bool) (hZ : Z.length = L) :
    visitsCost P.M P.base.J P.base.W L (visitRows P e L) Z (List.finRange P.walkLen) =
      P.walkLen * (visitBound P L + 2) + 1 := by
  unfold visitsCost visitBound
  have e1 : ∀ k : Fin P.walkLen, (levelWord P.M P.base.J P.base.W (visitRows P e L k)).length =
      lwLen P.M P.base.J P.base.W L := fun k => lw_len _ _ _ _ _ (fun j _ => by simp [visitRows, rowsOf])
  have e2 : ∀ k : Fin P.walkLen, capOf P.M P.base.J P.base.W (visitRows P e L k) Z.length =
      4 * (lwLen P.M P.base.J P.base.W L + L + 1) := by
    intro k; unfold capOf; rw [e1 k, hZ]
  simp only [e1, e2, List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]

theorem checkCost_le (a v s A M : ℕ) (ha : a ≤ A) (hs : s ≤ M) : checkCost a v s ≤ checkCost A v M := by
  unfold checkCost; omega

/-- **One state of the loop**: from the record before state `s + 1` (result `accR s`), to the record after it. -/
theorem sBody_spec (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (Z : List Bool) (hZ : Z.length = L)
    (hc : MajCap P e L cap) (s k m : ℕ) (hs : s + 1 ≤ P.M) (hm : m + 1 ≤ P.M) (rowsT : ℕ → List Bool)
    (hrows : ∀ j ≤ P.base.J, (rowsT j).length = L) (x : MSt) (hpt : x.pt = frame Z)
    (ht5 : x.t5 = levelWord P.M P.base.J P.base.W rowsT) (ht5h : x.t5h = 0)
    (hss : x.ss = List.replicate s true ++ List.replicate k false) (hssh : x.ssh = 0) (hft : x.ft = flatTable P e L)
    (hfth : x.fth = 0) (hc0 : x.c = 0) (ha : x.a = 0) (hv : x.v = 0) (hS : x.s = s) (hr : x.r = accR P e Z s)
    (hmc : x.mc = m + 1) (htt : x.tt = 0) (hf : x.f = 0) (h2 : x.t2 = 0) :
    ∃ b n, n ≤ sBodyBound P e L ∧ WExec cap sBody x.w
      { x with t5 := levelWord P.M P.base.J P.base.W
                 (lastRows (visitRows P e L) (List.finRange P.walkLen) rowsT),
               ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false, s := s + 1,
               r := accR P e Z (s + 1), mc := m, cell := b }.w n := by
  obtain ⟨hlw, hftc, htc, hMc⟩ := hc
  have hlw5 := lw_len P.M P.base.J P.base.W L rowsT hrows
  -- 1: the compared state
  have s1 := extendU_spec cap s k x hss hssh (by omega)
  -- 2: the state register
  have s2 := WExec.inc (cap := cap) mS
    ({ x with ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false } : MSt).w
    (show x.s < cap by omega)
  rw [m_s] at s2
  -- 3: the visits
  obtain ⟨b, s3⟩ := visits_spec cap P.M P.base.J P.base.W L (visitRows P e L) Z (s + 1) [] hZ
    (fun k j _ => by simp [visitRows, rowsOf]) hs (List.finRange P.walkLen) rowsT []
    ({ x with ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false, s := x.s + 1 } : MSt)
    hrows hpt ht5 ht5h (fun p => read_ss (s + 1) (k - 1) p) hssh hc0
    (by show x.ft = _; rw [hft]; exact flatTable_visits P e L) hfth
    (fun k' _ => by rw [lw_len P.M P.base.J P.base.W L _ (fun j _ => by simp [visitRows, rowsOf])]; omega)
    (by have := flatTable_visits P e L; rw [this] at hftc; simp at hftc ⊢; omega)
    (fun k' _ => by
      unfold capOf; rw [lw_len P.M P.base.J P.base.W L _ (fun j _ => by simp [visitRows, rowsOf]), hZ]; omega)
    (by show x.a + (List.finRange P.walkLen).length ≤ cap; simp; omega)
    (by show x.v + (List.finRange P.walkLen).length < cap; simp; omega)
  rw [hits_count P e L Z hZ] at s3
  -- 4: the check
  have hmajc : majCount P e Z (s + 1) ≤ P.walkLen := by
    unfold majCount
    have := Finset.card_le_univ (Finset.univ.filter fun k : Fin P.walkLen => visitReportFast P e k Z = s + 1)
    simpa using this
  have s4 := check_spec cap
    ({ x with ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false, s := x.s + 1,
               t5 := levelWord P.M P.base.J P.base.W (lastRows (visitRows P e L) (List.finRange P.walkLen) rowsT),
               fth := ([] ++ visitWords P.base.J (visitRows P e L) (List.finRange P.walkLen)).length,
               a := x.a + majCount P e Z (s + 1), v := x.v + (List.finRange P.walkLen).length, cell := b } : MSt)
    htt hf h2 (by simp only; rw [ha]; omega) (by simp only; rw [hv]; simp; omega) (by simp only; omega)
    (by simp only; rw [hr]; have := accR_le P e Z s; omega) (by omega)
  -- 5: the table rewound, 6: `MC` counted down
  obtain ⟨y, hy⟩ : ∃ y : MSt,
      y = { x with ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false,
                   s := x.s + 1,
                   t5 := levelWord P.M P.base.J P.base.W (lastRows (visitRows P e L) (List.finRange P.walkLen) rowsT),
                   fth := ([] ++ visitWords P.base.J (visitRows P e L) (List.finRange P.walkLen)).length,
                   a := 0,
                   v := 0,
                   r := x.r + (if x.v + (List.finRange P.walkLen).length ≤ 2 * (x.a + majCount P e Z (s + 1))
                     then x.s + 1 else 0),
                   cell := b } := ⟨_, rfl⟩
  have s4' : WExec cap checkM
      ({ x with ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false, s := x.s + 1,
                t5 := levelWord P.M P.base.J P.base.W (lastRows (visitRows P e L) (List.finRange P.walkLen) rowsT),
                fth := ([] ++ visitWords P.base.J (visitRows P e L) (List.finRange P.walkLen)).length,
                a := x.a + majCount P e Z (s + 1), v := x.v + (List.finRange P.walkLen).length, cell := b } : MSt).w
      y.w (checkCost (x.a + majCount P e Z (s + 1)) (x.v + (List.finRange P.walkLen).length) (x.s + 1)) := by
    rw [hy]; exact s4
  have hflen : (visitWords P.base.J (visitRows P e L) (List.finRange P.walkLen)).length < cap := by
    have := flatTable_visits P e L
    rw [this] at hftc
    simp at hftc
    omega
  have s5 := wrewind_spec cap sFT mFP y.fth y.w rfl (by
    rw [hy]
    show ([] ++ visitWords P.base.J (visitRows P e L) (List.finRange P.walkLen)).length ≤ cap
    rw [List.nil_append]; omega)
  rw [m_ft_rew] at s5
  have s6 := WExec.dec (cap := cap) mMC ({ y with fth := 0 } : MSt).w (by show y.mc ≤ cap; rw [hy]; simp only; omega)
  rw [m_mc] at s6
  refine ⟨b, sBodyBound P e L, le_refl _,
    WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4' (WExec.seq s5 s6))))) ?_ ?_⟩
  · have hstep : x.r + (if x.v + (List.finRange P.walkLen).length ≤ 2 * (x.a + majCount P e Z (s + 1))
        then x.s + 1 else 0) = accR P e Z (s + 1) := by
      rw [hr, hv, ha, hS, accR_succ, majStateFast_eq, List.length_finRange]
      congr 1
      by_cases h : P.walkLen ≤ 2 * majCount P e Z (s + 1)
      · rw [if_pos (by omega), decide_eq_true ((thr_iff _ _).mpr (by omega))]; rfl
      · rw [if_neg (by omega), decide_eq_false (fun h' => h (by have := (thr_iff _ _).mp h'; omega))]; rfl
    subst hy
    cases x
    simp only at hfth hmc hS ha hv hstep ⊢
    subst hfth ha hv hS
    rw [hstep, hmc]
    rfl
  · rw [visitsCost_eq P e L Z hZ]
    have hc1 := checkCost_le (x.a + majCount P e Z (s + 1)) (x.v + (List.finRange P.walkLen).length) (x.s + 1)
      P.walkLen P.M (by omega) (by omega)
    rw [hv, List.length_finRange, Nat.zero_add] at hc1
    have hfl : (y.fth) ≤ (flatTable P e L).length := by
      rw [hy]; have := flatTable_visits P e L; rw [this]; simp
    unfold sBodyBound
    rw [hv, List.length_finRange, Nat.zero_add]
    omega

/-! ## The states -/

/-- The states, counted down in `MC`. -/
def sLoop : MProg := .whr mMC sBody

theorem lastRows_len {κ : Type} (R : κ → ℕ → List Bool) (J L : ℕ) (hR : ∀ k j, j ≤ J → (R k j).length = L) :
    ∀ (ks : List κ) (r : ℕ → List Bool), (∀ j ≤ J, (r j).length = L) → ∀ j ≤ J, (lastRows R ks r j).length = L
  | [], _, hr => hr
  | k :: ks, _, _ => lastRows_len R J L hR ks (R k) (fun j hj => hR k j hj)

theorem sLoop_spec (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (Z : List Bool) (hZ : Z.length = L)
    (hc : MajCap P e L cap) :
    ∀ (m s k : ℕ) (rowsT : ℕ → List Bool) (x : MSt), s + m = P.M → (∀ j ≤ P.base.J, (rowsT j).length = L) →
    x.pt = frame Z → x.t5 = levelWord P.M P.base.J P.base.W rowsT → x.t5h = 0 →
    x.ss = List.replicate s true ++ List.replicate k false → x.ssh = 0 → x.ft = flatTable P e L → x.fth = 0 →
    x.c = 0 → x.a = 0 → x.v = 0 → x.s = s → x.r = accR P e Z s → x.mc = m → x.tt = 0 → x.f = 0 → x.t2 = 0 →
    ∃ (rowsF : ℕ → List Bool) (b : Bool) (n : ℕ), n ≤ m * (sBodyBound P e L + 2) + 1 ∧
      (∀ j ≤ P.base.J, (rowsF j).length = L) ∧
      WExec cap sLoop x.w
        { x with t5 := levelWord P.M P.base.J P.base.W rowsF,
                 ss := List.replicate P.M true ++ List.replicate (k - m) false, s := P.M, r := accR P e Z P.M,
                 mc := 0, cell := b }.w n
  | 0, s, k, rowsT, x, hsm, hrows, _, ht5, _, hss, _, _, _, _, _, _, hS, hr, hmc, _, _, _ => by
    refine ⟨rowsT, x.cell, 1, by omega, hrows, WExec.cast cap (WExec.whrF (show x.w.val mMC = 0 from hmc)) ?_
      (le_refl _)⟩
    have hs : s = P.M := by omega
    subst hs
    cases x
    simp only at ht5 hss hS hr hmc ⊢
    subst ht5 hss hS hr hmc
    simp
  | m + 1, s, k, rowsT, x, hsm, hrows, hpt, ht5, ht5h, hss, hssh, hft, hfth, hc0, ha, hv, hS, hr, hmc, htt, hf,
      h2 => by
    obtain ⟨b, n, hn, s1⟩ := sBody_spec cap P e L Z hZ hc s k m (by omega) (by omega) rowsT hrows x hpt ht5 ht5h hss
      hssh hft hfth hc0 ha hv hS hr hmc htt hf h2
    have hlast := lastRows_len (visitRows P e L) P.base.J L (fun k j _ => by simp [visitRows, rowsOf])
      (List.finRange P.walkLen) rowsT hrows
    obtain ⟨rowsF, b', n', hn', hrF, s2⟩ := sLoop_spec P e L Z hZ hc m (s + 1) (k - 1)
      (lastRows (visitRows P e L) (List.finRange P.walkLen) rowsT)
      { x with t5 := levelWord P.M P.base.J P.base.W (lastRows (visitRows P e L) (List.finRange P.walkLen) rowsT),
               ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false, s := s + 1,
               r := accR P e Z (s + 1), mc := m, cell := b }
      (by omega) hlast hpt rfl ht5h rfl hssh hft hfth hc0 ha hv rfl rfl rfl htt hf h2
    refine ⟨rowsF, b', n + 2 + n', by nlinarith, hrF,
      WExec.cast cap (WExec.whrT (show x.w.val mMC ≠ 0 by show x.mc ≠ 0; omega) s1 s2) ?_ (le_refl _)⟩
    have hk : k - 1 - m = k - (m + 1) := by omega
    cases x
    simp only [hk]

/-! ## Setup and cleanup -/

theorem m_readU (x : MSt) (n : ℕ) :
    ((x.w.seth sT5 (x.w.sh sT5 + n + 1)).setv mTP (x.w.val mTP + n + 1)).setv mMC (x.w.val mMC + n) =
      { x with t5h := x.t5h + n + 1, mc := x.mc + n }.w := by mst_eq

/-- Read `M` from the template into `MC`, the template rewound. -/
def setupM : MProg := .seq (WM.readU sT5 mTP mMC) (WM.rewind sT5 mTP)

theorem setup_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (x : MSt) (ht : x.t5 = levelWord M J W row)
    (hth : x.t5h = 0) (hmc : x.mc = 0) (hc : M + 1 ≤ cap) :
    WExec cap setupM x.w { x with mc := M }.w ((11 * M + 7) + 1 + (5 * (M + 1) + 1)) := by
  have hw : x.t5 = List.replicate M true ++ false :: ((levels J).flatMap (record J W row) ++ [false]) := by
    rw [ht]; simp [levelWord, unary]
  have s1 := wreadU_spec cap sT5 mTP mMC (by decide) M x.w
    (fun k hk => by show readTapeBit x.t5 (x.t5h + k) = true; rw [hw, hth, Nat.zero_add]
                    exact readTapeBit_unary_lt M k _ hk)
    (by show readTapeBit x.t5 (x.t5h + M) = false; rw [hw, hth, Nat.zero_add]; exact readTapeBit_unary_end M _)
    (by show x.t5h + M + 1 ≤ cap; omega) (by show x.mc + M ≤ cap; omega)
  rw [m_readU] at s1
  have s2 := wrewind_spec cap sT5 mTP ({ x with t5h := x.t5h + M + 1, mc := x.mc + M } : MSt).t5h
    ({ x with t5h := x.t5h + M + 1, mc := x.mc + M } : MSt).w rfl (by show x.t5h + M + 1 ≤ cap; omega)
  rw [m_t5_rew] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by simp only [hth]; omega)
  cases x; simp only at hth hmc ⊢; subst hth hmc; simp

theorem read_allFalse (l : List Bool) (hl : ∀ b ∈ l, b = false) (p : ℕ) : readTapeBit l p = false := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD]
  cases h : l[p]? with
  | none => rfl
  | some b => exact hl b (List.mem_of_getElem? h)

/-- Clear the compared state: every `true` of stream 2 overwritten by `false`. -/
def clrStep : MProg := .seq (.wr sSS false) fwdSS

theorem clrLoop_spec (k : ℕ) : ∀ (i j : ℕ) (x : MSt),
    x.ss = List.replicate j false ++ List.replicate i true ++ List.replicate k false → x.ssh = j → j + i < cap →
    WExec cap (.whs sSS clrStep) x.w
      { x with ss := List.replicate (j + i) false ++ List.replicate k false, ssh := j + i }.w (9 * i + 1)
  | 0, j, x, hs, hh, _ => by
    have hb : wbit x.w sSS = false := by
      rw [wbit_ss, hs, hh]
      exact read_allFalse _ (fun b hb => by simp at hb; tauto) _
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    cases x; simp only at hs hh ⊢; subst hs hh; simp
  | i + 1, j, x, hs, hh, hc => by
    have hb : wbit x.w sSS = true := by
      rw [wbit_ss, hs, hh, List.replicate_succ, List.append_assoc]
      simpa using readTapeBit_mid (List.replicate j false) (List.replicate i true ++ List.replicate k false) true
    have hw : writeTapeBit x.ss x.ssh false = List.replicate (j + 1) false ++ List.replicate i true ++
        List.replicate k false := by
      have hm := writeTapeBit_mid'' (List.replicate j false) (List.replicate i true ++ List.replicate k false) true false
      rw [List.length_replicate] at hm
      rw [hs, hh, List.replicate_succ, List.append_assoc, List.cons_append, hm]
      simp [List.replicate_succ']
    have s1 : WExec cap (.wr sSS false) x.w
        ({ x with ss := List.replicate (j + 1) false ++ List.replicate i true ++ List.replicate k false } : MSt).w 1 := by
      have h := WExec.wr (cap := cap) sSS false x.w
      rw [show x.w.st sSS = x.ss from rfl, show x.w.sh sSS = x.ssh from rfl, hw, m_ss_wr] at h
      exact h
    have s2 := fwdSS_spec cap
      ({ x with ss := List.replicate (j + 1) false ++ List.replicate i true ++ List.replicate k false } : MSt)
      (by simp only; omega)
    have ih := clrLoop_spec k i (j + 1)
      { x with ss := List.replicate (j + 1) false ++ List.replicate i true ++ List.replicate k false,
               ssh := x.ssh + 1 } rfl (by simp only; omega) (by omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq s1 s2) ih) ?_ (by omega)
    have e : j + 1 + i = j + (i + 1) := by omega
    cases x; simp only at hh ⊢; subst hh; simp only [e]

/-- The cleanup: `S` cleared, stream 2 cleared and rewound. -/
def cleanupM : MProg := .seq (WM.clear mS) (.seq (.whs sSS clrStep) (WM.rewind sSS mSP))

theorem cleanup_spec (M k : ℕ) (x : MSt) (hs : x.ss = List.replicate M true ++ List.replicate k false)
    (hh : x.ssh = 0) (hS : x.s = M) (hc : M + 1 ≤ cap) :
    WExec cap cleanupM x.w { x with ss := List.replicate M false ++ List.replicate k false, s := 0 }.w
      ((3 * M + 1) + 1 + ((9 * M + 1) + 1 + (5 * M + 1))) := by
  have s1 := wclear_spec cap mS M x.w hS (show x.s ≤ cap by omega)
  rw [m_s] at s1
  have s2 := clrLoop_spec cap k M 0 { x with s := 0 } (by simp only; rw [hs]; simp) hh (by omega)
  have s3 := wrewind_spec cap sSS mSP
    ({ x with s := 0, ss := List.replicate (0 + M) false ++ List.replicate k false, ssh := 0 + M } : MSt).ssh
    ({ x with s := 0, ss := List.replicate (0 + M) false ++ List.replicate k false, ssh := 0 + M } : MSt).w rfl
    (by show 0 + M ≤ cap; omega)
  rw [m_ss_rew] at s3
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by simp only; omega)
  cases x; simp only at hh ⊢; subst hh; simp

/-! ## The majority machine -/

/-- **The majority machine**: `M` read, the states `1, …, M`, the cleanup. -/
def majM : MProg := .seq setupM (.seq sLoop cleanupM)

/-- The cost bound of the majority machine. -/
def majBound (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) : ℕ :=
  ((11 * P.M + 7) + 1 + (5 * (P.M + 1) + 1)) + 1 + ((P.M * (sBodyBound P e L + 2) + 1) + 1 +
    ((3 * P.M + 1) + 1 + ((9 * P.M + 1) + 1 + (5 * P.M + 1))))

theorem majM_spec (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (Z : List Bool) (hZ : Z.length = L)
    (hc : MajCap P e L cap) (rowsT : ℕ → List Bool) (hrows : ∀ j ≤ P.base.J, (rowsT j).length = L) (k : ℕ)
    (x : MSt) (hpt : x.pt = frame Z) (ht5 : x.t5 = levelWord P.M P.base.J P.base.W rowsT) (ht5h : x.t5h = 0)
    (hss : x.ss = List.replicate k false) (hssh : x.ssh = 0) (hft : x.ft = flatTable P e L) (hfth : x.fth = 0)
    (hc0 : x.c = 0) (ha : x.a = 0) (hv : x.v = 0) (hS : x.s = 0) (hr : x.r = 0) (hmc : x.mc = 0) (htt : x.tt = 0)
    (hf : x.f = 0) (h2 : x.t2 = 0) :
    ∃ (rowsF : ℕ → List Bool) (b : Bool) (n : ℕ), n ≤ majBound P e L ∧ (∀ j ≤ P.base.J, (rowsF j).length = L) ∧
      WExec cap majM x.w
        { x with t5 := levelWord P.M P.base.J P.base.W rowsF,
                 ss := List.replicate P.M false ++ List.replicate (k - P.M) false,
                 r := flatReportFast P e Z, cell := b }.w n := by
  have hcM := hc.hM
  have s1 := setup_spec cap P.M P.base.J P.base.W rowsT x ht5 ht5h hmc (by omega)
  obtain ⟨rowsF, b, n, hn, hrF, s2⟩ := sLoop_spec cap P e L Z hZ hc P.M 0 k rowsT { x with mc := P.M }
    (by omega) hrows hpt ht5 ht5h (by rw [hss]; simp) hssh hft hfth hc0 ha hv hS
    (by rw [hr]; simp [accR]) rfl htt hf h2
  have s3 := cleanup_spec cap P.M (k - P.M)
    ({ x with t5 := levelWord P.M P.base.J P.base.W rowsF,
              ss := List.replicate P.M true ++ List.replicate (k - P.M) false, s := P.M, r := accR P e Z P.M,
              mc := 0, cell := b } : MSt) rfl hssh rfl (by omega)
  refine ⟨rowsF, b, _, ?_, hrF, WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (le_refl _)⟩
  · unfold majBound; omega
  · rw [accR_M] at *
    cases x; simp only at hS hmc ⊢; subst hS hmc; simp

/-- **The majority machine's ports** (for its consumers and controls): the result register holds the amplified
list's report, every other register and head is back at `0`, the point and the flat table are unchanged, the compared
state is blank and the template holds rows of length `L`. -/
theorem majM_ports (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (Z : List Bool) (hZ : Z.length = L)
    (hc : MajCap P e L cap) (rowsT : ℕ → List Bool) (hrows : ∀ j ≤ P.base.J, (rowsT j).length = L) (k : ℕ)
    (x : MSt) (hpt : x.pt = frame Z) (ht5 : x.t5 = levelWord P.M P.base.J P.base.W rowsT) (ht5h : x.t5h = 0)
    (hss : x.ss = List.replicate k false) (hssh : x.ssh = 0) (hft : x.ft = flatTable P e L) (hfth : x.fth = 0)
    (hc0 : x.c = 0) (ha : x.a = 0) (hv : x.v = 0) (hS : x.s = 0) (hr : x.r = 0) (hmc : x.mc = 0) (htt : x.tt = 0)
    (hf : x.f = 0) (h2 : x.t2 = 0) :
    ∃ (y : MSt) (n : ℕ), n ≤ majBound P e L ∧ WExec cap majM x.w y.w n ∧ y.r = flatReportFast P e Z ∧
      y.pt = x.pt ∧ y.ft = x.ft ∧ y.t5h = 0 ∧ y.ssh = 0 ∧ y.fth = 0 ∧ y.c = 0 ∧ y.a = 0 ∧ y.v = 0 ∧ y.s = 0 ∧
      y.mc = 0 ∧ y.tt = 0 ∧ y.f = 0 ∧ y.t2 = 0 ∧ (∀ p, readTapeBit y.ss p = false) ∧
      ∃ rowsF : ℕ → List Bool, (∀ j ≤ P.base.J, (rowsF j).length = L) ∧
        y.t5 = levelWord P.M P.base.J P.base.W rowsF := by
  obtain ⟨rowsF, b, n, hn, hrF, h⟩ := majM_spec cap P e L Z hZ hc rowsT hrows k x hpt ht5 ht5h hss hssh hft hfth
    hc0 ha hv hS hr hmc htt hf h2
  refine ⟨_, n, hn, h, rfl, rfl, rfl, ht5h, hssh, hfth, hc0, ha, hv, hS, hmc, htt, hf, h2, fun p => ?_, rowsF, hrF, rfl⟩
  exact read_allFalse _ (fun b hb => by simp at hb; exact hb.2) p

end NearCubicWires.WireExponent3_5.FinalPass.Maj
