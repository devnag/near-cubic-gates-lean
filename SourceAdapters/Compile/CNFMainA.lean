import SourceAdapters.Compile.CNFRequestB
import SourceAdapters.Compile.CNFRunOK
import SourceAdapters.Compile.CNFBalancedC
import SourceAdapters.Compile.CNFEmit

/-!
# The printer, part A: the token store and its three pieces

proof of `lem:multitape-refuter` (the Cook–Levin tableau of the bounded run is constructed by a fixed polynomial-time procedure):
`genP` writes the postfix token stream of the request once — the initial vector `I`, ONE round template `T`
(identical in every round) and the tail `A` (acceptance, rank, final conjunction), each followed by the sentinel
`inp K'` with `K' = W + n + 2` above every payload. `scanP` recovers the three lengths and the two start positions.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Registers of the main program (110..119, layout: parsing/main scratch range). -/
def mK : Fin VV := ⟨110, by decide⟩
def mS : Fin VV := ⟨111, by decide⟩
def mLI : Fin VV := ⟨112, by decide⟩
def mLT : Fin VV := ⟨113, by decide⟩
def mLA : Fin VV := ⟨114, by decide⟩
def mP2 : Fin VV := ⟨115, by decide⟩
def mP3 : Fin VV := ⟨116, by decide⟩
def mX : Fin VV := ⟨117, by decide⟩
def mT : Fin VV := ⟨118, by decide⟩
def mR : Fin VV := ⟨119, by decide⟩

variable {C : Ctx}

/-! ## Generation -/

/-- `mK := W + n + 2`. -/
def sentP : St VV MM := .seq (.op (.copy mK dW)) (.seq (.op (.add mK dN)) (.seq (.op (.inc mK)) (.op (.inc mK))))

def genP : St VV MM :=
  .seq sentP (.seq initP (.seq (emitInp mK) (.seq tmplP (.seq (emitInp mK) (.seq accP (.seq rankP
    (.seq (emitR kc4) (emitInp mK))))))))

def sentK (D : GD) : ℕ := D.W + D.n + 2
def genI (D : GD) (input : List Bool) : List RTok := initT D.t D.s D.width D.n D.st input
def genT (D : GD) : List RTok := tmplT D.td D.t D.s D.width
def genA (D : GD) (high : ℕ) : List RTok := accT D.td D.s ++ rankT 0 D.n high ++ [.conj]
/-- The stored stream: three pieces, each closed by the sentinel. -/
def ttToks (D : GD) (input : List Bool) (high : ℕ) : List RTok :=
  genI D input ++ [.inp (sentK D)] ++ genT D ++ [.inp (sentK D)] ++ genA D high ++ [.inp (sentK D)]

def genCost (D : GD) (Λ : ℕ) : ℕ := initCost Λ + tmplCost D Λ + accCost Λ + rankCost D.n + 31

theorem sentP_spec (D : GD) (a : DS VV MM) (hG : GC D a) (hK : D.W + D.n + 2 < 2 ^ C.Wd) :
    Hs C sentP a 7 (fun b => b.env mK = sentK D ∧ GC D b ∧ Fr a b [mK] ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      b.ip = a.ip ∧ b.out = a.out) := by
  apply hs_of_wpc
  simp only [sentP, wpc, opwp]
  vsimp [hG.W, hG.n]
  exact ⟨by omega, by omega, by omega, by unfold sentK; omega,
    hG.of (b := a.set mK (D.W + D.n + 1 + 1)) (T := [mK]) (Ext.of_eq rfl rfl rfl rfl)
      (Fr.set (x := mK) a _ (List.mem_singleton_self _)) (by decide),
    Fr.set (x := mK) a _ (List.mem_singleton_self _)⟩

theorem genP_spec (D : GD) (Λ : ℕ) (hOk : D.Ok Λ) (hΛ : 64 * Λ + 64 ≤ 2 ^ C.Wd) (input : List Bool)
    (hib : D.ib = input.map Bool.toNat) (high : ℕ) (a : DS VV MM) (hG : GC D a) (hH : a.env dH = high)
    (hW : 2 ^ (D.n + 1) ≤ 2 ^ C.Wd) (hK : 8 * (D.W + D.n + 2) + 10 < 2 ^ C.Wd) :
    Hs C genP a (genCost D Λ) (fun b => Ext a b (ttToks D input high) ∧ b.env mK = sentK D ∧ GC D b ∧
      (genI D input).length ≤ initCost Λ ∧ (genT D).length ≤ tmplCost D Λ ∧
      (genA D high).length ≤ accCost Λ + rankCost D.n + 1) := by
  have hn8 : 8 * D.n + 10 < 2 ^ C.Wd := by omega
  have hK8 : 8 * sentK D + 2 < 2 ^ C.Wd := by unfold sentK; omega
  refine Hs.seqc (t1 := 7) (t2 := initCost Λ + tmplCost D Λ + accCost Λ + rankCost D.n + 23)
    (sentP_spec D a hG (by omega)) (fun b1 ⟨k1, g1, f1, r1, c1, i1, o1⟩ => ?_) (by unfold genCost; omega)
  have hE1 : Ext a b1 [] := Ext.of_eq r1 c1 i1 o1
  have h1 : b1.env dH = high := by rw [f1 dH (by decide), hH]
  refine Hs.seqc (t1 := initCost Λ) (t2 := tmplCost D Λ + accCost Λ + rankCost D.n + 22)
    (Hs.ramLen (initP_spec D Λ hOk hΛ input hib b1 g1) sTT) (fun b2 ⟨⟨e2, f2⟩, l2⟩ => ?_) (by omega)
  have g2 := g1.of e2 f2 (by decide)
  have k2 : b2.env mK = sentK D := by rw [f2 mK (by decide), k1]
  have h2 : b2.env dH = high := by rw [f2 dH (by decide), h1]
  refine Hs.seqc (t1 := 5) (t2 := tmplCost D Λ + accCost Λ + rankCost D.n + 16)
    (emitInp_spec mK (by decide) (by decide) b2 g2.tt g2.kc (by rw [k2]; exact hK8))
    (fun b3 ⟨e3, f3⟩ => ?_) (by omega)
  have g3 := g2.of e3 f3 (by decide)
  have k3 : b3.env mK = sentK D := by rw [f3 mK (by decide), k2]
  have h3 : b3.env dH = high := by rw [f3 dH (by decide), h2]
  refine Hs.seqc (t1 := tmplCost D Λ) (t2 := accCost Λ + rankCost D.n + 15)
    (Hs.ramLen (tmplP_spec D Λ hOk hΛ b3 g3) sTT) (fun b4 ⟨⟨e4, f4⟩, l4⟩ => ?_) (by omega)
  have g4 := g3.of e4 f4 (by decide)
  have k4 : b4.env mK = sentK D := by rw [f4 mK (by decide), k3]
  have h4 : b4.env dH = high := by rw [f4 dH (by decide), h3]
  refine Hs.seqc (t1 := 5) (t2 := accCost Λ + rankCost D.n + 9)
    (emitInp_spec mK (by decide) (by decide) b4 g4.tt g4.kc (by rw [k4]; exact hK8))
    (fun b5 ⟨e5, f5⟩ => ?_) (by omega)
  have g5 := g4.of e5 f5 (by decide)
  have k5 : b5.env mK = sentK D := by rw [f5 mK (by decide), k4]
  have h5 : b5.env dH = high := by rw [f5 dH (by decide), h4]
  refine Hs.seqc (t1 := accCost Λ) (t2 := rankCost D.n + 8)
    (Hs.ramLen (accP_spec D Λ hOk hΛ b5 g5) sTT) (fun b6 ⟨⟨e6, f6⟩, l6⟩ => ?_) (by omega)
  have g6 := g5.of e6 f6 (by decide)
  have k6 : b6.env mK = sentK D := by rw [f6 mK (by decide), k5]
  have h6 : b6.env dH = high := by rw [f6 dH (by decide), h5]
  refine Hs.seqc (t1 := rankCost D.n) (t2 := 7)
    (Hs.ramLen (rankP_spec D.n high b6 ⟨g6.kc, g6.tt, g6.n⟩ h6 hW hn8) sTT) (fun b7 ⟨⟨e7, f7⟩, l7⟩ => ?_)
    (by omega)
  have g7 := g6.of e7 f7 (by decide)
  have k7 : b7.env mK = sentK D := by rw [f7 mK (by decide), k6]
  refine Hs.seqc (t1 := 1) (t2 := 5) (emitR_spec kc4 .conj b7 g7.tt g7.kc.k4) (fun b8 ⟨e8, f8⟩ => ?_)
    (by omega)
  have g8 := g7.of e8 f8 (by decide)
  have k8 : b8.env mK = sentK D := by rw [f8 mK (by decide), k7]
  refine Hs.mono (emitInp_spec mK (by decide) (by decide) b8 g8.tt g8.kc (by rw [k8]; exact hK8)) le_rfl ?_
  rintro b9 ⟨e9, f9⟩
  have hE := (((((((hE1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8).trans e9
  refine ⟨hE.congr (by simp [ttToks, genI, genT, genA, k2, k4, k8]), by rw [f9 mK (by decide), k8],
    g8.of e9 f9 (by decide), e2.len_le l2, e4.len_le l4, ?_⟩
  have := e6.len_le l6
  have := e7.len_le l7
  simp only [genA, List.length_append, List.length_singleton]; omega

/-! ## Scanning the three lengths -/

/-- Count the records of `sTT` from its cursor that are below `mS` into `c` (reading the stopping record). -/
def scanOne (c : Fin VV) : St VV MM :=
  .seq (.op (.zero c)) (.seq (.op (.rdM sTT mX)) (.loop (.lt mX mS) (.seq (.op (.inc c)) (.op (.rdM sTT mX)))))

theorem scanOne_spec (c : Fin VV) (hc : c ∉ [mX, mS]) (pre seg rest : List ℕ) (S : ℕ) (a : DS VV MM)
    (hS : a.env mS = S) (htt : a.ram sTT = pre ++ seg ++ [S] ++ rest) (hrc : a.rc sTT = pre.length)
    (hlt : ∀ x ∈ seg, x < S) (hW : seg.length + 1 < 2 ^ C.Wd) :
    Hs C (scanOne c) a (5 * seg.length + 6) (fun b => b.env c = seg.length ∧
      b.rc sTT = pre.length + seg.length + 1 ∧ b.ram = a.ram ∧ (∀ m, m ≠ sTT → b.rc m = a.rc m) ∧
      Fr a b [c, mX]) := by
  have hc' : c ≠ mX ∧ c ≠ mS := by simpa using hc
  set k := seg.length with hk
  have hget : ∀ i ≤ k, (a.ram sTT).getD (pre.length + i) 0 = (seg ++ [S]).getD i 0 := by
    intro i hi
    rw [htt, List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [← List.append_assoc, List.getD_append _ _ _ _ (by simp; omega)]
  have hlen : pre.length + k < (a.ram sTT).length := by rw [htt]; simp; omega
  let I : ℕ → DS VV MM → Prop := fun i b => b.env c = i ∧ b.rc sTT = pre.length + i + 1 ∧
    b.env mX = (seg ++ [S]).getD i 0 ∧ b.ram = a.ram ∧ (∀ m, m ≠ sTT → b.rc m = a.rc m) ∧ Fr a b [c, mX]
  have hloop := Hs.loopN (C := C) (c := .lt mX mS) (s := .seq (.op (.inc c)) (.op (.rdM sTT mX)))
    (show mX ≠ mS by decide) I k 3
    (fun i hi b ⟨b1, b2, b3, b4, b5, b6⟩ => by
      have bS : b.env mS = S := by rw [b6 mS (by simp; exact ⟨Ne.symm hc'.2, by decide⟩), hS]
      have hx : (seg ++ [S]).getD i 0 < S := by
        rw [List.getD_append _ _ _ _ hi]; exact hlt _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
      refine ⟨by simp only [Cnd.eval, b3, bS, decide_eq_true_eq]; exact hx, ?_⟩
      refine Hs.seqc (t1 := 1) (t2 := 1) (hs_inc C c b (by rw [b1]; omega)) (fun d hd => ?_) (by omega)
      subst hd
      refine Hs.op (OpEx.rdM sTT mX _ (by simp [b2, b4]; omega)) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [DS.adv, DS.set, Function.update_apply, hc'.1, b1]
      · simp [DS.adv, b2]; omega
      · simp only [DS.adv, DS.set_ram, DS.set_rc, DS.env_set, Function.update_self, b2, b4]
        rw [show pre.length + i + 1 = pre.length + (i + 1) by omega, hget (i + 1) (by omega)]
      · simp [DS.adv, b4]
      · intro m hm; simp [DS.adv, Function.update_of_ne hm, b5 m hm]
      · intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [DS.adv, DS.set, Function.update_apply, hy.1, hy.2]
        exact b6 y (by simp [hy.1, hy.2]))
    (fun b ⟨_, _, b3, _, _, b6⟩ => by
      have bS : b.env mS = S := by rw [b6 mS (by simp; exact ⟨Ne.symm hc'.2, by decide⟩), hS]
      simp only [Cnd.eval, b3, bS, List.getD_append_right _ _ _ _ (le_of_eq hk.symm)]
      simp [hk])
  refine Hs.seqc (t1 := 1) (t2 := 5 * k + 4) (hs_zero C c a) (fun b1 hb1 => ?_) (by omega)
  subst hb1
  refine Hs.seqc (t1 := 1) (t2 := k * (3 + 2) + 2) (hs_rdM C sTT mX _ (by simp [hrc]; omega))
    (fun b2 hb2 => ?_) (by omega)
  subst hb2
  refine Hs.mono (hloop _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl (fun b ⟨q1, q2, _, q4, q5, q6⟩ => ⟨q1, q2, q4, q5, q6⟩)
  · simp [DS.adv, DS.set, Function.update_apply, hc'.1]
  · simp [DS.adv, hrc]
  · simp only [DS.adv, DS.set_ram, DS.set_rc, DS.env_set, Function.update_self, hrc]
    have := hget 0 (by omega); simpa using this
  · rfl
  · intro m hm; simp [DS.adv, Function.update_of_ne hm]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [DS.adv, DS.set, Function.update_apply, hy.1, hy.2]

/-- `mP2 := |I| + 1`, `mP3 := |I| + 1 + |T| + 1`. -/
def posP : St VV MM :=
  .seq (.op (.copy mP2 mLI)) (.seq (.op (.inc mP2)) (.seq (.op (.copy mP3 mP2)) (.seq (.op (.add mP3 mLT))
    (.op (.inc mP3)))))

def scanP : St VV MM :=
  .seq (.op (.mul mK kc8 mS)) (.seq (.op (.inc mS)) (.seq (.op (.rwM sTT)) (.seq (scanOne mLI)
    (.seq (scanOne mLT) (.seq (scanOne mLA) posP)))))

theorem scanP_spec (l1 l2 l3 : List RTok) (K : ℕ) (a : DS VV MM) (hk : KC a) (hK : a.env mK = K)
    (htt : a.ram sTT = (l1 ++ [RTok.inp K] ++ l2 ++ [RTok.inp K] ++ l3 ++ [RTok.inp K]).map tcode)
    (hrc : a.rc sTT ≤ l1.length + l2.length + l3.length + 3)
    (hpay : ∀ t ∈ l1 ++ l2 ++ l3, tcode t < 8 * K + 1)
    (hW : 8 * K + l1.length + l2.length + l3.length + 10 < 2 ^ C.Wd) :
    Hs C scanP a (6 * (l1.length + l2.length + l3.length) + 60) (fun b => b.env mLI = l1.length ∧
      b.env mLT = l2.length ∧ b.env mLA = l3.length ∧ b.env mP2 = l1.length + 1 ∧
      b.env mP3 = l1.length + 1 + l2.length + 1 ∧ b.ram = a.ram ∧ (∀ m, m ≠ sTT → b.rc m = a.rc m) ∧
      b.rc sTT = l1.length + l2.length + l3.length + 3) := by
  set S := 8 * K + 1 with hSdef
  set L1 := l1.map tcode
  set L2 := l2.map tcode
  set L3 := l3.map tcode
  have hL1 : L1.length = l1.length := List.length_map _
  have hL2 : L2.length = l2.length := List.length_map _
  have hL3 : L3.length = l3.length := List.length_map _
  have htt' : a.ram sTT = L1 ++ [S] ++ L2 ++ [S] ++ L3 ++ [S] := by
    rw [htt]; simp [L1, L2, L3, tcode, hSdef]
  have h1 : ∀ x ∈ L1, x < S := fun x hx => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact hpay t (by simp [ht])
  have h2 : ∀ x ∈ L2, x < S := fun x hx => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact hpay t (by simp [ht])
  have h3 : ∀ x ∈ L3, x < S := fun x hx => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact hpay t (by simp [ht])
  refine Hs.seqc (t1 := 1) (t2 := 6 * (l1.length + l2.length + l3.length) + 58)
    (hs_mul C mK kc8 mS a (by decide) (by decide) (by decide) (by rw [hK, hk.k8]; omega)) (fun b1 hb1 => ?_)
    (by omega)
  subst hb1
  refine Hs.seqc (t1 := 1) (t2 := 6 * (l1.length + l2.length + l3.length) + 56)
    (hs_inc C mS _ (by vsimp [hK, hk.k8]; omega)) (fun b2 hb2 => ?_) (by omega)
  subst hb2
  set a2 := (a.set mS (a.env mK * a.env kc8)).set mS ((a.set mS (a.env mK * a.env kc8)).env mS + 1) with ha2
  have a2S : a2.env mS = S := by rw [ha2]; vsimp [hK, hk.k8]; ring
  refine Hs.seqc (t1 := l1.length + l2.length + l3.length + 4)
    (t2 := 5 * (l1.length + l2.length + l3.length) + 51) (Hs.mono (hs_rwM C sTT a2)
      (by rw [show a2.rc sTT = a.rc sTT from rfl]; omega) (fun b h => h)) (fun b3 hb3 => ?_) (by omega)
  subst hb3
  refine Hs.seqc (t1 := 5 * L1.length + 6) (t2 := 5 * (l2.length + l3.length) + 44)
    (scanOne_spec mLI (by decide) [] L1 (L2 ++ [S] ++ L3 ++ [S]) S (a2.rew sTT) a2S
      (by show a.ram sTT = _; rw [htt']; simp) (by simp [DS.rew]) h1 (by omega))
    (fun b4 ⟨d4, r4, m4, c4, f4⟩ => ?_) (by omega)
  have b4S : b4.env mS = S := by rw [f4 mS (by decide)]; exact a2S
  refine Hs.seqc (t1 := 5 * L2.length + 6) (t2 := 5 * l3.length + 32)
    (scanOne_spec mLT (by decide) (L1 ++ [S]) L2 (L3 ++ [S]) S b4 b4S
      (by rw [m4]; show a.ram sTT = _; rw [htt']; simp) (by rw [r4]; simp) h2 (by omega))
    (fun b5 ⟨d5, r5, m5, c5, f5⟩ => ?_) (by omega)
  have b5S : b5.env mS = S := by rw [f5 mS (by decide), b4S]
  refine Hs.seqc (t1 := 5 * L3.length + 6) (t2 := 9)
    (scanOne_spec mLA (by decide) (L1 ++ [S] ++ L2 ++ [S]) L3 [] S b5 b5S
      (by rw [m5, m4]; show a.ram sTT = _; rw [htt']; simp) (by rw [r5]; simp; omega) h3 (by omega))
    (fun b6 ⟨d6, r6, m6, c6, f6⟩ => ?_) (by omega)
  have e1 : b6.env mLI = l1.length := by rw [f6 mLI (by decide), f5 mLI (by decide), d4, hL1]
  have e2 : b6.env mLT = l2.length := by rw [f6 mLT (by decide), d5, hL2]
  have e3 : b6.env mLA = l3.length := by rw [d6, hL3]
  apply hs_of_wpc
  simp only [posP, wpc, opwp]
  vsimp [e1, e2, e3]
  exact ⟨by omega, by omega, by omega, by rw [m6, m5, m4]; rfl,
    fun m hm => by rw [c6 m hm, c5 m hm, c4 m hm]; exact DS.rew_rc_ne _ hm, by rw [r6]; simp [L1, L2, L3]; omega⟩

end NearCubicGates.Adapters.Compile
