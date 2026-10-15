import Proof.Gates.Dispatch.Arith2
import Proof.Gates.TomographyDirections

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

variable {C : Ctx}

def IPQ : Fin VV := ⟨119, by decide⟩
def IPF : Fin VV := ⟨120, by decide⟩
def IPD : Fin VV := ⟨121, by decide⟩
def IPQ2 : Fin VV := ⟨122, by decide⟩
def IPR : Fin VV := ⟨123, by decide⟩
def TOM : Fin VV := ⟨124, by decide⟩
def TOC : Fin VV := ⟨125, by decide⟩
def TOJ : Fin VV := ⟨126, by decide⟩
def DSQ1 : Fin VV := ⟨127, by decide⟩
def DSS : Fin VV := ⟨128, by decide⟩
def DSM : Fin VV := ⟨129, by decide⟩
def DST : Fin VV := ⟨130, by decide⟩

/-! ## Primality -/

def ipBody : St VV :=
  .seq (.op (.dm IPQ IPD IPQ2 IPR)) (.seq (.ite (.eq IPR vZ) (.op (.zero IPF)) skipS) (.op (.inc IPD)))

def isPrimeV : St VV :=
  .seq (setK IPD 2) (.seq (.op (.copy IPF v1)) (.seq (.ite (.lt IPQ v2) (.op (.zero IPF)) skipS)
    (.loop (.lt IPD IPQ) ipBody)))

def ipT : List (Fin VV) := [IPF, IPD, IPQ2, IPR, vJ]

theorem isPrimeV_spec (a : DS VV) (hc : Cst a) (q : ℕ) (hq : a.env IPQ = q) (hW : 2 * q + 4 < 2 ^ C.Wd) :
    Hs C isPrimeV a (q * 9 + 20) (fun b => b.env IPF = bnat (Nat.Prime q) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ Fr a b ipT) := by
  let Q : ℕ → Prop := fun d => 2 ≤ q ∧ ∀ m, 2 ≤ m → m < d → ¬ m ∣ q
  let I : ℕ → DS VV → Prop := fun k b => b.env IPD = 2 + k ∧ b.env IPF = bnat (Q (2 + k)) ∧ b.env IPQ = q ∧
    b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b ipT
  have l : ∀ b, I 0 b → Hs C (.loop (.lt IPD IPQ) ipBody) b ((q - 2) * (6 + 2) + 2) (I (q - 2)) := by
    refine Hs.loopN (c := .lt IPD IPQ) (show IPD ≠ IPQ by decide) I (q - 2) 6 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine ⟨by simp only [Cnd.eval, h1, h3, decide_eq_true_eq]; omega, ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 4) (hs_dm C IPQ IPD IPQ2 IPR b (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by rw [h1]; omega) (by rw [h1]; omega)) (fun d hd => ?_)
      subst hd
      set d := (b.set IPQ2 (b.env IPQ / b.env IPD)).set IPR (b.env IPQ % b.env IPD) with hdd
      have dR : d.env IPR = q % (2 + k) := by rw [hdd]; vsimp [h1, h3]
      have dF : d.env IPF = bnat (Q (2 + k)) := by rw [hdd]; vsimp [h2]
      have dc : Cst d := by rw [hdd]; exact (h7.set _ _ (by decide)).set _ _ (by decide)
      have hQ : Q (2 + k + 1) ↔ Q (2 + k) ∧ q % (2 + k) ≠ 0 := by
        constructor
        · rintro ⟨h2q, hall⟩
          exact ⟨⟨h2q, fun m hm1 hm2 => hall m hm1 (by omega)⟩, fun h0 => hall (2 + k) (by omega) (by omega)
            (Nat.dvd_of_mod_eq_zero h0)⟩
        · rintro ⟨⟨h2q, hall⟩, hne⟩
          refine ⟨h2q, fun m hm1 hm2 hdvd => ?_⟩
          rcases Nat.lt_or_ge m (2 + k) with h | h
          · exact hall m hm1 h hdvd
          · have : m = 2 + k := by omega
            subst this; exact hne (Nat.mod_eq_zero_of_dvd hdvd)
      have step : Hs C (.ite (.eq IPR vZ) (.op (.zero IPF)) skipS) d 2 (fun e => e.env IPF = bnat (Q (2 + k + 1)) ∧
          e.cp = d.cp ∧ e.wq = d.wq ∧ e.out = d.out ∧ Fr d e [IPF, vJ]) := by
        refine Hs.ite (c := .eq IPR vZ) (show IPR ≠ vZ by decide) (fun he => ?_) (fun he => ?_)
        · have h0 : q % (2 + k) = 0 := by simpa [Cnd.eval, dR, dc.z] using he
          refine Hs.mono (hs_zero C IPF d) le_rfl ?_
          rintro e rfl
          exact ⟨by rw [DS.set_env_self, bnat_congr hQ]; unfold bnat; simp [h0], rfl, rfl, rfl, Fr.set d _ (by decide)⟩
        · have h0 : q % (2 + k) ≠ 0 := by simpa [Cnd.eval, dR, dc.z] using he
          refine Hs.mono (skip_spec d) le_rfl ?_
          rintro e rfl
          exact ⟨by rw [DS.set_env_ne _ _ (by decide), dF, bnat_congr hQ]; exact bnat_congr (by simp [h0]), rfl, rfl,
            rfl, Fr.set d _ (by decide)⟩
      refine Hs.seq (t2 := 1) step (fun e ⟨e1, e2, e3, e4, e5⟩ => ?_)
      refine Hs.mono (hs_inc C IPD e (by rw [e5 IPD (by decide), hdd]; vsimp [h1]; omega)) le_rfl ?_
      rintro g rfl
      have eD : e.env IPD = 2 + k := by rw [e5 IPD (by decide), hdd]; vsimp [h1]
      refine ⟨by vsimp [eD]; ring, by vsimp [e1, show 2 + k + 1 = 2 + (k + 1) by ring],
        by vsimp [e5 IPQ (by decide), hdd, h3], by rw [← h4]; exact e2,
        by rw [← h5]; exact e3, by rw [← h6]; exact e4, ?_, ?_⟩
      · exact (Cst.of_fr dc e5 (by decide) (by rw [e5 vPOS (by decide), dc.pos, e2])).set _ _ (by decide)
      · exact Fr.trans h8 (Fr.trans (by rw [hdd]; exact Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
          (Fr.trans (Fr.weaken e5 (by decide)) (Fr.set _ _ (by decide))))
    · intro b ⟨h1, _, h3, _⟩
      simp only [Cnd.eval, h1, h3, decide_eq_false_iff_not]; omega
  refine Hx.hs (Hs.then (setK_spec IPD (by decide) 2 a (by omega)) (fun b ⟨b1, b2, b3, b4, b5⟩ n1 hn1 => ?_))
  have bc : Cst b := Cst.of_fr hc (Fr.weaken b5 (by decide : ∀ y ∈ [IPD, vJ], y ∈ [IPD, vJ])) (by decide)
    (by rw [b5 vPOS (by decide), b2]; exact hc.pos)
  refine Hs.then (hs_copy C IPF v1 b (by decide)) (fun d hd n2 hn2 => ?_)
  subst hd
  have step : Hs C (.ite (.lt IPQ v2) (.op (.zero IPF)) skipS) (b.set IPF (b.env v1)) 2 (fun e =>
      e.env IPF = bnat (Q 2) ∧ e.cp = b.cp ∧ e.wq = b.wq ∧ e.out = b.out ∧ Fr (b.set IPF (b.env v1)) e [IPF, vJ]) := by
    have bq : (b.set IPF (b.env v1)).env IPQ = q := by
      rw [DS.set_env_ne _ _ (by decide), b5 IPQ (by decide), hq]
    have bv2 : (b.set IPF (b.env v1)).env v2 = 2 := by rw [DS.set_env_ne _ _ (by decide), bc.two]
    refine Hs.ite (c := .lt IPQ v2) (show IPQ ≠ v2 by decide) (fun he => ?_) (fun he => ?_)
    · have h0 : q < 2 := by simp only [Cnd.eval, decide_eq_true_eq, bq, bv2] at he; exact he
      refine Hs.mono (hs_zero C IPF _) le_rfl ?_
      rintro e rfl
      refine ⟨by rw [DS.set_env_self]; unfold bnat; simp [Q, show ¬ 2 ≤ q by omega], rfl, rfl, rfl,
        Fr.set _ _ (by decide)⟩
    · have h0 : 2 ≤ q := by simp only [Cnd.eval, decide_eq_false_iff_not, not_lt, bq, bv2] at he; exact he
      refine Hs.mono (skip_spec _) le_rfl ?_
      rintro e rfl
      refine ⟨?_, rfl, rfl, rfl, Fr.set _ _ (by decide)⟩
      rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, bc.one]
      unfold bnat
      rw [decide_eq_true (show Q 2 from ⟨h0, fun m h1 h2 => by omega⟩)]
      rfl
  refine Hs.then step (fun e ⟨e1, e2, e3, e4, e5⟩ n3 hn3 => ?_)
  refine Hs.last (l e ⟨by rw [e5 IPD (by decide)]; vsimp [b1], by simpa using e1,
    by rw [e5 IPQ (by decide)]; vsimp [b5 IPQ (by decide), hq], by rw [e2]; exact b2, by rw [e3]; exact b3,
    by rw [e4]; exact b4, ?_, ?_⟩) ?_
  · exact Cst.of_fr (bc.set _ _ (by decide)) e5 (by decide) (by rw [e5 vPOS (by decide), e2]; vsimp [bc.pos])
  · exact Fr.trans (Fr.weaken b5 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken e5 (by decide)))
  · rintro g ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ n4 hn4
    refine ⟨⟨?_, g4, g5, g6, g7, g8⟩, by omega⟩
    rw [g2]
    apply bnat_congr
    rw [Nat.prime_def_lt']
    constructor
    · rintro ⟨h2q, hall⟩
      exact ⟨h2q, fun m hm1 hm2 => hall m hm1 (by omega)⟩
    · rintro ⟨h2q, hall⟩
      exact ⟨h2q, fun m hm1 hm2 => hall m hm1 (by omega)⟩

/-! ## Totient -/

theorem card_filter_range_succ (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    ((Finset.range (k + 1)).filter P).card = ((Finset.range k).filter P).card + (if P k then 1 else 0) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

def toBody : St VV :=
  .seq (.op (.copy GCA TOM)) (.seq (.op (.copy GCB TOJ)) (.seq gcdv (.seq (.ite (.eq GCA v1) (.op (.inc TOC)) skipS)
    (.op (.inc TOJ)))))

def totientV : St VV := .seq (.op (.zero TOC)) (.seq (.op (.zero TOJ)) (.loop (.lt TOJ TOM) toBody))

def totT : List (Fin VV) := [TOC, TOJ, GCA, GCB, GCQ, GCR, vJ]

theorem totientV_spec (a : DS VV) (hc : Cst a) (m : ℕ) (hm : a.env TOM = m) (hW : 2 * m + 2 ≤ 2 ^ C.Wd) :
    Hs C totientV a (m * (28 * m + 30) + 10) (fun b => b.env TOC = Nat.totient m ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ Fr a b totT) := by
  let I : ℕ → DS VV → Prop := fun k b => b.env TOJ = k ∧ b.env TOC = ((Finset.range k).filter m.Coprime).card ∧
    b.env TOM = m ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b totT
  have hsz : Nat.size m ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h]; rfl
    · exact Nat.size_le.2 Nat.lt_two_pow_self
  have l : ∀ b, I 0 b → Hs C (.loop (.lt TOJ TOM) toBody) b (m * (28 * m + 28 + 2) + 2) (I m) := by
    refine Hs.loopN (c := .lt TOJ TOM) (show TOJ ≠ TOM by decide) I m (28 * m + 28) ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine ⟨by simp [Cnd.eval, h1, h3, hk], ?_⟩
      refine Hx.hs (Hs.then (hs_copy C GCA TOM b (by decide)) (fun b1 e1 n1 hn1 => ?_))
      subst e1
      refine Hs.then (hs_copy C GCB TOJ _ (by decide)) (fun b2 e2 n2 hn2 => ?_)
      subst e2
      have hsk : Nat.size k ≤ m := le_trans (Nat.size_le_size hk.le) hsz
      refine Hs.then (gcdv_spec _ ((h7.set _ _ (by decide)).set _ _ (by decide)) m k m (by vsimp [h3]) (by vsimp [h1])
        le_rfl hk.le (by omega)) (fun b3 ⟨g1, g2, g3, g4, g5, g6⟩ n3 hn3 => ?_)
      have b3C : b3.env TOC = ((Finset.range k).filter m.Coprime).card := by rw [g6 TOC (by decide)]; vsimp [h2]
      have b3J : b3.env TOJ = k := by rw [g6 TOJ (by decide)]; vsimp [h1]
      have step : Hs C (.ite (.eq GCA v1) (.op (.inc TOC)) skipS) b3 2 (fun e =>
          e.env TOC = ((Finset.range (k + 1)).filter m.Coprime).card ∧ e.cp = b3.cp ∧ e.wq = b3.wq ∧ e.out = b3.out ∧
          Fr b3 e [TOC, vJ]) := by
        rw [card_filter_range_succ]
        refine Hs.ite (c := .eq GCA v1) (show GCA ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
        · have hcop : Nat.Coprime m k := by simpa [Cnd.eval, g1, g5.one, Nat.Coprime] using he
          have hcard : ((Finset.range k).filter m.Coprime).card ≤ k := by
            calc _ ≤ (Finset.range k).card := Finset.card_filter_le _ _
              _ = k := Finset.card_range k
          refine Hs.mono (hs_inc C TOC b3 (by rw [b3C]; omega)) (by omega) ?_
          rintro e rfl
          exact ⟨by rw [DS.set_env_self, b3C, if_pos hcop], rfl, rfl, rfl, Fr.set _ _ (by decide)⟩
        · have hcop : ¬ Nat.Coprime m k := by simpa [Cnd.eval, g1, g5.one, Nat.Coprime] using he
          refine Hs.mono (skip_spec b3) (by omega) ?_
          rintro e rfl
          exact ⟨by rw [DS.set_env_ne _ _ (by decide), b3C, if_neg hcop]; rfl, rfl, rfl, rfl, Fr.set _ _ (by decide)⟩
      refine Hs.then step (fun b4 ⟨s1, s2, s3, s4, s5⟩ n4 hn4 => ?_)
      refine Hs.last (hs_inc C TOJ b4 (by rw [s5 TOJ (by decide), b3J]; omega)) (fun b5 e5 n5 hn5 => ?_)
      subst e5
      have F : Fr a b4 totT := Fr.trans h8 (Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
        (Fr.trans (Fr.weaken g6 (by decide)) (Fr.weaken s5 (by decide))))
      refine ⟨⟨by rw [DS.set_env_self, s5 TOJ (by decide), b3J], by rw [DS.set_env_ne _ _ (by decide), s1],
        by rw [DS.set_env_ne _ _ (by decide), F TOM (by decide), hm],
        by rw [show (b4.set TOJ (b4.env TOJ + 1)).cp = b4.cp from rfl, s2, g2]; exact h4,
        by rw [show (b4.set TOJ (b4.env TOJ + 1)).wq = b4.wq from rfl, s3, g3]; exact h5,
        by rw [show (b4.set TOJ (b4.env TOJ + 1)).out = b4.out from rfl, s4, g4]; exact h6, ?_,
        Fr.trans F (Fr.set _ _ (by decide))⟩, ?_⟩
      · exact (Cst.of_fr g5 s5 (by decide) (by rw [s5 vPOS (by decide), s2]; exact g5.pos)).set _ _ (by decide)
      · have : n3 ≤ 28 * m + 9 := by
          have : (2 * (Nat.size m + Nat.size k) + 1) * (5 + 2) + 2 ≤ 28 * m + 9 := by omega
          omega
        omega
    · intro b ⟨h1, _, h3, _⟩
      simp [Cnd.eval, h1, h3]
  refine Hx.hs (Hs.then (hs_zero C TOC a) (fun b0 e0 n0 hn0 => ?_))
  subst e0
  refine Hs.then (hs_zero C TOJ _) (fun b1 e1 n1 hn1 => ?_)
  subst e1
  refine Hs.last (l _ ⟨by vsimp [], by vsimp [], by vsimp [hm], rfl, rfl, rfl,
    (hc.set _ _ (by decide)).set _ _ (by decide), Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))⟩) ?_
  rintro b ⟨_, b2, _, b4, b5, b6, b7, b8⟩ n2 hn2
  refine ⟨⟨by rw [b2]; rfl, b4, b5, b6, b7, b8⟩, ?_⟩
  have : m * (28 * m + 28 + 2) = m * (28 * m + 30) := by ring
  omega

/-! ## `degreeSum` -/

def dsBody : St VV :=
  .seq (.op (.copy TOM DSM)) (.seq totientV (.seq (.op (.mul TOC DSM DST)) (.seq (.op (.add DSS DST)) (.op (.inc DSM)))))

/-- `DSS := degreeSum q` from `DSQ1 = q + 1`. -/
def degSumV : St VV := .seq (.op (.zero DSS)) (.seq (.op (.copy DSM v1)) (.loop (.lt DSM DSQ1) dsBody))

def dsT : List (Fin VV) := [DSS, DSM, DST, TOM, TOC, TOJ, GCA, GCB, GCQ, GCR, vJ]

theorem sum_Icc_succ (f : ℕ → ℕ) (k : ℕ) : ∑ i ∈ Finset.Icc 1 (k + 1), f i = ∑ i ∈ Finset.Icc 1 k, f i + f (k + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem degreeSum_le (q : ℕ) : TomographyDirections.degreeSum q ≤ q * (q * q) := by
  unfold TomographyDirections.degreeSum
  calc ∑ m ∈ Finset.Icc 1 q, m * Nat.totient m ≤ ∑ _m ∈ Finset.Icc 1 q, q * q := by
        apply Finset.sum_le_sum
        intro m hm
        simp only [Finset.mem_Icc] at hm
        exact Nat.mul_le_mul hm.2 (le_trans (Nat.totient_le m) hm.2)
    _ = q * (q * q) := by simp

theorem degSumV_spec (a : DS VV) (hc : Cst a) (q : ℕ) (hq : a.env DSQ1 = q + 1)
    (hW : 2 * (q * (q * q)) + 4 ≤ 2 ^ C.Wd) :
    Hs C degSumV a (q * (q * (28 * q + 30) + 30) + 6) (fun b => b.env DSS = TomographyDirections.degreeSum q ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b dsT) := by
  let I : ℕ → DS VV → Prop := fun k b => b.env DSM = k + 1 ∧ b.env DSS = TomographyDirections.degreeSum k ∧
    b.env DSQ1 = q + 1 ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b dsT
  have l : ∀ b, I 0 b → Hs C (.loop (.lt DSM DSQ1) dsBody) b (q * (q * (28 * q + 30) + 28 + 2) + 2) (I q) := by
    refine Hs.loopN (c := .lt DSM DSQ1) (show DSM ≠ DSQ1 by decide) I q (q * (28 * q + 30) + 28) ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine ⟨by simp [Cnd.eval, h1, h3]; omega, ?_⟩
      refine Hx.hs (Hs.then (hs_copy C TOM DSM b (by decide)) (fun b1 e1 n1 hn1 => ?_))
      subst e1
      have hk1 : k + 1 ≤ q := hk
      have hq1 : 1 ≤ q := by omega
      have hqq : q * q ≤ q * (q * q) := Nat.le_mul_of_pos_left _ hq1
      have hq3 : q ≤ q * q := Nat.le_mul_of_pos_left _ hq1
      refine Hs.then (totientV_spec _ (h7.set _ _ (by decide)) (k + 1) (by vsimp [h1]) (by omega))
        (fun b2 ⟨t1, t2, t3, t4, t5, t6⟩ n2 hn2 => ?_)
      have b2M : b2.env DSM = k + 1 := by rw [t6 DSM (by decide)]; vsimp [h1]
      have hphi : Nat.totient (k + 1) * (k + 1) ≤ q * q := Nat.mul_le_mul (le_trans (Nat.totient_le _) hk1) hk1
      refine Hs.then (hs_mul C TOC DSM DST b2 (by decide) (by decide) (by decide) (by rw [t1, b2M]; omega))
        (fun b3 e3 n3 hn3 => ?_)
      subst e3
      have b2S : b2.env DSS = TomographyDirections.degreeSum k := by rw [t6 DSS (by decide)]; vsimp [h2]
      have hdk : TomographyDirections.degreeSum k ≤ q * (q * q) :=
        le_trans (degreeSum_le k) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega)))
      refine Hs.then (hs_add C DSS DST _ (by decide) (by vsimp [b2S, t1, b2M]; omega)) (fun b4 e4 n4 hn4 => ?_)
      subst e4
      refine Hs.last (hs_inc C DSM _ (by vsimp [b2M]; omega)) (fun b5 e5 n5 hn5 => ?_)
      subst e5
      refine ⟨⟨by vsimp [b2M], ?_, by vsimp [t6 DSQ1 (by decide), h3], by vsimp [t2, h4], by vsimp [t3, h5],
        by vsimp [t4, h6], ?_, ?_⟩, ?_⟩
      · vsimp [b2S, t1, b2M]
        unfold TomographyDirections.degreeSum
        rw [sum_Icc_succ]; ring
      · exact ((t5.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)
      · exact Fr.trans h8 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.weaken t6 (by decide))
          (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))))
      · have : n2 ≤ q * (28 * q + 30) + 10 := by
          have : (k + 1) * (28 * (k + 1) + 30) ≤ q * (28 * q + 30) := Nat.mul_le_mul hk1 (by omega)
          omega
        omega
    · intro b ⟨h1, _, h3, _⟩
      simp [Cnd.eval, h1, h3]
  refine Hx.hs (Hs.then (hs_zero C DSS a) (fun b0 e0 n0 hn0 => ?_))
  subst e0
  refine Hs.then (hs_copy C DSM v1 _ (by decide)) (fun b1 e1 n1 hn1 => ?_)
  subst e1
  refine Hs.last (l _ ⟨by vsimp [hc.one], by vsimp [TomographyDirections.degreeSum], by vsimp [hq], rfl, rfl, rfl,
    (hc.set _ _ (by decide)).set _ _ (by decide), Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))⟩) ?_
  rintro b ⟨_, b2, _, b4, b5, b6, b7, b8⟩ n2 hn2
  refine ⟨⟨b2, b4, b5, b6, b7, b8⟩, ?_⟩
  have : q * (q * (28 * q + 30) + 28 + 2) = q * (q * (28 * q + 30) + 30) := by ring
  omega

end NearCubicGates.Close.Dispatch
