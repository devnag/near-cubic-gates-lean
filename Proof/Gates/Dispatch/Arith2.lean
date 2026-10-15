import Proof.Gates.Dispatch.Scan
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Totient

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

variable {C : Ctx}

def P2E : Fin VV := ⟨100, by decide⟩
def P2X : Fin VV := ⟨101, by decide⟩
def P2I : Fin VV := ⟨102, by decide⟩
def PWB : Fin VV := ⟨103, by decide⟩
def PWE : Fin VV := ⟨104, by decide⟩
def PWX : Fin VV := ⟨105, by decide⟩
def PWI : Fin VV := ⟨106, by decide⟩
def PWT : Fin VV := ⟨107, by decide⟩
def LGX : Fin VV := ⟨108, by decide⟩
def LGR : Fin VV := ⟨109, by decide⟩
def LGT : Fin VV := ⟨110, by decide⟩
def SQX : Fin VV := ⟨111, by decide⟩
def SQS : Fin VV := ⟨112, by decide⟩
def SQF : Fin VV := ⟨113, by decide⟩
def SQT : Fin VV := ⟨114, by decide⟩
def SQU : Fin VV := ⟨98, by decide⟩
def GCA : Fin VV := ⟨115, by decide⟩
def GCB : Fin VV := ⟨116, by decide⟩
def GCQ : Fin VV := ⟨117, by decide⟩
def GCR : Fin VV := ⟨118, by decide⟩

theorem Cst.set {a : DS VV} (hc : Cst a) (x : Fin VV) (v : ℕ) (hx : x ∉ [vZ, v1, v2, vPOS]) : Cst (a.set x v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  exact ⟨by rw [DS.set_env_ne _ _ (Ne.symm hx.1)]; exact hc.z, by rw [DS.set_env_ne _ _ (Ne.symm hx.2.1)]; exact hc.one,
    by rw [DS.set_env_ne _ _ (Ne.symm hx.2.2.1)]; exact hc.two,
    by rw [DS.set_env_ne _ _ (Ne.symm hx.2.2.2)]; exact hc.pos⟩

/-! ## Powers -/

def pow2v : St VV :=
  .seq (.op (.copy P2X v1)) (.seq (.op (.zero P2I)) (.loop (.lt P2I P2E) (.seq (.op (.shl P2X)) (.op (.inc P2I)))))

theorem pow2v_spec (a : DS VV) (hc : Cst a) (e : ℕ) (he : a.env P2E = e) (hW : e < C.Wd) :
    Hs C pow2v a (5 * e + 6) (fun b => b.env P2X = 2 ^ e ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b [P2X, P2I]) := by
  have hpw : ∀ j ≤ e, 2 ^ j < 2 ^ C.Wd := fun j hj => Nat.pow_lt_pow_right (by norm_num) (by omega)
  let I : ℕ → DS VV → Prop := fun k b => b.env P2X = 2 ^ k ∧ b.env P2I = k ∧ b.env P2E = e ∧ b.cp = a.cp ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [P2X, P2I]
  have l : ∀ b, I 0 b → Hs C (.loop (.lt P2I P2E) (.seq (.op (.shl P2X)) (.op (.inc P2I)))) b (e * (3 + 2) + 2) (I e) := by
    refine Hs.loopN (c := .lt P2I P2E) (show P2I ≠ P2E by decide) I e 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine ⟨by simp [Cnd.eval, h2, h3, hk], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C P2X b (by rw [h1, ← pow_succ']; exact hpw _ hk)) (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_inc C P2I _ (by vsimp [h2]; have := Nat.lt_two_pow_self (n := C.Wd); omega)) le_rfl ?_
      rintro f rfl
      exact ⟨by vsimp [h1, pow_succ]; ring, by vsimp [h2], by vsimp [h3], h4, h5, h6,
        (h7.set _ _ (by decide)).set _ _ (by decide), Fr.trans h8 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
    · intro b ⟨_, h2, h3, _⟩
      simp [Cnd.eval, h2, h3]
  refine Hx.hs (Hs.then (hs_copy C P2X v1 a (by decide)) (fun b0 h0 n0 hn0 => ?_))
  subst h0
  refine Hs.then (hs_zero C P2I _) (fun b1 h1 n1 hn1 => ?_)
  subst h1
  refine Hs.last (l _ ⟨by vsimp [hc.one], by vsimp [], by vsimp [he], rfl, rfl, rfl,
    (hc.set _ _ (by decide)).set _ _ (by decide), Fr.trans (Fr.set a _ (by decide)) (Fr.set _ _ (by decide))⟩) ?_
  rintro b ⟨b1, _, _, b4, b5, b6, b7, b8⟩ n2 hn2
  exact ⟨⟨b1, b4, b5, b6, b7, b8⟩, by omega⟩

/-- `PWX := PWB ^ PWE`. -/
def powv : St VV :=
  .seq (.op (.copy PWX v1)) (.seq (.op (.zero PWI)) (.loop (.lt PWI PWE) (.seq (.op (.mul PWX PWB PWT))
    (.seq (.op (.copy PWX PWT)) (.op (.inc PWI))))))

theorem powv_spec (a : DS VV) (hc : Cst a) (b0 e : ℕ) (hb : a.env PWB = b0) (he : a.env PWE = e)
    (hW : ∀ j ≤ e, b0 ^ j < 2 ^ C.Wd) (heW : e < 2 ^ C.Wd) :
    Hs C powv a (7 * e + 6) (fun b => b.env PWX = b0 ^ e ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b [PWX, PWI, PWT]) := by
  let I : ℕ → DS VV → Prop := fun k b => b.env PWX = b0 ^ k ∧ b.env PWI = k ∧ b.env PWE = e ∧ b.env PWB = b0 ∧
    b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [PWX, PWI, PWT]
  have l : ∀ b, I 0 b → Hs C (.loop (.lt PWI PWE) (.seq (.op (.mul PWX PWB PWT)) (.seq (.op (.copy PWX PWT))
      (.op (.inc PWI))))) b (e * (5 + 2) + 2) (I e) := by
    refine Hs.loopN (c := .lt PWI PWE) (show PWI ≠ PWE by decide) I e 5 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      refine ⟨by simp [Cnd.eval, h2, h3, hk], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 3) (hs_mul C PWX PWB PWT b (by decide) (by decide) (by decide)
        (by rw [h1, h4, ← pow_succ]; exact hW _ hk)) (fun d hd => ?_)
      subst hd
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C PWX PWT _ (by decide)) (fun f hf => ?_)
      subst hf
      refine Hs.mono (hs_inc C PWI _ (by
        rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), h2]
        exact lt_of_le_of_lt (by omega : k + 1 ≤ e) heW)) le_rfl ?_
      rintro g rfl
      exact ⟨by vsimp [h1, h4, pow_succ], by vsimp [h2], by vsimp [h3], by vsimp [h4], h5, h6, h7,
        ((h8.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide),
        Fr.trans h9 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))⟩
    · intro b ⟨_, h2, h3, _⟩
      simp [Cnd.eval, h2, h3]
  refine Hx.hs (Hs.then (hs_copy C PWX v1 a (by decide)) (fun b0' h0 n0 hn0 => ?_))
  subst h0
  refine Hs.then (hs_zero C PWI _) (fun b1 h1 n1 hn1 => ?_)
  subst h1
  refine Hs.last (l _ ⟨by vsimp [hc.one], by vsimp [], by vsimp [he], by vsimp [hb], rfl, rfl, rfl,
    (hc.set _ _ (by decide)).set _ _ (by decide), Fr.trans (Fr.set a _ (by decide)) (Fr.set _ _ (by decide))⟩) ?_
  rintro b ⟨b1, _, _, _, b5, b6, b7, b8, b9⟩ n2 hn2
  exact ⟨⟨b1, b5, b6, b7, b8, b9⟩, by omega⟩

/-! ## Logarithm, square root -/

/-- `LGR := ⌊log₂ LGX⌋`. -/
def log2v : St VV :=
  .seq (.op (.copy LGT LGX)) (.seq (.op (.zero LGR)) (.loop (.lt v1 LGT) (.seq (.op (.half LGT)) (.op (.inc LGR)))))

theorem log2v_spec (a : DS VV) (hc : Cst a) (x : ℕ) (hx : a.env LGX = x) (hW : x < 2 ^ C.Wd) :
    Hs C log2v a (5 * Nat.log 2 x + 6) (fun b => b.env LGR = Nat.log 2 x ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ Fr a b [LGR, LGT]) := by
  have hlx : Nat.log 2 x < x ∨ x = 0 := by
    rcases Nat.eq_zero_or_pos x with h | h
    · right; exact h
    · left; exact Nat.log_lt_self 2 (by omega)
  let I : ℕ → DS VV → Prop := fun k b => b.env LGT = x / 2 ^ k ∧ b.env LGR = k ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
    b.out = a.out ∧ Cst b ∧ Fr a b [LGR, LGT]
  have l : ∀ b, I 0 b → Hs C (.loop (.lt v1 LGT) (.seq (.op (.half LGT)) (.op (.inc LGR)))) b
      (Nat.log 2 x * (3 + 2) + 2) (I (Nat.log 2 x)) := by
    refine Hs.loopN (c := .lt v1 LGT) (show v1 ≠ LGT by decide) I _ 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7⟩
      refine ⟨by simp only [Cnd.eval, h6.one, h1, decide_eq_true_eq]; exact (lt_div_iff_lt_log x k hk.le).2 hk, ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_half C LGT b) (fun d hd => ?_)
      subst hd
      have hkx : k + 1 < 2 ^ C.Wd := lt_of_le_of_lt (le_trans (by omega : k + 1 ≤ Nat.log 2 x) (Nat.log_le_self 2 x)) hW
      refine Hs.mono (hs_inc C LGR _ (by rw [DS.set_env_ne _ _ (by decide), h2]; exact hkx)) le_rfl ?_
      rintro e rfl
      exact ⟨by vsimp [h1, Nat.div_div_eq_div_mul, pow_succ], by vsimp [h2], h3, h4, h5,
        (h6.set _ _ (by decide)).set _ _ (by decide), Fr.trans h7 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
    · intro b ⟨h1, _, _, _, _, h6, _⟩
      simp only [Cnd.eval, h6.one, h1, decide_eq_false_iff_not]
      exact fun h => absurd ((lt_div_iff_lt_log x _ le_rfl).1 h) (lt_irrefl _)
  refine Hx.hs (Hs.then (hs_copy C LGT LGX a (by decide)) (fun b0 h0 n0 hn0 => ?_))
  subst h0
  refine Hs.then (hs_zero C LGR _) (fun b1 h1 n1 hn1 => ?_)
  subst h1
  refine Hs.last (l _ ⟨by vsimp [hx], by vsimp [], rfl, rfl, rfl, (hc.set _ _ (by decide)).set _ _ (by decide),
    Fr.trans (Fr.set a _ (by decide)) (Fr.set _ _ (by decide))⟩) ?_
  rintro b ⟨_, b2, b3, b4, b5, b6, b7⟩ n2 hn2
  exact ⟨⟨b2, b3, b4, b5, b6, b7⟩, by omega⟩

/-! ## Euclid -/

theorem mod_le_half (A B : ℕ) (hB : 0 < B) (hBA : B ≤ A) : A % B ≤ A / 2 := by
  by_cases h : 2 * B ≤ A
  · have := Nat.mod_lt A hB; omega
  · have e1 : A % B = (A - B) % B := Nat.mod_eq_sub_mod hBA
    have e2 : (A - B) % B = A - B := Nat.mod_eq_of_lt (by omega)
    omega

theorem size_mod_lt (A B : ℕ) (hB : 0 < B) (hBA : B ≤ A) : Nat.size (A % B) < Nat.size A := by
  have hA : 0 < A := by omega
  have hs : 0 < Nat.size A := Nat.size_pos.2 hA
  rcases Nat.eq_zero_or_pos (A % B) with h | h
  · rw [h, Nat.size_zero]; exact hs
  · have h1 := mod_le_half A B hB hBA
    have h2 : A < 2 ^ Nat.size A := Nat.lt_size_self A
    have h3 : A % B < 2 ^ (Nat.size A - 1) := by
      have : 2 ^ Nat.size A = 2 * 2 ^ (Nat.size A - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    have := Nat.size_le.2 h3
    omega

/-- `GCA := gcd GCA GCB`, `GCB := 0` (scratch `GCQ GCR`). -/
def gcdv : St VV :=
  .loop (.lt vZ GCB) (.seq (.op (.dm GCA GCB GCQ GCR)) (.seq (.op (.copy GCA GCB)) (.op (.copy GCB GCR))))

def gcdT : List (Fin VV) := [GCA, GCB, GCQ, GCR]

theorem gcdv_spec (a : DS VV) (hc : Cst a) (x y M : ℕ) (hx : a.env GCA = x) (hy : a.env GCB = y) (hxM : x ≤ M)
    (hyM : y ≤ M) (hM : 2 * M ≤ 2 ^ C.Wd) :
    Hs C gcdv a ((2 * (Nat.size x + Nat.size y) + 1) * (5 + 2) + 2) (fun b => b.env GCA = Nat.gcd x y ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b gcdT) := by
  let I : DS VV → Prop := fun b => Nat.gcd (b.env GCA) (b.env GCB) = Nat.gcd x y ∧ b.env GCA ≤ M ∧ b.env GCB ≤ M ∧
    b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b gcdT
  let μ : DS VV → ℕ := fun b => 2 * (Nat.size (b.env GCA) + Nat.size (b.env GCB)) +
    (if b.env GCA < b.env GCB then 1 else 0)
  have l := Hs.loopM (C := C) (c := .lt vZ GCB) (s := .seq (.op (.dm GCA GCB GCQ GCR)) (.seq (.op (.copy GCA GCB))
    (.op (.copy GCB GCR)))) (show vZ ≠ GCB by decide) I μ 5 (by
      rintro b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ he
      have hB : 0 < b.env GCB := by simpa [Cnd.eval, h7.z] using he
      refine Hs.seq (t1 := 1) (t2 := 3) (hs_dm C GCA GCB GCQ GCR b (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hB (by omega)) (fun d hd => ?_)
      subst hd
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C GCA GCB _ (by decide)) (fun f hf => ?_)
      subst hf
      refine Hs.mono (hs_copy C GCB GCR _ (by decide)) le_rfl ?_
      rintro g rfl
      set A := b.env GCA
      set B := b.env GCB
      have gA : (((((b.set GCQ (A / B)).set GCR (A % B)).set GCA (((b.set GCQ (A / B)).set GCR (A % B)).env GCB)).set GCB
        ((((b.set GCQ (A / B)).set GCR (A % B)).set GCA (((b.set GCQ (A / B)).set GCR (A % B)).env GCB)).env GCR)).env GCA)
          = B := by vsimp [] <;> rfl
      have gB : (((((b.set GCQ (A / B)).set GCR (A % B)).set GCA (((b.set GCQ (A / B)).set GCR (A % B)).env GCB)).set GCB
        ((((b.set GCQ (A / B)).set GCR (A % B)).set GCA (((b.set GCQ (A / B)).set GCR (A % B)).env GCB)).env GCR)).env GCB)
          = A % B := by vsimp [] <;> rfl
      refine ⟨⟨?_, by rw [gA]; exact h3, by rw [gB]; have := Nat.mod_lt A hB; omega, h4, h5, h6, ?_, ?_⟩, ?_⟩
      · rw [gA, gB, ← h1, Nat.gcd_comm A B, Nat.gcd_rec B A, Nat.gcd_comm]
      · exact (((h7.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)
      · exact Fr.trans h8 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
          (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))))
      · show 2 * (Nat.size _ + Nat.size _) + (if _ < _ then 1 else 0) < 2 * (Nat.size A + Nat.size B) +
          (if A < B then 1 else 0)
        rw [gA, gB]
        by_cases hAB : A < B
        · rw [Nat.mod_eq_of_lt hAB, if_neg (by omega), if_pos hAB]; omega
        · have := size_mod_lt A B hB (by omega)
          rw [if_neg (by have := Nat.mod_lt A hB; omega), if_neg hAB]; omega)
  have hI : I a := ⟨by rw [hx, hy], by rw [hx]; exact hxM, by rw [hy]; exact hyM, rfl, rfl, rfl, hc, Fr.refl a _⟩
  refine Hs.mono (l a hI) ?_ ?_
  · show μ a * (5 + 2) + 2 ≤ _
    have : μ a ≤ 2 * (Nat.size x + Nat.size y) + 1 := by
      show 2 * (Nat.size (a.env GCA) + Nat.size (a.env GCB)) + (if a.env GCA < a.env GCB then 1 else 0) ≤ _
      rw [hx, hy]; split_ifs <;> omega
    nlinarith
  · rintro b ⟨⟨h1, _, _, h4, h5, h6, h7, h8⟩, hstop⟩
    have hB0 : b.env GCB = 0 := by simpa [Cnd.eval, h7.z] using hstop
    exact ⟨by rw [← h1, hB0, Nat.gcd_zero_right], h4, h5, h6, h7, h8⟩

/-! ## Integer square root -/

theorem sqrt_eq_findGreatest (x : ℕ) : Nat.sqrt x = Nat.findGreatest (fun s => s * s ≤ x) x := by
  rw [eq_comm, Nat.findGreatest_eq_iff]
  refine ⟨Nat.sqrt_le_self x, fun _ => Nat.le_sqrt.1 le_rfl, fun k hk _ hkk => ?_⟩
  have := Nat.le_sqrt.2 hkk
  omega

def sqTest : St VV :=
  .seq (.op (.copy SQU SQS)) (.seq (.op (.mul SQS SQU SQT)) (.seq (.op (.copy SQF v1))
    (.ite (.lt SQX SQT) (.op (.zero SQF)) skipS)))

def sqrtv : St VV := .seq (.op (.copy SQS SQX)) (fgScan SQS SQF sqTest)

theorem sqrtv_spec (a : DS VV) (hc : Cst a) (x : ℕ) (hx : a.env SQX = x) (hW : x * x < 2 ^ C.Wd) :
    Hs C sqrtv a (1 + (8 + ((x + 1) * (8 + 3 + 2) + 2) + 1) + 1) (fun b => b.env SQS = Nat.sqrt x ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [SQS, SQF, SQT, SQU, vJ]) := by
  let Inv : DS VV → Prop := fun b => b.env SQX = x ∧ Cst b ∧ Fr a b [SQS, SQF, SQT, SQU, vJ]
  have ht : FlagTest C sqTest SQS SQF (fun s => s * s ≤ x) Inv 8 x := by
    rintro b ⟨h1, h3, h4⟩ h2
    set s := b.env SQS with hs
    have hm : s * s < 2 ^ C.Wd := lt_of_le_of_lt (Nat.mul_le_mul h2 h2) hW
    refine Hx.hs (Hs.then (hs_copy C SQU SQS b (by decide)) (fun b1 e1 n1 hn1 => ?_))
    subst e1
    refine Hs.then (hs_mul C SQS SQU SQT _ (by decide) (by decide) (by decide) (by vsimp []; exact hm))
      (fun b2 e2 n2 hn2 => ?_)
    subst e2
    refine Hs.then (hs_copy C SQF v1 _ (by decide)) (fun b3 e3 n3 hn3 => ?_)
    subst e3
    set d := (((b.set SQU (b.env SQS)).set SQT ((b.set SQU (b.env SQS)).env SQS * (b.set SQU (b.env SQS)).env SQU)).set
      SQF (((b.set SQU (b.env SQS)).set SQT ((b.set SQU (b.env SQS)).env SQS * (b.set SQU (b.env SQS)).env SQU)).env v1))
      with hd
    have dX : d.env SQX = x := by rw [hd]; vsimp [h1]
    have dT : d.env SQT = s * s := by rw [hd]; vsimp [] <;> rfl
    have dS : d.env SQS = s := by rw [hd]; vsimp [] <;> rfl
    have dI : Inv d := ⟨dX, by rw [hd]; exact ((h3.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide),
      Fr.trans h4 (by rw [hd]; exact Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.set _ _ (by decide))))⟩
    have step : Hs C (.ite (.lt SQX SQT) (.op (.zero SQF)) skipS) d 2 (fun g => g.env SQF = bnat (s * s ≤ x) ∧
        g.env SQS = s ∧ Inv g ∧ g.cp = d.cp ∧ g.wq = d.wq ∧ g.out = d.out) := by
      refine Hs.ite (c := .lt SQX SQT) (show SQX ≠ SQT by decide) (fun he => ?_) (fun he => ?_)
      · have hlt : x < s * s := by simpa [Cnd.eval, dX, dT] using he
        refine Hs.mono (hs_zero C SQF d) le_rfl ?_
        rintro g rfl
        refine ⟨by rw [DS.set_env_self]; unfold bnat; simp [show ¬ s * s ≤ x by omega],
          by rw [DS.set_env_ne _ _ (by decide), dS],
          ⟨by vsimp [dX], dI.2.1.set _ _ (by decide), Fr.trans dI.2.2 (Fr.set _ _ (by decide))⟩, rfl, rfl, rfl⟩
      · have hle : s * s ≤ x := by simpa [Cnd.eval, dX, dT] using he
        refine Hs.mono (skip_spec d) le_rfl ?_
        rintro g rfl
        refine ⟨by rw [DS.set_env_ne _ _ (by decide), hd]; vsimp [h3.one, bnat, hle],
          by rw [DS.set_env_ne _ _ (by decide), dS],
          ⟨by vsimp [dX], dI.2.1.set _ _ (by decide), Fr.trans dI.2.2 (Fr.set _ _ (by decide))⟩, rfl, rfl, rfl⟩
    refine Hs.last step (fun g ⟨g1, g2, g3, g4, g5, g6⟩ n4 hn4 => ⟨⟨g1, g2, g3, by rw [g4, hd]; rfl,
      by rw [g5, hd]; rfl, by rw [g6, hd]; rfl⟩, by omega⟩)
  refine Hs.mono (Hs.seq (hs_copy C SQS SQX a (by decide)) (fun b hb => ?_)) le_rfl (fun _ h => h)
  subst hb
  have h0 : Inv (a.set SQS (a.env SQX)) := ⟨by vsimp [hx], hc.set _ _ (by decide), Fr.set a _ (by decide)⟩
  refine Hs.mono (fgScan_spec SQS SQF (by decide) (by decide) (by decide) (by decide) sqTest (fun s => s * s ≤ x) Inv 8
    (fun b h => h.2.1) (fun b v h => ⟨by vsimp [h.1], h.2.1.set _ _ (by decide), Fr.trans h.2.2 (Fr.set _ _ (by decide))⟩)
    (fun b v h => ⟨by vsimp [h.1], h.2.1.set _ _ (by decide), Fr.trans h.2.2 (Fr.set _ _ (by decide))⟩) x ht _ h0
    (by vsimp [hx])) le_rfl ?_
  rintro d ⟨d1, ⟨d2, d3, d4⟩, d5, d6, d7⟩
  exact ⟨by rw [d1, sqrt_eq_findGreatest], d5, d6, d7, d3, d4⟩

end NearCubicGates.Close.Dispatch
