import Proof.Gates.CounterMachine.PrefixLoad2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace NearCubicGates.Close.Cells.PrefixLoader

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN callN paramsN witN circN gateN intN ratN bitN srList cellN_word
  flatMap_gateN_length flatMap_intN_length)

variable {C : Ctx}

def circP : St VV MM := .seq (readL gS) (.seq (readL v2) (readL v1))
def fixP (k : ℕ) : St VV MM := .seq (setK kf k) (readF kf)

/-- The call: `n`, kind, two circuits, the parity list, the radius. -/
def callP : St VV MM :=
  .seq rdStore (.seq (.op (.copy gN t3)) (.seq rdStore (.seq (.op (.copy gKd t3)) (.seq (.op (.copy gS gN))
    (.seq (.op (.shl gS)) (.seq (incS gS 3) (.seq circP (.seq circP (.seq (readL v1) (fixP 3))))))))))

/-- The load state after a prefix `L` with the remaining input `R`. -/
structure LS (a b : DS VV MM) (L : List ℕ) (R : List ℕ) (tail : List Bool) : Prop where
  ld : Loaded a b L
  cw : C.inp.drop b.ip = R.flatMap natWord ++ tail
  cst : Cst b
  rc : b.rc sN = (b.ram sN).length

theorem callN_eq (c : Call) : callN c = [c.n] ++ [kindTag c.kind] ++ circN c.first ++ circN c.second ++
    ([c.parity.length] ++ c.parity) ++ ratN c.radius := by
  simp [callN, List.append_assoc]

theorem LS.next {a b d : DS VV MM} {L S R : List ℕ} {tail : List Bool} (h : LS (C := C) a b L (S ++ R) tail)
    (hd : Loaded b d S) (hc : Cst d) : LS (C := C) a d (L ++ S) R tail :=
  ⟨Loaded.trans h.ld hd, Loaded.drop hd (by rw [h.cw]), hc, Loaded.rc_eq hd⟩

theorem LS.set {a b : DS VV MM} {L R : List ℕ} {tail : List Bool} (h : LS (C := C) a b L R tail) (x : Fin VV)
    (v : ℕ) (hx : x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2) : LS (C := C) a (b.set x v) L R tail :=
  ⟨h.ld, h.cw, ⟨by rw [DS.set_env_ne _ _ (Ne.symm hx.1)]; exact h.cst.z,
    by rw [DS.set_env_ne _ _ (Ne.symm hx.2.1)]; exact h.cst.one,
    by rw [DS.set_env_ne _ _ (Ne.symm hx.2.2)]; exact h.cst.two⟩, h.rc⟩

theorem LS.sh {a b d : DS VV MM} {L R : List ℕ} {tail : List Bool} (h : LS (C := C) a b L R tail)
    (hsh : d.sh = b.sh) (hc : Cst d) : LS (C := C) a d L R tail := by
  have hs := Same.of_sh hsh
  exact ⟨Loaded.sh h.ld hsh, by rw [hs.ip]; exact h.cw, hc, by rw [hs.rc, hs.ram]; exact h.rc⟩

theorem rdStore_LS {a b : DS VV MM} {L R : List ℕ} {tail : List Bool} (x : ℕ) (h : LS (C := C) a b L (x :: R) tail)
    (hW : natBitLength x + 2 ≤ C.Wd) :
    Hs C rdStore b (30 * natBitLength x + 32) (fun d => d.env t3 = x ∧ LS (C := C) a d (L ++ [x]) R tail ∧
      Fr b d rdNatT) := by
  refine Hs.mono (rdStore_spec b h.cst x (R.flatMap natWord ++ tail) (by rw [h.cw]; simp) hW h.rc) le_rfl ?_
  rintro d ⟨d1, d2, d3, d4⟩
  exact ⟨d1, LS.next (S := [x]) (R := R) (by simpa using h) d2 d3, d4⟩

theorem readL_LS {a b : DS VV MM} {L R : List ℕ} {tail : List Bool} (str : Fin VV) (hstr : str ∉ readLT) (S : List ℕ)
    (c : ℕ) (X : List ℕ) (hS : S = [c] ++ X) (h : LS (C := C) a b L (S ++ R) tail) (Λ : ℕ)
    (hX : X.length = c * b.env str) (hfit : ∀ x ∈ S, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd)
    (hL : c * b.env str < 2 ^ C.Wd) :
    Hs C (readL str) b (S.length * (30 * Λ + 45) + 10) (fun d => LS (C := C) a d (L ++ S) R tail ∧
      Fr b d readLT) := by
  refine Hs.mono (readL_spec' str hstr b h.cst S c X hS (R.flatMap natWord ++ tail) Λ
    (by rw [h.cw]; simp [List.append_assoc]) hX hfit hΛ hL h.rc) le_rfl ?_
  rintro d ⟨d1, d2, d3⟩
  exact ⟨LS.next h d1 d2, d3⟩

theorem fixP_LS {a b : DS VV MM} {L R : List ℕ} {tail : List Bool} (k : ℕ) (S : List ℕ) (hk : S.length = k)
    (h : LS (C := C) a b L (S ++ R) tail) (Λ : ℕ) (hfit : ∀ x ∈ S, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd)
    (hkW : k < 2 ^ C.Wd) (hk2 : k ≤ 20) :
    Hs C (fixP k) b (S.length * (30 * Λ + 45) + 50) (fun d => LS (C := C) a d (L ++ S) R tail ∧
      Fr b d (kf :: readT)) := by
  refine Hs.mono (readF_spec' k b h.cst S hk (R.flatMap natWord ++ tail) Λ (by rw [h.cw]; simp [List.append_assoc])
    hfit hΛ hkW h.rc hk2) le_rfl ?_
  rintro d ⟨d1, d2, d3⟩
  exact ⟨LS.next h d1 d2, d3⟩

theorem circ_LS {a b : DS VV MM} {L R : List ℕ} {tail : List Bool} (n : ℕ) (Cc : NCircuit n)
    (h : LS (C := C) a b L (circN Cc ++ R) tail) (hgS : b.env gS = 2 * n + 3) (Λ : ℕ)
    (hfit : ∀ x ∈ circN Cc, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd) (hbig : (circN Cc).length < 2 ^ C.Wd) :
    Hs C circP b ((circN Cc).length * (30 * Λ + 45) + 40) (fun d => LS (C := C) a d (L ++ circN Cc) R tail ∧
      Fr b d readLT) := by
  refine Hs.mono (circ_load b h.cst n Cc hgS (R.flatMap natWord ++ tail) Λ (by rw [h.cw]; simp [List.append_assoc])
    hfit hΛ hbig h.rc) le_rfl ?_
  rintro d ⟨d1, d2, d3⟩
  exact ⟨LS.next h d1 d2, d3⟩

theorem callP_spec (a : DS VV MM) (c : Call) (R : List ℕ) (tail : List Bool) (Λ : ℕ)
    (h0 : LS (C := C) a a [] (callN c ++ R) tail) (hfit : ∀ x ∈ callN c, natBitLength x ≤ Λ)
    (hΛ : Λ + 4 ≤ C.Wd) (hbig : (callN c).length < 2 ^ C.Wd) :
    Hs C callP a ((callN c).length * (30 * Λ + 45) + 400) (fun b => LS (C := C) a b (callN c) R tail ∧
      b.env gN = c.n ∧ b.env gKd = kindTag c.kind ∧ b.env gS = 2 * c.n + 3 ∧ Fr a b loadT) := by
  have hn : natBitLength c.n ≤ Λ := hfit c.n (by simp [callN])
  have hnW : 2 * c.n + 3 < 2 ^ C.Wd := by
    have := lt_natBitLength c.n
    have : 2 ^ natBitLength c.n * 8 ≤ 2 ^ C.Wd := by
      calc 2 ^ natBitLength c.n * 8 = 2 ^ (natBitLength c.n + 3) := by ring
        _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hseg := callN_eq c
  have hfit' : ∀ x ∈ [c.n] ++ [kindTag c.kind] ++ circN c.first ++ circN c.second ++
      ([c.parity.length] ++ c.parity) ++ ratN c.radius, natBitLength x ≤ Λ := by rw [← hseg]; exact hfit
  have hbig' := hbig; rw [hseg] at hbig'; simp only [List.length_append] at hbig'
  have hlen' : (callN c).length = 1 + 1 + (circN c.first).length + (circN c.second).length +
      (1 + c.parity.length) + 3 := by
    rw [hseg]; simp only [List.length_append, List.length_singleton, CounterMachine.ratN_length]
  rw [hseg] at h0
  have h0' : LS (C := C) a a [] (c.n :: ([kindTag c.kind] ++ circN c.first ++ circN c.second ++
      ([c.parity.length] ++ c.parity) ++ ratN c.radius ++ R)) tail := by simpa [List.append_assoc] using h0
  refine Hx.hs (Hs.then (rdStore_LS c.n h0' (by omega)) (fun b1 ⟨q1, L1, q4⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C gN t3 b1 (by decide)) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  have L2 := L1.set gN (b1.env t3) (by decide)
  have L2' : LS (C := C) a (b1.set gN (b1.env t3)) [c.n] (kindTag c.kind :: (circN c.first ++ circN c.second ++
      ([c.parity.length] ++ c.parity) ++ ratN c.radius ++ R)) tail := by simpa [List.append_assoc] using L2
  refine Hs.then (rdStore_LS (kindTag c.kind) L2' (by have := hfit' (kindTag c.kind) (by simp); omega))
    (fun b3 ⟨r1, L3, r4⟩ n3 hn3 => ?_)
  refine Hs.then (hs_copy C gKd t3 b3 (by decide)) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  have L4 := L3.set gKd (b3.env t3) (by decide)
  have b3n : b3.env gN = c.n := by rw [r4 gN (by decide)]; simp [DS.set, q1]
  refine Hs.then (hs_copy C gS gN _ (by decide)) (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  refine Hs.then (hs_shl C gS _ (by vsimp [b3n]; omega)) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  refine Hs.then (incS_spec gS (by decide) 3 _ (by vsimp [b3n]; omega)) (fun b7 ⟨s1, s2, s3⟩ n7 hn7 => ?_)
  have L7 := LS.sh ((L4.set gS _ (by decide)).set gS _ (by decide)) s2
    (Cst.of_fr ((L4.set gS _ (by decide)).set gS _ (by decide)).cst s3 (by decide))
  have b7S : b7.env gS = 2 * c.n + 3 := by rw [s1]; vsimp [b3n]
  -- the two circuits
  refine Hs.then (circ_LS (a := a) (L := [c.n] ++ [kindTag c.kind]) (tail := tail) c.n c.first (R := circN c.second ++ ([c.parity.length] ++ c.parity) ++ ratN c.radius ++ R)
    (by simpa [List.append_assoc] using L7) b7S Λ (fun x hx => hfit' x (by simp [hx])) (by omega) (by omega))
    (fun b8 ⟨L8, u3⟩ n8 hn8 => ?_)
  have b8S : b8.env gS = 2 * c.n + 3 := by rw [u3 gS (by decide), b7S]
  refine Hs.then (circ_LS (a := a) (L := [c.n] ++ [kindTag c.kind] ++ circN c.first) (tail := tail) c.n c.second
    (R := ([c.parity.length] ++ c.parity) ++ ratN c.radius ++ R)
    (by simpa [List.append_assoc] using L8) b8S Λ (fun x hx => hfit' x (by simp [hx])) (by omega) (by omega))
    (fun b9 ⟨L9, w3⟩ n9 hn9 => ?_)
  -- the parity list
  refine Hs.then (readL_LS (a := a) (L := [c.n] ++ [kindTag c.kind] ++ circN c.first ++ circN c.second)
    (tail := tail) v1 (by decide) _ c.parity.length c.parity rfl (R := ratN c.radius ++ R) (by simpa [List.append_assoc] using L9)
    Λ (by rw [L9.cst.one]; simp) (fun x hx => hfit' x (by simp at hx ⊢; tauto)) (by omega)
    (by rw [L9.cst.one]; omega)) (fun b10 ⟨L10, x3⟩ n10 hn10 => ?_)
  -- the radius
  refine Hs.last (fixP_LS (a := a) (L := [c.n] ++ [kindTag c.kind] ++ circN c.first ++ circN c.second ++
    ([c.parity.length] ++ c.parity)) (tail := tail) 3 (ratN c.radius) rfl (R := R) (by simpa [List.append_assoc] using L10) Λ
    (fun x hx => hfit' x (by simp at hx ⊢; tauto)) (by omega) (by omega) (by norm_num))
    (fun b11 ⟨L11, y3⟩ n11 hn11 => ?_)
  have hb3k : b3.env t3 = kindTag c.kind := r1
  refine ⟨⟨by rw [hseg]; simpa [List.append_assoc] using L11, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [y3 gN (by decide), x3 gN (by decide), w3 gN (by decide), u3 gN (by decide), s3 gN (by decide)]
    vsimp [b3n]
  · rw [y3 gKd (by decide), x3 gKd (by decide), w3 gKd (by decide), u3 gKd (by decide), s3 gKd (by decide)]
    vsimp [hb3k]
  · rw [y3 gS (by decide), x3 gS (by decide), w3 gS (by decide), u3 gS (by decide), b7S]
  · exact Fr.trans (Fr.weaken q4 (by decide)) (Fr.trans (Fr.set b1 _ (by decide)) (Fr.trans (Fr.weaken r4 (by decide))
      (Fr.trans (Fr.set b3 _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.weaken s3 (by decide)) (Fr.trans (Fr.weaken u3 (by decide)) (Fr.trans (Fr.weaken w3 (by decide))
      (Fr.trans (Fr.weaken x3 (by decide)) (Fr.weaken y3 (by decide)))))))))))
  · have : (callN c).length = 1 + 1 + (circN c.first).length + (circN c.second).length +
        (1 + c.parity.length) + 3 := hlen'
    simp only [List.length_append, List.length_singleton, CounterMachine.ratN_length] at hn1 hn3 hn8 hn9 hn10 hn11
    have hx1 := natBitLength_pos c.n
    have := hfit' (kindTag c.kind) (by simp)
    nlinarith

/-! ## The parameters -/

def parT : List (Fin VV) := [kf, gJ, c1, t0, t1, t2, t3, t4, vJ, lc]
def witT : List (Fin VV) := [c2, gRC, gJR, c1, t0, t1, t2, t3, t4, vJ, lc]

def parP : St VV MM :=
  .seq (fixP 12) (.seq (readL v1) (.seq (fixP 10) (.seq rdStore (.seq (.op (.copy gJ t3)) (.seq (readL v1)
    (fixP 2))))))

theorem paramsN_eq (p : Params) : paramsN p =
    ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e]) ++
    ([(p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·)) ++
    ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1]) ++ [p.J] ++
    ([p.factors.length] ++ p.factors) ++ [p.A, p.Lambda] := by
  simp [paramsN, List.append_assoc]

theorem parP_spec (a b : DS VV MM) (p : Params) (L R : List ℕ) (tail : List Bool) (Λ : ℕ)
    (h0 : LS (C := C) a b L (paramsN p ++ R) tail) (hfit : ∀ x ∈ paramsN p, natBitLength x ≤ Λ)
    (hΛ : Λ + 4 ≤ C.Wd) (hbig : (paramsN p).length < 2 ^ C.Wd) :
    Hs C parP b ((paramsN p).length * (30 * Λ + 45) + 400) (fun d => LS (C := C) a d (L ++ paramsN p) R tail ∧
      d.env gJ = p.J ∧ Fr b d parT) := by
  have hseg := paramsN_eq p
  rw [hseg] at h0 hfit hbig ⊢
  simp only [List.length_append, List.length_cons, List.length_nil, CounterMachine.ratN_length] at hbig
  refine Hx.hs (Hs.then (fixP_LS (a := a) (L := L) (tail := tail) 12
    ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e]) (by simp [CounterMachine.ratN_length])
    (R := ([(p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·)) ++
    ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1]) ++ [p.J] ++
    ([p.factors.length] ++ p.factors) ++ [p.A, p.Lambda] ++ R) (by simpa [List.append_assoc] using h0) Λ
    (fun x hx => hfit x (by simp only [List.mem_append] at hx ⊢; tauto)) (by omega) (by omega) (by norm_num))
    (fun b1 ⟨L1, f1⟩ n1 hn1 => ?_))
  refine Hs.then (readL_LS (a := a) (L := L ++ ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e])) (tail := tail) v1 (by decide) _ (p.primes.sort (· ≤ ·)).length
    (p.primes.sort (· ≤ ·)) rfl (R := ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1]) ++ [p.J] ++
    ([p.factors.length] ++ p.factors) ++ [p.A, p.Lambda] ++ R) (by simpa [List.append_assoc] using L1) Λ
    (by rw [L1.cst.one]; simp) (fun x hx => hfit x (by simp only [List.mem_append] at hx ⊢; tauto)) (by omega)
    (by rw [L1.cst.one]; omega)) (fun b2 ⟨L2, f2⟩ n2 hn2 => ?_)
  refine Hs.then (fixP_LS (a := a) (L := L ++ ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e]) ++ ([(p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·))) (tail := tail) 10 ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1])
    (by simp [CounterMachine.ratN_length])
    (R := [p.J] ++ ([p.factors.length] ++ p.factors) ++ [p.A, p.Lambda] ++ R) (by simpa [List.append_assoc] using L2)
    Λ (fun x hx => hfit x (by simp only [List.mem_append] at hx ⊢; tauto)) (by omega) (by omega) (by norm_num))
    (fun b3 ⟨L3, f3⟩ n3 hn3 => ?_)
  refine Hs.then (rdStore_LS (a := a) (L := L ++ ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e]) ++ ([(p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·)) ++ ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1])) (tail := tail) p.J (R := ([p.factors.length] ++ p.factors) ++ [p.A, p.Lambda] ++ R)
    (by simpa [List.append_assoc] using L3) (by have := hfit p.J (by simp); omega)) (fun b4 ⟨q1, L4, f4⟩ n4 hn4 => ?_)
  refine Hs.then (hs_copy C gJ t3 b4 (by decide)) (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  have L5 := L4.set gJ (b4.env t3) (by decide)
  refine Hs.then (readL_LS (a := a) (L := L ++ ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e]) ++ ([(p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·)) ++ ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1]) ++ [p.J]) (tail := tail) v1 (by decide)
    _ p.factors.length p.factors rfl
    (R := [p.A, p.Lambda] ++ R) (by simpa [List.append_assoc] using L5) Λ
    (by rw [L5.cst.one]; simp) (fun x hx => hfit x (by simp only [List.mem_append] at hx ⊢; tauto)) (by omega)
    (by rw [L5.cst.one]; omega)) (fun b6 ⟨L6, f6⟩ n6 hn6 => ?_)
  refine Hs.last (fixP_LS (a := a) (L := L ++ ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e]) ++ ([(p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·)) ++ ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1]) ++ [p.J] ++ ([p.factors.length] ++ p.factors)) (tail := tail) 2
    [p.A, p.Lambda] rfl (R := R) L6 Λ
    (fun x hx => hfit x (by simp only [List.mem_append] at hx ⊢; tauto)) (by omega) (by omega) (by norm_num))
    (fun b7 ⟨L7, f7⟩ n7 hn7 => ?_)
  refine ⟨⟨by simpa [List.append_assoc] using L7, ?_, ?_⟩, ?_⟩
  · rw [f7 gJ (by decide), f6 gJ (by decide)]; vsimp [q1]
  · exact Fr.trans (Fr.weaken f1 (by decide)) (Fr.trans (Fr.weaken f2 (by decide)) (Fr.trans (Fr.weaken f3 (by decide))
      (Fr.trans (Fr.weaken f4 (by decide)) (Fr.trans (Fr.set b4 _ (by decide)) (Fr.trans (Fr.weaken f6 (by decide))
      (Fr.weaken f7 (by decide)))))))
  · simp only [List.length_append, List.length_cons, List.length_nil, CounterMachine.ratN_length,
      List.length_singleton] at hn1 hn2 hn3 hn6 hn7 ⊢
    have hJb := hfit p.J (by simp)
    ring_nf at hn1 hn2 hn3 hn4 hn5 hn6 hn7 ⊢
    omega

/-! ## The witness -/

def rcP : St VV MM := .seq (setK gRC 1) (.ite (.eq gKd v1) (.op (.inc gRC)) skipS)

def witP : St VV MM :=
  .seq (readL v1) (.seq rcP (.seq (.op (.mul gJ gRC gJR)) (forS c2 gJR (readL v2))))

theorem srList_len (c : Call) (p : Params) : (srList c p).length = p.J * roleCount c.kind := by
  unfold srList; simp [List.length_flatMap, List.sum_replicate]

/-- One witness block: the coefficient list of a stage and role. -/
def wseg (c : Call) (wt : Wit c.n) (sr : ℕ × ℕ) : List ℕ :=
  [(wt.coef sr.1 sr.2).length] ++ (wt.coef sr.1 sr.2).flatMap intN

theorem witN_eq (c : Call) (p : Params) (wt : Wit c.n) :
    witN c p wt = ([(coordsOf wt.I).length] ++ coordsOf wt.I) ++ (srList c p).flatMap (wseg c wt) := by
  simp [CounterMachine.witN, wseg, List.append_assoc]; rfl

theorem rcP_spec (b : DS VV MM) (hc : Cst b) (k : CallKind) (hk : b.env gKd = kindTag k) (hW : 3 < 2 ^ C.Wd) :
    Hs C rcP b (2 * 1 + 3 + (1 + 1) + 1) (fun d => d.env gRC = roleCount k ∧ d.sh = b.sh ∧ Fr b d [gRC, vJ]) := by
  have h1W : 1 < 2 ^ C.Wd := by omega
  refine Hs.seq (t1 := 2 * 1 + 3) (t2 := 1 + 1) (setK_spec gRC (by decide) 1 b h1W) (fun d ⟨d1, d2, d3⟩ => ?_)
  have dk : d.env gKd = kindTag k := by rw [d3 gKd (by decide), hk]
  have dv1 : d.env v1 = 1 := by rw [d3 v1 (by decide)]; exact hc.one
  refine Hs.ite (show gKd ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
  · simp only [Cnd.eval, dk, dv1, decide_eq_true_eq] at he
    refine Hs.mono (hs_inc C gRC d (by rw [d1]; omega)) (by omega) ?_
    rintro e rfl
    refine ⟨by vsimp [d1]; cases k <;> simp_all [kindTag, roleCount], by simp [d2], Fr.trans d3 (Fr.set d _ (by decide))⟩
  · simp only [Cnd.eval, dk, dv1, decide_eq_false_iff_not] at he
    refine Hs.mono (skip_spec d) (by omega) ?_
    rintro e rfl
    refine ⟨by vsimp [d1]; cases k <;> simp_all [kindTag, roleCount], by simp [d2], Fr.trans d3 (Fr.set d _ (by decide))⟩

theorem len_le_flatMap {α β : Type} (l : List α) (f : α → List β) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem witP_spec (a b : DS VV MM) (c : Call) (p : Params) (wt : Wit c.n) (L R : List ℕ) (tail : List Bool)
    (Λ : ℕ) (h0 : LS (C := C) a b L (witN c p wt ++ R) tail) (hkd : b.env gKd = kindTag c.kind)
    (hJ : b.env gJ = p.J) (hfit : ∀ x ∈ witN c p wt, natBitLength x ≤ Λ) (hΛ : Λ + 4 ≤ C.Wd)
    (hbig : (witN c p wt).length + 4 * p.J + 4 < 2 ^ C.Wd) :
    Hs C witP b ((witN c p wt).length * (30 * Λ + 45) + 10 + ((2 * 1 + 3 + (1 + 1) + 1) + (1 + ((srList c p).length *
      ((witN c p wt).length * (30 * Λ + 45) + 10 + 4) + 4) + 1) + 1) + 1)
      (fun d => LS (C := C) a d (L ++ witN c p wt) R tail ∧ d.env gRC = roleCount c.kind ∧
        d.env gJR = p.J * roleCount c.kind ∧ Fr b d witT) := by
  have hseg := witN_eq c p wt
  set Sc := [(coordsOf wt.I).length] ++ coordsOf wt.I with hSc
  set Wl := (srList c p).flatMap (wseg c wt) with hWl
  have hlenW : (witN c p wt).length = Sc.length + Wl.length := by rw [hseg, List.length_append]
  rw [hseg] at h0
  have hrc2 := roleCount_le_two c
  have hsl := srList_len c p
  refine Hs.seq (Hs.mono (readL_LS (a := a) (L := L) (tail := tail) v1 (by decide) Sc _ (coordsOf wt.I) rfl
    (R := Wl ++ R) (by simpa [List.append_assoc] using h0) Λ (by rw [h0.cst.one]; simp)
    (fun x hx => hfit x (by rw [hseg]; exact List.mem_append_left _ hx)) (by omega)
    (by rw [h0.cst.one]; have : Sc.length ≤ (witN c p wt).length := by omega
        simp [hSc] at this; omega)) (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _) (fun _ h => h))
    (fun b1 ⟨L1, f1⟩ => ?_)
  refine Hs.seq (rcP_spec b1 L1.cst c.kind (by rw [f1 gKd (by decide), hkd]) (by omega))
    (fun b2 ⟨r1, r2, r3⟩ => ?_)
  have L2 := LS.sh L1 r2 (Cst.of_fr L1.cst r3 (by decide))
  have b2J : b2.env gJ = p.J := by rw [r3 gJ (by decide), f1 gJ (by decide), hJ]
  refine Hs.seq (hs_mul C gJ gRC gJR b2 (by decide) (by decide) (by decide) (by rw [b2J, r1]; nlinarith))
    (fun b3 hb3 => ?_)
  subst hb3
  have L3 := L2.set gJR (b2.env gJ * b2.env gRC) (by decide)
  set d0 := b2.set gJR (b2.env gJ * b2.env gRC) with hd0
  have d0JR : d0.env gJR = (srList c p).length := by rw [hd0]; vsimp [b2J, r1, hsl]
  let I : ℕ → DS VV MM → Prop := fun k e =>
    LS (C := C) a e (L ++ Sc ++ ((srList c p).take k).flatMap (wseg c wt))
      (((srList c p).drop k).flatMap (wseg c wt) ++ R) tail ∧ Fr d0 e (c2 :: readLT)
  have hJr : p.J * roleCount c.kind ≤ 2 * p.J := by nlinarith
  have hloop := forS_spec' (C := C) c2 gJR (by decide) (readL v2) d0 (srList c p).length (by omega) I
    ((witN c p wt).length * (30 * Λ + 45) + 10)
    (fun k e v ⟨i1, i2⟩ => ⟨i1.set c2 v (by decide), Fr.trans i2 (Fr.set e v (by decide))⟩)
    ⟨by simpa [List.append_assoc] using L3, Fr.refl _ _⟩ d0JR ?_
  · refine Hs.mono hloop le_rfl ?_
    rintro e ⟨⟨i1, i2⟩, _, _⟩
    refine ⟨by rw [hseg]; simpa [List.append_assoc] using i1, ?_, ?_, ?_⟩
    · rw [i2 gRC (by decide), hd0]; vsimp [r1]
    · rw [i2 gJR (by decide), d0JR, hsl]
    · exact Fr.trans (Fr.weaken f1 (by decide)) (Fr.trans (Fr.weaken r3 (by decide))
        (Fr.trans (Fr.set b2 _ (by decide)) (Fr.weaken i2 (by decide))))
  · intro k hk e ⟨i1, i2⟩ hek hem
    have hsr : (srList c p).drop k = (srList c p)[k] :: (srList c p).drop (k + 1) := List.drop_eq_getElem_cons hk
    set sr := (srList c p)[k] with hsrdef
    have hmem : sr ∈ srList c p := List.getElem_mem hk
    have hsegle : (wseg c wt sr).length ≤ (witN c p wt).length := by
      rw [hlenW]; have := len_le_flatMap (srList c p) (wseg c wt) sr hmem; rw [← hWl] at this; omega
    have i1' : LS (C := C) a e (L ++ Sc ++ ((srList c p).take k).flatMap (wseg c wt))
        (wseg c wt sr ++ (((srList c p).drop (k + 1)).flatMap (wseg c wt) ++ R)) tail := by
      have := i1; rw [hsr] at this; simpa [List.append_assoc] using this
    refine Hs.mono (readL_LS v2 (by decide) (wseg c wt sr) (wt.coef sr.1 sr.2).length
      ((wt.coef sr.1 sr.2).flatMap intN) rfl i1' Λ (by rw [i1'.cst.two, flatMap_intN_length]; ring)
      (fun x hx => hfit x (by
        rw [hseg]; apply List.mem_append_right; exact List.mem_flatMap.mpr ⟨sr, hmem, hx⟩)) (by omega)
      (by rw [i1'.cst.two]; have : (wt.coef sr.1 sr.2).length * 2 + 1 = (wseg c wt sr).length := by
            simp only [wseg, List.length_append, List.length_singleton, flatMap_intN_length]; omega
          omega)) (Nat.add_le_add_right (Nat.mul_le_mul_right _ hsegle) _) ?_
    rintro f ⟨g1, g2⟩
    refine ⟨⟨?_, Fr.trans i2 (Fr.weaken g2 (by decide))⟩, by rw [g2 c2 (by decide), hek],
      by rw [g2 gJR (by decide), hem]⟩
    have htk : (srList c p).take (k + 1) = (srList c p).take k ++ [sr] := List.take_succ_eq_append_getElem hk
    rw [htk, List.flatMap_append]; simpa [List.append_assoc] using g1

/-! ## The loader -/

def loadP : St VV MM := .seq callP (.seq parP witP)

/-- The loader's cost bound (`K = 30Λ + 45` per natural, the witness blocks re-bounded by `|witN|`). -/
def loadCost (Lc Lp Lw ns Λ : ℕ) : ℕ :=
  Lc * (30 * Λ + 45) + 400 + (Lp * (30 * Λ + 45) + 400 + (Lw * (30 * Λ + 45) + 10 + ((2 * 1 + 3 + (1 + 1) + 1) +
    (1 + (ns * (Lw * (30 * Λ + 45) + 10 + 4) + 4) + 1) + 1) + 1) + 1) + 1

theorem loadP_spec (a : DS VV MM) (c : Call) (p : Params) (wt : Wit c.n) (tail : List Bool) (Λ : ℕ)
    (h0 : LS (C := C) a a [] (cellN c p wt) tail) (hfit : ∀ x ∈ cellN c p wt, natBitLength x ≤ Λ)
    (hΛ : Λ + 4 ≤ C.Wd) (hbig : (cellN c p wt).length + 4 * p.J + 4 < 2 ^ C.Wd) :
    Hs C loadP a (loadCost (callN c).length (paramsN p).length (witN c p wt).length (srList c p).length Λ)
      (fun b => LS (C := C) a b (cellN c p wt) [] tail ∧ b.env gN = c.n ∧ b.env gKd = kindTag c.kind ∧
        b.env gS = 2 * c.n + 3 ∧ b.env gJ = p.J ∧ b.env gRC = roleCount c.kind ∧
        b.env gJR = p.J * roleCount c.kind ∧ Fr a b loadT) := by
  have hcell : cellN c p wt = callN c ++ paramsN p ++ witN c p wt := rfl
  have hl : (cellN c p wt).length = (callN c).length + (paramsN p).length + (witN c p wt).length := by
    rw [hcell]; simp; omega
  refine Hs.seq (callP_spec a c (paramsN p ++ witN c p wt) tail Λ (by simpa [hcell] using h0)
    (fun x hx => hfit x (by rw [hcell]; simp [hx])) hΛ (by omega)) (fun b1 ⟨L1, e1, e2, e3, f1⟩ => ?_)
  refine Hs.seq (parP_spec a b1 p (callN c) (witN c p wt) tail Λ (by simpa using L1)
    (fun x hx => hfit x (by rw [hcell]; simp [hx])) hΛ (by omega)) (fun b2 ⟨L2, e4, f2⟩ => ?_)
  refine Hs.mono (witP_spec a b2 c p wt (callN c ++ paramsN p) [] tail Λ (by simpa using L2)
    (by rw [f2 gKd (by decide), e2]) e4 (fun x hx => hfit x (by rw [hcell]; simp [hx])) hΛ (by omega)) le_rfl ?_
  rintro b3 ⟨L3, e5, e6, f3⟩
  refine ⟨by simpa [hcell] using L3, ?_, ?_, ?_, ?_, e5, e6, ?_⟩
  · rw [f3 gN (by decide), f2 gN (by decide), e1]
  · rw [f3 gKd (by decide), f2 gKd (by decide), e2]
  · rw [f3 gS (by decide), f2 gS (by decide), e3]
  · rw [f3 gJ (by decide), e4]
  · exact Fr.trans f1 (Fr.trans (Fr.weaken f2 (by decide)) (Fr.weaken f3 (by decide)))

end NearCubicGates.Close.Cells.PrefixLoader
