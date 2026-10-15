import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicWires.RepairOrdinary (frame)

/-- The field-width bound of the run. -/
def Lam {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : ℕ := 8 * ((cellInput r).length + 1) ^ 2

/-- The language cost of the run. -/
def costP {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : ℕ :=
  loadCost (callN r.c).length (paramsN r.p).length (witN r.c r.p r.wt).length (srList r.c r.p).length (Lam r) +
    16 * (cellN r.c r.p r.wt).length + 5 * r.c.n + 5 * r.p.k + 4 * preCost r.c r.p r.wt (Lam r) + 400

theorem nbl_le_self' (v : ℕ) : natBitLength v ≤ v + 1 := nbl_le_self v

theorem nbl_pow (k : ℕ) : natBitLength (2 ^ k) = k + 1 := by
  unfold natBitLength; rw [Nat.log_pow (by norm_num)]

theorem card_le_n {n : ℕ} (I : Finset (Fin n)) : I.card ≤ n := by
  have := Finset.card_le_univ I; simpa using this

/-! ## Stores after the pass -/

theorem storesOf_G1 (F : Fin MM → List ℕ) (c : Call) (wt : Wit c.n) :
    storesOf F c wt sG1 = F sG1 ++ c.first.gates.flatMap gateN := by
  unfold storesOf
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self]

theorem storesOf_G2 (F : Fin MM → List ℕ) (c : Call) (wt : Wit c.n) :
    storesOf F c wt sG2 = F sG2 ++ c.second.gates.flatMap gateN := by
  unfold storesOf
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]

theorem storesOf_Pa (F : Fin MM → List ℕ) (c : Call) (wt : Wit c.n) :
    storesOf F c wt sPa = F sPa ++ c.parity := by
  unfold storesOf
  rw [Function.update_of_ne (by decide), Function.update_self]

theorem storesOf_In (F : Fin MM → List ℕ) (c : Call) (wt : Wit c.n) :
    storesOf F c wt sIn = F sIn ++ coordsOf wt.I := by
  unfold storesOf
  rw [Function.update_self]

/-! ## Size facts -/

section B
variable {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT)

theorem lam_ge : 8 * ((cellInput r).length + 1) ≤ Lam r := by
  unfold Lam; rw [pow_two, ← mul_assoc]; exact Nat.le_mul_of_pos_right _ (by omega)

theorem n_le_X : r.c.n ≤ (cellInput r).length := (n_le_cellN r).trans (cellN_len_le r)

theorem k_le_n : r.p.k ≤ r.c.n := by rw [← cellReq_hk r]; exact card_le_n _

theorem G_le_X : r.c.first.gates.length + r.c.second.gates.length ≤ (cellInput r).length := by
  have h1 := gates_le_circ r.c.first
  have h2 := gates_le_circ r.c.second
  have h3 := split_len r
  have h4 := cellN_len_le r
  omega

theorem circ_le_X (ro : ℕ) : (circ r.c ro).gates.length ≤ (cellInput r).length := by
  have := G_le_X r
  unfold circ; split_ifs <;> omega

theorem kk_le_X : (coordsOf r.wt.I).length ≤ (cellInput r).length := by
  have h1 := tail_len r
  have h3 := split_len r
  have h4 := cellN_len_le r
  omega

theorem nbl_lam {v : ℕ} (h : v ≤ 2 * (cellInput r).length + 1) : natBitLength v ≤ Lam r :=
  (nbl_le_self' v).trans (by have := lam_ge r; omega)

theorem B0_lam : natBitLength (Call.B0 r.c.n) ≤ Lam r := by
  refine (nbl_le_self' _).trans ?_
  have hB := B0_le r.c.n
  have hn := n_le_X r
  have h1 : 4 * r.c.n * (r.c.n + 1) ≤ 4 * (((cellInput r).length + 1) * ((cellInput r).length + 1)) := by
    calc 4 * r.c.n * (r.c.n + 1) = 4 * (r.c.n * (r.c.n + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 4 (Nat.mul_le_mul (by omega) (by omega))
  have h2 : Lam r = 8 * (((cellInput r).length + 1) * ((cellInput r).length + 1)) := by unfold Lam; rw [pow_two]
  have h3 : 1 ≤ ((cellInput r).length + 1) * ((cellInput r).length + 1) := Nat.mul_pos (by omega) (by omega)
  rw [h2]; omega

theorem fitN : ∀ x ∈ cellN r.c r.p r.wt, natBitLength x ≤ Lam r :=
  fun x hx => (nbl_cellN r x hx).trans (by have := lam_ge r; omega)

theorem sq_le_lam : 8 * (r.c.n + 1) ^ 2 ≤ Lam r := by
  have : (r.c.n + 1) ^ 2 ≤ ((cellInput r).length + 1) ^ 2 := Nat.pow_le_pow_left (by have := n_le_X r; omega) 2
  unfold Lam; omega

/-- The cost of the six phases. -/
theorem cost_sum (n1 n2 n3 n4 n5 n6 : ℕ) (h1 : n1 ≤ 5)
    (h2 : n2 ≤ loadCost (callN r.c).length (paramsN r.p).length (witN r.c r.p r.wt).length (srList r.c r.p).length
      (Lam r))
    (h3 : n3 ≤ 16 * (cellN r.c r.p r.wt).length + 300) (h4 : n4 ≤ 5 * r.c.n + 5 * r.p.k + 60)
    (h5 : n5 ≤ preCost r.c r.p r.wt (Lam r) + preCost r.c r.p r.wt (Lam r) + 1 + 1)
    (h6 : n6 ≤ preCost r.c r.p r.wt (Lam r) + 3 + (preCost r.c r.p r.wt (Lam r) + 3 + 1) + 1) :
    n1 + (n2 + (n3 + (n4 + (n5 + n6 + 1) + 1) + 1) + 1) + 1 ≤ costP r := by
  unfold costP
  generalize loadCost (callN r.c).length (paramsN r.p).length (witN r.c r.p r.wt).length (srList r.c r.p).length
    (Lam r) = L at h2 ⊢
  generalize preCost r.c r.p r.wt (Lam r) = P at h5 h6 ⊢
  omega

end B

/-! ## The run -/

/-- The printing state after the set-up. -/
theorem gs_of {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) (C : Ctx) (f : DS VV MM) (vf : Valid C f) (cf : Cst f)
    (hW2 : 2 ≤ C.Wd) (hLW : (coordsOf r.wt.I).length < C.Wd)
    (fn : f.env gN = r.c.n) (ftag : f.env gKd = kindTag r.c.kind) (fk : f.env xk = r.p.k)
    (fs : f.env xs = r.c.n - r.p.k) (fB : f.env xB = Call.B0 r.c.n) (fK : f.env xK2 = 2 ^ r.p.k)
    (fG1 : f.env xG1 = r.c.first.gates.length) (fG2 : f.env xG2 = r.c.second.gates.length)
    (fGr : f.env xGr = r.c.first.gates.length + r.c.second.gates.length)
    (fm1 : f.env xm1 = (r.c.first.gates.flatMap gateN).length)
    (fm2 : f.env xm2 = (r.c.second.gates.flatMap gateN).length)
    (fnp : f.env xnp = r.c.parity.length) (fkk : f.env xkk = (coordsOf r.wt.I).length)
    (F : Fin MM → List ℕ) (hF : ∀ m : Fin MM, m ≠ sN → F m = []) (fram : f.ram = storesOf F r.c r.wt) :
    GS C f r.c r.p r.wt (Lam r) := by
  have hX := n_le_X r
  have hk := k_le_n r
  have hG := G_le_X r
  have hkk := kk_le_X r
  refine ⟨vf, cf, hW2, fn, ftag, fk, fs, fB, fK, fG1, fG2, fGr, fm1, fm2, fnp, fkk, ?_, ?_, ?_, ?_,
    cellReq_hk r, resGates_flat r.c B1 B2 r.adm, hLW, nbl_lam r (by omega), nbl_lam r (by omega),
    nbl_lam r (by omega), B0_lam r, ?_, nbl_lam r (by omega), nbl_lam r (by omega), nbl_lam r (by omega),
    nbl_lam r (by omega), nbl_lam r (by omega), fun x hx => fitN r x (blk1_sub r x hx),
    fun x hx => fitN r x (blk2_sub r x hx), fun x hx => fitN r x (coords_sub r x hx), nbl_lam r (by omega)⟩
  · rw [fram, storesOf_G1, hF sG1 (by decide), List.nil_append]
  · rw [fram, storesOf_G2, hF sG2 (by decide), List.nil_append]
  · rw [fram, storesOf_Pa, hF sPa (by decide), List.nil_append]
  · rw [fram, storesOf_In, hF sIn (by decide), List.nil_append]
  · rw [nbl_pow]; have := lam_ge r; omega

/-- **The run.** -/
theorem main_run {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) (C : Ctx) (hinp : C.inp = cellInput r)
    (hWd : Lam r + 5 * (cellInput r).length + 8 ≤ C.Wd) :
    Hs C mainP a0 (costP r) (fun b => b.out = prefixesWord r) := by
  have hNX : (cellN r.c r.p r.wt).length ≤ (cellInput r).length := cellN_len_le r
  have hlam := lam_ge r
  have hWpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hW2 : 2 ≤ C.Wd := by omega
  have hJ : r.p.J ≤ (callTail r.c r.p r.wt).length := J_le_tail r
  have hlen := split_len r
  have hkn := k_le_n r
  have hnX := n_le_X r
  have hG := G_le_X r
  have hkk := kk_le_X r
  -- 1. constants
  obtain ⟨a1, n1, ex1, hn1, ⟨⟨a1c, a1ram, a1rc, a1ip, a1out, -, -, -⟩, va1⟩⟩ :=
    Hs.valid (cstInit_spec C hW2) (a0_valid C) (by omega)
  -- 2. the loader
  have h0 : LS (C := C) a1 a1 [] (cellN r.c r.p r.wt) [] := by
    refine ⟨⟨?_, ?_, by simp, rfl, rfl, rfl, rfl⟩, ?_, a1c, ?_⟩
    · rw [List.append_nil, Function.update_eq_self]
    · rw [a1rc]; funext m; by_cases hm : m = sN
      · subst hm; simp [a1ram]
      · simp [Function.update_of_ne hm]
    · rw [a1ip, hinp, cellInput_eq]; simp
    · rw [a1rc, a1ram]; rfl
  have hbig : (cellN r.c r.p r.wt).length + 4 * r.p.J + 4 < 2 ^ C.Wd := by omega
  obtain ⟨b, n2, ex2, hn2, ⟨⟨bLS, bN, bKd, bS, _, _, _, -⟩, vb⟩⟩ :=
    Hs.valid (loadP_spec a1 r.c r.p r.wt [] (Lam r) h0 (fitN r) (by omega) hbig) va1 (by omega)
  have bram : b.ram = Function.update (fun _ => []) sN (cellN r.c r.p r.wt) := by
    rw [bLS.ld.1, a1ram]; simp
  have brc : b.rc = Function.update (fun _ => 0) sN (cellN r.c r.p r.wt).length := by
    rw [bLS.ld.2.1, a1rc, a1ram]; simp
  have bout : b.out = [] := by rw [bLS.ld.2.2.2.1, a1out]
  -- 3. the pass
  obtain ⟨e, n3, ex3, hn3, ⟨⟨eP, eG1, em1, eG2, em2, enp, ek, ekk, -⟩, ve⟩⟩ :=
    Hs.valid (parseP_spec C r.c r.p r.wt b (by rw [bram]; simp) (fun m hm => by
      rw [brc, bram, Function.update_of_ne hm, Function.update_of_ne hm]; rfl) (by rw [brc]; simp) bS
      (by omega)) vb (by omega)
  have ec : Cst e := Cst.of_fr bLS.cst eP.fr (by decide)
  have en : e.env gN = r.c.n := by rw [eP.fr gN (by decide), bN]
  have ekd : e.env gKd = kindTag r.c.kind := by rw [eP.fr gKd (by decide), bKd]
  -- 4. the set-up
  have hn8 : 8 * (r.c.n + 1) ^ 2 < 2 ^ C.Wd := by have := sq_le_lam r; omega
  obtain ⟨f, n4, ex4, hn4, ⟨⟨fs, fB, fK, fGr, fsm, ffr⟩, vf⟩⟩ :=
    Hs.valid (setupG_spec C e ec r.c.n r.p.k r.c.first.gates.length r.c.second.gates.length en ek hkn eG1 eG2 hn8
      (by omega) (by omega)) ve (by omega)
  -- 5. the printing state
  have hGS : GS C f r.c r.p r.wt (Lam r) :=
    gs_of r C f vf (Cst.of_fr ec ffr (by decide)) hW2 (by omega) (by rw [ffr gN (by decide), en])
      (by rw [ffr gKd (by decide), ekd]) (by rw [ffr xk (by decide), ek]) fs fB fK
      (by rw [ffr xG1 (by decide), eG1]) (by rw [ffr xG2 (by decide), eG2]) fGr
      (by rw [ffr xm1 (by decide), em1]) (by rw [ffr xm2 (by decide), em2]) (by rw [ffr xnp (by decide), enp])
      (by rw [ffr xkk (by decide), ekk]) b.ram (fun m hm => by rw [bram, Function.update_of_ne hm])
      (by rw [fsm.ram, eP.ram])
  -- 6. the prefixes
  have h0' : 2 * (circ r.c 0).gates.length < 2 ^ C.Wd := by have := circ_le_X r 0; omega
  have h1' : 2 * (circ r.c 1).gates.length < 2 ^ C.Wd := by have := circ_le_X r 1; omega
  obtain ⟨g, n5, ex5, hn5, ⟨g1, g2, g3, g4, g5⟩⟩ := resBlockO C hGS
  have hGSg := hGS.tr g2 g4 g5
  obtain ⟨h, n6, ex6, hn6, ⟨h1, -, -, -, -⟩⟩ := momBlockO C hGSg h0' h1'
  refine ⟨h, n1 + (n2 + (n3 + (n4 + (n5 + n6 + 1) + 1) + 1) + 1) + 1,
    Ex.seq ex1 (Ex.seq ex2 (Ex.seq ex3 (Ex.seq ex4 (Ex.seq ex5 ex6)))), cost_sum r n1 n2 n3 n4 n5 n6 hn1 hn2 hn3 hn4
      hn5 hn6, ?_⟩
  show h.out = prefixesWord r
  rw [h1, g1, fsm.out, eP.out, bout]
  simp [prefixesWord]

end NearCubicGates.Close.CounterMachine.PrefixProg
