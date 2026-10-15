import Proof.Gates.CounterMachine.TabCallStageA3

/-! # RK, part 10: RG's formula state (`FState`) of a request

`fdataOf x`: RG's data of RK's request — the call's circuits and witness, the rates, `q` and the residue vector
(residue requests) or `q = 1` and no residues (moments). **`fstate_of`**: the stream and register facts RK
establishes give `FState`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {B1 B2 cT : ℕ}

/-- The prime of a request (`1` for moments). -/
def qOf (id : ReqId) : ℕ := if dTag id = 0 then dF2 id else 1

/-- RG's data of a request. -/
def fdataOf (x : TabCallReq B1 B2 cT) : FData := fdata x.r.c x.r.p x.r.wt (qOf x.id) (dRho x.id)

theorem cellReq_coef1 (r : CellReq B1 B2 cT) (hk : r.c.kind ≠ .pair) (s : ℕ) : r.wt.coef s 1 = [] := by
  obtain ⟨w, hw⟩ := r.hw
  have h2 : r.c.second = NCircuit.empty r.c.n := r.adm.2.2.2.1 hk
  unfold decodeWitness at hw
  simp only at hw
  split_ifs at hw with hok
  rw [← Option.some.inj hw]
  simp [circ, h2, NCircuit.empty]

theorem flatMap_flatten' {α β : Type} (L : List (List α)) (f : α → List β) :
    L.flatten.flatMap f = L.flatMap (fun l => l.flatMap f) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.flatMap_append, ih]

theorem W0_eq (c : Call) (p : Params) (wt : Wit c.n) :
    encI ((List.range p.J).map fun s => wt.coef s 0).flatten = encN (W0 c wt p.J) := by
  rw [encI_eq_encN, W0, flatMap_flatten', List.flatMap_map]

theorem W1_eq (r : CellReq B1 B2 cT) :
    encI ((List.range r.p.J).map fun s => r.wt.coef s 1).flatten = encN (W1 r.c r.wt r.p.J) := by
  rw [encI_eq_encN, W1, flatMap_flatten', List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro s _
  by_cases hp : r.c.kind = .pair
  · simp [hp]
  · simp [hp, cellReq_coef1 r hp]

open TabCallProg in
/-- **RG's formula state from RK's facts.** -/
theorem fstate_of (tP tK : ℕ) (x : TabCallReq B1 B2 cT) (σ : WState (TabCallProg.NS tP tK) TabCallProg.NR)
    (hS : σ.st (Y tP tK 0) = []) (hSh : σ.sh (Y tP tK 0) = 0) (hF : ∀ i, σ.val (F i) = 0)
    (hy1 : σ.st (Y tP tK 1) = encN (W0 x.r.c x.r.wt x.r.p.J))
    (hy2 : σ.st (Y tP tK 2) = encN (x.r.c.first.coeffs.flatMap intN))
    (hy3 : σ.st (Y tP tK 3) = encN (W1 x.r.c x.r.wt x.r.p.J))
    (hy4 : σ.st (Y tP tK 4) = encN (x.r.c.second.coeffs.flatMap intN))
    (hy5 : σ.st (Y tP tK 5) = encN (x.r.p.factors ++ [x.r.p.M1, x.r.p.A]))
    (hy6 : σ.st (Y tP tK 6) = encN (dRho x.id)) (hsh : ∀ i : Fin 8, i ≠ 0 → σ.sh (Y tP tK i) = 0)
    (h0 : σ.val (X 0) = if x.r.c.kind = .pair then 1 else 0) (h1 : σ.val (X 1) = x.r.p.J)
    (h5 : σ.val (X 5) = qOf x.id - 1) (hb : ∀ d ∈ bndRegs, σ.val d = 2 * (tabCallInput x).length)
    (h8 : σ.val (X 8) = x.r.p.e)
    (h11 : σ.val (X 11) = ((if x.r.c.kind = .pair then 1 else 0) + 1) * (x.r.p.J + 1))
    (h14 : σ.val (X 14) = x.r.c.first.gates.length) (h15 : σ.val (X 15) = 0)
    (h18 : σ.val (X 18) = x.r.c.second.gates.length) (h19 : σ.val (X 19) = x.r.c.first.gates.length)
    (h22 : σ.val (X 22) = 2 * x.r.p.k) (hz : ∀ i : Fin 24, i ∈ ([2, 3, 4] : List (Fin 24)) → σ.val (X i) = 0) :
    FState (Y tP tK) X F σ (fdataOf x) := by
  have hb' := streams_le x
  simp only [allN] at hb'
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hb'
  have hle := len_eq x
  have hB : ∀ i : Fin 24, i ∈ ([6, 7, 16, 17, 20, 21] : List (Fin 24)) → σ.val (X i) = 2 * (tabCallInput x).length := by
    intro i hi
    apply hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bndRegs]
  have hrc : (fdataOf x).rc = (if x.r.c.kind = .pair then 1 else 0) + 1 := by
    unfold fdataOf; rw [fdata_rc]; unfold roleCount; cases x.r.c.kind <;> simp
  refine ⟨⟨⟨by rw [hSh, hS]; rfl, fun i _ => hF _⟩, hF 9, hF 10, hF 17, hF 18, hF 19⟩, fun i j => by lne,
    ⟨[], ?_⟩, ⟨[], ?_⟩, ⟨[], ?_⟩, ⟨[], ?_⟩, ⟨[], ?_⟩, ⟨[], ?_⟩, hsh, ?_, h1, h5, ?_, ?_, h8, ?_, h14, h15, ?_, ?_,
    h18, h19, ?_, ?_, ?_, hz⟩
  · rw [hy1, List.append_nil]; exact (W0_eq x.r.c x.r.p x.r.wt).symm
  · rw [hy2, List.append_nil, encI_eq_encN]; rfl
  · rw [hy3, List.append_nil]; exact (W1_eq x.r).symm
  · rw [hy4, List.append_nil, encI_eq_encN]; rfl
  · rw [hy5, List.append_nil]; rfl
  · rw [hy6, List.append_nil]; rfl
  · rw [h0]; simp [fdataOf, fdata]
  · rw [hB 6 (by simp)]; show (encN (x.r.p.factors ++ [x.r.p.M1, x.r.p.A])).length ≤ _; omega
  · rw [hB 7 (by simp)]; show (encN (dRho x.id)).length ≤ _; omega
  · rw [h11, hrc]; rfl
  · rw [hB 16 (by simp)]; show (encI ((List.range x.r.p.J).map fun s => x.r.wt.coef s 0).flatten).length ≤ _
    rw [W0_eq]; omega
  · rw [hB 17 (by simp)]; show (encI x.r.c.first.coeffs).length ≤ _; rw [encI_eq_encN]; omega
  · rw [hB 20 (by simp)]; show (encI ((List.range x.r.p.J).map fun s => x.r.wt.coef s 1).flatten).length ≤ _
    rw [W1_eq]; omega
  · rw [hB 21 (by simp)]; show (encI x.r.c.second.coeffs).length ≤ _; rw [encI_eq_encN]; omega
  · rw [h22]; rfl

theorem mem_wit (c : Call) (p : Params) (wt : Wit c.n) (s r : ℕ) (hs : s < p.J) (hr : r < roleCount c.kind)
    (z : ℤ) (hz : z ∈ wt.coef s r) : z.natAbs ∈ witN c p wt := by
  unfold witN srList
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  right
  refine ⟨(s, r), ⟨s, hs, r, hr, rfl⟩, ?_⟩
  simp only [List.mem_append, List.mem_flatMap]
  right; exact ⟨z, hz, by simp [intN]⟩

theorem mem_circ {n : ℕ} (C : NCircuit n) (z : ℤ) (hz : z ∈ C.coeffs) : z.natAbs ∈ circN C := by
  rw [circN_split]; simp only [List.mem_append, List.mem_flatMap]
  left; left; right; exact ⟨z, hz, by simp [intN]⟩

theorem mem_params_L (p : Params) (v : ℕ) (hv : v ∈ p.factors ++ [p.M1, p.A]) : v ∈ paramsN p := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold paramsN
  rcases hv with h | h | h
  · simp [h]
  · subst h; simp
  · subst h; simp

/-- **RG's bounds for a request.** -/
theorem fbound_of (x : TabCallReq B1 B2 cT) (Λ : ℕ) (hbits : ∀ v ∈ descN x.id ++ cellN x.r.c x.r.p x.r.wt, natBitLength v ≤ Λ)
    (hJ : x.r.p.J ≤ Λ) (hq : qOf x.id - 1 ≤ Λ) (he : x.r.p.e ≤ Λ) (hk : 2 * x.r.p.k ≤ Λ)
    (hG : x.r.c.first.gates.length + x.r.c.second.gates.length ≤ Λ) : FBound (fdataOf x) Λ := by
  obtain ⟨w, hw⟩ := x.r.hw
  have hadm := x.r.adm
  have wf1 : x.r.c.first.gates.length = x.r.c.first.coeffs.length := hadm.2.1.1
  have wf2 : x.r.c.second.gates.length = x.r.c.second.coeffs.length := hadm.2.2.1.1
  have hspec := cellReq_spec x.r
  have hfl := factors_length hspec
  have hcell : ∀ v ∈ cellN x.r.c x.r.p x.r.wt, natBitLength v ≤ Λ := fun v hv => hbits v (by simp [hv])
  have hwit : ∀ v ∈ witN x.r.c x.r.p x.r.wt, natBitLength v ≤ Λ := fun v hv => hcell v (by simp [cellN, hv])
  have hcall : ∀ v ∈ callN x.r.c, natBitLength v ≤ Λ := fun v hv => hcell v (by simp [cellN, hv])
  have hpar : ∀ v ∈ paramsN x.r.p, natBitLength v ≤ Λ := fun v hv => hcell v (by simp [cellN, hv])
  have hrc2 : roleCount x.r.c.kind = 2 ↔ x.r.c.kind = .pair := by cases x.r.c.kind <;> simp [roleCount]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hJ, hq, he, hk, hG, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only [fdataOf, fdata, List.mem_map, List.mem_range] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    rw [coef_length_of_decode _ _ w _ hw s 0 hs (roleCount_pos _)]; simp [circ, wf1, fdataOf, fdata]
  · intro b hb
    simp only [fdataOf, fdata, List.mem_map, List.mem_range] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    by_cases hp : x.r.c.kind = .pair
    · rw [coef_length_of_decode _ _ w _ hw s 1 hs (by rw [(hrc2).2 hp]; omega)]; simp [circ, wf2, fdataOf, fdata]
    · rw [cellReq_coef1 x.r hp]; simp [hadm.2.2.2.1 hp, NCircuit.empty, fdataOf, fdata]
  · simp [fdataOf, fdata, wf1]
  · simp [fdataOf, fdata, wf2]
  · simp [fdataOf, fdata]
  · simp [fdataOf, fdata]
  · simp [fdataOf, fdata]; omega
  · intro b hb z hz
    simp only [fdataOf, fdata, List.mem_append, List.mem_map, List.mem_range] at hb
    rcases hb with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · exact hwit _ (mem_wit _ _ _ s 0 hs (roleCount_pos _) z hz)
    · by_cases hp : x.r.c.kind = .pair
      · exact hwit _ (mem_wit _ _ _ s 1 hs (by rw [(hrc2).2 hp]; omega) z hz)
      · rw [cellReq_coef1 x.r hp] at hz; simp at hz
  · intro z hz
    simp only [fdataOf, fdata, List.mem_append] at hz
    rcases hz with hz | hz
    · exact hcall _ (by rw [callN]; simp [mem_circ _ z hz])
    · exact hcall _ (by rw [callN]; simp [mem_circ _ z hz])
  · intro v hv
    exact hpar v (mem_params_L _ v hv)
  · intro v hv
    exact hbits v (by
      simp only [List.mem_append]; left
      cases hid : x.id with
      | residue part q κ σ => simp only [fdataOf, fdata, hid, dRho] at hv; simp [descN, hv]
      | digitMoment r j => simp [fdataOf, fdata, hid, dRho] at hv
      | phiMoment r => simp [fdataOf, fdata, hid, dRho] at hv)
  · exact ⟨hpar _ (mem_params_L _ _ (by simp [fdataOf, fdata])), hpar _ (mem_params_L _ _ (by simp [fdataOf, fdata]))⟩

end NearCubicGates.Close.CounterMachine
