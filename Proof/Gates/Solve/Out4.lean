import Proof.Gates.Solve.Out3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open NearCubicWires.RepairRepresentation (natWord)

def okP : WMX NS NR :=
  .seq (CounterMachine.emitL sOUT (natWord 1)) (.seq wordNP (.seq (printW 1)
    (.seq (addR rNN rLV rTa) (.whr rLV (.seq (WMX.dec rLV) entP)))))

def okCost (W N C n : ℕ) : ℕ :=
  4 * 3 + 1 + (wordNCost W n + 1 + (printCost W + 1 + (18 * n + 3 + 1 + (n * (entCost W N C + 4) + 1))))

theorem ok_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C m n : ℕ} {a : ℕ → ℕ → ℤ}
    {D : ℤ} {junk : List Bool} (hc : MatCtx σ0 W R C a junk) (hmR : m + n ≤ R) (hn : n < C) (hCN : C ≤ R * C + 2)
    (hCC : σ0.val rCC = C) (hNN : σ0.val rNN = n) (hWL : σ0.val rWL = W + 1) (hR2 : σ0.val rR2 = 2 * (W + 1) + 1)
    (hSD : σ0.val rSD = (decide (D < 0)).toNat) (hD0 : D ≠ 0) (hDlt : D.natAbs < 2 ^ W)
    (hbd : ∀ i < R, (a i n).natAbs < 2 ^ W) (hnW : n < 2 ^ (W + 1)) (hIX : σ0.val rIX = m * C + n)
    (hNZ : σ0.val rNZ = 0) (hSY : σ0.val rSY = 0) (hLE : σ0.val rLE = 0) (hLV : σ0.val rLV = 0)
    (hO : σ0.st sOUT = []) (hOh : σ0.sh sOUT = 0) (hDA : v wAV = D.natAbs) (hcap : capE (R * C) W ≤ cap) :
    Runs cap okP σ (okCost W (R * C) C n) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      σ1.st sOUT = natWord 1 ++ natWord n ++ (List.range n).flatMap (fun j => entW (a (m + j) n) D) ∧
      σ1.sh sOUT = (σ1.st sOUT).length ∧ SameExcept σ0 σ1 [sOUT] [rIX, rNZ, rSY, rLE, rLV]) := by
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  have hco := capE_out (R * C) W
  have hnN : n ≤ R * C := le_trans (show n ≤ R by omega) (Nat.le_mul_of_pos_right _ (by omega))
  -- 1. `natWord 1`
  refine Runs.seq ((opEmit cap h (natWord 1) (by rw [hO, hOh]; rfl)).cost
    (show 4 * (natWord 1).length ≤ 4 * 3 by rw [natWord_flag_len 1 (by omega)])) (fun τ1 h1 => ?_)
  set σ1 := appO σ0 (natWord 1) with hσ1
  have hv1 : ∀ r, σ1.val r = σ0.val r := fun r => appO_val _ _ r
  -- 2. `wQ := n`
  refine Runs.seq (opWordN cap h1 (by rw [hv1, hLV]) (by rw [hv1, hNN]) hnW (by omega))
    (fun τ2 ⟨σ2, h2, hfr2, hLV2⟩ => ?_)
  have hv2 : ∀ r, r ≠ rLV → σ2.val r = σ0.val r := fun r hr => by rw [hfr2.val (by simp [hr]), hv1]
  -- 3. print it
  refine Runs.seq (opPrint cap h2 1 (Or.inl rfl) (by rw [hfr2.sh (by simp), hfr2.st (by simp)]; exact appO_sh _ _)
    (by rw [hv2 _ (by decide), hWL]) (by rw [hv2 _ (by decide), hR2]) (by rw [show pP 1 = wQ from rfl, Function.update_self]; exact hnW) (by omega))
    (fun τ3 h3 => ?_)
  rw [show (Function.update v wQ n) (pP 1) = n from by simp [show pP 1 = wQ from rfl]] at h3
  set σ3 := appO σ2 (natWord n) with hσ3
  have hv3 : ∀ r, r ≠ rLV → σ3.val r = σ0.val r := fun r hr => by rw [appO_val, hv2 r hr]
  -- 4. `rLV := n`
  refine Runs.seq ((opAddR cap h3 (A := rNN) (B := rLV) (by decide) (by decide) (by decide)
    (by rw [appO_val, hLV2, hv3 _ (by decide), hNN]; omega)).cost
    (show 18 * σ3.val rNN + 3 ≤ 18 * n + 3 by rw [hv3 _ (by decide), hNN])) (fun τ4 h4 => ?_)
  rw [show σ3.val rLV + σ3.val rNN = n by rw [appO_val, hLV2, hv3 _ (by decide), hNN]; omega] at h4
  set σA := σ3.setv rLV n with hσA
  have hfrA : SameExcept σ0 σA [sOUT] [rIX, rNZ, rSY, rLE, rLV] :=
    (((appO_same σ0 _).weaken (by simp) (by simp)).trans (hfr2.weaken (by simp) (by simp))).trans
      (((appO_same σ2 _).weaken (by simp) (by simp)).trans (sameExcept_setv σ3 (by simp) _))
  have hvA : ∀ r, r ≠ rLV → σA.val r = σ0.val r := fun r hr => by
    rw [hσA, WState.setv_val, Function.update_of_ne hr, hv3 r hr]
  have hpA : LPar σA W R C m n a D junk :=
    ⟨hc.same hfrA (by decide), hmR, hn, hCN, by rw [hvA _ (by decide), hCC], by rw [hvA _ (by decide), hWL],
      by rw [hvA _ (by decide), hR2], by rw [hvA _ (by decide), hSD], hD0, hDlt, hbd⟩
  have hloop := Runs.count (cap := cap) (K := rLV) (body := entP) (entCost W (R * C) C) n
    (LInv σA W C m n a D (Function.update v wQ n)) (by omega)
    (fun k hk τ hτ _ => ent_step cap hpA hcap (by rw [Function.update_of_ne (by decide)]; exact hDA) k hk τ hτ) τ4
    ⟨σA, _, h4, by simp, by simp [hσA, hσ3, appO], by rw [hvA _ (by decide), hIX]; ring,
      by rw [hvA _ (by decide), hNZ], by rw [hvA _ (by decide), hSY], by rw [hvA _ (by decide), hLE],
      SameExcept.refl _ _ _, rfl, rfl⟩
    (by rw [h4.val (by decide)]; simp [hσA])
  refine hloop.post (fun τ ⟨⟨σ5, v5, h5, hO5, hOh5, _, _, _, _, hfr5, _, _⟩, _⟩ => ⟨σ5, v5, h5, ?_, hOh5,
    hfrA.trans hfr5⟩)
  rw [hO5]
  simp only [hσA, WState.setv_st, hσ3, appO_st, hfr2.st (show sOUT ∉ ([] : List Str) by simp), hσ1, hO,
    List.nil_append, List.append_assoc]

/-! ## The whole output phase -/

def outP : WMX NS NR :=
  .seq (SInt.split wDD wAV rSD rF rR) (.seq chkP
    (.ifr rBAD (.seq (WMX.dec rBAD) (CounterMachine.emitL sOUT (natWord 0))) okP))

def outRegs : List Reg := [rSD, rIX, rBAD, rNZ, rLC, rSY, rLE, rLV]

/-- The output word as printed. -/
def outW (a : ℕ → ℕ → ℤ) (D : ℤ) (m n : ℕ) : List Bool :=
  if ∃ i < m, a i n ≠ 0 then natWord 0
  else natWord 1 ++ natWord n ++ (List.range n).flatMap (fun j => entW (a (m + j) n) D)

def outCost (W N C m n : ℕ) : ℕ := 76 * W + 125 + 1 + (chkCost W N m + 1 + (14 + okCost W N C n + 1))

/-- The data of the output phase (on its reference state). -/
structure OPar (σ0 : MS) (W R C m n : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (junk : List Bool) : Prop where
  mc : MatCtx σ0 W R C a junk
  hmR : m + n ≤ R
  hn : n < C
  hCN : C ≤ R * C + 2
  CC : σ0.val rCC = C
  NN : σ0.val rNN = n
  MM : σ0.val rMM = m
  WL : σ0.val rWL = W + 1
  R2 : σ0.val rR2 = 2 * (W + 1) + 1
  z : ∀ r ∈ outRegs, σ0.val r = 0
  O : σ0.st sOUT = []
  Oh : σ0.sh sOUT = 0
  D0 : D ≠ 0
  Dlt : D.natAbs < 2 ^ W
  bd : ∀ i < R, (a i n).natAbs < 2 ^ W
  nW : n < 2 ^ (W + 1)

theorem out_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C m n : ℕ} {a : ℕ → ℕ → ℤ}
    {D : ℤ} {junk : List Bool} (hp : OPar σ0 W R C m n a D junk) (hDD : v wDD = encS D) (hcap : capE (R * C) W ≤ cap) :
    Runs cap outP σ (outCost W (R * C) C m n) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sOUT = outW a D m n ∧
      σ1.sh sOUT = (σ1.st sOUT).length ∧ SameExcept σ0 σ1 [sOUT] outRegs) := by
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  have hz : ∀ r ∈ outRegs, σ0.val r = 0 := hp.z
  -- 1. `wAV := |D|`, `rSD := [D < 0]`
  refine Runs.seq (opSplit cap h (X := wDD) (M := wAV) (by decide) (by decide) (by decide) (S := rSD) (by decide)
    (hz rSD (by decide)) hDD hp.Dlt cap2) (fun τ1 h1 => ?_)
  set σ1 := σ0.setv rSD (decide (D < 0)).toNat with hσ1
  have hv1 : ∀ r, r ≠ rSD → σ1.val r = σ0.val r := fun r hr => by simp [hσ1, Function.update_of_ne hr]
  have hfr1 : SameExcept σ0 σ1 [sOUT] outRegs := sameExcept_setv σ0 (by simp [outRegs]) _
  -- 2. the check
  refine Runs.seq (chk_spec cap h1 (hp.mc.same hfr1 (by decide)) hcap (by have := hp.hmR; omega) hp.hn hp.hCN
    (by rw [hv1 _ (by decide), hp.CC]) (by rw [hv1 _ (by decide), hp.NN]) (by rw [hv1 _ (by decide), hp.MM])
    (by rw [hv1 _ (by decide), hz rIX (by decide)]) (by rw [hv1 _ (by decide), hz rBAD (by decide)])
    (by rw [hv1 _ (by decide), hz rNZ (by decide)]) (by rw [hv1 _ (by decide), hz rLC (by decide)]) hp.bd)
    (fun τ2 ⟨σ2, v2, h2, h2IX, h2BAD, h2NZ, h2LC, hfr2, ho2⟩ => ?_)
  have hv2 : ∀ r, r ∉ [rIX, rBAD, rNZ, rLC] → r ≠ rSD → σ2.val r = σ0.val r := fun r hr hr' => by
    rw [hfr2.val hr, hv1 r hr']
  have hfr12 : SameExcept σ0 σ2 [sOUT] outRegs := hfr1.trans (hfr2.weaken (by simp) (by simp [outRegs]))
  have hO2 : σ2.st sOUT = [] := by rw [hfr2.st (by simp)]; simp [hσ1, hp.O]
  have hOh2 : σ2.sh sOUT = 0 := by rw [hfr2.sh (by simp)]; simp [hσ1, hp.Oh]
  by_cases hb : ∃ i < m, a i n ≠ 0
  · -- a contradiction: `natWord 0`
    have hB1 : σ2.val rBAD = 1 := by rw [h2BAD]; simp [hb]
    refine (Runs.ifrT (by rw [h2.val (by decide), hB1]; omega) (Runs.seq (opDecR cap h2 (r := rBAD) (by decide)
      (by rw [hB1]; omega)) (fun τ3 h3 => (opEmit cap h3 (natWord 0) (by simp [hO2, hOh2])).post
      (fun τ4 h4 => ⟨_, v2, h4, ?_, appO_sh _ _, ?_⟩)))).cost ?_
    · rw [natWord_flag_len 0 (by omega)]; omega
    · rw [appO_st]; simp [hO2, outW, hb]
    · exact hfr12.trans ((sameExcept_setv σ2 (r := rBAD) (by simp [outRegs]) _).trans
        ((appO_same _ _).weaken (by simp) (by simp)))
  · -- consistent: the solution
    have hB0 : σ2.val rBAD = 0 := by rw [h2BAD]; simp [hb]
    refine (Runs.ifrF (by rw [h2.val (by decide), hB0]) ((ok_spec cap h2 (hp.mc.same hfr12 (by decide)) hp.hmR hp.hn
      hp.hCN (by rw [hv2 _ (by decide) (by decide), hp.CC]) (by rw [hv2 _ (by decide) (by decide), hp.NN])
      (by rw [hv2 _ (by decide) (by decide), hp.WL]) (by rw [hv2 _ (by decide) (by decide), hp.R2])
      (by rw [hfr2.val (by decide)]; simp [hσ1]) hp.D0 hp.Dlt hp.bd hp.nW h2IX h2NZ
      (by rw [hv2 _ (by decide) (by decide), hz rSY (by decide)]) (by rw [hv2 _ (by decide) (by decide), hz rLE (by decide)])
      (by rw [hv2 _ (by decide) (by decide), hz rLV (by decide)]) hO2 hOh2
      (by rw [ho2 _ (by decide)]; simp) hcap).post (fun τ3 ⟨σ3, v3, h3, hO3, hOh3, hfr3⟩ =>
        ⟨σ3, v3, h3, ?_, hOh3, hfr12.trans (hfr3.weaken (by simp) (by simp [outRegs]))⟩))).cost (by omega)
    rw [hO3]; simp [outW, hb]

end NearCubicGates.Close.Solve
