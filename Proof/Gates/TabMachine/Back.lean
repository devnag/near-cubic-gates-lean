import Proof.Gates.TabMachine.Decode
import Proof.Hierarchy.CompetitorCountTableBounds
import Proof.Supplier.EquationRowProducer

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (WilliamsAlgorithm)
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (physicalInput leftScore rightScore weight)
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicGates.Close.WordPrograms.SInt (encS)

variable {ns nr : ℕ}

/-! ## Writing `1^n` -/

/-- `X := 1^n` (`n` in register `K`, kept). -/
def writeOnes (X : Fin (ns + 1)) (K K2 : Fin nr) : WMX ns nr :=
  .seq (repK K K2 (.seq (WMX.wr X true) (WMX.fwd X))) (repK K K2 (WMX.bwd X))

theorem writeOnes_spec (cap : ℕ) {X : Fin (ns + 1)} {K K2 : Fin nr} (hK : K ≠ K2) (σ : WState ns nr) (n : ℕ)
    (hX : σ.st X = []) (hXh : σ.sh X = 0) (hKv : σ.val K = n) (hK2 : σ.val K2 = 0) (hcap : 2 * n ≤ cap) :
    WXExec cap (writeOnes X K K2) σ (σ.sets X (List.replicate n true)) (34 * n + 7) := by
  have h1 := Runs.repE (cap := cap) (body := .seq (WMX.wr X true) (WMX.fwd X)) hK 3 n
    (fun k => (σ.sets X (List.replicate k true)).seth X k) hcap (fun k => by simp) (fun k => by simp)
    (fun k _ v1 v2 => by
      have e1 := WXExec.wr cap X true (((σ.sets X (List.replicate k true)).seth X k).setv K v1 |>.setv K2 v2)
      have e2 := WXExec.fwd cap X ((((σ.sets X (List.replicate k true)).seth X k).setv K v1 |>.setv K2 v2).sets X
        (writeTapeBit ((((σ.sets X (List.replicate k true)).seth X k).setv K v1 |>.setv K2 v2).st X)
          ((((σ.sets X (List.replicate k true)).seth X k).setv K v1 |>.setv K2 v2).sh X) true))
      refine (WXExec.seq e1 e2).cast cap ?_ (by omega)
      have hw : writeTapeBit (List.replicate k true) k true = List.replicate (k + 1) true := by
        have := writeTapeBit_end' (List.replicate k true) true
        rw [List.length_replicate] at this; rw [this, List.replicate_succ']
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      · funext i; by_cases hi : i = X
        · subst hi; simp [hw]
        · simp [Function.update_of_ne hi]
      · rfl
      · rfl) (by simp [hKv]) (by simp [hK2])
  have e0 : (σ.sets X (List.replicate 0 true)).seth X 0 = σ := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hXh]
      · simp [Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [hX]
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
  rw [e0] at h1
  have h2 := Runs.repE (cap := cap) (body := WMX.bwd X) hK 1 n
    (fun k => (σ.sets X (List.replicate n true)).seth X (n - k)) hcap (fun k => by simp) (fun k => by simp)
    (fun k hk v1 v2 => by
      refine (WXExec.bwd cap X _).cast cap ?_ le_rfl
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp; omega
        · simp [Function.update_of_ne hi]
      · rfl
      · rfl
      · rfl) (by simp [hKv]) (by simp [hK2])
  have e1 : (σ.sets X (List.replicate n true)).seth X (n - 0) = (σ.sets X (List.replicate n true)).seth X n := by simp
  have e2 : (σ.sets X (List.replicate n true)).seth X (n - n) = σ.sets X (List.replicate n true) := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hXh]
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
    · rfl
  rw [e1, e2] at h2
  exact (WXExec.seq h1 h2).mono (by ring_nf; omega)

/-! ## The printer's entry bank and its table -/

/-- The printer's first fresh tape index (`1^q`), and the third (`[odd]`). -/
noncomputable def freshQ (a : WilliamsAlgorithm) : Fin (CompetitorCountBanks.tapes (producer a) + 124) :=
  ⟨CompetitorCountBanks.tapes (producer a) + 1, by omega⟩
noncomputable def freshOdd (a : WilliamsAlgorithm) : Fin (CompetitorCountBanks.tapes (producer a) + 124) :=
  ⟨CompetitorCountBanks.tapes (producer a) + 3, by omega⟩

theorem cb_large (a : WilliamsAlgorithm) : 692 ≤ CompetitorCountBanks.tapes (producer a) := by
  show 692 ≤ CompetitorCrossScheduler.tapes (producer a) + 511
  unfold CompetitorCrossScheduler.tapes; omega

/-- The printer's entry bank, tape by tape. -/
theorem printerIn_val (a : WilliamsAlgorithm) (r : MatrixScoreBatch.Request) (q : ℕ) (odd : Bool)
    (j : Fin (CompetitorCountBanks.tapes (producer a) + 124)) :
    CompetitorCountTable.input (producer a) r q odd j =
      if j.val = 0 then physicalInput r else if j = freshQ a then List.replicate q true
      else if j = freshOdd a then [odd] else [] := by
  have hcb := cb_large a
  unfold CompetitorCountTable.input CompetitorCountTable.extend
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.addCases_left]
    have h1 : (Fin.castAdd 124 i : Fin _) ≠ freshQ a := by
      intro h; have := congrArg Fin.val h; simp [freshQ] at this; omega
    have h2 : (Fin.castAdd 124 i : Fin _) ≠ freshOdd a := by
      intro h; have := congrArg Fin.val h; simp [freshOdd] at this; omega
    rw [if_neg h1, if_neg h2]
    unfold CompetitorCountBanks.input CompetitorCountBanks.extend
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · simp only [Fin.addCases_left, CompetitorCrossScheduler.input, Fin.val_castAdd]
      split_ifs <;> rfl
    · rw [Fin.addCases_right]
      split_ifs with h
      · exfalso
        have h' : CompetitorCrossScheduler.tapes (producer a) + i'.val = 0 := h
        unfold CompetitorCrossScheduler.tapes at h'; omega
      · rfl
  · simp only [Fin.addCases_right, Fin.val_natAdd, CompetitorCountTable.metadata]
    have h0 : ¬ (CompetitorCountBanks.tapes (producer a) + i.val = 0) := by omega
    rw [if_neg h0]
    by_cases hi1 : i = 1
    · subst hi1
      have : (Fin.natAdd (CompetitorCountBanks.tapes (producer a)) (1 : Fin 124)) = freshQ a := by
        apply Fin.ext; simp [freshQ]
      simp [this]
    · by_cases hi3 : i = 3
      · subst hi3
        have h1 : (Fin.natAdd (CompetitorCountBanks.tapes (producer a)) (3 : Fin 124)) ≠ freshQ a := by
          intro h; have := congrArg Fin.val h; simp [freshQ] at this
        have h2 : (Fin.natAdd (CompetitorCountBanks.tapes (producer a)) (3 : Fin 124)) = freshOdd a := by
          apply Fin.ext; simp [freshOdd]
        rw [if_neg h1, if_pos h2]; rfl
      · have h1 : (Fin.natAdd (CompetitorCountBanks.tapes (producer a)) i) ≠ freshQ a := by
          intro h; apply hi1; apply Fin.ext; have := congrArg Fin.val h; simp [freshQ] at this; simp; omega
        have h2 : (Fin.natAdd (CompetitorCountBanks.tapes (producer a)) i) ≠ freshOdd a := by
          intro h; apply hi3; apply Fin.ext; have := congrArg Fin.val h; simp [freshOdd] at this; simp; omega
        simp [hi1, hi3, h1, h2]

/-- The printed integers in the printer's order: row-major, the lower half of the columns when `odd`. -/
def pvals {u : ℕ} (odd : Bool) (g : Fin u → Fin u → ℤ) : List ℤ :=
  if odd then (List.ofFn fun i => List.ofFn fun j => g i (CompetitorFinalTable.lowerColumn j)).flatten
  else (List.ofFn fun i => List.ofFn fun j => g i j).flatten

theorem values_map {u : ℕ} (odd : Bool) (f : Fin u → Fin u → ℕ) (g : Fin u → Fin u → ℤ) (t : ℕ → ℤ)
    (h : ∀ i j, t (f i j) = g i j) : (CompetitorFinalTable.values odd f).map t = pvals odd g := by
  unfold CompetitorFinalTable.values pvals WilliamsProductCertificate.rowMajorNatMatrix
  cases odd <;> simp [List.map_flatten, List.map_ofFn, Function.comp_def, h]

/-- The table's integer entries are small: `|entry| ≤ #cuts · 2^p`. -/
theorem wd_bound (r : EquationRow.Input) (i j : Fin (EquationRow.request r).U) :
    (SupplierPrinter.weightedDominance (leftScore (EquationRow.request r)) (rightScore (EquationRow.request r))
      (weight (EquationRow.request r)) i j).natAbs ≤ r.cuts.length * 2 ^ r.p := by
  rw [EquationRow.request_value]
  have hc : ∀ c ∈ r.cuts, (EquationRow.exactValue c i.val j.val).natAbs ≤ 2 ^ r.p := by
    intro c hc
    unfold EquationRow.exactValue
    rw [Int.natAbs_mul]
    have h1 := (r.fits c hc).2.2
    have h2 : ((SupplierPrinter.exactCut c.threshold (MatrixScoreBatch.linearForm c.leftWeights i.val +
        MatrixScoreBatch.linearForm c.rightWeights j.val)).toNat : ℤ).natAbs ≤ 1 := by
      cases SupplierPrinter.exactCut c.threshold _ <;> simp
    calc c.coefficient.natAbs * _ ≤ c.coefficient.natAbs * 1 := Nat.mul_le_mul_left _ h2
      _ ≤ 2 ^ r.p := by omega
  have key : ∀ (cs : List MatrixScoreBatch.Cut), (∀ c ∈ cs, (EquationRow.exactValue c i.val j.val).natAbs ≤ 2 ^ r.p) →
      ((cs.map fun c => EquationRow.exactValue c i.val j.val).sum).natAbs ≤ cs.length * 2 ^ r.p := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      intro h
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := Int.natAbs_add_le (EquationRow.exactValue c i.val j.val) ((cs.map fun c => EquationRow.exactValue c
        i.val j.val).sum)
      have h1 := h c (by simp)
      have h2 := ih (fun c' hc' => h c' (by simp [hc']))
      nlinarith
  exact key r.cuts hc

/-! ## Residues -/

theorem toNat_emod_lt (z : ℤ) (q : ℕ) : (z % 2 ^ q).toNat < 2 ^ q := by
  have hp : (0 : ℤ) < 2 ^ q := by positivity
  have h1 := Int.emod_nonneg z hp.ne'
  have h2 := Int.emod_lt_of_pos z hp
  have : ((z % 2 ^ q).toNat : ℤ) < ((2 ^ q : ℕ) : ℤ) := by rw [Int.toNat_of_nonneg h1]; push_cast; exact h2
  exact_mod_cast this

theorem toNat_emod_modEq (z : ℤ) (q : ℕ) : Int.ModEq ((2 : ℤ) ^ q) z (((z % 2 ^ q).toNat : ℕ) : ℤ) := by
  have hp : (0 : ℤ) < 2 ^ q := by positivity
  rw [Int.toNat_of_nonneg (Int.emod_nonneg z hp.ne')]
  exact (Int.mod_modEq z _).symm

theorem mem_rowMajor {a b : ℕ} (g : Fin a → Fin b → ℕ) (v : ℕ)
    (hv : v ∈ WilliamsProductCertificate.rowMajorNatMatrix g) : ∃ i j, g i j = v := by
  unfold WilliamsProductCertificate.rowMajorNatMatrix at hv
  obtain ⟨l, hl, hvl⟩ := List.mem_flatten.mp hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hvl
  exact ⟨i, j, rfl⟩

/-! ## The back end -/

/-- The printer's table tape (`CompetitorCountTable.slot … 141`). -/
noncomputable def outSlot (a : WilliamsAlgorithm) : Fin (CompetitorCountBanks.tapes (producer a) + 124) :=
  CompetitorCountTable.slot (producer a) 141

theorem outSlot_val (a : WilliamsAlgorithm) : (outSlot a).val = CompetitorCountBanks.tapes (producer a) + 106 := by
  unfold outSlot; rw [CompetitorCountTable.slot_value]; simp

/-- The residue width the printer is run with: its maximum `d + 2p' + 3`, `p' = p + 1`. -/
def qOf (r : EquationRow.Input) : ℕ := r.d + 2 * r.p + 5

/-- The number of printed entries: `U²`, or `U·U/2` with the odd crop (`U = 2^d`). -/
def nOf (r : EquationRow.Input) : ℕ := if r.odd then 2 ^ r.d * (2 ^ r.d / 2) else 2 ^ r.d * 2 ^ r.d

theorem prod_input (r : EquationRow.Input) :
    EquationRowFramed.input r = fun i : Fin 130 => if i.val = 0 then frame (EquationRowRaw.source r) else [] := by
  rw [← EquationRowFramed.input_eq]; rfl

/-- The table the printer prints for `r`: `weightedDominance` of its request. -/
noncomputable def wdOf (r : EquationRow.Input) : Fin (EquationRow.request r).U → Fin (EquationRow.request r).U → ℤ :=
  SupplierPrinter.weightedDominance (leftScore (EquationRow.request r)) (rightScore (EquationRow.request r))
    (weight (EquationRow.request r))

/-- **The back end**: request writer, the printer's metadata, the printer, the decoder. -/
noncomputable def back (a : WilliamsAlgorithm) (pmap : Fin 130 → Fin (ns + 1))
    (qmap : Fin (CompetitorCountBanks.tapes (producer a) + 124) → Fin (ns + 1)) (OUT : Fin (ns + 1))
    (NR N2 QR Q1R K2 CO CP TOP SEEN ODDR : Fin nr) : WMX ns nr :=
  .seq (.mach EquationRowFramed.machine pmap)
    (.seq (writeOnes (qmap (freshQ a)) QR K2)
      (.seq (.ifr ODDR (WMX.wr (qmap (freshOdd a)) true) (WMX.wr (qmap (freshOdd a)) false))
        (.seq (.mach (CompetitorCountTable.machine a) qmap)
          (decode (qmap (outSlot a)) OUT NR N2 QR Q1R K2 CO CP TOP SEEN))))

/-- The cost bound of the back end. -/
noncomputable def backCost (a : WilliamsAlgorithm) (r : EquationRow.Input) : ℕ :=
  EquationRowFramed.uniformBudget r + 1 + (34 * qOf r + 7 + 1 + (2 + 1 +
    (CompetitorCountTable.budget a (EquationRow.request r) (qOf r) + 1 + decodeCost (nOf r) (qOf r))))

theorem back_spec (cap : ℕ) (a : WilliamsAlgorithm) {pmap : Fin 130 → Fin (ns + 1)}
    {qmap : Fin (CompetitorCountBanks.tapes (producer a) + 124) → Fin (ns + 1)} {OUT : Fin (ns + 1)}
    {NR N2 QR Q1R K2 CO CP TOP SEEN ODDR : Fin nr}
    (hp : Function.Injective pmap) (hq : Function.Injective qmap) (hq0 : qmap 0 = pmap 128)
    (hpq : ∀ i j, pmap i = qmap j → i = 128 ∧ j = 0) (hOp : ∀ i, pmap i ≠ OUT) (hOq : ∀ j, qmap j ≠ OUT)
    (hR : [NR, N2, QR, Q1R, K2, CO, CP, TOP, SEEN, ODDR].Nodup) (r : EquationRow.Input) (σ : WState ns nr)
    (hsrc : σ.st (pmap 0) = frame (EquationRowRaw.source r)) (hpb : ∀ i, i ≠ 0 → σ.st (pmap i) = [])
    (hqb : ∀ j, j ≠ 0 → σ.st (qmap j) = []) (hph : ∀ i, σ.sh (pmap i) = 0) (hqh : ∀ j, σ.sh (qmap j) = 0)
    (hOUT : σ.st OUT = []) (hOUTh : σ.sh OUT = 0) (hN : σ.val NR = nOf r) (hQ : σ.val QR = qOf r)
    (hQ1 : σ.val Q1R = qOf r - 1) (hODD : σ.val ODDR = r.odd.toNat) (hN2 : σ.val N2 = 0) (hK2 : σ.val K2 = 0)
    (hCO : σ.val CO = 0) (hCP : σ.val CP = 0) (hT : σ.val TOP = 0) (hSE : σ.val SEEN = 0)
    (hg : r.cuts.length ≤ 2 ^ r.d) (hcap : nOf r * (2 * qOf r + 3) + 2 * qOf r + 4 ≤ cap) :
    Runs cap (back a pmap qmap OUT NR N2 QR Q1R K2 CO CP TOP SEEN ODDR) σ (backCost a r)
      (fun τ => τ.st OUT = recStream ((pvals r.odd (wdOf r)).map fun z => binary (qOf r + 1) (encS z)) ∧
        τ.sh OUT = 0 ∧ (∀ i, (∀ j, pmap j ≠ i) → (∀ j, qmap j ≠ i) → i ≠ OUT → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
        τ.val = σ.val ∧ τ.cell = σ.cell) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨hNN2, hNQ, hNQ1, hNK2, hNCO, hNCP, hNT, hNS, hNO⟩, ⟨hN2Q, hN2Q1, hN2K2, hN2CO, hN2CP, hN2T, hN2S, hN2O⟩,
    ⟨hQQ1, hQK2, hQCO, hQCP, hQT, hQS, hQO⟩, ⟨hQ1K2, hQ1CO, hQ1CP, hQ1T, hQ1S, hQ1O⟩,
    ⟨hK2CO, hK2CP, hK2T, hK2S, hK2O⟩, ⟨hCOCP, hCOT, hCOS, hCOO⟩, ⟨hCPT, hCPS, hCPO⟩, ⟨hTS, hTO⟩, hSO⟩ := hR'
  set q := qOf r with hqdef
  have hq1 : 1 ≤ q := by rw [hqdef]; unfold qOf; omega
  set R := EquationRow.request r with hRdef
  -- (1) the request writer
  obtain ⟨act1, hrun1, htape1, hheads1, -⟩ := EquationRowFramed.producer_run r
  have hin1 : (fun j => σ.st (pmap j)) = EquationRowFramed.input r := by
    rw [prod_input]; funext j
    by_cases hj : j.val = 0
    · have : j = 0 := Fin.ext hj
      subst this; simp [hsrc]
    · rw [if_neg hj, hpb j (fun h => hj (by rw [h]; rfl))]
  rw [← hin1] at hrun1
  obtain ⟨τ1, e1, d1⟩ := WXExec.mach_run cap hp σ hph hrun1
  -- the printer's tapes outside the writer's (all but tape 0)
  have hqnp : ∀ j, j ≠ 0 → ∀ i, pmap i ≠ qmap j := fun j hj i h => hj (hpq i j h).2
  have hτ1q : ∀ j, j ≠ 0 → τ1.st (qmap j) = [] ∧ τ1.sh (qmap j) = 0 := by
    intro j hj
    obtain ⟨h1, h2⟩ := d1.other (qmap j) (hqnp j hj)
    exact ⟨h1.trans (hqb j hj), h2.trans (hqh j)⟩
  have hfQ : freshQ a ≠ 0 := by intro h; have := congrArg Fin.val h; simp [freshQ] at this
  have hfO : freshOdd a ≠ 0 := by intro h; have := congrArg Fin.val h; simp [freshOdd] at this
  have hQO : freshQ a ≠ freshOdd a := by intro h; have := congrArg Fin.val h; simp [freshQ, freshOdd] at this
  -- (2) `1^q`
  have e2 := writeOnes_spec cap (X := qmap (freshQ a)) hQK2 τ1 q (hτ1q _ hfQ).1 (hτ1q _ hfQ).2
    (by rw [d1.val, hQ]) (by rw [d1.val, hK2]) (by nlinarith)
  set τ2 := τ1.sets (qmap (freshQ a)) (List.replicate q true) with hτ2
  -- (3) `[odd]`
  have hX3 : τ2.st (qmap (freshOdd a)) = [] := by
    simp [hτ2, Function.update_of_ne (fun h => hQO (hq h).symm), (hτ1q _ hfO).1]
  have hX3h : τ2.sh (qmap (freshOdd a)) = 0 := by simp [hτ2, (hτ1q _ hfO).2]
  have e3 : WXExec cap (.ifr ODDR (WMX.wr (qmap (freshOdd a)) true) (WMX.wr (qmap (freshOdd a)) false)) τ2
      (τ2.sets (qmap (freshOdd a)) [r.odd]) 2 := by
    have hw := fun b => WXExec.wr cap (qmap (freshOdd a)) b τ2
    cases ho : r.odd
    · have h := hw false
      rw [hX3, hX3h] at h
      exact (WXExec.ifrF (by rw [hτ2, WState.sets_val, d1.val, hODD, ho]; rfl) h).cast cap rfl (by omega)
    · have h := hw true
      rw [hX3, hX3h] at h
      exact (WXExec.ifrT (by rw [hτ2, WState.sets_val, d1.val, hODD, ho]; decide) h).cast cap rfl (by omega)
  set τ3 := τ2.sets (qmap (freshOdd a)) [r.odd] with hτ3
  -- (4) the printer
  set f : Fin R.U → Fin R.U → ℕ := fun i j => (wdOf r i j % 2 ^ q).toNat with hf
  have hwidth : q ≤ CompetitorSameBucketColdDense.width R := by
    rw [CompetitorSameBucketColdDense.width_eq, hRdef, hqdef]; unfold qOf; simp [EquationRow.request]; omega
  obtain ⟨act2, hrun2, -, hheads2, htab2, -, -, -, -⟩ := CompetitorCountTable.cold_run a R q r.odd f hwidth
    (fun h => CompetitorRowCountMeaning.odd_even_size r h)
    (fun i => toNat_emod_lt _ q)
    (fun i => toNat_emod_modEq _ q)
  have hin2 : (fun j => τ3.st (qmap j)) = CompetitorCountTable.input (producer a) R q r.odd := by
    funext j
    rw [printerIn_val]
    by_cases hj0 : j.val = 0
    · have : j = 0 := Fin.ext hj0
      subst this
      rw [if_pos (by simp), hq0]
      have h1 : pmap 128 ≠ qmap (freshQ a) := fun h => hfQ (hpq _ _ h).2
      have h2 : pmap 128 ≠ qmap (freshOdd a) := fun h => hfO (hpq _ _ h).2
      simp [hτ3, hτ2, Function.update_of_ne h1, Function.update_of_ne h2, d1.st, htape1, hRdef]
    · rw [if_neg hj0]
      have hj : j ≠ 0 := fun h => hj0 (by rw [h]; rfl)
      by_cases jQ : j = freshQ a
      · subst jQ
        simp [hτ3, hτ2, Function.update_of_ne (fun h => hQO (hq h)), if_pos]
      · by_cases jO : j = freshOdd a
        · subst jO; simp [hτ3, jQ]
        · simp [hτ3, hτ2, jQ, jO, Function.update_of_ne (fun h => jQ (hq h)), Function.update_of_ne (fun h => jO (hq h)),
            (hτ1q j hj).1]
  have hh3 : ∀ j, τ3.sh (qmap j) = 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp [hτ3, hτ2, hq0, d1.sh, hheads1]
    · simp [hτ3, hτ2, (hτ1q j hj).2]
  rw [← hin2] at hrun2
  obtain ⟨τ4, e4, d4⟩ := WXExec.mach_run cap hq τ3 hh3 hrun2
  -- (5) the decoder
  have hOP : τ4.st (qmap (outSlot a)) = (CompetitorFinalTable.values r.odd f).flatMap (binary q) ++ [] := by
    rw [List.append_nil, d4.st]; unfold outSlot; rw [htab2]; rfl
  have hOPh : τ4.sh (qmap (outSlot a)) = 0 := by
    rw [d4.sh, hheads2]
    unfold CompetitorCountTable.heads
    rw [outSlot_val]; have := cb_large a; split_ifs <;> omega
  have hOUT4 : τ4.st OUT = [] ∧ τ4.sh OUT = 0 := by
    obtain ⟨h1, h2⟩ := d4.other OUT (fun j h => hOq j h)
    have e1' : τ3.st OUT = σ.st OUT := by
      rw [hτ3, hτ2]; simp [Function.update_of_ne (fun h => hOq _ h.symm), (d1.other OUT (fun j h => hOp j h)).1]
    have e2' : τ3.sh OUT = σ.sh OUT := by
      rw [hτ3, hτ2]; simp [(d1.other OUT (fun j h => hOp j h)).2]
    exact ⟨by rw [h1, e1', hOUT], by rw [h2, e2', hOUTh]⟩
  have hval4 : τ4.val = σ.val := by rw [d4.val, hτ3, hτ2]; simp [d1.val]
  have hlen : (CompetitorFinalTable.values r.odd f).length = nOf r := by
    rw [CompetitorFinalTable.values_cardinality]; unfold nOf; simp [hRdef, EquationRow.request,
      MatrixScoreBatch.Request.U]
  have hvlt : ∀ v ∈ CompetitorFinalTable.values r.odd f, v < 2 ^ q := by
    intro v hv
    unfold CompetitorFinalTable.values at hv
    split_ifs at hv
    · obtain ⟨i, j, rfl⟩ := mem_rowMajor _ v hv; exact toNat_emod_lt _ q
    · obtain ⟨i, j, rfl⟩ := mem_rowMajor _ v hv; exact toNat_emod_lt _ q
  have e5 := decode_spec cap (OP := qmap (outSlot a)) (OUT := OUT) (N := NR) (N2 := N2) (K := QR) (K1 := Q1R)
    (K2 := K2) (CO := CO) (CP := CP) (TOP := TOP) (SEEN := SEEN) (hOq _)
    (by simp [hNN2, hNQ, hNQ1, hNK2, hNCO, hNCP, hNT, hNS, hN2Q, hN2Q1, hN2K2, hN2CO, hN2CP, hN2T, hN2S, hQQ1, hQK2,
      hQCO, hQCP, hQT, hQS, hQ1K2, hQ1CO, hQ1CP, hQ1T, hQ1S, hK2CO, hK2CP, hK2T, hK2S, hCOCP, hCOT, hCOS, hCPT, hCPS,
      hTS]) τ4 q (CompetitorFinalTable.values r.odd f) [] hq1 hvlt hOP hOPh hOUT4.1 hOUT4.2
    (by rw [hval4, hN, hlen]) (by rw [hval4, hN2]) (by rw [hval4, hQ]) (by rw [hval4, hQ1]) (by rw [hval4, hK2])
    (by rw [hval4, hCO]) (by rw [hval4, hCP]) (by rw [hval4, hT]) (by rw [hval4, hSE]) (by rw [hlen]; exact hcap)
  -- the printed entries are the exact integers
  have hbnd : ∀ i j, (wdOf r i j).natAbs < 2 ^ (q - 1) := by
    intro i j
    have h1 := wd_bound r i j
    have h2 : r.cuts.length * 2 ^ r.p ≤ 2 ^ r.d * 2 ^ r.p := Nat.mul_le_mul_right _ hg
    have h3 : 2 ^ r.d * 2 ^ r.p < 2 ^ (q - 1) := by
      rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by rw [hqdef]; unfold qOf; omega)
    exact lt_of_le_of_lt (h1.trans h2) h3
  have hmap : (CompetitorFinalTable.values r.odd f).map (tc q) = pvals r.odd (wdOf r) :=
    values_map r.odd f (wdOf r) (tc q) (fun i j => tc_residue q hq1 _ (hbnd i j))
  have hrec : (CompetitorFinalTable.values r.odd f).map (fun v => binary (q + 1) (encS (tc q v))) =
      (pvals r.odd (wdOf r)).map fun z => binary (q + 1) (encS z) := by
    rw [← hmap, List.map_map]; rfl
  rw [hrec] at e5
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold backCost; rw [hlen]
  · simp
  · simp [hOUT4.2]
  · intro i hi1 hi2 hi3
    have h4 := d4.other i hi2
    have h1 := d1.other i hi1
    have hiQ : qmap (freshQ a) ≠ i := hi2 _
    have hiO : qmap (freshOdd a) ≠ i := hi2 _
    simp [Function.update_of_ne hi3, h4.1, h4.2, hτ3, hτ2, Function.update_of_ne (Ne.symm hiQ),
      Function.update_of_ne (Ne.symm hiO), h1.1, h1.2]
  · simp [hval4]
  · simp [d4.cell, hτ3, hτ2, d1.cell]

end NearCubicGates.Close.TabMachine
