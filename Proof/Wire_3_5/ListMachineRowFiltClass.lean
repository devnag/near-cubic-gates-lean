import Proof.Wire_3_5.ListMachineRowFiltInst

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.BlockPlatform NearCubicWires.SupplierWalk

/-- A FILTER row's population and call width. -/
structure FiltPop where
  L : ℕ
  sgn : Bool
  labs : List ℕ
  n : ℕ

/-- A FILTER row request: the fixed filter seed `(P, e)`, the population, the call width. -/
def FiltReq : Type := Σ P : GapParams, GapSeed P × FiltPop

def FiltReq.P (r : FiltReq) : GapParams := r.1
def FiltReq.e (r : FiltReq) : GapSeed r.P := r.2.1
def FiltReq.L (r : FiltReq) : ℕ := r.2.2.L
def FiltReq.sgn (r : FiltReq) : Bool := r.2.2.sgn
def FiltReq.labs (r : FiltReq) : List ℕ := r.2.2.labs
def FiltReq.n (r : FiltReq) : ℕ := r.2.2.n

/-- The request's table and threshold. -/
def FiltReq.tbl (r : FiltReq) : List (List (List Bool)) := Filt.filterTable r.P r.e r.L
def FiltReq.thr (r : FiltReq) : ℕ := majorityThreshold r.P.walkLen

/-- The row record of a request. -/
def FiltReq.record (r : FiltReq) : List Bool := filtRecC r.tbl r.thr r.L r.sgn r.labs

/-- The row's explicit cost bound. -/
def FiltReq.bound (r : FiltReq) : ℕ := filtCostC r.tbl r.thr r.L r.sgn r.labs

theorem FiltReq.hlen (r : FiltReq) : ∀ vs ∈ r.tbl, ∀ cs ∈ vs, cs.length ≤ r.L :=
  fun vs hvs cs hcs => (Filt.filterTable_lengths r.P r.e r.L vs hvs cs hcs).le

/-- **The FILTER row contract** at the ledger `B`. -/
def filtContract {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : MachineContract E where
  Req := FiltReq
  input := FiltReq.record
  pre := fun r => 4 * r.L ≤ r.labs.length ∧ 1 ≤ r.n ∧
    r.bound ≤ classBound E .preprocessing r.n (B.kOf r.n) (B.psiOf r.n)
  Out := Expr
  ref := fun r => filtRefC r.tbl r.thr r.L r.sgn r.labs
  encode := Rec.exprWord
  cls := .preprocessing
  q := fun r => r.n
  k := fun r => B.kOf r.n
  psi := fun r => B.psiOf r.n
  coef := 4
  errSpec := fun r V => ∀ σ : ℕ → Bool, IntExpression.eval V σ =
    bitInt (gapFilter r.P r.e (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ)))

/-- **The FILTER row's value is the seed's regular filter** at the population point, at every assignment. -/
theorem filtRow_value (r : FiltReq) (σ : ℕ → Bool) :
    IntExpression.eval (filtRefC r.tbl r.thr r.L r.sgn r.labs) σ =
      bitInt (gapFilter r.P r.e (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ))) := by
  have hX : (readX (4 * r.L) r.labs σ).length = 4 * r.L := by simp [readX]
  have hZ := Pop.popBits_length r.sgn r.L _ hX
  have hv := filtPoly_eval r.thr r.tbl r.L r.hlen r.sgn r.labs σ
  rw [gapFilter_eq_filterBits, Filt.filterBits_eq_tab, hZ]
  simp only [filtRefC, IntExpression.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    List.sum_cons, List.sum_nil]
  rw [hv]
  have e1 : Filt.tabEval (majorityThreshold r.P.walkLen) (Filt.filterTable r.P r.e r.L)
      (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ)) = Filt.tabEval r.thr r.tbl (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ)) :=
    rfl
  rw [e1]
  cases Filt.tabEval r.thr r.tbl (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ)) <;> simp [bitZ, bitInt]

/-! ## The word-function run -/

/-- The FILTER row layout with the final log. -/
abbrev filtTapes : ℕ := 1 + (1 + (14 + F37.t) + 1) + 1

/-- The output tape. -/
def filtOutT : Fin filtTapes := Fin.castAdd 1 (flR F37.t (outI F37.t))

/-- The FILTER row word machine: the row, then every head rewound. -/
noncomputable def filtWordM := MaskedReset.machine (filterRowM F37) (fun _ => true)

theorem filt_heads_zero : rH F37.t 0 (fH F37.t 0 0) = fun _ => 0 := by
  funext i
  rcases rcover F37.t i with rfl | ⟨j, rfl⟩
  · rw [rH_in]
  · rw [rH_fl]
    rcases cover F37.t j with rfl | ⟨c, rfl⟩ | ⟨j', rfl⟩ | rfl
    · rw [fH_srcO]
    · rw [fH_prSlot]; fin_cases c <;> rfl
    · rw [fH_prSlot]; simp
    · rw [fH_logI]

theorem filt_entry (w : List Bool) :
    (Fin.addCases (rA F37.t (frame w ++ []) (fA [] (entryBank [] []) (fun _ => []) (List.replicate 0 false)))
      (fun _ : Fin 1 => List.replicate 0 false) : Fin filtTapes → List Bool) =
      fun i => if i.val = 0 then frame w else [] := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · rw [Fin.addCases_left]
    rcases rcover F37.t a with rfl | ⟨j, rfl⟩
    · rw [rA_in]; simp [inR]
    · rw [rA_fl]
      have hv : (Fin.castAdd 1 (flR F37.t j) : Fin filtTapes).val ≠ 0 := by simp [flR]
      rw [if_neg hv]
      rcases cover F37.t j with rfl | ⟨c, rfl⟩ | ⟨j', rfl⟩ | rfl
      · simp [fA, iA, srcO, srcI]
      · rw [fA_prSlot]; fin_cases c <;> simp [NearCubicWires.WireExponent3_5.ListMachine.Print.Bank.tapes, entryBank, overlay]
      · rw [fA_prSlot]; simp
      · simp [fA, logI]
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd (1 + (1 + (14 + F37.t) + 1)) a : Fin filtTapes).val ≠ 0 := by simp
    rw [if_neg hv]; rfl

/-- **The FILTER row as a rewound word function run.** -/
theorem filtRow_word (r : FiltReq) (hl : 4 * r.L ≤ r.labs.length) :
    ∃ n A, n ≤ 2 * r.bound + 2 ∧ Step filtWordM n (fun _ => 0)
      (fun i => if i.val = 0 then frame r.record else []) (fun _ => 0) A ∧
      A filtOutT = Rec.exprWord (filtRefC r.tbl r.thr r.L r.sgn r.labs) := by
  obtain ⟨⟨n, A', hn, hs, _, hout⟩, _⟩ := filtRow_run r.tbl r.thr r.L r.hlen r.sgn r.labs hl [] [] [] [] 0
  simp only [List.length_nil, List.nil_append] at hs hout
  rw [filt_heads_zero] at hs
  obtain ⟨m, hm⟩ := maskBlank hs (fun _ => true) (by
    intro i _
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rfl
    · rfl) 0
  refine ⟨2 * n + 2, Fin.addCases A' (fun _ : Fin 1 => List.replicate m false), by unfold FiltReq.bound; omega, ?_, ?_⟩
  · refine hm.congr_in ?_ ?_ |>.congr ?_ rfl
    · funext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> simp
    · exact filt_entry r.record
    · funext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> simp
  · calc Fin.addCases A' (fun _ : Fin 1 => List.replicate m false) filtOutT
          = A' (flR F37.t (outI F37.t)) := Fin.addCases_left _
      _ = Rec.exprWord (filtRefC r.tbl r.thr r.L r.sgn r.labs) := by rw [hout]; simp [overlay]

/-! ## The class blocks and the certificate -/

/-- **The class blocks of the FILTER row contract.** -/
noncomputable def filtBlocks {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : ClassBlocks (filtContract B) where
  tapeCount := filtTapes
  stateCount := _
  twoTapes := by simp [filtTapes]
  machine := filtWordM
  outputTape := filtOutT
  outputFresh := by simp [filtOutT, flR]
  cost := fun r => Classical.choose (filtRow_word r.1 r.2.1)
  exitA := fun r => Classical.choose (Classical.choose_spec (filtRow_word r.1 r.2.1))
  step := fun r => (Classical.choose_spec (Classical.choose_spec (filtRow_word r.1 r.2.1))).2.1
  exitOut := fun r => (Classical.choose_spec (Classical.choose_spec (filtRow_word r.1 r.2.1))).2.2
  within := by
    intro r
    have hn := (Classical.choose_spec (Classical.choose_spec (filtRow_word r.1 r.2.1))).1
    have hpre := r.2.2.2
    have hpos := classBound_pos E .preprocessing (B.kOf r.1.n) (B.psiOf r.1.n) r.2.2.1
    show Classical.choose (filtRow_word r.1 r.2.1) ≤ 4 * classBound E .preprocessing r.1.n (B.kOf r.1.n) (B.psiOf r.1.n)
    omega

/-- **The FILTER row contract is certified**: the class blocks, and at every admissible request the reference's value
is the seed's regular filter at the population point. -/
noncomputable def filtCertified {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : Certified (filtContract B) :=
  (filtBlocks B).certified fun r _ => filtRow_value r

end NearCubicWires.WireExponent3_5.ListMachine.Row
