import Proof.Wire_3_5.ListMachineRowRadixContract

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.BlockPlatform

/-- A RADIX row request. -/
structure RadReq where
  D : ListData
  digs : List Dig
  p : ℕ
  b0 : ℕ
  s : ℕ
  n : ℕ

/-- The row record of a request. -/
def RadReq.record (r : RadReq) : List Bool := radRowRecC r.D r.digs r.p r.b0 r.s

/-- The row's explicit cost bound. -/
def RadReq.bound (r : RadReq) : ℕ := (r.D.M + 1) ^ (2 * r.digs.length) * (128 * (r.record.length + 1) ^ 2)

/-- The admissible requests. -/
def RadReq.Pre (r : RadReq) : Prop :=
  DigsOk r.digs ∧ (∀ j i, r.D.inLevel (j + 1) i = true → r.D.inLevel j i = true) ∧ 1 ≤ r.digs.length ∧ r.s < r.p

/-- **The RADIX row contract** at the ledger `B`. -/
def radContract {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : MachineContract E where
  Req := RadReq
  input := RadReq.record
  pre := fun r => r.Pre ∧ 1 ≤ r.n ∧ r.bound ≤ classBound E .preprocessing r.n (B.kOf r.n) (B.psiOf r.n)
  Out := Expr
  ref := fun r => radRefC r.D r.digs r.p r.b0 r.s
  encode := Rec.exprWord
  cls := .preprocessing
  q := fun r => r.n
  k := fun r => B.kOf r.n
  psi := fun r => B.psiOf r.n
  coef := 4
  errSpec := fun r V => ∀ σ : ℕ → Bool, IntExpression.eval V σ =
    bitInt (decide (Rows.tupleResidue r.p r.b0 (fun d : Fin r.digs.length => repAt r.D r.digs true σ d)
      (fun d : Fin r.digs.length => repAt r.D r.digs false σ d) = (r.s : ZMod r.p)))

/-! ## The word-function run -/

/-- The RADIX row word machine: the row, then every head rewound. -/
noncomputable def radWordM := MaskedReset.machine radMachine (fun _ => true)

/-- **The RADIX row as a rewound word function run.** -/
theorem radRow_word (r : RadReq) (h : r.Pre) :
    ∃ A, Step radWordM (2 * radRowCostC r.D r.digs r.p r.b0 r.s h.1 + 2) (fun _ => 0)
      (fun i => if i.val = 0 then frame r.record else []) (fun _ => 0) A ∧
      A popOutT = Rec.exprWord (radRefC r.D r.digs r.p r.b0 r.s) := by
  obtain ⟨⟨q, A', hs, _, hout⟩, _, _⟩ := radRow_run r.D r.digs r.p r.b0 r.s h.1 h.2.1 h.2.2.1
    (by have := h.2.2.2; omega) h.2.2.2 [] [] [] []
  simp only [List.length_nil, List.nil_append] at hs hout
  rw [popH_zeros] at hs
  obtain ⟨m, hm⟩ := maskBlank hs (fun _ => true) (by
    intro i _
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [Fin.addCases_left]
      rcases qcover (19 + 1) a with rfl | ⟨j, rfl⟩
      · rw [qH_in]
      · rw [qH_p]
    · rw [Fin.addCases_right]) 0
  refine ⟨Fin.addCases A' (fun _ : Fin 1 => List.replicate m false), ?_, ?_⟩
  · refine hm.congr_in ?_ ?_ |>.congr ?_ rfl
    · funext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i
      · rw [Fin.addCases_left]
        refine Fin.addCases (fun b => ?_) (fun b => ?_) a
        · rw [Fin.addCases_left]
          rcases qcover (19 + 1) b with rfl | ⟨j, rfl⟩
          · rw [qH_in]
          · rw [qH_p]
        · rw [Fin.addCases_right]
      · rw [Fin.addCases_right]
    · exact pop_entry r.record
    · funext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> simp
  · calc Fin.addCases A' (fun _ : Fin 1 => List.replicate m false) popOutT
          = A' (Fin.castAdd 1 (pQ (19 + 1) (eI (19 + 1) 6))) := Fin.addCases_left _
      _ = Rec.exprWord (radRefC r.D r.digs r.p r.b0 r.s) := by rw [hout]; simp [overlay]

/-! ## The class blocks and the certificate -/

/-- **The class blocks of the RADIX row contract.** -/
noncomputable def radBlocks {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : ClassBlocks (radContract B) where
  tapeCount := popTapes
  stateCount := _
  twoTapes := by simp [popTapes, IPL, SL]
  machine := radWordM
  outputTape := popOutT
  outputFresh := by simp [popOutT]
  cost := fun r => 2 * radRowCostC r.1.D r.1.digs r.1.p r.1.b0 r.1.s r.2.1.1 + 2
  exitA := fun r => Classical.choose (radRow_word r.1 r.2.1)
  step := fun r => (Classical.choose_spec (radRow_word r.1 r.2.1)).1
  exitOut := fun r => (Classical.choose_spec (radRow_word r.1 r.2.1)).2
  within := by
    intro r
    obtain ⟨_, _, hcost⟩ := radRow_run r.1.D r.1.digs r.1.p r.1.b0 r.1.s r.2.1.1 r.2.1.2.1 r.2.1.2.2.1
      (by have := r.2.1.2.2.2; omega) r.2.1.2.2.2 [] [] [] []
    have hpre := r.2.2.2
    have hpos := classBound_pos E .preprocessing (B.kOf r.1.n) (B.psiOf r.1.n) r.2.2.1
    show 2 * radRowCostC r.1.D r.1.digs r.1.p r.1.b0 r.1.s r.2.1.1 + 2 ≤
      4 * classBound E .preprocessing r.1.n (B.kOf r.1.n) (B.psiOf r.1.n)
    have hb : radRowCostC r.1.D r.1.digs r.1.p r.1.b0 r.1.s r.2.1.1 ≤ r.1.bound := hcost
    omega

noncomputable def radCertified {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : Certified (radContract B) :=
  (radBlocks B).certified fun r hr => (radRow_run r.D r.digs r.p r.b0 r.s hr.1.1 hr.1.2.1 hr.1.2.2.1
    (by have := hr.1.2.2.2; omega) hr.1.2.2.2 [] [] [] []).2.1

end NearCubicWires.WireExponent3_5.ListMachine.Row
