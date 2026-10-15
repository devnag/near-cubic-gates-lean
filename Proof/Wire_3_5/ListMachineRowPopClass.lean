import Proof.Wire_3_5.ListMachineRowPopContract
import Proof.Wire_3_5.BlockCost

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.BlockPlatform

/-- A POP row request. -/
structure PopReq where
  P : FlatListParams
  e : P.FlatSeed
  L : ℕ
  sgn : Bool
  labs : List ℕ
  s : Fin (P.M + 1)
  n : ℕ

/-- The row record of a request. -/
def PopReq.record (r : PopReq) : List Bool := popRowRecC r.P r.e r.L r.sgn r.labs r.s

/-- The row's explicit cost bound. -/
def PopReq.bound (r : PopReq) : ℕ := 2 ^ r.P.walkLen * (128 * (r.record.length + 1) ^ 3)

/-- **The POP row contract** at the ledger `B`. -/
def popContract {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : MachineContract E where
  Req := PopReq
  input := PopReq.record
  pre := fun r => 4 * r.L ≤ r.labs.length ∧
    (∀ h j i, r.P.base.inLevel h (j + 1) i = true → r.P.base.inLevel h j i = true) ∧ 1 ≤ r.n ∧
    r.bound ≤ classBound E .preprocessing r.n (B.kOf r.n) (B.psiOf r.n)
  Out := Expr
  ref := fun r => popRefC r.P r.e r.L r.sgn r.labs r.s
  encode := Rec.exprWord
  cls := .preprocessing
  q := fun r => r.n
  k := fun r => B.kOf r.n
  psi := fun r => B.psiOf r.n
  coef := 4
  errSpec := fun r V => ∀ σ : ℕ → Bool, IntExpression.eval V σ =
    bitInt (decide (r.P.flatReport r.e (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ)) = r.s.val))

/-! ## The word-function run -/

/-- The POP row layout with the final log. -/
abbrev popTapes : ℕ := IPL (19 + 1) + 1 + 1

/-- The output tape. -/
def popOutT : Fin popTapes := Fin.castAdd 1 (Fin.castAdd 1 (pQ (19 + 1) (eI (19 + 1) 6)))

/-- The POP row word machine: the row, then every head rewound. -/
noncomputable def popWordM := MaskedReset.machine popMachine (fun _ => true)

theorem popH_zeros (u : ℕ) : popH u 0 ![0, 0, 0, 0, 0, 0, 0, 0] = fun _ => 0 := by
  funext i
  rcases pcover u i with ⟨a, rfl⟩ | ⟨k, rfl⟩
  · rw [popH_sI]
    refine Scrub.cover (motive := fun a => Scrub.heads (fH u 0 0) a = 0) (fun k => ?_) (by simp) (by simp) a
    rw [Scrub.heads_inner]
    rcases cover u k with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
    · rw [fH_srcO]
    · rw [fH_prSlot]; fin_cases c <;> rfl
    · rw [fH_prSlot]; simp
    · rw [fH_logI]
  · rw [popH_eI]; fin_cases k <;> rfl

theorem pop_entry (w : List Bool) :
    (Fin.addCases (Fin.addCases (qA (19 + 1) (frame w ++ []) (entryA (19 + 1) [] [])) (fun _ : Fin 1 => []))
      (fun _ : Fin 1 => List.replicate 0 false) : Fin popTapes → List Bool) =
      fun i => if i.val = 0 then frame w else [] := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · refine Fin.addCases (fun b => ?_) (fun b => ?_) a
    · rcases qcover (19 + 1) b with rfl | ⟨j, rfl⟩
      · rw [Fin.addCases_left, Fin.addCases_left, qA_in]; simp [inQ]
      · rw [Fin.addCases_left, Fin.addCases_left, qA_p]
        have hv : (Fin.castAdd 1 (Fin.castAdd 1 (pQ (19 + 1) j)) : Fin popTapes).val ≠ 0 := by simp
        rw [if_neg hv]
        unfold entryA
        split_ifs <;> simp [overlay]
    · rw [Fin.addCases_left, Fin.addCases_right]
      have hv : (Fin.castAdd 1 (Fin.natAdd (IPL (19 + 1)) b) : Fin popTapes).val ≠ 0 := by simp
      rw [if_neg hv]
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd (IPL (19 + 1) + 1) a : Fin popTapes).val ≠ 0 := by simp
    rw [if_neg hv]; rfl

/-- **The POP row as a rewound word function run.** -/
theorem popRow_word (r : PopReq) (hl : 4 * r.L ≤ r.labs.length)
    (hnest : ∀ h j i, r.P.base.inLevel h (j + 1) i = true → r.P.base.inLevel h j i = true) :
    ∃ A, Step popWordM (2 * popRowCostC r.P r.e r.L r.sgn r.labs hl r.s + 2) (fun _ => 0)
      (fun i => if i.val = 0 then frame r.record else []) (fun _ => 0) A ∧
      A popOutT = Rec.exprWord (popRefC r.P r.e r.L r.sgn r.labs r.s) := by
  obtain ⟨⟨A', h, _, hout⟩, _, _⟩ := popRow_run r.P r.e r.L r.sgn r.labs hl hnest r.s [] [] [] []
  simp only [List.length_nil, List.nil_append] at h hout
  rw [popH_zeros] at h
  obtain ⟨m, hm⟩ := maskBlank h (fun _ => true) (by
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
      _ = Rec.exprWord (popRefC r.P r.e r.L r.sgn r.labs r.s) := by rw [hout]; simp [overlay]

/-! ## The class blocks and the certificate -/

/-- **The class blocks of the POP row contract.** -/
noncomputable def popBlocks {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : ClassBlocks (popContract B) where
  tapeCount := popTapes
  stateCount := _
  twoTapes := by simp [popTapes, IPL, SL]
  machine := popWordM
  outputTape := popOutT
  outputFresh := by simp [popOutT]
  cost := fun r => 2 * popRowCostC r.1.P r.1.e r.1.L r.1.sgn r.1.labs r.2.1 r.1.s + 2
  exitA := fun r => Classical.choose (popRow_word r.1 r.2.1 r.2.2.1)
  step := fun r => (Classical.choose_spec (popRow_word r.1 r.2.1 r.2.2.1)).1
  exitOut := fun r => (Classical.choose_spec (popRow_word r.1 r.2.1 r.2.2.1)).2
  within := by
    intro r
    obtain ⟨_, _, hcost⟩ := popRow_run r.1.P r.1.e r.1.L r.1.sgn r.1.labs r.2.1 r.2.2.1 r.1.s [] [] [] []
    have hpre := r.2.2.2.2
    have hpos := classBound_pos E .preprocessing (B.kOf r.1.n) (B.psiOf r.1.n) r.2.2.2.1
    show 2 * popRowCostC r.1.P r.1.e r.1.L r.1.sgn r.1.labs r.2.1 r.1.s + 2 ≤
      4 * classBound E .preprocessing r.1.n (B.kOf r.1.n) (B.psiOf r.1.n)
    have hb : popRowCostC r.1.P r.1.e r.1.L r.1.sgn r.1.labs r.2.1 r.1.s ≤ r.1.bound := hcost
    omega

/-- **The POP row contract is certified**: the class blocks, and at every admissible request the reference's value is
the amplified state at the population point. -/
noncomputable def popCertified {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : Certified (popContract B) :=
  (popBlocks B).certified fun r hr => (popRow_run r.P r.e r.L r.sgn r.labs hr.1 hr.2.1 r.s [] [] [] []).2.1

end NearCubicWires.WireExponent3_5.ListMachine.Row
