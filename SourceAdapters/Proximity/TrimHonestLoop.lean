import SourceAdapters.Proximity.TrimHonestRow

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the actual bounded source-coin loop constructs every
auxiliary row in numeric order, retaining the original input and proof. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def loopProgram (q : ℕ) : St VV MM := forS QueryStep.rowReg SourceCallee.coinLimitReg (rowProgram q)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest) budget)

theorem loop_run (S : SourceCircuit) {N : ℕ} (input : BitInput S.arity) (proof : BitInput N)
    (Wd Lk Bk Λ : ℕ) (pre tail : List Bool) (a : DS VV MM)
    (ready : HonestRowTable.Ready (SourceCallee.context V proofSize honest budget P Wd
      (pre ++ sourceCircuitWord S ++ tail) Lk Bk) input proof q (sourceCircuitWord S).length pre.length a)
    (auxiliary : AuxiliaryReady (V S) input (finiteProofOracle proof) 0 a)
    (hlimit : a.env SourceCallee.coinLimitReg = 2 ^ (V S).randomBits)
    (hwidth : 2 ^ (V S).randomBits < 2 ^ Wd)
    (H : ∀ coins, HonestRowTable.Bounds V budget S coins input proof Wd Lk Bk Λ)
    (hshift : q + blockVariableBound q < 2 ^ Wd)
    (hkey : ∀ row < 2 ^ (V S).randomBits, ∀ i < blockVariableBound q,
      2 * Nat.pair row i + 1 < 2 ^ Wd)
    (hcount : 2 ^ (V S).randomBits * blockVariableBound q < 2 ^ Wd) :
    let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (loopProgram q) a
      (2 ^ (V S).randomBits * (rowCost q S.arity N (sourceCircuitWord S).length Lk Bk Λ + 4) + 4)
      (fun b => LoopState (V S) C input proof (sourceCircuitWord S).length pre.length a b
        (2 ^ (V S).randomBits)) := by
  dsimp only
  let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  let I := fun k b => LoopState (V S) C input proof (sourceCircuitWord S).length pre.length a b k
  have run := forS_spec' (C := C) QueryStep.rowReg SourceCallee.coinLimitReg (by decide)
    (rowProgram q) a (2 ^ (V S).randomBits) hwidth I
    (rowCost q S.arity N (sourceCircuitWord S).length Lk Bk Λ)
    (fun _ _ v h => h.set_row v)
    ⟨ready, auxiliary, rfl, rfl, rfl, Fr.refl _ _⟩ hlimit ?_
  · exact run.mono le_rfl (fun _ h => h.1)
  · intro k hk b hb hi hlim
    have er := row_run V proofSize honest budget P S ⟨k, hk⟩ input proof Wd Lk Bk Λ pre tail b
      hb.ready hb.auxiliary hi (H ⟨k, hk⟩) hshift (hkey k hk)
      ((Nat.mul_le_mul_right (blockVariableBound q) (by omega : k + 1 ≤ 2 ^ (V S).randomBits)).trans_lt hcount)
    refine er.mono le_rfl ?_
    rintro d ⟨hd, di, dlim⟩
    exact ⟨⟨hd.ready, hd.auxiliary, hd.out.trans hb.out, hd.schedule.trans hb.schedule,
      hd.schedule_cursor.trans hb.schedule_cursor, hb.vars.trans hd.vars⟩,
      di.trans hi, dlim.trans hlim⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
