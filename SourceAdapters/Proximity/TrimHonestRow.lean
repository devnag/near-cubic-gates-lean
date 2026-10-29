import SourceAdapters.Proximity.TrimHonestLoopData
import SourceAdapters.Proximity.HonestRowTableRun

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": one complete actual honest row, from source queries to
the retained auxiliary dictionary, with reusable state for the next row. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest) budget)

theorem row_run (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    {N : ℕ} (input : BitInput S.arity) (proof : BitInput N)
    (Wd Lk Bk Λ : ℕ) (pre tail : List Bool) (a : DS VV MM)
    (ready : HonestRowTable.Ready (SourceCallee.context V proofSize honest budget P Wd
      (pre ++ sourceCircuitWord S ++ tail) Lk Bk) input proof q (sourceCircuitWord S).length pre.length a)
    (auxiliary : AuxiliaryReady (V S) input (finiteProofOracle proof) coins.val a)
    (hrow : a.env QueryStep.rowReg = coins.val)
    (H : HonestRowTable.Bounds V budget S coins input proof Wd Lk Bk Λ)
    (hshift : q + blockVariableBound q < 2 ^ Wd)
    (hkey : ∀ i < blockVariableBound q, 2 * Nat.pair coins.val i + 1 < 2 ^ Wd)
    (hcount : (coins.val + 1) * blockVariableBound q < 2 ^ Wd) :
    let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (rowProgram q) a (rowCost q S.arity N (sourceCircuitWord S).length Lk Bk Λ) (fun b =>
      LoopState (V S) C input proof (sourceCircuitWord S).length pre.length a b (coins.val + 1) ∧
      b.env QueryStep.rowReg = a.env QueryStep.rowReg ∧
      b.env SourceCallee.coinLimitReg = a.env SourceCallee.coinLimitReg) := by
  dsimp only
  let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  obtain ⟨b, nb, eb, hb, rb⟩ := HonestRowTable.run V proofSize honest budget P S coins input proof
    Wd Lk Bk Λ pre tail a ready hrow H
  obtain ⟨d, nd, ed, hd, ad, drc, fd⟩ := append_row (C := C) (V S) coins input proof b rb.ready.source.constants
    (table_preserves_auxiliary auxiliary rb) ((rb.vars QueryStep.rowReg (by decide)).trans hrow)
    rb.ready.local_bound rb.ready.source.bound_eq rb.assignment rb.row_cursor.le hshift hkey hcount
  have f : Fr a d rowTemps :=
    (rb.vars.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (fd.env.weaken (fun _ hx => List.mem_append_right _ hx))
  refine ⟨d, nb + nd + 1, Ex.seq eb ed, by unfold rowCost; omega, ?_⟩
  refine ⟨⟨ready_after_append rb.ready fd drc, ad, fd.out.trans rb.out, ?_, ?_,
    f.weaken (fun _ hx => List.mem_cons_of_mem _ hx)⟩,
    f QueryStep.rowReg (by decide), f SourceCallee.coinLimitReg (by decide)⟩
  · exact (fd.ram scheduleStore (by decide) (by decide)).trans (rb.other_store scheduleStore (by decide))
  · exact (fd.cursor scheduleStore (by decide) (by decide) (by decide)).trans
      (rb.other_cursor scheduleStore (by decide))

end NearCubicGates.Adapters.Proximity.TrimHonest
