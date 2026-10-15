import Proof.CaseAnalysis.RowsEstimatorPaidDriverReady
import Proof.CaseAnalysis.RowsEstimatorPreparedRun

/-! Actual D production hands the literal bank to the paid reusable Warm consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Returned (p : Program) (D : ℕ) (word : List Bool) (fields : Fin 7 → List Bool)
    (A : Fin (WarmPrepare.tapes p) → List Bool) : Prop :=
  A (WarmPrepare.spare p)=word ∧
    (∀ i,A (WarmPrepare.work p i)=List.replicate D false) ∧
    A (WarmPrepare.driver p)=List.replicate D true ∧ A (WarmPrepare.log p)=List.replicate (D+1) false ∧
    (∀ i,A (WarmPrepare.source p i)=fields i)

def WarmJoined {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (worker : Machine (tapes a p) s)
    (fuel bound : ℕ) (initial : Configuration (tapes a p) s) (D : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) : Prop := ∃ A extra r,
  runFrom worker fuel initial=some r ∧ r.final.heads=heads a p word ∧
    r.final.tapes=Fin.addCases A extra ∧ r.steps ≤ bound ∧ Returned p D word fields A ∧
    extra (ScannedClean.fresh a 1)=List.replicate D true

theorem prepare_config {t s u : ℕ} (first : Machine t s) (second : Machine t u)
    (H : Fin t → ℕ) (A : Fin t → List Bool) :
    WarmPrepared.startWith first second H A=(⟨(Composition.machine first second).start,H,A⟩ : Configuration t (s+u)) := rfl

theorem heads_eq (a : WilliamsAlgorithm) (p : Program) (out : List Bool) :
    heads a p out=Fin.addCases (WarmPrepare.heads p out) (fun _ : Fin (ScannedClean.tapes a)=>0) := rfl

theorem restart_embed {n e s t : ℕ} (c : Configuration (n+e) s) (worker : Machine n t)
    (H : Fin n → ℕ) (A : Fin n → List Bool) (extra : Fin e → List Bool)
    (hh : c.heads=Fin.addCases H (fun _=>0)) (ht : c.tapes=Fin.addCases A extra) :
    Composition.restart c (TapeEmbedding.machine e worker).start=
      TapeEmbedding.config (fun _ : Fin e=>0) extra (⟨worker.start,H,A⟩ : Configuration n t) := by
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht

theorem warm_join {s t : ℕ} (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input)
    (C D b fp fq : ℕ) (fields : Fin 7 → List Bool) (out word : List Bool)
    (first : Machine (tapes a p) s) (initial : Configuration (tapes a p) s)
    (worker : Machine (WarmPrepare.tapes p) t) (source : Configuration (WarmPrepare.tapes p) t)
    (hp : DriverResult a p first fp initial row C D fields out)
    (he : source=⟨worker.start,WarmPrepare.heads p out,publicInput p row C D fields out⟩)
    (hq : WarmPrepared.Result p worker fq source D b out word fields) :
    WarmJoined a p (Composition.machine first (TapeEmbedding.machine (ScannedClean.tapes a) worker))
      (fp+1+fq) (fp+1+(8*D+40*b+74)) (Composition.leftConfig t initial) D (out++word) fields := by
  obtain ⟨extra,x,hx,xh,xt,xs,xd⟩:=hp
  obtain ⟨y,hy,ys,yh,yt,yw,yd,yl,yfields⟩:=hq
  let z:=TapeEmbedding.receipt (fun _ : Fin (ScannedClean.tapes a)=>0) extra y
  have hz:=TapeEmbedding.run_embed worker (fun _ : Fin (ScannedClean.tapes a)=>0) extra _ _ y hy
  have hc : Composition.restart x.final (TapeEmbedding.machine (ScannedClean.tapes a) worker).start=
      TapeEmbedding.config (fun _ : Fin (ScannedClean.tapes a)=>0) extra source := by
    rw [he]
    rw [heads_eq] at xh
    exact restart_embed x.final worker _ _ extra xh xt
  rw [←hc] at hz
  have hr:=Composition.run_join first (TapeEmbedding.machine (ScannedClean.tapes a) worker) _ _ _ x z hx hz
  refine ⟨y.final.tapes,extra,Composition.joinedReceipt x z,hr,?_,rfl,?_,⟨yt,yw,yd,yl,yfields⟩,xd⟩
  · change Fin.addCases y.final.heads (fun _ : Fin (ScannedClean.tapes a)=>0)=heads a p (out++word)
    rw [yh]
    rfl
  · change x.steps+1+y.steps ≤ fp+1+(8*D+40*b+74)
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
