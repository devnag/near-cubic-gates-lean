import Proof.CaseAnalysis.RowsSupportPublishedBody
import Proof.CaseAnalysis.RowsCircuitWholeBudget

/-! The existing guarded composition joins the original cold parser to
the actual support-retaining body. Its paid bound includes the extra copies. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape RepairRepresentation ExtDecompositionBatch
open RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem guarded_step {t a b fp fq : ℕ} {p : Machine t a} {q : Machine t b}
    {H0 H1 H2 : Fin t → ℕ} {A0 A1 A2 : Fin t → List Bool}
    (hp : Step p fp H0 A0 H1 A1) (hq : Step q fq H1 A1 H2 A2)
    (test : (Fin t → Bool) → Bool)
    (yes : test (fun i=>readTapeBit (A1 i) (H1 i))=true) :
    Step (CloseoutRowsGateColdPair.machine p q test) (fp+1+fq+1) H0 A0 H2 A2 := by
  obtain ⟨first,fr,fh,ft,_fs⟩:=hp
  obtain ⟨last,lr,lh,lt,_ls⟩:=hq
  have next:runFrom q fq (RecoveryCalls.restarted q first.final.heads first.final.tapes)=some last:=by
    rw [fh,ft];exact lr
  have observed:test first.final.scanned=true:=by
    change test (fun i=>readTapeBit (first.final.tapes i) (first.final.heads i))=true
    rw [fh,ft];exact yes
  obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.accepted p q test fp fq H0 A0 first last fr next observed
  exact ⟨r,hr,rh.trans lh,rt.trans lt,rs⟩

theorem rejected_step {t a b fp : ℕ} {p : Machine t a} (q : Machine t b)
    {H0 H1 : Fin t → ℕ} {A0 A1 : Fin t → List Bool}
    (hp : Step p fp H0 A0 H1 A1) (test : (Fin t → Bool) → Bool)
    (no : test (fun i=>readTapeBit (A1 i) (H1 i))=false) :
    Step (CloseoutRowsGateColdPair.machine p q test) (fp+1) H0 A0 H1 A1 := by
  obtain ⟨first,fr,fh,ft,_fs⟩:=hp
  have observed:test first.final.scanned=false:=by
    change test (fun i=>readTapeBit (first.final.tapes i) (first.final.heads i))=false
    rw [fh,ft];exact no
  obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.rejected p q test fp H0 A0 first fr observed
  exact ⟨r,hr,rh.trans fh,rt.trans ft,rs⟩

def circuitBudget (C core N : ℕ):=2000*(N+2)*(C+core+1)

theorem body_bound (threshold : Bool) (C core retained D n wire L W : ℕ) (top : List Bool)
    (hheader : EquationHeaderAppend.budget retained+1 ≤ C) (htop : 2*top.length+1 ≤ C)
    (hc : 32*(D+n+wire+3) ≤ C) :
    bodyBudget threshold C core retained top D n wire L W ≤ n*(12*C+4*core+43)+40*C+220 := by
  have ha:=CloseoutRowsCircuitWholeBudget.arithmetic_bound threshold D n
  have hm:=CloseoutRowsCircuitWholeBudget.amount_bound threshold D n
  have md:=Nat.min_le_left (CloseoutRowsCircuitArithmeticDock.amount threshold D n) L
  have mw:=Nat.min_le_left wire W
  unfold bodyBudget tailBudget Dock.returnBudget budget CloseoutRowsCircuitPreparedRun.budget
    CloseoutRowsCircuitNativePrepare.budget CloseoutRowsCircuitNativePrefix.budget
    CloseoutRowsCircuitCountHeader.budget CloseoutRowsCircuitResourceRun.budget
    CloseoutRowsCircuitCaps.budget RawCompare.budget
  omega

theorem joined_bound (C core N n cold work : ℕ) (hn : n ≤ N+1)
    (hc : cold ≤ 14*C+40) (hb : work ≤ n*(12*C+4*core+43)+40*C+220) :
    cold+1+work+1 ≤ circuitBudget C core N := by
  have hm:=Nat.mul_le_mul_right (12*C+4*core+43) hn
  unfold circuitBudget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
