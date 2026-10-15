import Proof.MachineModel.OrdinaryMatrixScoreLeftFields

/-! Literal score/id append in the enclosing assignment carrier. The record
output remains streaming while source and assignment cursors are retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRecordDock
open LocalBitMultitape SignedSortKey
open MatrixScoreWeight (zeros scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos apos opos : ℕ) : Fin 26 → ℕ :=
  Fin.addCases (m := 22) (n := 4) (motive := fun _ => ℕ) (MatrixScoreLeftFields.heads pos apos) ![0,0,opos,0]
def tapes (source assignment : List Bool) (d c cap w x m id template : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool) : Fin 26 → List Bool :=
  Fin.addCases (m := 22) (n := 4) (motive := fun _ => List Bool)
    (MatrixScoreLeftFields.tapes source assignment d c cap w x 0 work driver counter)
    ![frame (binary m id),frame (binary m template),out,zeros c]
def slots : Fin 6 → Fin 26 := ![22,23,2,19,24,25]
theorem injective : Function.Injective slots := by decide
def picked : Fin 26 → Option (Fin 6) :=
  ![none,none,some 2,none,none,none,none,none,none,none,none,none,none,none,none,none,
    none,none,none,some 3,none,none,some 0,some 1,some 4,some 5]
theorem pick_slots (i : Fin 26) : RecoveryFocus.pick slots i=picked i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot slots injective 0 | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2 | exact RecoveryFocus.pick_slot slots injective 3
    | exact RecoveryFocus.pick_slot slots injective 4 | exact RecoveryFocus.pick_slot slots injective 5
noncomputable def machine := RecoveryFocus.machine slots KeyPair.machine

theorem append_run (source assignment : List Bool) (pos apos d c cap s x m id template : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool) (score : ℤ)
    (hscore : work 0=scalar c (s+1) (shifted s score)) (hm : 2*m≤c) (hw : 2*(s+1)≤c) :
    ∃ actual,runFrom machine (4*(m+(s+1))+7)
      (RecoveryCalls.restarted machine (heads pos apos out.length)
        (tapes source assignment d c cap (s+1) x m id template work driver counter out))=some actual ∧
      actual.final.heads=heads pos apos (out++StablePartition.recordBits (encode s m score id)).length ∧
      actual.final.tapes=tapes source assignment d c cap (s+1) x m id template work driver counter
        (out++StablePartition.recordBits (encode s m score id)) ∧ actual.steps≤4*(m+(s+1))+7 := by
  let ambient := tapes source assignment d c cap (s+1) x m id template work driver counter out
  obtain ⟨base,hb,hf,hs⟩ := MatrixScoreRecord.encoded_run s m c id template score out hm hw
  have hi : RecoveryFocus.config slots (heads pos apos out.length) ambient
      (MatrixScoreRecord.cfg 0 m (s+1) c id template (shifted s score) out)=
      RecoveryCalls.restarted machine (heads pos apos out.length) ambient := by
    apply WilliamsSourceCrop.focus_same slots (RecoveryCalls.restarted machine (heads pos apos out.length) ambient)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> first | exact hscore | rfl
  obtain ⟨actual,hr,ha,has⟩ := RecoveryFocus.run_config slots injective KeyPair.machine
    (heads pos apos out.length) ambient _ _ base hb
  rw [hi] at hr
  refine ⟨actual,hr,?_,?_,has.trans_le hs⟩
  · rw [ha,hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_slots,picked,MatrixScoreRecord.cfg,KeyPair.config,
      heads,MatrixScoreLeftFields.heads,MatrixScoreFoldEntry.heads,Fin.addCases]
  · rw [ha,hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_slots,picked,MatrixScoreRecord.cfg,KeyPair.config,
      ambient,tapes,MatrixScoreLeftFields.tapes,MatrixScoreFoldEntry.tapes,Fin.addCases,hscore,zeros]

end NearCubicWires.RepairOrdinary.MatrixScoreRecordDock
