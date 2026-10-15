import Proof.MachineModel.OrdinaryMatrixScoreLeft
import Proof.MachineModel.OrdinaryMatrixScoreRecordDock

/-! Reusable literal left record body. The temporary threshold tapes are
physically erased before every assignment and the global output stays streaming. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreLeftRecord
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreRecordDock
open MatrixScoreWeight (zeros scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clearSlots : Fin 4 → Fin 26 := ![20,21,15,16]
theorem clear_injective : Function.Injective clearSlots := by decide
def clearPick : Fin 26 → Option (Fin 4) :=
  ![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 2,some 3,
    none,none,none,some 0,some 1,none,none,none,none]
theorem pick_clear (i : Fin 26) : RecoveryFocus.pick clearSlots i=clearPick i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 0
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 1
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 2
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 3
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def compute := TapeEmbedding.machine 4 MatrixScoreLeft.machine
noncomputable def first := Composition.machine clear compute
noncomputable def machine := Composition.machine first MatrixScoreRecordDock.machine
def budget (d p s c m : ℕ) := (2*c+4)+1+MatrixScoreLeft.budget d p s c+1+(4*(m+(s+1))+7)

theorem clear_run (source assignment : List Bool) (pos apos d c cap w x m id template : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (hcap : cap≤c+1) (hd : driver.length≤c) (hc : counter.length≤c) :
    ∃ actual,runFrom clear (2*c+4)
      (RecoveryCalls.restarted clear (heads pos apos out.length)
        (tapes source assignment d c cap w x m id template work driver counter out))=some actual ∧
      actual.final.heads=heads pos apos out.length ∧
      actual.final.tapes=tapes source assignment d c (c+1) w x m id template work (zeros c) (zeros c) out ∧
      actual.steps=2*c+4 := by
  have ready := RecoveryScratchErase.erase_ready c cap ![driver,counter] (by intro i; fin_cases i; exact hd; exact hc)
  rw [Nat.max_eq_right hcap] at ready
  obtain ⟨actual,hr,hh,ht,hs⟩ := HierarchyBinary.focused_run clearSlots clear_injective _ _ _ ready
    (heads pos apos out.length) (tapes source assignment d c cap w x m id template work driver counter out)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨actual,hr,hh,?_,hs⟩
  rw [ht]
  funext i
  fin_cases i <;> simp [install,pick_clear,clearPick,tapes,MatrixScoreLeftFields.tapes,
    MatrixScoreFoldEntry.tapes,Fin.addCases,zeros]

def padding (c : ℕ) : Fin 22 → ℕ := fun i => if i=20 ∨ i=21 then c else 0

theorem padded_tapes (source assignment : List Bool) (d c cap w x y : ℕ) (work : Fin 12 → List Bool)
    (driver counter : List Bool) :
    (fun i => ZeroPadding.pad (padding c i)
      (MatrixScoreLeftFields.tapes source assignment d c cap w x y work driver counter i))=
      MatrixScoreLeftFields.tapes source assignment d c cap w x y work
        (ZeroPadding.pad c driver) (ZeroPadding.pad c counter) := by
  funext i
  fin_cases i <;> simp [padding,MatrixScoreLeftFields.tapes,Fin.addCases]

theorem padded_zeros (c : ℕ) (hc : 2≤c) : ZeroPadding.pad c (zeros 2)=zeros c := by
  simp only [zeros,ZeroPadding.pad,List.length_replicate,← List.replicate_add]
  congr 1
  omega

theorem left_record_run (weights right : List ℤ) (pre suffix apre asuffix : List Bool)
    (p n s c cap m id template : ℕ) (theta : ℤ) (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (hlen : right.length=weights.length)
    (hf : ∀ z ∈ weights,z.natAbs<2^p) (htheta : theta.natAbs<2^p)
    (hw : p≤ s+1) (hc : 4*(s+1)+5≤c) (hm : 2*m≤c) (hcap : cap≤c+1)
    (hs : ∀ i,(work i).length≤c) (hdr : driver.length≤c) (hctr : counter.length≤c)
    (hp : MatrixScoreBatch.part true weights n+theta.natAbs<2^s)
    (hn : MatrixScoreBatch.part false weights n+theta.natAbs<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      finalWork 0=scalar c (s+1) (shifted s (theta-MatrixScoreBatch.linearForm weights n)) ∧
      ∃ actual,runFrom machine (budget weights.length p s c m)
        (RecoveryCalls.restarted machine (heads pre.length apre.length out.length)
          (tapes (pre++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++
              frame (MatrixScoreBatch.signMagnitude p theta)++suffix)
            (apre++frame (binary weights.length n)++asuffix) weights.length c cap (s+1) (2^s) m id template work driver counter out))=some actual ∧
        actual.final.heads=heads
          (pre.length+(MatrixScoreCanonical.fields p weights).length+(MatrixScoreCanonical.fields p right).length+2*p+3)
          (apre.length+2*weights.length)
          (out++StablePartition.recordBits (encode s m (theta-MatrixScoreBatch.linearForm weights n) id)).length ∧
        actual.final.tapes=tapes
          (pre++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++
            frame (MatrixScoreBatch.signMagnitude p theta)++suffix)
          (apre++frame (binary weights.length n)++asuffix) weights.length c (c+1) (s+1) (2^s) m id template finalWork
          (ZeroPadding.pad c [true,true]) (zeros c)
          (out++StablePartition.recordBits (encode s m (theta-MatrixScoreBatch.linearForm weights n) id)) ∧
        actual.steps≤budget weights.length p s c m := by
  let source := pre++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++
    frame (MatrixScoreBatch.signMagnitude p theta)++suffix
  let assignment := apre++frame (binary weights.length n)++asuffix
  let pos := pre.length+(MatrixScoreCanonical.fields p weights).length+(MatrixScoreCanonical.fields p right).length+2*p+3
  let apos := apre.length+2*weights.length
  obtain ⟨cleared,he,eh,et,es⟩ := clear_run source assignment pre.length apre.length weights.length c cap (s+1) (2^s) m id template
    work driver counter out hcap hdr hctr
  obtain ⟨finalWork,hws,hw0,base,hb,bh,bt,bs⟩ := MatrixScoreLeft.left_run weights right pre suffix apre asuffix
    p n s c (c+1) theta work hlen hf htheta hw hc (by omega) hs hp hn
  obtain ⟨padded,hpRun,hpf,hps,_⟩ := ZeroPadding.run_config MatrixScoreLeft.machine (padding c) _ _ base hb
  have px : padded.final.heads=MatrixScoreLeftFields.heads pos apos := by rw [hpf]; exact bh
  have pt : padded.final.tapes=MatrixScoreLeftFields.tapes source assignment weights.length c (c+1) (s+1) (2^s) 0 finalWork
      (ZeroPadding.pad c [true,true]) (zeros c) := by
    rw [hpf]
    change (fun i => ZeroPadding.pad (padding c i) (base.final.tapes i))=_
    rw [bt,padded_tapes,padded_zeros c (by omega)]
  have expandedRun := TapeEmbedding.run_embed MatrixScoreLeft.machine ![0,0,out.length,0]
    ![frame (binary m id),frame (binary m template),out,zeros c] _ _ padded hpRun
  let expanded := TapeEmbedding.receipt ![0,0,out.length,0]
    ![frame (binary m id),frame (binary m template),out,zeros c] padded
  have ci : TapeEmbedding.config ![0,0,out.length,0]
      ![frame (binary m id),frame (binary m template),out,zeros c]
      (ZeroPadding.config (padding c) (RecoveryCalls.restarted MatrixScoreLeft.machine
        (MatrixScoreLeftFields.heads pre.length apre.length)
        (MatrixScoreLeftFields.tapes source assignment weights.length c (c+1) (s+1) (2^s) 0 work [] [])))=
      Composition.restart cleared.final compute.start := by
    apply configuration_ext
    · rfl
    · exact eh.symm
    · rw [show (Composition.restart cleared.final compute.start).tapes=cleared.final.tapes by rfl,et]
      funext i
      fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,ZeroPadding.config,padding,tapes,
        MatrixScoreLeftFields.tapes,MatrixScoreFoldEntry.tapes,RecoveryCalls.restarted,ZeroPadding.pad,zeros]
  rw [ci] at expandedRun
  have firstRun := Composition.run_join clear compute _ _ _ cleared expanded he expandedRun
  have xh : expanded.final.heads=heads pos apos out.length := by
    funext i; fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,px,
      heads,MatrixScoreLeftFields.heads,MatrixScoreFoldEntry.heads]
  have xt : expanded.final.tapes=tapes source assignment weights.length c (c+1) (s+1) (2^s) m id template finalWork
      (ZeroPadding.pad c [true,true]) (zeros c) out := by
    funext i; fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,pt,tapes]
  obtain ⟨appended,ha,ah,atapes,as⟩ := MatrixScoreRecordDock.append_run source assignment pos apos weights.length c (c+1)
    s (2^s) m id template finalWork (ZeroPadding.pad c [true,true]) (zeros c) out
    (theta-MatrixScoreBatch.linearForm weights n) hw0 hm (by omega)
  have ai : Composition.restart (Composition.joinedReceipt cleared expanded).final MatrixScoreRecordDock.machine.start=
      RecoveryCalls.restarted MatrixScoreRecordDock.machine (heads pos apos out.length)
        (tapes source assignment weights.length c (c+1) (s+1) (2^s) m id template finalWork
          (ZeroPadding.pad c [true,true]) (zeros c) out) := by
    apply configuration_ext
    · rfl
    · exact xh
    · exact xt
  rw [← ai] at ha
  have joined := Composition.run_join first MatrixScoreRecordDock.machine _ _ _
    (Composition.joinedReceipt cleared expanded) appended firstRun ha
  refine ⟨finalWork,hws,hw0,Composition.joinedReceipt (Composition.joinedReceipt cleared expanded) appended,
    joined,ah,atapes,?_⟩
  change (cleared.steps+1+padded.steps)+1+appended.steps≤_
  rw [es,hps]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreLeftRecord
