import Proof.CaseAnalysis.RowsCircuitCapCompare

/-! The two original circuit resource guards execute on the produced
small counters and retained policy caps. One final instruction writes the
circuit verdict; the measured-counter bound pays all private scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps
open LocalBitMultitape RecoveryRootRound RecoveryExecution RepairSource.CloseoutSchedule CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def descriptionSlots (threshold : Bool) : Fin 6 → Fin 1703 :=
  ![if threshold then 653 else 649,1699,656,657,658,659]
def wireSlots : Fin 6 → Fin 1703 := ![660,1698,661,662,663,664]
def flagSlots : Fin 3 → Fin 1703 := ![658,663,1700]
noncomputable def description (threshold : Bool):=RecoveryFocus.machine (descriptionSlots threshold) RawCompare.machine
noncomputable def wires:=RecoveryFocus.machine wireSlots RawCompare.machine

def flagWorker : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then
    some ⟨1,![none,none,some (bits 0 && bits 1)],fun _=>.stay⟩ else none
noncomputable def finish:=RecoveryFocus.machine flagSlots flagWorker
noncomputable def first (threshold : Bool):=Composition.machine (description threshold) wires
noncomputable def machine (threshold : Bool):=Composition.machine (first threshold) finish
def budget (desc wire L W : ℕ):=RawCompare.budget desc L+1+RawCompare.budget wire W+2

theorem flag_run (left right old : List Bool) : ClockJoin.ReadyRun flagWorker 1
    ![left,right,old] ![left,right,writeTapeBit old 0 (readTapeBit left 0 && readTapeBit right 0)]:=by
  let final:Configuration 3 2:=⟨1,fun _=>0,
    ![left,right,writeTapeBit old 0 (readTapeBit left 0 && readTapeBit right 0)]⟩
  have hs:step flagWorker (initialConfiguration flagWorker ![left,right,old])=some final:=by
    apply congrArg some;apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

private theorem together {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H : Fin t → ℕ) (A B D : Fin t → List Bool) (hp : ReadyAt p fp H A B) (hq : ReadyAt q fq H B D) :
    ReadyAt (Composition.machine p q) (fp+1+fq) H A D:=by
  obtain ⟨r,hr,rt,rh,rs⟩:=hp
  obtain ⟨s,hs,st,sh,ss⟩:=hq
  have he:Composition.restart r.final q.start=RecoveryCalls.restarted q H B:=configuration_ext rfl rh rt
  rw [←he] at hs
  refine ⟨Composition.joinedReceipt r s,Composition.run_join p q _ _ _ r s hr hs,st,sh,?_⟩
  change r.steps+1+s.steps ≤ fp+1+fq
  omega

theorem caps_run (threshold : Bool) (C desc wire L W : ℕ) (H : Fin 1703 → ℕ)
    (A : Fin 1703 → List Bool) (hc : 4*desc+4*wire+34 ≤ C)
    (dh : ∀ i,H (descriptionSlots threshold i)=0) (wh : ∀ i,H (wireSlots i)=0) (fh : H 1700=0)
    (dt : ∀ i,A (descriptionSlots threshold i)=CloseoutRowsCircuitCapCompare.input C desc L i)
    (wt : ∀ i,A (wireSlots i)=CloseoutRowsCircuitCapCompare.input C wire W i) : ∃ out,
    ReadyAt (machine threshold) (budget desc wire L W) H A out ∧
      (readTapeBit (out 1700) 0=true ↔ desc ≤ L ∧ wire ≤ W) ∧
      (∀ i,H i=0 → (A i).length ≤ C → (out i).length ≤ C) ∧
      (∀ i,(∀ j,descriptionSlots threshold j≠i) → (∀ j,wireSlots j≠i) →
        (∀ j,flagSlots j≠i) → out i=A i):=by
  have di:Function.Injective (descriptionSlots threshold):=by cases threshold <;> decide
  have wi:Function.Injective wireSlots:=by decide
  have disjoint:∀ i j,descriptionSlots threshold j≠wireSlots i:=by
    cases threshold <;> decide
  obtain ⟨d,_,_,dv,_⟩:=CloseoutRowsCircuitCapCompare.compare_run C desc L (by omega)
  obtain ⟨p,pr,ph,pt,ps⟩:=d.focus_at (descriptionSlots threshold) di H A dt dh
  let B:=install (descriptionSlots threshold) A (CloseoutRowsCircuitCapCompare.output C desc L)
  have dready:ReadyAt (description threshold) (RawCompare.budget desc L) H A B:=⟨p,pr,pt,ph,ps⟩
  have bw:∀ i,B (wireSlots i)=CloseoutRowsCircuitCapCompare.input C wire W i:=by
    intro i;exact (install_other _ _ _ _ (disjoint i)).trans (wt i)
  obtain ⟨w,_,_,wv,_⟩:=CloseoutRowsCircuitCapCompare.compare_run C wire W (by omega)
  obtain ⟨q,qr,qh,qt,qs⟩:=w.focus_at wireSlots wi H B bw wh
  let D:=install wireSlots B (CloseoutRowsCircuitCapCompare.output C wire W)
  have wready:ReadyAt wires (RawCompare.budget wire W) H B D:=⟨q,qr,qt,qh,qs⟩
  have descValue:readTapeBit (D 658) 0=true ↔ desc ≤ L:=by
    rw [show D=install wireSlots B _ by rfl,install_other _ _ _ _ (by decide)]
    change readTapeBit (B (descriptionSlots threshold 4)) 0=true ↔ _
    rw [show B=install (descriptionSlots threshold) A _ by rfl,install_slot _ di]
    exact dv
  have wireValue:readTapeBit (D 663) 0=true ↔ wire ≤ W:=by
    change readTapeBit (D (wireSlots 4)) 0=true ↔ _
    rw [show D=install wireSlots B _ by rfl,install_slot _ wi]
    exact wv
  obtain ⟨s,sr,sh,st,ss⟩:=(flag_run (D 658) (D 663) (D 1700)).focus_at flagSlots (by decide) H D
    (by intro i;fin_cases i <;> rfl) (by
      intro i;fin_cases i
      · exact dh 4
      · exact wh 4
      · exact fh)
  let result:=install flagSlots D
    ![D 658,D 663,writeTapeBit (D 1700) 0 (readTapeBit (D 658) 0 && readTapeBit (D 663) 0)]
  have ready:ReadyAt finish 1 H D result:=⟨s,sr,st,sh,ss⟩
  have all:=together (first threshold) finish _ _ H _ _ _
    (together (description threshold) wires _ _ H _ _ _ dready wready) ready
  have time:(RawCompare.budget desc L+1+RawCompare.budget wire W)+1+1=budget desc wire L W:=by
    unfold budget;omega
  rw [time] at all
  refine ⟨result,all,?_,?_,?_⟩
  · change readTapeBit (result (flagSlots 2)) 0=true ↔ _
    rw [show result=install flagSlots D _ by rfl,install_slot _ (by decide : Function.Injective flagSlots)]
    change readTapeBit (writeTapeBit (D 1700) 0 _) 0=true ↔ _
    have read_write (bits : List Bool) (b : Bool) : readTapeBit (writeTapeBit bits 0 b) 0=b:=by
      cases bits <;> rfl
    rw [read_write,Bool.and_eq_true,descValue,wireValue]
  · intro i hi ha
    obtain ⟨r,hr,rt,_rh,rs⟩:=all
    rw [←rt]
    apply CloseoutRowsProjectionReset.scratch_support (machine threshold) _ C _ r hr i hi ha
    have hb:=CloseoutRowsCircuitCapCompare.budget_bound desc L
    have hw:=CloseoutRowsCircuitCapCompare.budget_bound wire W
    unfold budget at rs
    omega
  · intro i hdi hwi hfi
    rw [show result=install flagSlots D _ by rfl,install_other _ _ _ _ hfi,
      show D=install wireSlots B _ by rfl,install_other _ _ _ _ hwi,
      show B=install (descriptionSlots threshold) A _ by rfl,install_other _ _ _ _ hdi]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps
