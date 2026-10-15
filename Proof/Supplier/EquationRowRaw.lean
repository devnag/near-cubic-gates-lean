import Proof.Supplier.EquationRowPrepare
import Proof.Supplier.EquationRowCutsRequest

/-! Whole original-row to literal matrix-request byte production. Every
header, loop driver, scratch buffer and two-cut output is physically made. -/
namespace NearCubicWires.RepairOrdinary.EquationRowRaw
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 22 → Fin 126 := ![1,111,112,113,114,115,116,117,118,119,120,121,122,123,110,60,125,34,38,33,124,40]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def last := RecoveryFocus.machine slots EquationRowCuts.machine
noncomputable def machine := Composition.machine EquationRowPrepare.machine last
def pre (r : EquationRow.Input) := EquationHeaderRead.header r.d r.p r.cuts.length++[r.odd]
def source (r : EquationRow.Input) := EquationHeaderRead.word r.d r.p r.cuts.length
  (r.odd::EquationRowCuts.stream r.p r.cuts)
def input (r : EquationRow.Input) := EquationRowPrepare.input r.d r.p r.cuts.length r.odd
  (EquationRowCuts.stream r.p r.cuts)
/-- The output header: the three counts, then the φ part of the identity instance
(`natWord d` and the identity columns). -/
def outHeader (r : EquationRow.Input) :=
  EquationHeaderRead.header r.d (r.p+1) (2*r.cuts.length)++EquationRowPrepare.phiHeader r.d
def budget (r : EquationRow.Input) :=
  EquationRowPrepare.budget r.d r.p r.cuts.length r.odd (EquationRowCuts.stream r.p r.cuts)+1+
    EquationRowCuts.budget r.cuts.length (EquationRowCuts.rowCapacity r)

theorem source_eq (r : EquationRow.Input) :
    source r=pre r++EquationRowCuts.stream r.p r.cuts++[] := by
  simp [source,pre,EquationHeaderRead.word,List.append_assoc]
/-- The identity columns written by the producer are the header's columns of `φ = id`. -/
theorem identity_columns (d : ℕ) : EquationIdentityColumns.word d=
    MatrixScorePhi.columnsWord d ((List.range d).map (fun j => 2^j)) := by
  simp [EquationIdentityColumns.word,MatrixScorePhi.columnsWord,List.flatMap_map]

theorem header_eq (r : EquationRow.Input) : outHeader r=MatrixScoreBatch.header (EquationRow.request r) := by
  simp only [outHeader,EquationRowPrepare.phiHeader,EquationHeaderRead.header,MatrixScoreBatch.header,
    Request.Gates,EquationRow.request,EquationRow.doubled_length,Request.cols,identity_columns,
    List.append_assoc]

theorem raw_run (r : EquationRow.Input) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 0=frame (source r) ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 110=MatrixScoreBatch.word (EquationRow.request r) ∧
    actual.final.heads 110=(MatrixScoreBatch.word (EquationRow.request r)).length ∧
    actual.steps ≤ budget r := by
  obtain ⟨prepared,hp,pt0,ph0,pt1,ph1,ptOut,phOut,fields,fresh,ps⟩ :=
    EquationRowPrepare.prepare_run r.d r.p r.cuts.length r.odd (EquationRowCuts.stream r.p r.cuts)
  obtain ⟨body,hb,bf,bs⟩ := EquationRowCuts.request_run (pre r) [] (outHeader r) r
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes
      (EquationRowCuts.cfg 0 (pre r++EquationRowCuts.stream r.p r.cuts++[]) (outHeader r)
        (pre r).length (EquationRowCuts.rowCapacity r) (EquationRowCuts.rowWeightCount r)
        r.p r.odd r.cuts.length 1)=Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · change prepared.final.heads 1=(pre r).length
        simpa only [pre,List.length_append,List.length_singleton] using ph1
      · exact (fresh 0).2
      · exact (fresh 1).2
      · exact (fresh 2).2
      · exact (fresh 3).2
      · exact (fresh 4).2
      · exact (fresh 5).2
      · exact (fresh 6).2
      · exact (fresh 7).2
      · exact (fresh 8).2
      · exact (fresh 9).2
      · exact (fresh 10).2
      · exact (fresh 11).2
      · exact (fresh 12).2
      · exact phOut
      · exact (fields 30 (by decide)).2
      · exact (fresh 14).2
      · exact (fields 4 (by decide)).2
      · exact (fields 8 (by decide)).2
      · exact (fields 3 (by decide)).2
      · exact (fresh 13).2
      · exact (fields 10 (by decide)).2
    · intro j; fin_cases j
      · exact pt1.trans (source_eq r)
      · exact (fresh 0).1
      · exact (fresh 1).1
      · exact (fresh 2).1
      · exact (fresh 3).1
      · exact (fresh 4).1
      · exact (fresh 5).1
      · exact (fresh 6).1
      · exact (fresh 7).1
      · exact (fresh 8).1
      · exact (fresh 9).1
      · exact (fresh 10).1
      · exact (fresh 11).1
      · exact (fresh 12).1
      · exact ptOut
      · have h := (fields 30 (by decide)).1
        change prepared.final.tapes 60=List.replicate ((2*r.d+1)*(r.p+1)*128) true at h
        change prepared.final.tapes 60=List.replicate (EquationRowCuts.rowCapacity r) true
        simpa only [EquationRowCuts.rowCapacity,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
      · exact (fresh 14).1
      · exact (fields 4 (by decide)).1
      · exact (fields 8 (by decide)).1
      · exact (fields 3 (by decide)).1
      · exact (fresh 13).1
      · exact (fields 10 (by decide)).1
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective EquationRowCuts.machine
    prepared.final.heads prepared.final.tapes _ _ body hb
  rw [hi] at hf
  have joined := Composition.run_join EquationRowPrepare.machine last _ _ _ prepared focused hp hf
  have zero : RecoveryFocus.pick slots 0=none := by decide
  have pick : RecoveryFocus.pick slots (slots 14)=some 14 := RecoveryFocus.pick_slot slots slots_injective 14
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=frame (source r)
    rw [ff]
    simp only [RecoveryFocus.config,zero]
    exact pt0
  · change focused.final.heads 0=0
    rw [ff]
    simpa only [RecoveryFocus.config,zero] using ph0
  · change focused.final.tapes (slots 14)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick,bf]
    change outHeader r++(EquationRow.request r).cuts.flatMap (cutWord (EquationRow.request r).p)=_
    rw [header_eq]
    rfl
  · change focused.final.heads (slots 14)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick,bf]
    change (outHeader r++(EquationRow.request r).cuts.flatMap (cutWord (EquationRow.request r).p)).length=_
    rw [header_eq]
    rfl
  · change prepared.steps+1+focused.steps ≤ _
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationRowRaw
