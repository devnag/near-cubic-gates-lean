import Proof.CaseAnalysis.RowsBankPacket

/-! One actual packet load, head positioning, complete polynomial call and
native clear compose into the reusable enclosing bank body. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketPolynomial
open LocalBitMultitape CloseoutRowsPreparationBounds CloseoutRowsBankPacket
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def data {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  (CloseoutRowsPolynomial.input gs p F Q w C rows out).tapes
noncomputable def native := Composition.machine (CloseoutRowsBankClear.position true) CloseoutRowsBankPolynomial.machine
def nativeBudget (Q C : ℕ) := 2+CloseoutRowsBankPolynomial.budget Q C

theorem data_fields {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    data gs p F Q w C rows out 31=out ∧
      data gs p F Q w C rows out 104=List.replicate C true ∧
      data gs p F Q w C rows out 105=List.replicate (C+1) false := by
  refine ⟨?_,rfl,rfl⟩
  exact (CloseoutRowsPolynomial.output_fields gs p F w 0 C rows out).1

theorem data_bound {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length≤2^w)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∀ i,i≠31 → i≠105 →
      (data gs p F Q w (capacity n p F w gs.length Q) rows out i).length≤capacity n p F w gs.length Q := by
  exact CloseoutRowsBankCapacity.loop_bound CloseoutRowsPolynomial.body gs 0 p F Q w 0 rows out
    hl hw (Nat.zero_le _) hF

theorem native_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q≤p) (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=capacity (l+r) p F w gs.length Q
    let result:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom native (nativeBudget Q C)
      ⟨native.start,CloseoutRowsBankClear.zeroHeads out,padded C (data gs p F Q w C rows out)⟩=some actual ∧
      actual.final.heads=CloseoutRowsBankClear.zeroHeads result ∧
      actual.final.tapes=CloseoutRowsBankClear.blank C result := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  let result:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
  obtain ⟨a,ha,af,_⟩:=CloseoutRowsBankClear.position_run true out (padded C (data gs p F Q w C rows out))
  obtain ⟨b,hb,bh,bo,bt,_⟩:=CloseoutRowsBankPolynomial.polynomial_run gs p F Q w rows out hl hM hw hQp hp hF
  have he : Composition.restart a.final CloseoutRowsBankPolynomial.machine.start=
      CloseoutRowsBankPolynomial.entry gs p F Q w C rows out := by
    rw [af]
    apply configuration_ext
    · rfl
    · exact (CloseoutRowsBankCapacity.loop_heads CloseoutRowsPolynomial.body gs 0 p F Q w 0 C rows out).symm
    · rfl
  rw [←he] at hb
  have hwhole:=Composition.run_join (CloseoutRowsBankClear.position true) CloseoutRowsBankPolynomial.machine _ _ _ a b ha hb
  have ht:=CloseoutRowsBankPorts.erased_store C result b.final.tapes bo bt
  exact ⟨Composition.joinedReceipt a b,hwhole,bh,ht⟩

noncomputable def last := TapeEmbedding.machine 1 native
noncomputable def machine := Composition.machine CloseoutRowsBankPacket.machine last
noncomputable def budget {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsBankPacket.budget (data gs p F Q w C rows out)+1+nativeBudget Q C

theorem packet_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w : ℕ) (rows : List (List Bool)) (out pre tail : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q≤p) (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=capacity (l+r) p F w gs.length Q
    let packet:=word (data gs p F Q w C rows out)
    let result:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom machine (budget gs p F Q w C rows out)
      ⟨machine.start,heads out pre.length,tapes C out (pre++packet++tail)⟩=some actual ∧
      actual.final.heads=heads result (pre.length+packet.length) ∧
      actual.final.tapes=tapes C result (pre++packet++tail) ∧
      actual.steps≤CloseoutRowsBankPolynomial.budget Q C+110*(3*C+3)+3 := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  let inputData:=data gs p F Q w C rows out
  let packet:=word inputData
  let result:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
  have df:=data_fields gs p F Q w C rows out
  have db:=data_bound gs p F Q w rows out hl hw.le hF
  obtain ⟨a,ha,ah,atape,_⟩:=load_run C inputData out pre tail df.1 df.2.1 df.2.2 db
  obtain ⟨b,hb,bh,bt⟩:=native_run gs p F Q w rows out hl hM hw hQp hp hF
  let e:=TapeEmbedding.receipt (fun _ : Fin 1=>pre.length+packet.length) (fun _=>pre++packet++tail) b
  have he:=TapeEmbedding.run_embed native
    (fun _ : Fin 1=>pre.length+packet.length) (fun _=>pre++packet++tail) _ _ b hb
  have ef : e.final=TapeEmbedding.config (fun _ : Fin 1=>pre.length+packet.length)
      (fun _=>pre++packet++tail) b.final := rfl
  have eh : TapeEmbedding.config (fun _ : Fin 1=>pre.length+packet.length)
      (fun _=>pre++packet++tail)
      (⟨native.start,CloseoutRowsBankClear.zeroHeads out,padded C inputData⟩ : Configuration 113 _)=
        Composition.restart a.final last.start := by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact atape.symm
  rw [eh] at he
  have whole:=Composition.run_join CloseoutRowsBankPacket.machine last _ _ _ a e ha he
  refine ⟨Composition.joinedReceipt a e,whole,?_,?_,?_⟩
  · change e.final.heads=_
    rw [ef]
    change extend b.final.heads (pre.length+packet.length)=_
    rw [bh]
    rfl
  · change e.final.tapes=_
    rw [ef]
    change extend b.final.tapes (pre++packet++tail)=_
    rw [bt]
    rfl
  · have hs:=runFrom_steps_le machine _ _ _ whole
    have hpkt:=CloseoutRowsBankPacket.budget_bound C inputData db
    unfold nativeBudget at hs
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketPolynomial
