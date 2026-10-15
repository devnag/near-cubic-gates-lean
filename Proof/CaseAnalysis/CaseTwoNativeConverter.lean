import Proof.CaseAnalysis.CaseTwoCanonicalWalk
import Proof.CaseAnalysis.CaseTwoNativeHeaderJoin
import Proof.Assembly.AppendOutputFrame

/-! The same canonical description is converted to the original native
descriptor. Its header uses the in-walk count, and both stream copies and
the final descriptor frame are physically executed and charged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.NativeConverter
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (n : ℕ) (j : Fin 38):=if j=0 then List.replicate n true else []
def input {n : ℕ} (C bound : ℕ) (c : BooleanCircuit n) : Fin 70→List Bool:=
  Fin.addCases (m:=32) (n:=38) (CanonicalWalk.measuredInput C bound c) (extra n)
def headerSlots (j : Fin 41) : Fin 70:=
  if j=0 then 27 else if j=1 then 30 else if j=2 then 32 else if j=3 then 29 else ⟨j.val+29,by omega⟩
theorem header_injective : Function.Injective headerSlots:=by decide
noncomputable def first:=TapeEmbedding.machine 38 CanonicalWalk.measured
noncomputable def last:=RecoveryFocus.machine headerSlots NativeHeaderJoin.machine
noncomputable def machine:=Composition.machine first last
def budget {n : ℕ} (C : ℕ) (c : BooleanCircuit n):=
  (2*CanonicalWalk.budget C c+2)+1+NativeHeaderJoin.budget n c.size (CanonicalWalk.body c).length

theorem extra_fresh {s : ℕ} (n : ℕ) (r : ExecutionReceipt 32 s) (i : Fin 70)
    (hi : 32 ≤ i.val) (hn : i≠32) :
    (TapeEmbedding.receipt (fun _ : Fin 38=>0) (extra n) r).final.tapes i=[]:=by
  let j : Fin 38:=⟨i.val-32,by omega⟩
  have he : j.natAdd 32=i:=by apply Fin.ext;dsimp [j];omega
  rw [←he,TapeEmbedding.receipt_tapes_new]
  unfold extra
  apply if_neg
  intro h
  have hv:=congrArg Fin.val h
  have hiveq : i.val=32:=by dsimp [j] at hv;omega
  exact hn (Fin.ext hiveq)

theorem convert_run {n bound : ℕ} (C : ℕ) (c : BooleanCircuit n) (hc : c.size≤bound)
    (h : Traversal.Fits C (boundedCircuitFieldLimit n bound) (canonicalBoundedCircuitDescription bound c).length bound) :
    ∃ r,run machine (budget C c) (input C bound c)=some r ∧ r.steps≤budget C c ∧
      r.final.tapes 49=PCPPNative.descriptor c ∧ r.final.heads 49=(PCPPNative.descriptor c).length := by
  obtain ⟨a,ar,asteps,ah,ab,ac,al,_asource⟩:=CanonicalWalk.measured_run C c hc h
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 38=>0) (extra n) a
  have firstRun:=TapeEmbedding.run_embed CanonicalWalk.measured (fun _ : Fin 38=>0) (extra n) _ _ a ar
  have allHeads : ∀ i,lifted.final.heads i=0:=by
    intro i
    refine Fin.addCases (m:=32) (n:=38) (fun j=>?_) (fun j=>?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ a j).trans (ah j)
    · exact TapeEmbedding.receipt_heads_new _ _ a j
  have headerInput (j : Fin 41) : lifted.final.tapes (headerSlots j)=NativeHeaderJoin.input n c.size (CanonicalWalk.body c) j:=by
    by_cases h0 : j=0
    · subst j;exact (TapeEmbedding.receipt_tapes_old _ _ a 27).trans ab
    by_cases h1 : j=1
    · subst j;exact (TapeEmbedding.receipt_tapes_old _ _ a 30).trans al
    by_cases h2 : j=2
    · subst j;exact TapeEmbedding.receipt_tapes_new _ _ a 0
    by_cases h3 : j=3
    · subst j;exact (TapeEmbedding.receipt_tapes_old _ _ a 29).trans ac
    have hj : 4≤j.val:=by
      have h0v : j.val≠0:=fun x=>h0 (Fin.ext x)
      have h1v : j.val≠1:=fun x=>h1 (Fin.ext x)
      have h2v : j.val≠2:=fun x=>h2 (Fin.ext x)
      have h3v : j.val≠3:=fun x=>h3 (Fin.ext x)
      omega
    have hi : 32≤(headerSlots j).val:=by simp only [headerSlots,h0,h1,h2,h3,if_false];omega
    have hn : headerSlots j≠32:=by
      intro he
      have hv:=congrArg Fin.val he
      simp only [headerSlots,h0,h1,h2,h3,if_false] at hv
      omega
    rw [extra_fresh n a (headerSlots j) hi hn]
    simp only [NativeHeaderJoin.input,h0,h1,h2,h3,if_false]
  obtain ⟨base,br,bs,bt,bh⟩:=NativeHeaderJoin.join_run n c.size (CanonicalWalk.body c)
  obtain ⟨b,hr,_bf,bst,bheads,btapes,_keep⟩:=RecoveryFocus.dock headerSlots header_injective NativeHeaderJoin.machine _
    lifted.final.heads lifted.final.tapes (initialConfiguration NativeHeaderJoin.machine (NativeHeaderJoin.input n c.size (CanonicalWalk.body c)))
    (fun j=>allHeads _) headerInput base br
  have whole:=Composition.run_join first last _ _ _ lifted b firstRun hr
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 38=>0) (extra n)
      (initialConfiguration CanonicalWalk.measured (CanonicalWalk.measuredInput C bound c)))=
      initialConfiguration machine (input C bound c):=by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=32) (n:=38) (fun j=>?_) (fun j=>?_) i <;>
        simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hi] at whole
  have he : natWord n++natWord c.size++CanonicalWalk.body c=PCPPNative.descriptor c:=by
    rw [PCPPNative.descriptor_eq]
    simp only [CanonicalWalk.body,BooleanCircuit.size,List.append_assoc]
  refine ⟨Composition.joinedReceipt lifted b,whole,?_,?_,?_⟩
  · change a.steps+1+b.steps≤budget C c
    rw [bst]
    unfold budget
    omega
  · change b.final.tapes (headerSlots 20)=_
    exact (btapes 20).trans (bt.trans he)
  · change b.final.heads (headerSlots 20)=_
    exact (bheads 20).trans (bh.trans (congrArg List.length he))

theorem forward : CursorRestore.NoLeft machine 49:=
  CursorRestore.composition_forward first last 49
    (EquationRowRaw.embedded_extra_forward CanonicalWalk.measured (17 : Fin 38))
    (CursorRestore.focus_forward headerSlots header_injective NativeHeaderJoin.machine 20 NativeHeaderJoin.forward)

noncomputable def framed:=AppendOutputFrame.machine machine 49
def framedInput {n : ℕ} (C bound : ℕ) (c : BooleanCircuit n):=AppendOutputFrame.input (input C bound c)
def framedBudget {n : ℕ} (C : ℕ) (c : BooleanCircuit n):=2*budget C c+4*(PCPPNative.descriptor c).length+7

theorem framed_run {n bound : ℕ} (C : ℕ) (c : BooleanCircuit n) (hc : c.size≤bound)
    (h : Traversal.Fits C (boundedCircuitFieldLimit n bound) (canonicalBoundedCircuitDescription bound c).length bound) :
    ∃ r,run framed (framedBudget C c) (framedInput C bound c)=some r ∧
      r.steps≤framedBudget C c ∧ r.final.tapes 72=frame (PCPPNative.descriptor c) ∧ (∀ i,r.final.heads i=0) := by
  obtain ⟨base,br,bs,bt,bh⟩:=convert_run C c hc h
  obtain ⟨r,rr,rt,rh,rs⟩:=AppendOutputFrame.frame_run machine 49 forward _ _ base br (PCPPNative.descriptor c) bt bh
  have hf : 2*base.steps+4*(PCPPNative.descriptor c).length+7≤framedBudget C c:=by unfold framedBudget;omega
  have more:=run_moreFuel framed _ (framedBudget C c-(2*base.steps+4*(PCPPNative.descriptor c).length+7)) _ r rr
  rw [Nat.add_sub_of_le hf] at more
  exact ⟨r,more,rs.trans hf,rt,rh⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.NativeConverter
