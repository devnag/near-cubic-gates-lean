import Proof.SourceAssembly.SourceSymmetricHeader

/- Consume the actual selected-count tape produced by the queried SYM scan.
Its bottom streams retain their append cursors while TOP/header are produced. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricHeaderQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots (i : Fin 26) : Fin 166:=if _h3:i=3 then 140 else if h:i.val<3 then ⟨141+i.val,by omega⟩ else ⟨140+i.val,by omega⟩
theorem slots_inj : Function.Injective slots:=by decide
def fresh (i : Fin 26) (_hi : i≠3) : Fin 25:=⟨if i.val<3 then i.val else i.val-1,by split_ifs <;>have hv:=i.isLt <;>omega⟩
theorem slots_fresh (i : Fin 26) (hi : i≠3) : slots i=(fresh i hi).natAdd 141 := by
  apply Fin.ext
  by_cases h:i.val<3
  · simp [slots,hi,fresh,h]
  · simp [slots,hi,fresh,h]
    have hn:i.val≠3:=by intro he;exact hi (Fin.ext he)
    omega

def first:=TapeEmbedding.machine 25 SourceAssemblySymmetricQuery.machine
def last:=RecoveryFocus.machine slots SourceAssemblySymmetricHeader.machine
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 166→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (SourceAssemblySymmetricQuery.input a r ci C) (fun _ : Fin 25=>[])
def count (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=
  (SourceAssemblySymmetricScan.selected (SourceAssemblySymmetricQuery.bitmap a r ci) r.arity).length
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) : Fin 166→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (SourceAssemblySymmetricQuery.finalHeads a r ci) (fun _ : Fin 25=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=dockH slots (beforeHeads a r ci) (fun _=>0)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  SourceAssemblySymmetricQuery.budget a r ci C+1+
    SourceAssemblySymmetricHeader.budget (count a r ci)

theorem selected_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 26) :
    beforeHeads a r ci (slots i)=SourceAssemblySymmetricHeader.heads i := by
  by_cases hi:i=3
  · subst i
    change beforeHeads a r ci ((140 : Fin 141).castAdd 25)=1
    rw [beforeHeads,Fin.addCases_left]
    change dockH SourceAssemblySymmetricQuery.slots _ _
      (SourceAssemblySymmetricQuery.slots 7)=1
    rw [dockH_slot _ SourceAssemblySymmetricQuery.slots_inj]
    rfl
  · rw [slots_fresh i hi]
    simp only [beforeHeads,Fin.addCases_right,SourceAssemblySymmetricHeader.heads,hi,if_false]

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci) A ∧
      A 138=SourceAssemblySymmetricScan.outputs r.arity (SourceAssemblySymmetricQuery.bitmap a r ci) r.arity 0 ∧
      A 139=SourceAssemblySymmetricScan.outputs r.arity (SourceAssemblySymmetricQuery.bitmap a r ci) r.arity 1 ∧
      A 140=CompareMachine.word (count a r ci) ∧
      A 142=frame (SourceAssemblySymmetricTop.table (count a r ci)) ∧
      A 161=natWord (count a r ci) ∧A 101=List.replicate (Capacity.value r.arity) true := by
  obtain ⟨A,ha,h138,h139,h140,_h13,_h3,_h4,h101⟩:=SourceAssemblySymmetricQuery.run a r ci C hc
  let bank : Fin 166→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 25=>[])
  have stepA : Step first (SourceAssemblySymmetricQuery.budget a r ci C)
      (fun _=>0) (input a r ci C) (beforeHeads a r ci) bank :=
    (ha.embed (fun _ : Fin 25=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  obtain ⟨B,hb,top,header,_framed,driver⟩:=SourceAssemblySymmetricHeader.run (count a r ci)
  have selected : ∀ i,bank (slots i)=SourceAssemblySymmetricHeader.input (count a r ci) i := by
    intro i
    by_cases hi:i=3
    · subst i;exact h140
    · rw [slots_fresh i hi]
      simp only [bank,Fin.addCases_right,SourceAssemblySymmetricHeader.input,hi,if_false]
  have lastStep:=hb.dock slots slots_inj (beforeHeads a r ci) bank (selected_heads a r ci) selected
  refine ⟨install slots bank B,stepA.seq lastStep,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank B 138 (by decide)).trans h138
  · exact (install_other slots bank B 139 (by decide)).trans h139
  · exact (install_slot slots slots_inj bank B 3).trans driver
  · exact (install_slot slots slots_inj bank B 1).trans top
  · exact (install_slot slots slots_inj bank B 21).trans header
  · exact (install_other slots bank B 101 (by decide)).trans h101

end
end SourceAssemblySymmetricHeaderQuery
