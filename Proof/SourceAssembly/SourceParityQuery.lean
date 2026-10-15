import Proof.SourceAssembly.SourceParityPrep

/- Actual queried clause -> actual support bitmaps and paid SYM writer inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyParityQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots (i : Fin 47) : Fin 137:=if i=0 then 13 else ⟨90+i.val,by omega⟩
theorem slots_inj : Function.Injective slots:=by decide
def first:=TapeEmbedding.machine 46 SourceAssemblyPairSupport.machine
def last:=RecoveryFocus.machine slots SourceAssemblyParityPrep.machine
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 137→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (SourceAssemblyLiteralRefs.input a r ci C) (fun _ : Fin 46=>[])
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  SourceAssemblyPairSupport.budget a r ci C+1+SourceAssemblyParityPrep.budget r.arity

theorem arity_eq (q : Nat) : UnaryTemplate.tape q=UWalkUnary.source (q+2) q := by
  simp [UnaryTemplate.tape,UWalkUnary.source,ZeroPadding.pad,CompareMachine.word]

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (fun _=>0) A ∧
      A 3=ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (SourceAssemblyLiteralSupport.value a r (index ((a.output r).clauses ci).left)) ∧
      A 4=ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (SourceAssemblyLiteralSupport.value a r (index ((a.output r).clauses ci).right)) ∧
      A 131=frame (natWord r.arity) ∧A 133=List.replicate (Capacity.value r.arity) false ∧
      A 135=CompareMachine.word r.arity ∧A 101=List.replicate (Capacity.value r.arity) true ∧
      A 13=UnaryTemplate.tape r.arity := by
  obtain ⟨A,ha,h3,h4,cache⟩:=SourceAssemblyPairSupport.run a r ci C hc
  let bank : Fin 137→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 46=>[])
  have stepA : Step first (SourceAssemblyPairSupport.budget a r ci C)
      (fun _=>0) (input a r ci C) (fun _=>0) bank :=
    ((ha.embed (fun _ : Fin 46=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl).congr
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have arity : A 13=UWalkUnary.source (r.arity+2) r.arity := by
    have h:=cache 13 (by decide) (by decide)
    exact h.trans (arity_eq r.arity)
  obtain ⟨B,hb,b0,b41,b43,b45,b11⟩:=SourceAssemblyParityPrep.run r.arity
  have selected : ∀ i,bank (slots i)=SourceAssemblyParityPrep.input r.arity i := by
    intro i
    by_cases hi:i=0
    · subst i;exact arity
    · have he : slots i=(⟨i.val-1,by omega⟩ : Fin 46).natAdd 91 := by
        apply Fin.ext;simp [slots,hi];omega
      rw [he]
      simp only [bank,Fin.addCases_right,SourceAssemblyParityPrep.input,hi,if_false]
  obtain ⟨s,hs,st,sh,ss⟩:=hb.focus slots slots_inj bank selected
  have stepB : Step last (SourceAssemblyParityPrep.budget r.arity)
      (fun _=>0) bank (fun _=>0) (install slots bank B):=⟨s,hs,funext sh,st,ss⟩
  refine ⟨install slots bank B,stepA.seq stepB,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other slots bank B 3 (by decide)).trans h3
  · exact (install_other slots bank B 4 (by decide)).trans h4
  · exact (install_slot slots slots_inj bank B 41).trans b41
  · exact (install_slot slots slots_inj bank B 43).trans b43
  · exact (install_slot slots slots_inj bank B 45).trans b45
  · exact (install_slot slots slots_inj bank B 11).trans b11
  · exact (install_slot slots slots_inj bank B 0).trans (b0.trans (arity_eq r.arity).symm)

end
end SourceAssemblyParityQuery
