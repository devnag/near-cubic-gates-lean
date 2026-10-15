import Proof.Hierarchy.CompetitorFinalTableOdd

/-! One actual controller: merge P/N, read the retained parity, execute
full signed residue and, precisely in the odd case, the paid zero slice. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFinalTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneTable CompetitorOddRowSlice
open CompetitorPlaneStream (oldWords)
open SourceInterfaces WilliamsProductCertificate WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : ℕ} (_ : Machine t s) := s
noncomputable def sizes : Fin 3 → ℕ := ![stateCount mergeProgram,stateCount (residueProgram false),stateCount oddProgram]
noncomputable def programs : (j : Fin 3) → Machine 159 (sizes j)
  | ⟨0,_⟩ => mergeProgram
  | ⟨1,_⟩ => residueProgram false
  | ⟨2,_⟩ => oddProgram
  | ⟨n+3,h⟩ => False.elim (by omega)
noncomputable def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 159 → Bool) : Option (Fin 3) :=
  if j=0 then if bits 38 then some 2 else some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (u w q : ℕ) := CompetitorBankMergeDock.budget w (u*u)+oddBudget u w q+2

theorem table_run {u : ℕ} (b w q pos : ℕ) (odd : Bool)
    (cross same : State (u*u)) (f : Fin u → Fin u → ℕ) (ambient : Fin 159 → List Bool)
    (hc : Native b w cross ambient) (h35 : ambient 35=oldWords w (canonical same))
    (h36 : ambient 36=List.replicate q true) (h37 : ambient 37=UnaryTemplate.tape u) (h38 : ambient 38=[odd])
    (fresh : ∀ i : Fin 159,39 ≤ i.val → ambient i=[])
    (hq : q≤w) (he : odd=true → u/2+u/2=u)
    (hfit : ∀ i,cross.positive i+same.positive i<2^w ∧ cross.negative i+same.negative i<2^w)
    (hcount : ∀ i : Fin (u*u),f i.divNat i.modNat<2^q)
    (hcongruent : ∀ i : Fin (u*u),Int.ModEq ((2:ℤ)^q)
      (((cross.positive i+same.positive i:ℕ):ℤ)-((cross.negative i+same.negative i:ℕ):ℤ)) (f i.divNat i.modNat)) :
    ∃ r,runFrom machine (budget u w q) (RecoveryCalls.restarted machine (heads pos) ambient)=some r ∧
      r.steps≤budget u w q ∧ r.final.heads=heads pos ∧ r.final.tapes 141=word q odd f ∧
      Native b w (CompetitorBankMergeDock.stateAdd cross same) r.final.tapes ∧
      (∀ i : Fin 39,i≠19 → r.final.tapes (i.castAdd 120)=ambient (i.castAdd 120)) := by
  let summed := CompetitorBankMergeDock.stateAdd cross same
  have hsfit : ∀ i,summed.positive i<2^w ∧ summed.negative i<2^w := hfit
  have hsemantic := residue_counts w q summed f hq hsfit hcount hcongruent
  obtain ⟨first,hfirst,_,hfh,hcontext,hkeep,hfresh⟩ := merge_run b w pos cross same ambient hc h35 fresh hfit
  have qfield : first.final.tapes 36=List.replicate q true := (hkeep 36 (by decide)).trans h36
  have ufield : first.final.tapes 37=UnaryTemplate.tape u := (hkeep 37 (by decide)).trans h37
  have flag : first.final.scanned 38=odd := by
    simp only [Configuration.scanned,hfh,heads]
    have ht : first.final.tapes 38=[odd] := (hkeep 38 (by decide)).trans h38
    rw [ht]
    rfl
  have close (j : Fin 3) (fuel : ℕ) (last : ExecutionReceipt 159 (sizes j))
      (hj : j≠0) (hbranch : next 0 first.final.control first.final.scanned=some j)
      (hlast : runFrom (programs j) fuel (RecoveryCalls.restarted (programs j) (heads pos) first.final.tapes)=some last)
      (hbound : fuel≤oddBudget u w q) (hlh : last.final.heads=heads pos)
      (hout : last.final.tapes 141=word q odd f)
      (hlkeep : ∀ i : Fin 39,last.final.tapes (i.castAdd 120)=first.final.tapes (i.castAdd 120)) :
      ∃ r,runFrom machine (budget u w q) (RecoveryCalls.restarted machine (heads pos) ambient)=some r ∧
        r.steps≤budget u w q ∧ r.final.heads=heads pos ∧ r.final.tapes 141=word q odd f ∧
        Native b w summed r.final.tapes ∧
        (∀ i : Fin 39,i≠19 → r.final.tapes (i.castAdd 120)=ambient (i.castAdd 120)) := by
    obtain ⟨t0,h0,path0⟩ := call_receipt sizes programs 0 next 0 j (CompetitorBankMergeDock.budget w (u*u))
      (RecoveryCalls.restarted (programs 0) (heads pos) ambient) first hfirst hbranch
    rw [hfh] at path0
    obtain ⟨t1,h1,path1⟩ := stop_receipt sizes programs 0 next j fuel
      (RecoveryCalls.restarted (programs j) (heads pos) first.final.tapes) last hlast (by simp [next,hj])
    have path := path0.trans path1
    obtain ⟨actual,ha,hf,hs⟩ := path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have ht : t0+t1≤budget u w q := by unfold budget; omega
    have ha' : runFrom machine (t0+t1) (RecoveryCalls.restarted machine (heads pos) ambient)=some actual := ha
    have hm := runFrom_moreFuel machine (t0+t1) (budget u w q-(t0+t1)) _ actual ha'
    rw [Nat.add_sub_of_le ht] at hm
    refine ⟨actual,hm,hs.le.trans ht,?_,?_,?_,?_⟩
    · rw [hf]; exact hlh
    · rw [hf]; exact hout
    · rw [hf]
      have heq : (fun i : Fin 34 => last.final.tapes (i.castAdd 125))=
          (fun i : Fin 34 => first.final.tapes (i.castAdd 125)) := by
        funext i
        exact hlkeep (i.castAdd 5)
      unfold Native
      change TableContext b w summed (fun i : Fin 34 => last.final.tapes (i.castAdd 125))
      rw [heq]
      exact hcontext
    · intro i hi
      rw [hf]
      exact (hlkeep i).trans (hkeep i hi)
  cases odd with
  | false =>
    obtain ⟨last,hl,_,hh,hout,hpres,_⟩ := residue_run b w q pos false summed first.final.tapes hcontext hq qfield hfresh hsfit
    exact close 1 _ last (by decide) (by simp [next,flag]) hl (by unfold oddBudget; omega) hh
      (hout.trans hsemantic) hpres
  | true =>
    obtain ⟨last,hl,_,hh,hout,hpres⟩ := odd_run b w q pos summed f (he rfl) first.final.tapes
      hcontext hq qfield ufield hfresh hsfit hsemantic
    exact close 2 _ last (by decide) (by simp [next,flag]) hl (by rfl) hh hout hpres

end NearCubicWires.RepairOrdinary.CompetitorFinalTable
