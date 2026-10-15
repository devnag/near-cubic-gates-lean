import Proof.CaseAnalysis.CaseTwoParityMeaning
import Proof.PCP.PCPPQueryCachedReaders

/-! One actual SAME-cache support read followed by the physical masked
parity scan. The source-derived capacity stays on the mask buffer; it is
neither erased nor recopied before its q actual bits are consumed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SystematicBit
open LocalBitMultitape RepairRepresentation SourceInterfaces RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def supportSlots (i : Fin 9) : Fin 13:=i.castAdd 4
def paritySlots : Fin 5→Fin 13:=![9,4,10,11,12]
def support:=RecoveryFocus.machine supportSlots PCPPQuerySupportReuse.machine
def parity:=RecoveryFocus.machine paritySlots Parity.machine
def machine:=Composition.machine support parity
def maskPads (C : ℕ) (i : Fin 5):=if i=1 then C else 0
theorem padded_parity {n : ℕ} (S : Finset (Fin n)) (u : BitInput n) (C : ℕ) : ∃ out,
    ClockJoin.ReadyRun Parity.machine (2*n+6)
      ![List.replicate n true,ZeroPadding.pad C (List.ofFn fun i : Fin n=>decide (i∈S)),List.ofFn u,[],[]] out ∧
      out 3=[parityOn S u]:=by
  obtain ⟨out,⟨base,hb,bt,bh,bs⟩,b3⟩:=Parity.systematic_run S u
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config Parity.machine (maskPads C) _ _ base hb
  have hi:ZeroPadding.config (maskPads C)
      (initialConfiguration Parity.machine
        ![List.replicate n true,List.ofFn (fun i : Fin n=>decide (i∈S)),List.ofFn u,[],[]])=
      initialConfiguration Parity.machine
        ![List.replicate n true,ZeroPadding.pad C (List.ofFn fun i : Fin n=>decide (i∈S)),List.ofFn u,[],[]]:=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;>simp [ZeroPadding.config,maskPads,initialConfiguration,ZeroPadding.pad_zero]
  rw [hi] at hr
  refine ⟨_,⟨r,hr,rfl,?_,rs.trans_le bs⟩,?_⟩
  · intro i;rw [rf];exact bh i
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 3)=_
    rw [ZeroPadding.pad_zero,bt]
    exact b3

def data (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : ℕ) : Fin 13→List Bool:=
  Fin.addCases (m:=9) (n:=4)
    (PCPPQuerySupportReuse.data (pcppOutput r (a.output r)) r.arity index
      (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [])
    ![List.replicate r.arity true,List.ofFn u,[],[]]
def heads : Fin 13→ℕ:=Fin.addCases (m:=9) (n:=4) PCPPQuerySupportReuse.heads (fun _=>0)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity):=
  PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+1+(2*r.arity+6)

theorem bit_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (i : Fin (a.output r).systematicBits) : ∃ result,
    runFrom machine (budget a r) ⟨machine.start,heads,data a r u i.val⟩=some result ∧
      result.steps≤budget a r ∧ result.final.tapes 11=[parityOn ((a.output r).systematicSupport i) u]:=by
  obtain ⟨base,hb,bt,bh,bs⟩:=PCPPQueryCachedBounds.support_run a r i
  rw [PCPPQuerySupportReuse.entry_literal] at hb
  obtain ⟨first,hfirst,_,fs,fh,ft,keep⟩:=RecoveryFocus.dock supportSlots
    (by intro j k he;apply Fin.ext;exact congrArg (fun x : Fin 13=>x.val) he)
    PCPPQuerySupportReuse.machine _ heads (data a r u i.val) _
    (by intro j;exact Fin.addCases_left j) (by intro j;exact Fin.addCases_left j) base hb
  obtain ⟨out,hp,pbit⟩:=padded_parity ((a.output r).systematicSupport i) u
    (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
  obtain ⟨last,hl,lh,lt,ls⟩:=hp.focus_at paritySlots (by decide) first.final.heads first.final.tapes
    (by intro j;fin_cases j
        · exact (keep 9 (by decide)).2
        · have h:=ft 4;rw [bt] at h;exact h
        · exact (keep 10 (by decide)).2
        · exact (keep 11 (by decide)).2
        · exact (keep 12 (by decide)).2)
    (by intro j;fin_cases j
        · exact (keep 9 (by decide)).1
        · have h:=fh 4;rw [bh] at h;exact h
        · exact (keep 10 (by decide)).1
        · exact (keep 11 (by decide)).1
        · exact (keep 12 (by decide)).1)
  have whole:=Composition.run_join support parity _ _ _ first last hfirst hl
  refine ⟨_,whole,?_,?_⟩
  · change first.steps+1+last.steps≤_
    rw [fs]
    unfold budget
    omega
  · change last.final.tapes (paritySlots 3)=_
    rw [lt]
    exact (install_slot paritySlots (by decide) _ out 3).trans pbit

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SystematicBit
