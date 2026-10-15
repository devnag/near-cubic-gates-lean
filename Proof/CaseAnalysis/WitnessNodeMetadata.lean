import Proof.CaseAnalysis.WitnessNodeBankPrepare

/-! The retained hierarchy arity bits and input-derived unary width produce
the four literal node-bank fields. Existing scalar normalization supplies
both framed bounds, and fixed finite control prints the tag width three. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeMetadata
open LocalBitMultitape RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def printSlots : Fin 2→Fin 11:=![9,10]
def aritySlots : Fin 5→Fin 11:=![0,1,2,3,4]
def zeroSlots : Fin 5→Fin 11:=![0,5,6,7,8]
def fieldSlots : Fin 4→Fin 11:=![9,0,2,6]
def input (w : ℕ) (bits : List Bool) : Fin 11→List Bool:=
  ![List.replicate w true,frame bits,[],[],[],[],[],[],[],[],[]]
def printed (w : ℕ) (bits : List Bool) : Fin 11→List Bool:=
  ![List.replicate w true,frame bits,[],[],[],[],[],[],[],List.replicate 3 true,List.replicate 3 false]
def scalarOutput (w : ℕ) (bits : List Bool) : Fin 5→List Bool:=
  ![List.replicate w true,frame bits,frame (binary w (value bits)),[true],List.replicate (2*w+1) false]
noncomputable def arityDone (w : ℕ) (bits : List Bool):=
  install aritySlots (printed w bits) (scalarOutput w bits)
noncomputable def print:=RecoveryFocus.machine printSlots (HierarchyFixedWord.machine (List.replicate 3 true))
noncomputable def arity:=RecoveryFocus.machine aritySlots ClockNormalize.machine
noncomputable def zero:=RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def initial:=Composition.machine print arity
noncomputable def machine:=Composition.machine initial zero

theorem print_ready (w : ℕ) (bits : List Bool) :
    ClockJoin.ReadyRun print 8 (input w bits) (printed w bits):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=HierarchyFixedWord.word_ready (List.replicate 3 true)
  have hp:ClockJoin.ReadyRun (HierarchyFixedWord.machine (List.replicate 3 true)) 8
      (fun _=>[]) ![List.replicate 3 true,List.replicate 3 false]:=
    ⟨r,hr,ht,hh,hs.le⟩
  have h:=hp.focus printSlots (by decide) (input w bits) (by intro i;fin_cases i <;> rfl)
  have he:install printSlots (input w bits) ![List.replicate 3 true,List.replicate 3 false]=printed w bits:=by
    apply HierarchyAllocation.install_eq _ (by decide)
    · intro i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp [input,printed]
      · exact False.elim (hi 0 rfl)
      · exact False.elim (hi 1 rfl)
  rw [he] at h
  exact h

theorem scalar_ready (w : ℕ) (bits : List Bool) (hb : bits.length≤w) :
    ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockNormalize.input w bits) (scalarOutput w bits):=by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩:=ClockScalarFields.scalar_run w bits hb
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem arity_ready (w : ℕ) (bits : List Bool) (hb : bits.length≤w) :
    ClockJoin.ReadyRun arity (4*w+4) (printed w bits) (arityDone w bits):=
  (scalar_ready w bits hb).focus aritySlots (by decide) (printed w bits)
    (by intro i;fin_cases i <;> rfl)

theorem zero_input (w : ℕ) (bits : List Bool) :
    ∀ i,arityDone w bits (zeroSlots i)=ClockScalarFields.zeroInput w i:=by
  intro i
  fin_cases i
  · change install aritySlots _ _ (aritySlots 0)=_
    rw [install_slot _ (by decide)]
    rfl
  all_goals
    rw [arityDone,install_other _ _ _ _ (by decide)]
    rfl

theorem metadata_run (w : ℕ) (bits : List Bool) (hb : bits.length≤w) :
    ∃ out,ClockJoin.ReadyRun machine (8*w+18) (input w bits) out ∧
      (∀ j,out (fieldSlots j)=NodeGuard.shared w (binary w (value bits)) (binary w 0) j):=by
  obtain ⟨z,hz,z0,_,z2,_,_,zh,zs⟩:=ClockScalarFields.zero_run w
  have hzero:ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockScalarFields.zeroInput w) z.final.tapes:=
    ⟨z,hz,rfl,zh,zs.le⟩
  have h1:=ClockJoin.join print arity _ _ _ _ _ (print_ready w bits) (arity_ready w bits hb)
  have h2:=hzero.focus zeroSlots (by decide) (arityDone w bits) (zero_input w bits)
  have h:=ClockJoin.join initial zero _ _ _ _ _ h1 h2
  have he:8+1+(4*w+4)+1+(4*w+4)=8*w+18:=by omega
  rw [he] at h
  refine ⟨_,h,?_⟩
  intro j
  fin_cases j
  · change install zeroSlots (arityDone w bits) z.final.tapes 9=_
    rw [install_other _ _ _ _ (by decide),arityDone,install_other _ _ _ _ (by decide)]
    rfl
  · change install zeroSlots _ _ (zeroSlots 0)=_
    rw [install_slot _ (by decide)]
    exact z0
  · change install zeroSlots (arityDone w bits) z.final.tapes 2=_
    rw [install_other _ _ _ _ (by decide)]
    change install aritySlots _ _ (aritySlots 2)=_
    rw [install_slot _ (by decide)]
    rfl
  · change install zeroSlots _ _ (zeroSlots 2)=_
    rw [install_slot _ (by decide)]
    exact z2

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeMetadata
