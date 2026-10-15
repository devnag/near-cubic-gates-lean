import Proof.CaseAnalysis.WitnessPairHeader
import Proof.CaseAnalysis.WitnessNat
import Proof.CaseAnalysis.RowsCanonicalFlag

/-! The same sum's tagged pair, canonical arity and balanced term list are
read once. The field stream and actual count survive for the term loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumFields
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def headerSlots (i : Fin 149) : Fin 501:=i.castAdd 352
def aritySlots (i : Fin 178) : Fin 501:=
  ⟨if i.val=0 then 38 else 149+i.val,by split_ifs <;> omega⟩
def listSlots (i : Fin 174) : Fin 501:=
  ⟨if i.val=0 then 78 else 327+i.val,by split_ifs <;> omega⟩
def header:=RecoveryFocus.machine headerSlots PairHeader.machine
def arity:=RecoveryFocus.machine aritySlots NatCold.machine
def terms:=RecoveryFocus.machine listSlots CanonicalTest.machine
def prime : Machine 501 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=0 then some false else none,fun _=>.stay⟩ else none
def first:=Composition.machine prime header
def prefixMachine:=Composition.machine first arity
def machine:=Composition.machine prefixMachine terms
def input (bits : List Bool) (i : Fin 501):=if i.val=1 then frame bits else []
def primed (bits : List Bool):=Function.update (input bits) 0 [false]
def arityCode (bits : List Bool):=PairHeader.codeWord bits 0
def listCode (bits : List Bool):=PairHeader.codeWord bits 1
def payload (bits : List Bool):=BitFields.payload (arityCode bits)
def atoms (bits : List Bool):=(tree (value (listCode bits))).atoms
def count (bits : List Bool):=(atoms bits).length
def budget (bits : List Bool):=1+1+PairHeader.budget bits+1+NatCold.budget (arityCode bits)+1+
  CanonicalTest.budget (listCode bits)

theorem prime_ready (bits : List Bool) : ClockJoin.ReadyRun prime 1 (input bits) (primed bits):=by
  let final:Configuration 501 2:=⟨1,fun _=>0,primed bits⟩
  have hs:step prime (initialConfiguration prime (input bits))=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=0
      · subst i
        simp [applyAction,initialConfiguration,prime,final,primed,input,writeTapeBit]
      · simp [applyAction,initialConfiguration,prime,final,primed,hi]
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],ht.le⟩

theorem header_injective : Function.Injective headerSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 501=>k.val) h)
theorem arity_injective : Function.Injective aritySlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 501=>k.val) h
  dsimp only [aritySlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem list_injective : Function.Injective listSlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 501=>k.val) h
  dsimp only [listSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem arity_outside (i : Fin 501) (hi : i.val≠38 ∧ (i.val<149 ∨ 327 ≤ i.val)) :
    ∀ j,aritySlots j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 501=>k.val) h
  have hj:=j.isLt
  dsimp only [aritySlots] at hv
  split_ifs at hv <;> omega
theorem list_outside (i : Fin 501) (hi : i.val≠78 ∧ i.val ≤ 327) :
    ∀ j,listSlots j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 501=>k.val) h
  dsimp only [listSlots] at hv
  split_ifs at hv <;> omega

theorem fields_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      output 323=frame (payload bits) ∧
      output 357=atomStream (listCode bits).length (atoms bits) ∧
      output 368=CompareMachine.word (count bits) ∧
      output 499=[CloseoutRowsCanonicalFlag.flag (listCode bits)] ∧
      (readTapeBit (output 148) 0=true ↔ PairHeader.valid bits) ∧
      (readTapeBit (output 324) 0=true ↔
        (CanonicalBinary.decodeNat (value (arityCode bits))).isSome) ∧
      (readTapeBit (output 324) 0=true→
        CanonicalBinary.decodeNat (value (arityCode bits))=some (value (payload bits))):=by
  obtain ⟨hh,hflag,ha,hl⟩:=PairHeader.header_run bits
  have hhf:=hh.focus headerSlots header_injective (primed bits) (by
    refine Fin.addCases (m:=148) (n:=1) ?_ ?_
    · intro i
      rw [PairHeader.input,Fin.addCases_left,CompetitorWitnessHeader.input_eq]
      by_cases h0:i.val=0
      · have he:i=0:=Fin.ext h0
        subst i
        rfl
      · have he:headerSlots (i.castAdd 1)≠0:=by
          intro h;have hv:=congrArg Fin.val h;exact h0 hv
        rw [primed,Function.update_of_ne he,if_neg h0]
        rfl
    · intro i;fin_cases i;rfl)
  let hbank:=install headerSlots (primed bits) (PairHeader.output bits)
  have hold (i : Fin 149) : hbank (headerSlots i)=PairHeader.output bits i:=
    install_slot _ header_injective _ _ _
  have hfresh (i : Fin 501) (hi : 149 ≤ i.val) : hbank i=[]:=by
    rw [show hbank=install headerSlots _ _ by rfl,install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg (fun k : Fin 501=>k.val) h
      change j.val=i.val at hv
      omega)]
    simp only [primed,Function.update_of_ne (show i≠0 by intro h;subst i;omega),input,
      if_neg (show i.val≠1 by omega)]
  obtain ⟨a,har,ap,_,af,ad⟩:=NatCold.nat_run (arityCode bits)
  have haf:=har.focus aritySlots arity_injective hbank (by
    intro i
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0
      rw [he]
      exact (hold 38).trans ha
    have hn:∀ j : Fin 178,j.val≠0→NatCold.input (arityCode bits) j=[]:=by
      refine Fin.addCases (m:=174) (n:=4) ?_ ?_
      · intro j hj
        change j.val≠0 at hj
        rw [NatCold.input,Fin.addCases_left]
        simp only [CanonicalTest.input,if_neg hj]
      · intro j _
        rw [NatCold.input,Fin.addCases_right]
    have he:=hn i h0
    rw [he]
    exact hfresh _ (by simp only [aritySlots,if_neg h0];omega))
  let abank:=install aritySlots hbank a
  have aold (i : Fin 178) : abank (aritySlots i)=a i:=install_slot _ arity_injective _ _ _
  have akeep (i : Fin 501) (hi : i.val≠38 ∧ (i.val<149 ∨ 327 ≤ i.val)) : abank i=hbank i:=
    install_other _ _ _ _ (arity_outside i hi)
  obtain ⟨c,hc,cs,cn,_⟩:=CanonicalTest.fields_run (listCode bits)
  obtain ⟨cf,_⟩:=CloseoutRowsCanonicalFlag.retained (listCode bits) c hc
  have hcf:=hc.focus listSlots list_injective abank (by
    intro i
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0
      rw [he]
      rw [akeep _ ⟨by decide,Or.inl (by decide)⟩]
      exact (hold 78).trans hl
    rw [CanonicalTest.input,if_neg h0]
    rw [akeep _ ⟨by simp only [listSlots,if_neg h0];omega,
      Or.inr (by simp only [listSlots,if_neg h0];omega)⟩]
    exact hfresh _ (by simp only [listSlots,if_neg h0];omega))
  have keep (i : Fin 501) (hi : i.val≠78 ∧ i.val ≤ 327) : install listSlots abank c i=abank i:=
    install_other _ _ _ _ (list_outside i hi)
  have kp:install listSlots abank c 323=frame (payload bits):=by
    rw [keep _ ⟨by decide,by decide⟩]
    exact (aold 174).trans ap
  have kh:install listSlots abank c 148=PairHeader.output bits 148:=by
    rw [keep _ ⟨by decide,by decide⟩,akeep _ ⟨by decide,Or.inl (by decide)⟩]
    exact hold 148
  have kn:install listSlots abank c 324=a 175:=by
    rw [keep _ ⟨by decide,by decide⟩]
    exact aold 175
  refine ⟨_,ClockJoin.join prefixMachine terms _ _ _ _ _
    (ClockJoin.join first arity _ _ _ _ _
      (ClockJoin.join prime header _ _ _ _ _ (prime_ready bits) hhf) haf) hcf,kp,?_,?_,?_,?_,?_,?_⟩
  · exact (install_slot listSlots list_injective _ c 30).trans cs
  · exact (install_slot listSlots list_injective _ c 41).trans cn
  · exact (install_slot listSlots list_injective _ c 172).trans cf
  · rw [kh];exact hflag
  · rw [kn];exact af
  · rw [kn];exact ad

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumFields
