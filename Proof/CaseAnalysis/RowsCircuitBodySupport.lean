import Proof.CaseAnalysis.RowsCircuitBody
import Proof.CaseAnalysis.RowsCircuitTailSupport

/-! The complete post-top circuit body exports exactly the private support
bound required by the successful outer reset, on its same actual receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBody
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsCircuit CloseoutRowsCircuitBottomDock CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem body_support (threshold : Bool) (C core retained : ℕ) (words : List (List Bool))
    (top out members : List Bool) (initial L W : ℕ) (A : Fin 1703 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1 ≤ C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4 ≤ C)
    (hinit : threshold=true → 1 ≤ initial)
    (hc : 32*(descriptions core words initial words.length+words.length+
      wires threshold core 1 members words 0 words.length+3) ≤ C)
    (hsource : (words.flatMap frame).length ≤ C ∧ 1+2*words.length ≤ C)
    (hn : retained ≤ C) (hheader : EquationHeaderAppend.budget retained+1 ≤ C)
    (hbits : 2*top.length+1 ≤ C)
    (small : ∀ j,(A (CloseoutRowsCircuitAllocate.gate j)).length ≤ C)
    (hdriver : A 1694=List.replicate C true) (hlog : A 1695=List.replicate (C+1) false)
    (hretained : A 1702=ZeroPadding.pad C (List.replicate retained true))
    (htop : A 1701=ZeroPadding.pad C (frame top)) (hnative : A 1688=out)
    (hscratch : A 1696=List.replicate C false) (hcount : A 624=UnaryTemplate.tape words.length)
    (fields : ∀ i : Fin 7,A (![1689,1690,297,1692,1693,1697,1674] i)=
      (![List.replicate initial true,[],words.flatMap frame,members,[true],ZeroPadding.pad C [true],UnaryTemplate.tape core] : Fin 7 → List Bool) i)
    (hnraw : A 622=List.replicate words.length true)
    (hL : A 1699=List.replicate L true) (hW : A 1698=List.replicate W true) (hflag : A 1700=[])
    (hmember : members.length ≤ C+1)
    (initialSupport : ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (A i).length ≤ C+1) : ∃ r,
    runFrom (machine threshold) (budget threshold C retained top (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W)
      ⟨(machine threshold).start,CloseoutRowsCircuitBottomEntry.heads threshold out initial 0,A⟩=some r ∧
    r.steps ≤ budget threshold C retained top (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W ∧
    r.final.heads=CloseoutRowsCircuitColdEntry.heads
      ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) ∧
    (readTapeBit (r.final.tapes 1700) 0=true ↔ validity core true words words.length=true ∧
      CloseoutRowsCircuitArithmeticDock.amount threshold (descriptions core words initial words.length) words.length ≤ L ∧
      wires threshold core 1 members words 0 words.length ≤ W) ∧
    r.final.tapes 1688=(out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words) ∧
    r.final.tapes 1674=UnaryTemplate.tape core ∧ r.final.tapes 1694=List.replicate C true ∧
    r.final.tapes 1698=A 1698 ∧ r.final.tapes 1699=A 1699 ∧ r.final.tapes 1=A 1 ∧
    ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (r.final.tapes i).length ≤ C+1 :=by
  obtain ⟨r,hr,rs,rh,verdict,native,domain,driver,capW,capL,raw,mid,mt,mkeep,kept,small⟩:=
    body_run threshold C core retained words top out members initial L W A hin hcap hinit hc hsource
      hn hheader hbits small hdriver hlog hretained htop hnative hscratch hcount fields hnraw hL hW hflag
  refine ⟨r,hr,rs,rh,verdict,native,domain,driver,capW,capL,raw,?_⟩
  exact CloseoutRowsCircuitTailSupport.final_support C core words.length
    ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words))
    (words.flatMap frame) members (descriptions core words initial words.length)
    (wires threshold core 1 members words 0 words.length) (validity core true words words.length)
    A mid r.final.tapes (by omega) (by omega) (by omega) hsource.1 hmember (by omega)
    mt mkeep kept small hflag initialSupport

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBody
