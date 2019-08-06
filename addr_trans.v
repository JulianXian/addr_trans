(* *********************************************************************)
(*                                                                     *)
(*              Coq model of an address translation algorithm          *)
(*          based on Memory Management Unit of PowerPC e200 CPU        *)
(*                                                                     *)
(*               Julian Zhu   (zlponline@163.com)                      *)
(*                                                                     *)
(*  This file is distributed  under the terms of the GNU General       *)
(*  Public License as published by the Free Software Foundation        *)
(*                                                                     *)
(* *********************************************************************)


Require Import BinNums. (* Definition of Z, from Coq   *)
Require Import String. (* Definition of string, from Coq  *)
Require Import HexString. (* Defition of HexString, from 8.9 Coq   *)
Require Import ZArith. (* omega tactic *)

Add LoadPath "lib_from_compcert".
Require Import Integers. (* Definition of int,  from Compcert   *)


Definition MyHex (s: string) : int :=
     Int.repr (HexString.to_Z s).


Definition low_u (n: int) := Int.and n (Int.repr 65535).
Definition high_u (n: int) := Int.shru n (Int.repr 16).

Definition another_low_u (n: int) := Int.and n (MyHex "FFFF").


Definition get_pn_from_epn (n: int) := Int.shru n (Int.repr 6). (* Shift 6 bits *)
Definition get_pn_from_ea  (n: int) := Int.and (Int.shru n (Int.repr 16)) (Int.repr 65535). (*  Get high 16  *)
Definition get_offset_from_ea  (n: int) :=  Int.and n (Int.repr 65535). (* Get low 16  *)
Definition make_up_two_16 (m: int) (n: int) :int := Int.or (Int.shl m (Int.repr 16))  n.

Record CPUContext: Type := mk_cpucontext { MSR_PR: bool; 
                                   MSR_IS: bool; 
                                   MSR_DS: bool;
                                   PID: int }.
								   
(* TLB is Translation Lookaside Buffer, TLBE is an entry of TLB  *)								   
Record  TLBEntry: Type := mk_tlbe {
	V: bool; 
	TS:bool;
	TID:int;
	EPN:int;
	RPN:int;
	SIZE:int;
	SX:bool;
	SW:bool;
	SR:bool;
	UX:bool;
	UW:bool;
	UR:bool;
	W:bool;
	I:bool;
	M:bool;
	G:bool;
	E:bool;
	U0:bool;
	U1:bool;
	U2:bool;
	U3:bool;
	IPROT:bool;
	VLE:bool }.


Inductive TLB : Type :=
   | empty : TLB 
   | record : TLBEntry -> TLB -> TLB.

Definition insert  (entry : TLBEntry) (buf : TLB) : TLB :=
   (record entry buf).


Inductive tlbe_option : Type :=
   | Some : TLBEntry -> tlbe_option
   | None : tlbe_option.

Notation "x || y" := (orb x y).
Notation "x && y" := (andb x y). (* Got error with  bool_scope  *)

Fixpoint find_tlbe (cxt : CPUContext) (ea : int) (b : TLB)  : tlbe_option := 
   match b with 
   | empty => None
   | record tlbe b' => if (V tlbe)
                        && (negb (xorb (MSR_DS cxt)  (TS tlbe))) 
                        && (Int.eq (PID cxt) (TID tlbe) || Int.eq (PID cxt) Int.zero)
                        && (Int.eq (get_pn_from_epn (EPN tlbe)) (get_pn_from_ea ea)  )
                        then (Some tlbe)
                        else (find_tlbe cxt ea b')
   end.

(*  storage-class data access as an example *)
Definition grant_access (cxt : CPUContext) (tlbe : TLBEntry) : bool :=
    if ((MSR_PR cxt) && (UW tlbe))
       || ( negb(MSR_PR cxt) && (SW tlbe) )  
    then true
    else false.  


Definition grant_access2 (cxt : CPUContext) (tlbeo : tlbe_option) : bool :=
     match tlbeo with
     | None => false 
     | Some tlbe =>  
           if ((MSR_PR cxt) && (UW tlbe))
            || ( negb(MSR_PR cxt) && (SW tlbe) )  
           then true
           else false
     end.  

Definition addr_translate (tlbe:TLBEntry) (ea:int) : int :=
   make_up_two_16 (get_pn_from_epn (RPN tlbe)) (get_offset_from_ea ea).

Definition addr_translate2 (tlbeo : tlbe_option) (ea:int) : int :=
     match tlbeo with
     | None => Int.zero 
     | Some tlbe => make_up_two_16 (get_pn_from_epn (RPN tlbe)) (get_offset_from_ea ea) 
     end.  



Definition tlbe0 := mk_tlbe 
        true   
	false (* 0: privileged *)
	(Int.repr 255)
	(Int.repr 1048576) (* 0x4000<<6 *)
	(Int.repr 1048576) (* 0x4000<<6 *)
	(Int.repr 6)
	false (* SX SW SR UX UW UR *)
	true   (* OS write permitted *)
	false
	false
	false  (* APP write forbidden *)
	false
	false (* WIMGE *)
	false
	false
	false
	false
	false (* U0 *)
	false
	false
	false
	false (* IPROT *)
	false (* VLE *).


Definition tlbe1 := mk_tlbe 
        true   
	true (* 1: unprivileged *)
	(Int.repr 1)
	(Int.repr 1048832) (* 0x4004<<6 *)
	(Int.repr 1048832) (* 0x4004<<6 *)
	(Int.repr 6)
	false (* SX SW SR UX UW UR *)
	true  (* OS write permitted *)
	false
	false
	true (* APP write permitted *)
	false
	false (* WIMGE *)
	false
	false
	false
	false
	false (* U0 *)
	false
	false
	false
	false (* IPROT *)
	false (* VLE *).

Definition tlbe2 := mk_tlbe 
        true   
	true (* 1: unprivileged *)
	(Int.repr 2)
	(Int.repr 1048896) (* 0x4005<<6 *)
	(Int.repr 1048896) (* 0x4005<<6 *)
	(Int.repr 6)
	false (* SX SW SR UX UW UR *)
	true  (* OS write permitted *)
	false
	false
	true  (* APP write permitted *)
	false
	false (* WIMGE *)
	false
	false
	false
	false
	false (* U0 *)
	false
	false
	false
	false (* IPROT *)
	false (* VLE *).


Definition TLB1 := insert tlbe2 ( (insert tlbe1 (insert tlbe0 empty) ) ).



Definition CPUContextOS := mk_cpucontext false false false (Int.repr 255).

Definition CPUContextAPP1 := mk_cpucontext true true true (Int.repr 1).

Definition CPUContextAPP2 := mk_cpucontext true true true (Int.repr 2).


(*  privileged access  *)

Remark os_tlbe0_grant : grant_access  CPUContextOS tlbe0 = true.
Proof.
trivial.
Qed.

Remark os_tlbe1_grant : grant_access  CPUContextOS tlbe1 = true.
Proof.
trivial.
Qed.


Remark os_tlbe2_grant : grant_access  CPUContextOS tlbe2 = true.
Proof.
trivial.
Qed.

(*  unprivileged access  *)
Remark app1_tlbe0_deny : grant_access  CPUContextAPP1 tlbe0 = false.
Proof.
trivial.
Qed.


Remark app1_tlbe1_grant : grant_access  CPUContextAPP1 tlbe1 = true.
Proof.
trivial.
Qed.

Remark app1_tlbe2_grant : grant_access  CPUContextAPP1 tlbe2 = true.
Proof.
trivial.
Qed.


Remark app2_tlbe0_deny : grant_access  CPUContextAPP2 tlbe0 = false.
Proof.
trivial.
Qed.


Remark app2_tlbe1_grant : grant_access  CPUContextAPP2 tlbe1 = true.
Proof.
trivial.
Qed.

Remark app2_tlbe2_grant : grant_access  CPUContextAPP2 tlbe2 = true.
Proof.
trivial.
Qed.

Definition ea_in_range (ea : int) : Prop :=  Int.lt ea (MyHex "FFFFFFFF") = true. 

Definition ea_in_os_range (ea : int) : Prop :=  (Int.lt  (MyHex "3fffffff") ea  && Int.lt ea (MyHex "40010000") ) = true. 


Definition access_granted (cxt : CPUContext) (tlbeo : tlbe_option) : Prop := grant_access2 cxt tlbeo = true.

Definition tlb_hit  (tlbeo : tlbe_option) : Prop := tlbeo <> None.

Definition addr_tranlate_ok (tlbeo : tlbe_option) (ea : int) : Prop := (addr_translate2 tlbeo ea) = ea.


Definition  find_tlbe_none_empty (cxt : CPUContext) (ea : int) (b : TLB) : Prop := find_tlbe cxt ea b <> None.

Lemma os_access_tlbe_always_hit :
             forall (ea : int), 
             ea_in_os_range ea ->  find_tlbe_none_empty CPUContextOS ea TLB1.
Proof.
intros ea H H'.
simpl in H'.
simpl in H.
unfold ea_in_os_range in H.
unfold get_pn_from_epn in H'.
unfold get_pn_from_ea in H'.
simpl in H'.
unfold MyHex in H.

change (Int.eq (Int.repr 255) (Int.repr 255)) with true in H'. simpl in H'.
change (Int.shru (Int.repr 1048576) (Int.repr 6)) with (Int.repr 16384) in H'. simpl in H'.

assert (Int.lt (Int.repr (to_Z "3fffffff")) ea && Int.lt ea (Int.repr (to_Z "40010000")) = true -> Int.eq (Int.repr 16384) (Int.and (Int.shru ea (Int.repr 16)) (Int.repr 65535)) = true ).


(* To be done *)
Abort.

(* Goal: For any 32 bits effective address, if the tlb search indicate that there is valid tlb entry,then access is granted, and  the translated address is the same as the original one  *)


Lemma os_access_ok :
    forall (ea : int), 
           ea_in_range ea ->
            let tlbe := find_tlbe CPUContextOS ea TLB1 in  ( tlb_hit tlbe  
           -> access_granted  CPUContextOS  tlbe
           -> addr_tranlate_ok tlbe ea  ) .


Proof.
(* To be done *)
Abort.


