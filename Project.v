Require Import Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Lists.List.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorInt :=
  | error_int : ErrorInt
  | nr : Z -> ErrorInt.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString :=
  | error_string : ErrorString
  | strval : string -> ErrorString.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Coercion nr : Z >-> ErrorInt.
Notation "string( S )" := (strval S).

Inductive Val :=
| undecl: Val
| unassign: Val
| default: Val
| number: ErrorNat -> Val
| integer : ErrorInt -> Val
| bool: ErrorBool -> Val
| str: string -> Val
.

Scheme Equality for Val.
Definition Env := string -> Val.
Definition env : Env := fun x => undecl.
Compute env "x".


Inductive AExp :=
| avar: string -> AExp
| anum: ErrorNat -> AExp
| aint: ErrorInt -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp
| adiv: AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp
| apow: AExp -> AExp -> AExp
.

Coercion anum : ErrorNat >-> AExp.
Coercion avar : string >-> AExp.
Coercion aint : ErrorInt >-> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (asub A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).
Notation "A ^' B" := (apow A B) (at level 46).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| bval : ErrorBool -> BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bgreaterthan: AExp -> AExp -> BExp
| bor : BExp -> BExp -> BExp
| bxor : BExp -> BExp -> BExp
| bxand : BExp -> BExp -> BExp
| strcmp : string -> string -> BExp
| blet : AExp -> AExp -> BExp
| bget : AExp -> AExp -> BExp
| beq : AExp -> AExp -> BExp
| bneq : AExp -> AExp -> BExp
.

Coercion bvar: string >-> BExp.
Coercion bval: ErrorBool >-> BExp.


Notation "A <' B" := (blessthan A B) (at level 53).
Notation "A >' B" := (bgreaterthan A B) (at level 53).
Notation "A <=' B" := (blet A B) (at level 53).
Notation "A >=' B" := (bget A B) (at level 53).
Notation "` A " := (bnot A) (at level 40).
Notation "A &&' B" := (band A B) (at level 55).
Notation "A ||' B" := (bor A B) (at level 55).
Notation "A 'xor'' B" := (bxor A B) (at level 55).
Notation "A 'xand'' B" := (bxand A B) (at level 55).
Notation "A ==' B" := (beq A B) (at level 53).
Notation "A !=' B" := (bneq A B) (at level 53).

Inductive STREXP := 
| sval : ErrorString -> STREXP
| strcat : ErrorString -> ErrorString -> STREXP
| strcpy : ErrorString -> ErrorString -> STREXP
| snat : ErrorString -> STREXP.

Coercion sval: ErrorString >-> STREXP.

Inductive Stmt :=
| def_nat : string -> AExp ->Stmt
| def_bool : string -> BExp -> Stmt
| def_int : string -> AExp -> Stmt
| def_string : string -> ErrorString -> Stmt
| assignment : string -> AExp -> Stmt
| bassignment : string -> BExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| dowhile : Stmt -> BExp -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt ->Stmt
| forcontent : BExp -> Stmt -> Stmt -> Stmt
| switch: AExp -> list cases -> Stmt
with cases:=
| def: Stmt -> cases
| basic : nat -> Stmt -> cases.


Inductive func := 
| funcMain : Stmt -> func
| funcs : string -> list string -> Stmt -> func.

Notation "X ::= A" := (assignment X A ) (at level 50).
Notation "X :b:= A" := (bassignment X A ) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 92).
Notation "'If' ( C ) 'then' { A } 'else' { B } 'end''" := (ifthenelse C A B) (at level 59).
Notation "'If' ( C ) 'then' { A } 'end''" := (ifthen C A) (at level 59).
Notation "'while'' ( A ) { B } " := (while A B) (at level 91).
Notation "'do' { A } 'while' ( B )" := (dowhile A B) (at level 91).
Notation "'for' ( A ; B ; C ) { D }" := (For A B C D) (at level 91).
Notation "'nat' A := B" := (def_nat A B)(at level 50).
Notation "'bool' A := B" := (def_bool A B)(at level 50).
Notation "'int' A := B" := (def_int A B)(at level 50).
Notation "'string' A := B" := (def_string A B)(at level 50).
Notation "'default' : { A }" := (def A) (at level 92).
Notation "'case' ( A ) : { B }" := (basic A B) (at level 92).
Notation "'switch'' ( A ) : { B } " := (switch A (cons B nil)) (at level 93).
Notation "'switch'' ( A ) : { B1 B2 .. Bn  }" := (switch A (cons B1 (cons B2 .. (cons Bn nil) ..))) (at level 93).

Notation "'func' A ( B1 B2 .. Bn ) { C }" := (func A (cons B1 (cons B2 .. (cons Bn nil) ..)) C )(at level 20).

Compute switch' (5):{case (1): {If(1=='1) then {nat "AA" := 7} else {int "BB" := 7} end'} case(2): {If(1=='1) then {int "CC":= 13}end'} default : {bool "3" := true}}.
Compute func "test" ("text1" "text2"){ If(1=='1)then{"text1" ::= String("test")}end'}.

