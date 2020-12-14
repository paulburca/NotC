Require Import Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Lists.List.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num :  nat -> ErrorNat.

Inductive ErrorInt :=
  | error_int : ErrorInt
  | nr : Z -> ErrorInt.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString :=
  | error_string : ErrorString
  | strval : string -> ErrorString.


Coercion boolean: bool >-> ErrorBool.
Coercion nr : Z >-> ErrorInt.
Coercion num : nat >-> ErrorNat.
Notation "string( S )" := (strval S).
Notation "nat( N )" := (num N).
Notation "int( I )" := (nr I).
Notation "bool( B )" := (boolean B).

Inductive Val :=
| undecl: Val
| unassign: Val
| default: Val
| number: ErrorNat -> Val
| integer : ErrorInt -> Val
| bol: ErrorBool -> Val
| str: ErrorString -> Val
| vector: vect -> Val
| ptr: string -> Val
with vect :=
| error_vect: vect
| vector_int : nat -> list ErrorInt -> vect
| vector_nat : nat -> list ErrorNat -> vect
| vector_bool : nat -> list ErrorBool -> vect
| vector_str : nat -> list ErrorString -> vect
.

Coercion number: ErrorNat >-> Val.
Coercion integer: ErrorInt >-> Val.
Coercion bol: ErrorBool >-> Val.
Coercion str : ErrorString >-> Val.

Definition Env := string -> Val.
Definition env_loc : Env := fun x => undecl.
Definition env_globe : Env := fun x => undecl.

Compute env_loc "x".

Inductive AExp :=
| avar: string -> AExp
| anum: ErrorNat -> AExp
| aint: ErrorInt -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp
| adiv: AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp
| apow: AExp -> AExp -> AExp.

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
Notation "strcmp( A ; B )" := (strcmp A B) (at level 52).

Inductive STREXP := 
| svar : ErrorString -> STREXP
| sconst: string -> STREXP
| strcat : ErrorString -> ErrorString -> STREXP
| strcpy : ErrorString -> ErrorString -> STREXP
.

Notation "strcat( A , B )" := (strcat A B)(at level 52).
Notation "strcpy( A , B )" := (strcat A B)(at level 52).

Coercion svar: ErrorString >-> STREXP.
Coercion sconst: string >-> STREXP.

Inductive func := 
| funcMain : Stmt -> func
| funcs : string -> list string -> Stmt -> func
with Stmt :=
| def_nat : string -> AExp ->Stmt
| def_bool : string -> BExp -> Stmt
| def_int : string -> AExp -> Stmt
| def_string : string -> STREXP -> Stmt
| def_vector : string -> vect -> Stmt
| get_vval : vect -> nat -> Stmt
| assignment : string -> AExp -> Stmt
| bassignment : string -> BExp -> Stmt
| sassignment : string -> STREXP -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| dowhile : Stmt -> BExp -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt ->Stmt
| forcontent : BExp -> Stmt -> Stmt -> Stmt
| get_func : string -> list string -> Stmt
| break : Stmt
| continue  : Stmt
| switch: AExp -> list cases -> Stmt
| to_nat: Val -> Stmt
| to_int: Val -> Stmt
| to_bool: Val -> Stmt
| to_string: Val -> Stmt
| read: string -> Stmt
| write: STREXP -> Stmt
with cases:=
| def: Stmt -> cases
| basic : nat -> Stmt -> cases.

Inductive Lang :=
| functions : func -> Lang 
| gdecl_int : string -> ErrorInt -> Lang
| gdecl_nat : string -> ErrorNat -> Lang
| gdecl_str : string -> ErrorString -> Lang
| gdecl_bool : string -> ErrorBool -> Lang
.


Notation "X ::= A" := (assignment X A ) (at level 50).
Notation "X :b:= A" := (bassignment X A ) (at level 50).
Notation "X :s:= A" := (sassignment X A ) (at level 50).
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
Notation "'switch'' ( A ) : { B1 B2 .. Bn }" := (switch A (cons B1 (cons B2 .. (cons Bn nil) ..))) (at level 93).
Notation "'(int)' { A }" := (to_int A)( at level 35).
Notation "'(nat)' { A }" := (to_nat A)( at level 35).
Notation "'(bool)' { A }" := (to_bool A)( at level 35).
Notation "'(string)' { A }" := (to_string A)( at level 35).
Notation "'func'' main():{ C } 'end''" := (funcMain C )(at level 20).
Notation "'func'' A (( B1 ; B2 ; .. ; Bn )):{ C } 'end''" := (funcs A (cons B1 (cons B2 .. (cons Bn nil) ..)) C )(at level 20).
Notation "'->' A (( B1 ; B2 ; .. ; Bn )) " := (get_func A (cons B1 (cons B2 .. (cons Bn nil) ..)))(at level 20).
Notation "A [ B ]i={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_int B (cons int(C1) (cons int(C2) .. (cons int(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]n={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_nat B (cons nat(C1) (cons nat(C2) .. (cons nat(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]b={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_bool B (cons bool(C1) (cons bool(C2) .. (cons bool(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]s={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_str B (cons string(C1) (cons string(C2) .. (cons string(Cn) nil) ..) ) ) )(at level 50).

Compute switch' (5) : {case (1): {If(1=='1) then {nat "AA" := 7} else {int "BB" := 7} end'} case(2): {If(1=='1) then {int "CC":= 13}end'} default : {bool "3" := true}}.
Compute "ASD" [50]i={ -1 ; 2 ; -3 }.
Compute "ASD"[50]n={ 1 ; 2 ; 3 }.
Compute "ASD"[50]b={ true ; false ; true }.
Compute "ASD"[50]s={ "1" ; "2" ; "3" }.
Compute func' main():{ If( 1=='1) then { "x" ::= 3 } end' } end'.
Compute func' "test" (( "text1" ; "text2" )):{ If ( 1 ==' 1 ) then { "text1" :s:= string( "test" ) } end' } end'.
Compute func' "test" (( "text1" ; "text2" )):{ If ( 1 ==' 1 ) then { -> "test" (( "text1" ; "text2" )) } end'} end'.





