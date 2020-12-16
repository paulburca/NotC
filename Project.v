Require Import Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Lists.List.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Inductive NatType :=
  | error_nat : NatType
  | num :  nat -> NatType.

Inductive IntType :=
  | error_int : IntType
  | nr : Z -> IntType.

Inductive BoolType :=
  | error_bool : BoolType
  | boolean : bool -> BoolType.

Inductive StringType :=
  | error_string : StringType
  | strval : string -> StringType.

Coercion boolean: bool >-> BoolType.
Coercion nr : Z >-> IntType.
Coercion num : nat >-> NatType.
Notation "string( S )" := (strval S).
Notation "nat( N )" := (num N).
Notation "int( I )" := (nr I).
Notation "bool( B )" := (boolean B).


Inductive STREXP := 
| svar : string -> STREXP
| sconst: StringType -> STREXP
| strcat : STREXP -> STREXP -> STREXP
| to_string : string -> STREXP.

Notation "strcat( A , B )" := (strcat A B)(at level 52).
Notation "strcpy( A , B )" := (strcat A B)(at level 52).

Coercion sconst: StringType >-> STREXP.
Coercion svar: string >-> STREXP.

Inductive AExp :=
| avar: string -> AExp
| anum: NatType -> AExp
| aint: IntType -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp
| adiv: AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp
| apow: AExp -> AExp -> AExp
| to_nat: string -> AExp 
| to_int: string -> AExp
| strlen: STREXP -> AExp.

Coercion anum : NatType >-> AExp.
Coercion avar : string >-> AExp.
Coercion aint : IntType >-> AExp.

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
| bval : BoolType -> BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bgreaterthan: AExp -> AExp -> BExp
| bor : BExp -> BExp -> BExp
| bxor : BExp -> BExp -> BExp
| bxand : BExp -> BExp -> BExp
| strcmp : STREXP -> STREXP -> BExp
| blet : AExp -> AExp -> BExp
| bget : AExp -> AExp -> BExp
| beq : AExp -> AExp -> BExp
| bneq : AExp -> AExp -> BExp
| to_bool : string -> BExp.

Coercion bvar: string >-> BExp.
Coercion bval: BoolType >-> BExp.

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

Inductive vect :=
| error_vect: vect
| vector_int : nat -> list IntType -> vect
| vector_nat : nat -> list NatType -> vect
| vector_bool : nat -> list BoolType -> vect
| vector_str : nat -> list StringType -> vect.

Inductive Stmt :=
| def_nat : string -> AExp ->Stmt
| def_bool : string -> BExp -> Stmt
| def_int : string -> AExp -> Stmt
| def_string : string -> STREXP -> Stmt
| def_nat0 : string ->Stmt
| def_bool0 : string -> Stmt
| def_int0 : string  -> Stmt
| def_string0 : string -> Stmt
| def_vector : string -> vect -> Stmt
| get_vval : string -> nat -> Stmt
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
| read: string -> Stmt
| write: STREXP -> Stmt
| strcpy : string -> string -> Stmt
with cases:=
| def: Stmt -> cases
| case : nat -> Stmt -> cases.

Inductive Val :=
| undecl: Val
| unassign: Val
| default: Val
| number: NatType -> Val
| integer : IntType -> Val
| bol: BoolType -> Val
| str: StringType -> Val
| vector: vect -> Val
| code: Stmt -> Val.

Coercion number: NatType >-> Val.
Coercion integer: IntType >-> Val.
Coercion bol: BoolType >-> Val.
Coercion str : StringType >-> Val.
Coercion code: Stmt >-> Val.

Definition Env := string -> Val.
Definition env_loc : Env := fun x => undecl.
Definition env_globe : Env := fun x => undecl.

Compute env_loc "x".
Inductive Lang := 
| funcMain : Stmt -> Lang
| funcs : string -> list string -> Stmt -> Lang
| gdecl_int : string -> IntType -> Lang
| gdecl_nat : string -> NatType -> Lang
| gdecl_str : string -> StringType -> Lang
| gdecl_bool : string -> BoolType -> Lang
| gdecl_int0 : string -> Lang
| gdecl_nat0 : string -> Lang
| gdecl_str0 : string -> Lang
| gdecl_bool0 : string -> Lang
| secv : Lang -> Lang-> Lang
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
Notation "'nat' A |" := (def_nat0 A )(at level 50).
Notation "'bool' A |" := (def_bool0 A )(at level 50).
Notation "'int' A |" := (def_int0 A )(at level 50).
Notation "'string' A |" := (def_string0 A )(at level 50).
Notation "'nat'' A := B \" := (gdecl_nat A B)(at level 97).
Notation "'bool'' A := B \" := (gdecl_bool A B)(at level 97).
Notation "'int'' A := B \" := (gdecl_int A B)(at level 97).
Notation "'string'' A := B \" := (gdecl_str A B)(at level 97).
Notation "'nat'' A \" := (gdecl_nat0 A )(at level 97).
Notation "'bool'' A \" := (gdecl_bool0 A )(at level 97).
Notation "'int'' A \" := (gdecl_int0 A)(at level 97).
Notation "'string'' A \" := (gdecl_str0 A )(at level 97).

Notation "'default' : { A }" := (def A) (at level 92).
Notation "'case' ( A ) : { B }" := (case A B) (at level 92).
Notation "'switch'' ( A ) : { B } " := (switch A (cons B nil)) (at level 93).
Notation "'switch'' ( A ) : { B1 ; B2 ; .. ; Bn }" := (switch A (cons B1 (cons B2 .. (cons Bn nil) ..))) (at level 93).
Notation "'(int)' { A }" := (to_int A)( at level 35).
Notation "'(nat)' { A }" := (to_nat A)( at level 35).
Notation "'(bool)' { A }" := (to_bool A)( at level 35).
Notation "'(string)' { A }" := (to_string A)( at level 35).
Notation "'func'' main():{ C }" := (funcMain C )(at level 97).
Notation "'func'' A (( B1 ; B2 ; .. ; Bn )):{ C }" := (funcs A (cons B1 (cons B2 .. (cons Bn nil) ..)) C )(at level 97).
Notation "'func'' A (( B )):{ C }" := (funcs A (cons B nil) C )(at level 97).
Notation "'func'' A (()):{ C }" := (funcs A C )(at level 97).
Notation "A '|'' B" := (secv A B)(at level 96).
Notation "'->' A (( B1 ; B2 ; .. ; Bn )) " := (get_func A (cons B1 (cons B2 .. (cons Bn nil) ..)))(at level 91).
Notation "A [ B ]i={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_int B (cons int(C1) (cons int(C2) .. (cons int(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]n={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_nat B (cons nat(C1) (cons nat(C2) .. (cons nat(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]b={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_bool B (cons bool(C1) (cons bool(C2) .. (cons bool(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]s={ C1 ; C2 ; .. ; Cn }" := ( def_vector A ( vector_str B (cons string(C1) (cons string(C2) .. (cons string(Cn) nil) ..) ) ) )(at level 50).
Notation "A [ B ]i" := ( def_vector A ( vector_int B nil ) )(at level 50).
Notation "A [ B ]n" := ( def_vector A ( vector_nat B nil ) )(at level 50).
Notation "A [ B ]b" := ( def_vector A ( vector_bool B nil ) )(at level 50).
Notation "A [ B ]s" := ( def_vector A ( vector_str B nil ) )(at level 50).

Notation "A [ B ]" :=(get_vval A B)(at level 50).

Compute switch' (5) : {case (1): {If(1=='1) then {nat "AA" := 7} else {int "BB" := 7} end'} ; case(2): {If(1=='1) then {int "CC":= 13}end'} ; default : {bool "3" := true}}.
Compute "ASD" [50]i={ -1 ; 2 ; -3 }.
Compute "ASD"[50]n={ 1 ; 2 ; 3 }.
Compute "ASD"[50]b={ true ; false ; true }.
Compute "ASD"[50]s={ "1" ; "2" ; "3" }.
Compute "ASD"[50]n.
Compute "ASD"[50].
Compute func' main():{ If( 1=='1) then { "x" ::= 3 } end' }.
Compute func' "test" (( "text1" )):{
           If ( 1 ==' 1 ) then 
              { "text1" :s:= string( "test" ) } end' ;; } .
Compute func' "test" (( "text1" ; "text2" )):{
          If ( 1 ==' 1 ) then 
            { -> "test" (( "text1" ; "text2" )) 
            } end' 
          } |' 
          int' "x" \ |' 
          func' main():{ 
          If( 1=='1) then 
            { "x" ::= 3 }
            end'
          }.





